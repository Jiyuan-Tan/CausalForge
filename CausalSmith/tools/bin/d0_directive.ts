#!/usr/bin/env -S npx tsx
/**
 * Orchestrator-only: inject a standalone DIRECTIVE into the D0 escalation log so the
 * next D0 solve round acts on it — WITHOUT hand-appending to
 * `discovery/d0_escalation_log.jsonl`. Mirrors the `f2_directive` / `f3_directive`
 * channels for the discovery phase.
 *
 * Use when a D0 open_obligation (or a D0.5 finding routed back for re-derivation) needs
 * a concrete construction/recipe: consult the literature FIRST, then hand the solver the
 * extracted direction here. The entry is appended as `{round, changed: [], directive}` —
 * the same shape `d0_apply_change` writes for a standalone directive (no applied change) —
 * and the solver renders it as `[round N] DIRECTIVE: …` in its escalation context.
 *
 * `round` is taken from the current d0 working state (the round the next solve will use),
 * matching `d0_apply_change`'s behavior.
 *
 * Usage:
 *   npx tsx tools/bin/d0_directive.ts <qid> <spec> --directive "<direction / construction>"
 *   npx tsx tools/bin/d0_directive.ts <qid> <spec> --directive -        # read from stdin
 *   npx tsx tools/bin/d0_directive.ts <qid> <spec> --directive "…" --note "<short note>" --require-core-changes --require-core-target sym:len
 *
 * Capture artifacts (literal `null` lines from a mis-built `jq` pipe, a raw codex
 * event stream) are stripped or refused — see `src/shared/directive_text.ts`.
 * `--allow-dirty-capture` writes the text verbatim.
 */
import { existsSync, readFileSync } from "node:fs";
import path from "node:path";
import process from "node:process";
import type { PipelineContext } from "../src/types.js";
import { appendEscalationLog, loadWorkingState } from "../src/discovery/stages/d0_working.js";
import { sanitizeDirectiveForCli } from "../src/shared/directive_text.js";
import { loadState, saveState } from "../src/state.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { readArgs } from "../src/shared/cli_args.js";


async function main(): Promise<void> {
  const args = process.argv.slice(2);
  const cli = readArgs(args);
  let directive = cli.value("--directive");
  const note = cli.value("--note");
  const requireCoreChanges = cli.bool("--require-core-changes");
  const requiredCoreTargets = cli.values("--require-core-target");
  const [qid, spec] = cli.positionals();
  if (!qid || !spec || directive === undefined) {
    console.error('Usage: d0_directive.ts <qid> <spec> --directive "<direction>" [--note "<note>"] [--require-core-changes] [--require-core-target <id> ...]  (--directive - reads stdin)');
    process.exitCode = 1;
    return;
  }
  // `--directive -` reads the (often multi-line) direction from stdin.
  if (directive === "-") directive = readFileSync(0, "utf8").trim();
  // why: a broken capture (`jq -r` over a codex event stream) yields the agent's
  // reasoning interleaved with literal `null` lines, which used to be written to the
  // escalation log verbatim and re-sent to every solve unit. See directive_text.ts.
  const text = sanitizeDirectiveForCli(directive ?? "", args.includes("--allow-dirty-capture"));
  if (text === null) {
    process.exitCode = 1;
    return;
  }

  const repoRoot = findCausalSmithRoot(process.cwd());
  const ctx: PipelineContext = { repoRoot, qid, specialization: spec, dryRun: false, resume: true };
  const working = await loadWorkingState(ctx);
  const round = working?.round ?? 0;
  await appendEscalationLog(ctx, {
    round,
    changed: [],
    ...(note ? { note } : {}),
    directive: text,
    ...(requireCoreChanges ? { require_core_changes: true } : {}),
    ...(requiredCoreTargets.length > 0 ? { required_core_targets: requiredCoreTargets } : {}),
  });
  // Rewind the stage pointer, mirroring `stage0_apply.ts`'s pre-publish rewind.
  //
  // Without this there is a silent path into F1 on UNPROVEN mathematics: inject a
  // directive while stage_completed is "0.5" → resume routes to D0 via the pending
  // directive → the solve round comes back INCOMPLETE (advance:false, so the cursor is
  // never updated) but has already marked the entries consumed → the next resume sees no
  // pending directive, reads stage_completed "0.5", and dispatches F1 on a core still
  // carrying `status:"to-prove"` statements. That commits the entire F1-F5 arm to
  // undischarged math. Pinning the cursor at "-0.5" constrains every resume to D0 until
  // D0.5 genuinely passes.
  // Only a LOAD failure is benign (a bare fixture run has no state to rewind). A SAVE
  // failure is the disaster described above: the escalation row is already appended, so
  // reporting success leaves the operator believing the cursor was pinned to "-0.5" when
  // it still reads "0.5" -- and the next resume dispatches F1 over undischarged math.
  // The blanket catch swallowed both.
  let state: Awaited<ReturnType<typeof loadState>> | null = null;
  try {
    state = await loadState(repoRoot, qid, spec);
  } catch {
    state = null; // nothing to rewind
  }
  if (state && state.stage_completed !== "-0.5") {
    state.stage_completed = "-0.5";
    try {
      await saveState(repoRoot, qid, spec, state);
    } catch (err) {
      throw new Error(
        `d0_directive: the directive was APPENDED but the stage cursor could NOT be rewound to "-0.5" ` +
          `(${(err as Error).message}). Do not resume: the next resume would read the un-rewound stage and ` +
          `may dispatch F1 over undischarged math. Fix the state write, then re-run this command.`,
      );
    }
  }
  console.log(
    `Appended a D0 directive (round ${round}) for ${qid} / ${spec}. ` +
      `--resume re-enters D0 and the next solve renders it as an escalation directive.`,
  );
}

main().catch((e) => {
  console.error(e);
  process.exitCode = 1;
});
