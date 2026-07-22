#!/usr/bin/env -S npx tsx
/**
 * Orchestrator-only: inject (or clear) a load-bearing PROOF hint for the F3 phase-B
 * proof-fill loop. Sets `state.flags.f3_filler_directive`, which `runProofReviewLoop`
 * reads on `--resume` and injects verbatim into EVERY filler call for the rest of the
 * loop run (loop-wide + persistent, mirroring the D0 escalation-log directive channel).
 *
 * Use when the fill loop is stuck (filler-stuck / no-progress) and you can hand the
 * filler the missing step: a Mathlib lemma name, a tactic strategy, the right induction,
 * an existing Causalean helper to reuse. It is a PROOF hint ONLY — the per-iteration
 * anti-laundering + assumption/def gates still reject any use that weakens a statement,
 * adds an unsanctioned hypothesis, or axiomatizes a goal. To steer a STATEMENT change,
 * rewind (fix-source / redo-math), not this.
 *
 * The directive PERSISTS across resumes until you clear it (unlike the one-shot
 * correction directives). Clear it once the hint has landed so it doesn't bias later
 * unrelated fills.
 *
 * Usage:
 *   npx tsx tools/bin/f3_directive.ts <qid> <spec> --directive "<proof hint>"
 *   npx tsx tools/bin/f3_directive.ts <qid> <spec> --directive -        # read hint from stdin
 *   npx tsx tools/bin/f3_directive.ts <qid> <spec> --clear              # remove the directive
 *   npx tsx tools/bin/f3_directive.ts <qid> <spec> --show               # print the current directive
 */
import { existsSync, readFileSync } from "node:fs";
import path from "node:path";
import process from "node:process";
import { loadState, saveState } from "../src/state.js";
import { sanitizeDirectiveForCli } from "../src/shared/directive_text.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { readArgs } from "../src/shared/cli_args.js";



async function main(): Promise<void> {
  const args = process.argv.slice(2);
  const cli = readArgs(args);
  const clear = args.includes("--clear");
  const show = args.includes("--show");
  let directive = cli.value("--directive");
  const positional = args.filter((a, i) => !a.startsWith("--") && !args[i - 1]?.startsWith("--"));
  const [qid, spec] = positional;
  if (!qid || !spec || (!clear && !show && directive === undefined)) {
    console.error(
      'Usage: f3_directive.ts <qid> <spec> (--directive "<hint>" | --directive - | --clear | --show)',
    );
    process.exitCode = 1;
    return;
  }
  // `--directive -` reads the (often multi-line) hint from stdin.
  if (directive === "-") directive = readFileSync(0, "utf8").trim();

  const repoRoot = findCausalSmithRoot(process.cwd());
  const state = await loadState(repoRoot, qid, spec);

  if (show) {
    const cur = state.flags.f3_filler_directive;
    console.log(cur && cur.trim().length > 0 ? cur : "(no F3 filler directive set)");
    return;
  }
  if (clear) {
    state.flags.f3_filler_directive = null;
    await saveState(repoRoot, qid, spec, state);
    console.log(`Cleared f3_filler_directive for ${qid} / ${spec}.`);
    return;
  }
  // why: strip/refuse broken consult captures before they reach the F3 filler prompt.
  const text = sanitizeDirectiveForCli(directive ?? "", args.includes("--allow-dirty-capture"));
  if (text === null) {
    console.error("(use --clear to remove the directive instead of setting an empty one)");
    process.exitCode = 1;
    return;
  }
  state.flags.f3_filler_directive = text;
  await saveState(repoRoot, qid, spec, state);
  console.log(
    `Set f3_filler_directive for ${qid} / ${spec} (${text.length} chars). ` +
      `--resume re-enters the proof-review loop and the filler will apply it every iteration until you --clear it.`,
  );
}

main().catch((e) => {
  console.error(e);
  process.exitCode = 1;
});
