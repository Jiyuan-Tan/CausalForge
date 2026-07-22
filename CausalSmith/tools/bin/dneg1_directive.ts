#!/usr/bin/env -S npx tsx
/**
 * Orchestrator-only: inject a standalone DIRECTIVE into the D-1.2 escalation log so
 * the next proposal draft (cold-start / revise / pivot / kernel-replace /
 * draft-rebuild) acts on it — WITHOUT hand-appending to
 * `discovery/dneg1_escalation_log.jsonl`. Mirrors the `d0_directive` channel for
 * the discovery-proposal stage.
 *
 * Use when the D-1.2 proposer needs a concrete steer the automatic Stage 0.5
 * rejection context does not carry: a literature-grounded reframe, a donor/witness
 * to anchor the kernel to, or a recurring drift the reviewer keeps flagging that a
 * plain revise round isn't fixing. The entry is appended as `{version, directive}`
 * and rendered verbatim as `[vN] DIRECTIVE: …` in the proposer's prompt context.
 *
 * `version` is taken from the current `proposed_from.current_version` (the version
 * the NEXT draft will produce), matching `d0_directive`'s round semantics.
 *
 * Usage:
 *   npx tsx tools/bin/dneg1_directive.ts <qid> <spec> --directive "<direction / reframe>"
 *   npx tsx tools/bin/dneg1_directive.ts <qid> <spec> --directive -        # read from stdin
 *   npx tsx tools/bin/dneg1_directive.ts <qid> <spec> --directive "…" --note "<short note>"
 */
import { existsSync, readFileSync } from "node:fs";
import path from "node:path";
import process from "node:process";
import type { PipelineContext } from "../src/types.js";
import { sanitizeDirectiveForCli } from "../src/shared/directive_text.js";
import { appendNeg1EscalationLog } from "../src/discovery/stageNeg1_directive.js";
import { loadState } from "../src/state.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { readArgs } from "../src/shared/cli_args.js";



async function main(): Promise<void> {
  const args = process.argv.slice(2);
  const cli = readArgs(args);
  let directive = cli.value("--directive");
  const note = cli.value("--note");
  const positional = args.filter((a, i) => !a.startsWith("--") && !args[i - 1]?.startsWith("--"));
  const [qid, spec] = positional;
  if (!qid || !spec || directive === undefined) {
    console.error('Usage: dneg1_directive.ts <qid> <spec> --directive "<direction>" [--note "<note>"]  (--directive - reads stdin)');
    process.exitCode = 1;
    return;
  }
  // `--directive -` reads the (often multi-line) direction from stdin.
  if (directive === "-") directive = readFileSync(0, "utf8").trim();
  // why: strip/refuse broken consult captures before they reach the draft prompt.
  const text = sanitizeDirectiveForCli(directive ?? "", args.includes("--allow-dirty-capture"));
  if (text === null) {
    process.exitCode = 1;
    return;
  }

  const repoRoot = findCausalSmithRoot(process.cwd());
  const ctx: PipelineContext = { repoRoot, qid, specialization: spec, dryRun: false, resume: true };
  const state = await loadState(repoRoot, qid, spec);
  const version = state.proposed_from?.current_version ?? 0;
  await appendNeg1EscalationLog(ctx, { version, ...(note ? { note } : {}), directive: text });
  console.log(
    `Appended a D-1.2 directive (v${version}) for ${qid} / ${spec}. ` +
      `--resume (or --from-stage -1.2) re-enters D-1.2 and the next draft renders it as an escalation directive.`,
  );
}

main().catch((e) => {
  console.error(e);
  process.exitCode = 1;
});
