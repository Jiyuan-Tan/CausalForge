#!/usr/bin/env -S npx tsx
/**
 * Orchestrator-only: set or inspect the one-shot F1 revision directive consumed by
 * runStage1. This exposes the existing `state.flags.f1_revise_directive` channel
 * without hand-editing state.json.
 *
 * Usage:
 *   npx tsx tools/bin/f1_directive.ts <qid> <spec> --directive "<revision>"
 *   npx tsx tools/bin/f1_directive.ts <qid> <spec> --directive -
 *   npx tsx tools/bin/f1_directive.ts <qid> <spec> --clear
 *   npx tsx tools/bin/f1_directive.ts <qid> <spec> --show
 */
import { readFileSync } from "node:fs";
import process from "node:process";
import { readArgs } from "../src/shared/cli_args.js";
import { sanitizeDirectiveForCli } from "../src/shared/directive_text.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { loadState, saveState } from "../src/state.js";

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
      'Usage: f1_directive.ts <qid> <spec> (--directive "<revision>" | --directive - | --clear | --show)',
    );
    process.exitCode = 1;
    return;
  }
  if (directive === "-") directive = readFileSync(0, "utf8").trim();

  const repoRoot = findCausalSmithRoot(process.cwd());
  const state = await loadState(repoRoot, qid, spec);
  if (show) {
    const current = state.flags.f1_revise_directive;
    console.log(current && current.trim().length > 0 ? current : "(no F1 revision directive set)");
    return;
  }
  if (clear) {
    state.flags.f1_revise_directive = null;
    await saveState(repoRoot, qid, spec, state);
    console.log(`Cleared f1_revise_directive for ${qid} / ${spec}.`);
    return;
  }
  const text = sanitizeDirectiveForCli(directive ?? "", args.includes("--allow-dirty-capture"));
  if (text === null) {
    console.error("Use --clear instead of setting an empty F1 revision directive.");
    process.exitCode = 1;
    return;
  }
  state.flags.f1_revise_directive = text;
  await saveState(repoRoot, qid, spec, state);
  console.log(`Set one-shot f1_revise_directive for ${qid} / ${spec} (${text.length} chars).`);
}

main().catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
