#!/usr/bin/env -S npx tsx
/**
 * Orchestrator-only: inject (or clear) a PERSISTENT scaffold-faithfulness directive for
 * the F2 scaffolder. Sets `state.flags.f2_scaffold_directive`, which `runStage2` reads on
 * every scaffold/revise pass and injects verbatim as a top-priority constraint on top of
 * the .md spec (loop-wide + persistent, mirroring F3's `f3_filler_directive` channel).
 *
 * Use when the F2.5 faithfulness loop keeps escalating a STATEMENT-SHAPE drift the scaffolder
 * re-introduces every pass (an over-assumed premise the note DERIVES; a universal constant
 * quantified after the model parameters; a missing mechanical domain hypothesis; a weakened
 * conclusion). Unlike `scaffold_redirect` — which is one-shot, capped at 2 attempts, review-loop
 * driven, and self-clears — this directive PERSISTS across resumes and steers EVERY F2 pass
 * until you clear it, so a fix cannot be silently reverted by the next re-scaffold.
 *
 * It is a faithfulness/statement-SHAPE steer ONLY — the F2.5 review + anti-laundering + assumption
 * gates still reject any use that INVENTS a hypothesis the spec does not state or WEAKENS a
 * statement. To hand the proof-fill loop a PROOF hint, use `f3_directive.ts`; to change the note
 * itself, rewind (fix-source / redo-math).
 *
 * Clear it once the drift is resolved so it does not bias later unrelated scaffolds.
 *
 * Usage:
 *   npx tsx tools/bin/f2_directive.ts <qid> <spec> --directive "<faithfulness constraint>"
 *   npx tsx tools/bin/f2_directive.ts <qid> <spec> --append "<additional constraint>"
 *   npx tsx tools/bin/f2_directive.ts <qid> <spec> --directive -   # read directive from stdin
 *   npx tsx tools/bin/f2_directive.ts <qid> <spec> --clear         # remove the directive
 *   npx tsx tools/bin/f2_directive.ts <qid> <spec> --show          # print the current directive
 */
import { existsSync, readFileSync } from "node:fs";
import { sanitizeDirectiveForCli } from "../src/shared/directive_text.js";
import path from "node:path";
import process from "node:process";
import { loadState, saveState } from "../src/state.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { readArgs } from "../src/shared/cli_args.js";



async function main(): Promise<void> {
  const args = process.argv.slice(2);
  const cli = readArgs(args);
  const clear = args.includes("--clear");
  const show = args.includes("--show");
  let append = cli.value("--append");
  let directive = cli.value("--directive");
  const positional = args.filter((a, i) => !a.startsWith("--") && !args[i - 1]?.startsWith("--"));
  const [qid, spec] = positional;
  if (!qid || !spec || (!clear && !show && directive === undefined && append === undefined) ||
      (directive !== undefined && append !== undefined)) {
    console.error(
      'Usage: f2_directive.ts <qid> <spec> (--directive "<constraint>" | --directive - | --append "<constraint>" | --append - | --clear | --show)',
    );
    process.exitCode = 1;
    return;
  }
  // `--directive -` reads the (often multi-line) directive from stdin.
  if (directive === "-") directive = readFileSync(0, "utf8").trim();
  if (append === "-") append = readFileSync(0, "utf8").trim();

  const repoRoot = findCausalSmithRoot(process.cwd());
  const state = await loadState(repoRoot, qid, spec);

  if (show) {
    const cur = state.flags.f2_scaffold_directive;
    console.log(cur && cur.trim().length > 0 ? cur : "(no F2 scaffold directive set)");
    return;
  }
  if (clear) {
    state.flags.f2_scaffold_directive = null;
    await saveState(repoRoot, qid, spec, state);
    console.log(`Cleared f2_scaffold_directive for ${qid} / ${spec}.`);
    return;
  }
  // why: sanitize only the INCOMING text — an already-stored directive was cleaned
  // when it was set, and re-checking the concatenation would re-report its artifacts.
  const incoming = sanitizeDirectiveForCli(
    (append !== undefined ? append : directive) ?? "",
    args.includes("--allow-dirty-capture"),
  );
  if (incoming === null) {
    console.error("(use --clear to remove the directive instead of setting an empty one)");
    process.exitCode = 1;
    return;
  }
  const text = append !== undefined
    ? [state.flags.f2_scaffold_directive?.trim(), incoming].filter(Boolean).join("\n\n")
    : incoming;
  state.flags.f2_scaffold_directive = text;
  await saveState(repoRoot, qid, spec, state);
  console.log(
    `Set f2_scaffold_directive for ${qid} / ${spec} (${text.length} chars). ` +
      `Every F2 scaffold/revise pass applies it verbatim until you --clear it (persists across resumes).`,
  );
}

main().catch((e) => {
  console.error(e);
  process.exitCode = 1;
});
