#!/usr/bin/env node
/**
 * One-shot Stage 0.5 reviewer test against an existing .tex artifact with
 * novelty_target = "field". Does NOT mutate state or re-run Stage 0; only
 * dispatches the reviewer once and prints the JSON verdict to stdout.
 *
 * Usage:
 *   npx tsx tools/bin/oneshot_stage0_5_field.ts <qid> <specialization>
 */
import { existsSync, readFileSync } from "node:fs";
import { readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import { artifactPaths, baseBrief, readPrompt } from "../src/pipeline_support.js";
import { tierFloorBlock } from "../src/pipeline_stages.js";
import { runCodex } from "../src/workers/codex.js";
import { loadState } from "../src/state.js";
import { MODEL_PLAN } from "../src/constants.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";


async function main() {
  const rawArgs = process.argv.slice(2);
  const noteIdx = rawArgs.indexOf("--note");
  const notePath = noteIdx >= 0 ? rawArgs[noteIdx + 1] : undefined;
  const [qid, spec] = rawArgs.filter((a, i) => i !== noteIdx && i !== noteIdx + 1 && !a.startsWith("--"));
  if (!qid || !spec) {
    console.error("Usage: oneshot_stage0_5_field.ts <qid> <specialization> [--note <path>]");
    process.exit(1);
  }
  const repoRoot = findCausalSmithRoot(process.cwd());
  const state = await loadState(repoRoot, qid, spec);
  const ctx = {
    repoRoot,
    qid,
    specialization: spec,
    dryRun: false,
    resume: true,
    noveltyTarget: "field" as const,
  };
  const paths = artifactPaths(ctx, state);
  const tex = notePath ? await readFile(notePath, "utf8") : await readFile(paths.tex, "utf8");
  const promptHeader = await readPrompt(ctx, "stage0_5_review.txt");
  const prompt = [
    promptHeader,
    "",
    baseBrief(ctx, state),
    "",
    "novelty_target: field",
    "Review the TeX derivation. Report only.",
    "",
    tierFloorBlock("field"),
    `TeX:\n${tex}`,
    "",
    "Lean files are under the Lean artifact directory; read them as needed.",
    "RETURN ONLY ReviewResult JSON.",
  ].join("\n");

  const out = await runCodex({
    prompt,
    cwd: repoRoot,
    model: MODEL_PLAN.stage0_5.model,
    reasoningEffort: MODEL_PLAN.stage0_5.effort,
    inactivityTimeoutMs: 40 * 60 * 1000,
  });
  const stamp = new Date().toISOString();
  const outFile = path.join(
    path.dirname(paths.tex),
    `${qid}_${spec}_oneshot_stage0_5_field_${stamp.replace(/[:.]/g, "-")}.txt`,
  );
  await writeFile(outFile, out.stdout, "utf8");
  console.log(`# raw output written to: ${outFile}`);
  console.log("# --- stdout ---");
  console.log(out.stdout);
}

main().catch((err) => {
  console.error(err instanceof Error ? err.stack ?? err.message : String(err));
  process.exit(1);
});
