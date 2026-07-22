#!/usr/bin/env node
/**
 * One-shot D0.5.1 MATH referee — the dedicated correctness leg (errors of
 * omission), run standalone against a candidate note. This is the rigorous
 * correctness check the pipeline runs FIRST and injects into D0.5.2; the
 * oneshot_stage0_5_field harness skips it (fallback correctness only), so use
 * this for pipeline-grade soundness on a D0.R round.
 *
 * Usage: npx tsx bin/oneshot_stage0_5_math.ts <qid> <spec> [--note <path>]
 */
import { existsSync, readFileSync } from "node:fs";
import { readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import { artifactPaths, baseBrief, readPrompt } from "../src/pipeline_support.js";
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
    console.error("Usage: oneshot_stage0_5_math.ts <qid> <spec> [--note <path>]");
    process.exit(1);
  }
  const repoRoot = findCausalSmithRoot(process.cwd());
  const state = await loadState(repoRoot, qid, spec);
  const ctx = { repoRoot, qid, specialization: spec, dryRun: false, resume: true, noveltyTarget: "field" as const };
  const paths = artifactPaths(ctx, state);
  const tex = notePath ? await readFile(notePath, "utf8") : await readFile(paths.tex, "utf8");

  const prompt = [
    await readPrompt(ctx, "stage0_5_math_review.txt"),
    "",
    baseBrief(ctx, state),
    "",
    `TeX (reproduce the derivation; hunt errors of omission):\n${tex}`,
    "",
    "RETURN ONLY the correctness-verdict JSON described above.",
  ].join("\n");

  console.error(`[oneshot D0.5.1 math] ${qid} ${spec}${notePath ? ` · note=${notePath}` : ""} · dispatching math referee…`);
  const out = await runCodex({
    prompt,
    cwd: repoRoot,
    model: MODEL_PLAN.stage0_5_math.model,
    reasoningEffort: MODEL_PLAN.stage0_5_math.effort,
    inactivityTimeoutMs: 40 * 60 * 1000,
  });
  const stamp = (notePath ? path.basename(notePath).replace(/\W+/g, "-") : "canonical");
  const outFile = path.join(path.dirname(paths.tex), `${qid}_${spec}_oneshot_math_${stamp}.txt`);
  await writeFile(outFile, out.stdout, "utf8");
  console.log(`# raw -> ${outFile}`);
  console.log(out.stdout);
}

main().catch((err) => {
  console.error(err instanceof Error ? err.stack ?? err.message : String(err));
  process.exit(1);
});
