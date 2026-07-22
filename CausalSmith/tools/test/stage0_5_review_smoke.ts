#!/usr/bin/env node
// Re-runs the Stage 0.5 reviewer against the current .tex with the corrected
// prompt (formalization-readiness no longer credited). Reviewer-only — no
// Stage 0 producer redo.
import { readFile } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { runCodex } from "../src/workers/codex.js";
import { MODEL_PLAN, REUSE_LIST } from "../src/constants.js";
import { extractJsonObject } from "../src/judgment.js";

const REPO = path.dirname(findCausalSmithRoot(path.dirname(fileURLToPath(import.meta.url))));
const QID = "panel_spectral_phase_transition";
const SPEC = "p1_markov";

async function main(): Promise<void> {
  const texFile = path.join(
    REPO,
    "CausalSmith/doc/research",
    QID,
    `${QID}_${SPEC}.tex`,
  );
  const stateFile = path.join(
    REPO,
    "CausalSmith/doc/research",
    QID,
    `${QID}_${SPEC}_state.json`,
  );
  const promptFile = path.join(REPO, "tools/src/discovery/prompts/stage0_5_review.txt");

  const [promptText, texSrc, stateRaw] = await Promise.all([
    readFile(promptFile, "utf8"),
    readFile(texFile, "utf8"),
    readFile(stateFile, "utf8"),
  ]);
  const state = JSON.parse(stateRaw) as {
    lean_subdir: string;
    design_decisions: Record<string, string>;
    added_assumptions: unknown;
  };

  const brief = [
    `Repository: ${REPO}`,
    `QID: ${QID}`,
    `Specialization: ${SPEC}`,
    `Lean target subdirectory: ${state.lean_subdir}`,
    `TeX artifact: ${texFile}`,
    `Reuse list: ${REUSE_LIST.join(", ")}`,
    `Design decisions: ${JSON.stringify(state.design_decisions, null, 2)}`,
    `Added assumptions: ${JSON.stringify(state.added_assumptions, null, 2)}`,
  ].join("\n");

  const prompt = [
    promptText,
    "",
    brief,
    "",
    "Review the TeX derivation. Report only.",
    "",
    `TeX:\n${texSrc}`,
    "",
    "Lean files are under the Lean artifact directory; read them as needed.",
    "RETURN ONLY ReviewResult JSON.",
  ].join("\n");

  console.log(`[smoke] dispatching corrected stage 0.5 reviewer (codex ${MODEL_PLAN.stage0_5.model} effort=${MODEL_PLAN.stage0_5.effort})`);
  const started = Date.now();
  const out = await runCodex({
    prompt,
    cwd: REPO,
    model: MODEL_PLAN.stage0_5.model,
    reasoningEffort: MODEL_PLAN.stage0_5.effort,
  });
  const ms = Date.now() - started;
  console.log(`[smoke] codex returned in ${(ms / 1000).toFixed(1)}s`);

  let json: unknown;
  try {
    json = extractJsonObject(out.stdout);
  } catch (err) {
    console.error(`[smoke] parse failed: ${err instanceof Error ? err.message : String(err)}`);
    console.error("[smoke] raw stdout tail:");
    console.error(out.stdout.slice(-2000));
    process.exit(1);
  }
  const review = json as Record<string, unknown>;
  console.log(`[smoke] status=${review.status}  classification=${review.classification ?? "(n/a)"}  tier_at_derivation=${review.tier_at_derivation ?? "(n/a)"}`);
  const dims = review.dimension_findings as Record<string, { verdict: string; notes: string }> | undefined;
  if (dims) {
    for (const [k, v] of Object.entries(dims)) {
      console.log(`  - ${k}: ${v.verdict}`);
    }
  }
  if (Array.isArray(review.journal_recommendations)) {
    console.log("Journal recommendations:");
    for (const j of review.journal_recommendations as Array<{ journal: string; tier: string }>) {
      console.log(`  - ${j.journal} | ${j.tier}`);
    }
  }
  console.log("\n=== FULL REVIEW JSON ===");
  console.log(JSON.stringify(review, null, 2));
}

main().catch((err) => {
  console.error(`[smoke] runCodex threw: ${err instanceof Error ? err.stack : String(err)}`);
  process.exit(1);
});
