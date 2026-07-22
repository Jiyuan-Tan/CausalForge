#!/usr/bin/env node
// Smoke test for runIntervention: replays the two existing stage_0.5_to_0
// reviews on panel_spectral_phase_transition_p1_markov and verifies that the
// intervention judge returns a parseable route (or that the fallback fires
// cleanly on parse failure).
import { readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { runIntervention } from "../src/shared/intervention_routing.js";
import { runClaude } from "../src/workers/claude.js";
import { runCodex } from "../src/workers/codex.js";
import { createLeanLspClient } from "../src/workers/leanLsp.js";
import type { ReviewResult } from "../src/judgment.js";
import type { PipelineContext, StateJson } from "../src/types.js";

const REPO = path.dirname(findCausalSmithRoot(path.dirname(fileURLToPath(import.meta.url))));
const QID = "panel_spectral_phase_transition";
const SPEC = "p1_markov";

const reviewsPath = path.join(
  REPO,
  "CausalSmith/doc/research",
  QID,
  `${QID}_${SPEC}_reviews.jsonl`,
);

interface ReviewLine {
  kind?: string;
  stage?: string;
  review?: ReviewResult;
}

function loadStage0_5Reviews(): ReviewResult[] {
  const lines = readFileSync(reviewsPath, "utf8").trim().split(/\r?\n/);
  const reviews: ReviewResult[] = [];
  for (const line of lines) {
    if (!line.trim()) continue;
    const parsed = JSON.parse(line) as ReviewLine;
    if (parsed.kind === "review" && parsed.stage === "stage_0.5_to_0" && parsed.review) {
      reviews.push(parsed.review);
    }
  }
  return reviews;
}

async function main(): Promise<void> {
  const ctx: PipelineContext = {
    repoRoot: REPO,
    qid: QID,
    specialization: SPEC,
    resume: true,
    dryRun: false,
  };
  const deps = {
    runCodex,
    runClaude,
    lean: createLeanLspClient({ repoRoot: REPO }),
  };
  const state: StateJson = {
    stage_completed: "0",
    lean_subdir: QID,
    pending_sorries: [],
    design_decisions: {},
    added_assumptions: [],
    flags: {
      local_fix_from_4d: false,
      missing_architecture: false,
    },
  };
  const reviews = loadStage0_5Reviews();
  console.log(`[smoke] loaded ${reviews.length} stage_0.5_to_0 reviews from disk`);
  if (reviews.length === 0) {
    console.error("[smoke] no reviews to feed the judge — aborting");
    process.exit(2);
  }
  const started = Date.now();
  const intervention = await runIntervention({
    ctx,
    deps,
    state,
    boundary: "stage_0.5_to_0",
    heuristic:
      "Algebra slip or missing case routes to stage_0; counterexample-grade or inconsistent setup routes to user.",
    originalBrief: `Repository: ${REPO}\nQID: ${QID}\nSpecialization: ${SPEC}\n(Smoke-test replay)`,
    reviews,
    producerOutputs: [
      "[smoke] attempt 1 was reviewer-only (no producer call).",
      "[smoke] attempt 2 producer ran a Stage 0 redo; .tex grew 681 → 767 lines.",
    ],
  });
  const ms = Date.now() - started;
  console.log(`[smoke] runIntervention returned in ${ms}ms`);
  console.log(JSON.stringify(intervention, null, 2));
}

main().catch((err) => {
  console.error(`[smoke] runIntervention threw: ${err instanceof Error ? err.stack : String(err)}`);
  process.exit(1);
});
