import type { PipelineContext, Stage, StageResult, StateJson } from "./types.js";
import { formatStageLabel } from "./constants.js";
import { defaultDeps } from "./pipeline_support.js";
import { runDiscoveryStage } from "./discovery/dispatcher.js";
import { runStage1 } from "./formalization/stage1.js";
import { runStage1_5 } from "./formalization/stage1_5.js";
import { runFormalizationStage } from "./formalization/dispatcher.js";
// Re-export externally consumed names so callers that imported them from
// "./pipeline_stages.js" continue to work unchanged after the staged splits.
export { runStage1, runStage1_5 };
export { runStage2 } from "./formalization/stage2.js";
export { runStage5 } from "./formalization/stage5.js";
export { reviewWithCodex } from "./formalization/review_codex.js";
export {
  applyInterventionRoute,
  bucketAApprovedBlock,
  interventionBlock,
  runReviewBoundary,
} from "./shared/intervention_routing.js";

// Novelty-target / tier-floor logic lives in the leaf `novelty.ts` module (so
// `parseArgs` and the state schema can depend on it without pulling in the
// pipeline dispatcher). Re-exported here for the callers that import it from
// "./pipeline_stages.js".
export { meetsNoveltyFloor, tierFloorBlock } from "./novelty.js";

export type StageHandler = (args: {
  ctx: PipelineContext;
  state: StateJson;
  stage: Stage;
}) => Promise<StageResult>;

export const dryRunStageHandler: StageHandler = async ({ ctx, stage }) => {
  const { setTimeout: delay } = await import("node:timers/promises");
  await delay(1);
  return {
    stage,
    status: "completed",
    message: `dry-run completed stage ${stage} for ${ctx.qid}_${ctx.specialization}`,
  };
};

export const liveStageHandler: StageHandler = async ({ ctx, state, stage }) => {
  const deps = defaultDeps(ctx, stage, state);
  try {
    const discoveryResult = await runDiscoveryStage({ ctx, state, stage, deps });
    if (discoveryResult !== null) return discoveryResult;
    const formalizationResult = await runFormalizationStage({ ctx, state, stage, deps });
    if (formalizationResult !== null) return formalizationResult;
    throw new Error(`liveStageHandler: unhandled stage ${formatStageLabel(stage)}`);
  } finally {
    // A fresh StageDeps (and lazily, a lean-lsp MCP server tree: python →
    // lake serve → lean workers) is constructed per stage iteration; nothing
    // closed it, so every F2.5/F3 entry — including every rewind — leaked one
    // server tree and kept the node event loop alive at exit.
    await deps.lean.close().catch(() => undefined);
  }
};
