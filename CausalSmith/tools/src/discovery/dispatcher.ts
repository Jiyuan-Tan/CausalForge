// Discovery-phase stage dispatcher.
// Extracted from pipeline_stages.ts in Step 2.2 of the three-submodules refactor.

import type { PipelineContext, Stage, StageResult, StateJson } from "../types.js";
import { type StageDeps } from "../pipeline_support.js";
// Side-effect: gate registry population must not depend on a transitive import.
import "./framework/gate_registrations.js";
import { runStageNeg1_1 } from "./stages/neg1_1.js";
import { runStageNeg1_2 } from "./stages/neg1_2.js";
import { runStageNeg0_5 } from "./stages/neg0_5.js";
import { runStage0Typed, runStage0_5Typed } from "./stages/d0.js";

/**
 * Route a discovery-phase stage to its handler. Returns `null` when the
 * stage is not a discovery stage (caller should fall through to the
 * formalization dispatcher). Discovery owns: -1.1, -1.2, -0.5, 0, 0.5.
 */
export async function runDiscoveryStage(args: {
  ctx: PipelineContext;
  state: StateJson;
  stage: Stage;
  deps: StageDeps;
}): Promise<StageResult | null> {
  switch (args.stage) {
    case "-1.1":
      return runStageNeg1_1({ ctx: args.ctx, state: args.state, deps: args.deps });
    case "-1.2":
      return runStageNeg1_2({ ctx: args.ctx, state: args.state, deps: args.deps });
    case "-0.5":
      return runStageNeg0_5({ ctx: args.ctx, state: args.state, deps: args.deps });
    case "0":
      // Typed-core D0: D0-SOLVE → D0-RENDER.
      return runStage0Typed({ ctx: args.ctx, state: args.state, deps: args.deps });
    case "0.5":
      return runStage0_5Typed({ ctx: args.ctx, state: args.state, deps: args.deps });
    default:
      return null;
  }
}
