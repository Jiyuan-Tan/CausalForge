// Stage 0-SOLVE — the D0 math solver (replaces the old D0-CORE + D0-PROVE split).
//
// D0-CORE is retired: pre-committing a proof route + lemma decomposition that the
// prover must then follow was redundant — DECIDING the decomposition IS part of
// solving. So one solver owns it end-to-end. Dispatch granularity: ONE agent per
// WEAKLY-CONNECTED COMPONENT of the to-prove statement dependency graph (edges =
// `depends_on` references between two to-prove statements). Coupled statements —
// a thm and the props that depend on it, a conj and the prop/lemma it consumes —
// MUST be solved by the same agent so shared objects (a definition's envelope, a
// rate functional) are reconciled coherently: when one statement narrows such an
// object, every statement that depends on it has to move with it, which only
// happens inside one unit. Independent results land in separate components and
// still solve in parallel. Each agent:
//   - writes `proof_tex` for its target statement(s),
//   - ADDS the lemmas its proof needs (with their own proofs, inline),
//   - may PROPOSE a statement change when a target is too strong to prove as
//     stated — flagged, NEVER silently applied (direction-of-truth: narrow a
//     genuinely-too-strong claim for review; never weaken to ease the proof).
// Then: merge proofs, DEDUP shared lemmas, and either (a) escalate the proposed
// statement changes as a checkpoint (no silent change), or (b) run the structural
// gate with `requireDischarged:true` and write the solved core. D0-RENDER renders
// the .tex from it. Spec: D0_CORE_REDESIGN.md §4 (simplified).
import type { StageDeps } from "../../pipeline_support.js";
import type { PipelineContext, StageResult, StateJson } from "../../types.js";
import { assembleSolveContext } from "../solve/context.js";
import { dispatchSolveUnits } from "../solve/dispatch.js";
import { mergeSolveOutputs } from "../solve/merge.js";
import { runFinalAssemblyGates } from "../solve/gates.js";
import {
  makeCommitRound,
  surfaceProposalCheckpoint,
  finalizeRound,
  type Stage0SolveResult,
} from "../solve/commit.js";

// Payload shapes, the multi-unit write-ownership model, the WCC partitioner and
// the proof/target partition moved beside this file in the T1 carve; re-exported
// so existing importers (tests, bin/) are unaffected.
export * from "../solve/schemas.js";
export * from "../solve/ownership.js";
export { groupToProveByComponent, repairSolveUnitLatexSerialization } from "../solve/dispatch.js";
export { partitionProofsByTarget } from "../solve/merge.js";
export type { Stage0SolveResult } from "../solve/commit.js";

export async function runStage0Solve(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
}): Promise<Stage0SolveResult | StageResult> {
  const { ctx, state, deps } = args;
  // Step 1/5 — assembleContext: proto→core clone, incremental carry, resolved-OEQ
  // re-application, escalation/directive assembly.
  const sctx = await assembleSolveContext({ ctx, state });
  // Step 2/5 — dispatchAgents: WCC partitioning, ownership selection, one solver
  // agent per open component.
  const dr = await dispatchSolveUnits({ ctx, state, deps, sctx });
  // Step 3/5 — parseOutputs/merge: capability projection, conflict withholding,
  // proof/lemma merge, OEQ resolution, prose, id heal, self-containment.
  const mr = mergeSolveOutputs({ sctx, dr });
  // Step 4/5 — runGates: prune + derived metadata + manifest validation. (The
  // commit-time coherence checks and the structural gate run inside step 5.)
  runFinalAssemblyGates(sctx);
  // Step 5/5 — persist: checkpoint when the round surfaced proposals/withheld
  // content; otherwise open-gap / incomplete-round / clean discharge.
  const commitRound = makeCommitRound({
    ctx, sctx,
    protoChangedByProse: mr.protoChangedByProse,
    withheldProofBytes: mr.withheldProofBytes,
  });
  const checkpoint = await surfaceProposalCheckpoint({ ctx, sctx, mr, commitRound });
  if (checkpoint) return checkpoint;
  return finalizeRound({ ctx, state, sctx, mr, dispatchCount: dr.dispatch.length, commitRound });
}
