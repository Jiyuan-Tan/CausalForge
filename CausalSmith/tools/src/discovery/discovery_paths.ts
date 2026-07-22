// One definition of where each D-stage artifact lives.
// (The five legacy `proposed_*.json` mirror paths were retired 2026-07-20 with
// the store fold; `solve/proposals.ts` and `bin/migrate_dstage_stores.ts` keep
// their own knowledge of those historical names for detection/migration.)
//
// These filenames were constructed independently in five places — `stage0_apply`
// (four exported helpers), `stage0_solve` (inline), `solve/proposals` (a LEGACY map),
// `core/paper_view` (its own private helper), and `bin/d0_rebuild_review_packet` (its
// own `discovery()` helper). Each repeated both the filename AND the legacy
// `<qid>_<name>.json` fallback, so a writer and a reader could disagree about which
// file they meant — and the failure is silent: the reader finds no file and behaves as
// though the stage produced nothing.
//
// Every path takes the same shape, so the shape is written once and the names are data.
// NOTE: `core.json`, `proto_core.json`, and `d0_working.json` keep their own modules —
// they are canonical stores with load/save logic attached, not bare artifact paths.

import { artifactPath } from "../paths.js";
import type { PipelineContext } from "../types.js";

/** Resolve a discovery-stage artifact, including its legacy `<qid>_`-prefixed name. */
function discoveryArtifact(ctx: PipelineContext, name: string): string {
  return artifactPath(ctx.repoRoot, ctx.qid, "discovery", name, [`${ctx.qid}_${name}`]);
}

/** The adjudication packet assembled for the orchestrator at a proposal checkpoint. */
export const proposalReviewPacketPath = (ctx: PipelineContext): string =>
  discoveryArtifact(ctx, "proposal_review_packet.json");

/** Open obligations surfaced by a round that did not fully discharge. */
export const openObligationsPath = (ctx: PipelineContext): string =>
  discoveryArtifact(ctx, "open_obligations.json");
