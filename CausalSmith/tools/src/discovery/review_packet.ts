// The adjudication packet, built one way.
//
// Two code paths write `proposal_review_packet.json`: the normal checkpoint in
// `stage0_solve`, and `bin/d0_rebuild_review_packet` (mechanical recovery, no solver
// run). Both hand-authored the same nine-key object and their own copy of the
// `contract` string — and they had ALREADY DRIFTED. The recovery packet told the
// adjudicator:
//
//     "open_question_partial_results are context only and never discharge an OEQ."
//
// and the normal packet did not. So the path taken EVERY round shipped a weaker
// instruction than the path taken almost never, in runs where OEQs and partial results
// are exactly what is under adjudication. Nothing detected this: the contract is prose
// consumed by a model, so a divergence produces subtly different verdicts rather than
// an error.
//
// The union of the two is kept below — the recovery copy's extra OEQ sentence was
// strictly more informative, and "completed payload" is the more precise wording.

import type { Core } from "./core/schema.js";
import { renderCoreTex } from "./core/render_tex.js";
import type { WorkingState } from "./stages/d0_working.js";

/**
 * Standing instructions to the adjudicator, shipped with every packet.
 *
 * Prose read by a model, so keep it declarative and keep it HERE — a second copy is
 * how the last divergence happened.
 */
export const REVIEW_PACKET_CONTRACT =
  "Review the full current paper together with all same-round deltas. " +
  "For any id in provisional_proofs, that completed payload supersedes core/prose proof text " +
  "during adjudication. open_question_partial_results are context only and never discharge an OEQ. " +
  "Agent-added nodes absent from proto_core persist through durable_working_state and must be " +
  "reviewed there, not treated as dropped.";

export interface ReviewPacketInput {
  core: Core;
  working: WorkingState;
  proposedStatementChanges: unknown[];
  proposedDefinitionChanges: unknown[];
  proposedAssumptions: unknown[];
  proposedCoreEdits: unknown[];
  provisionalProofs: unknown[];
  /** Provenance for a mechanically recovered packet; omitted on the normal path. */
  recovery?: Record<string, unknown>;
}

/** Assemble the packet the orchestrator adjudicates. */
export function buildReviewPacket(input: ReviewPacketInput): Record<string, unknown> {
  return {
    contract: REVIEW_PACKET_CONTRACT,
    ...(input.recovery ? { recovery: input.recovery } : {}),
    full_current_paper_tex: renderCoreTex(input.core),
    current_typed_core: input.core,
    durable_working_state: input.working,
    proposed_statement_changes: input.proposedStatementChanges,
    proposed_definition_changes: input.proposedDefinitionChanges,
    proposed_assumptions: input.proposedAssumptions,
    proposed_core_edits: input.proposedCoreEdits,
    provisional_proofs: input.provisionalProofs,
  };
}
