// One way to write a proof into the D0 working state.
//
// `runStage0Solve` had 19 separate write sites into `next.solved` and FOUR
// near-identical "refresh every snapshot" loops. That redundancy was not merely
// untidy — it silently diverged in two ways that each cost a run:
//
//   • Three refresh loops snapshotted against `proto`, one against `core`. Only
//     `proto` is correct: `computeValidNodes` compares stored snapshots to
//     `snapshotMember(proto, …)`, so a core-based snapshot has no valid comparison
//     basis the moment `core` holds a definition or assumption `proto` lacks (an
//     in-flight `definition-add`). The node then reads as stale every round.
//   • Some branches wrote `core.statements` without writing `solved`. Since every
//     carry branch reads `prev.solved`, such a node renders once and then vanishes
//     — and TERMINAL results are the systematic victims, having no inbound edge to
//     trigger the self-containment repair.
//
// So: snapshots are computed HERE, against `proto`, and nowhere else.

import type { Core, CoreStatement } from "./core/schema.js";
import { snapshotMember, type SolvedMember, type WorkingState } from "./stages/d0_working.js";

/** One proof record to write. `snapshotOf` and `node` are separate on purpose — see below. */
export interface ProofRecordSpec {
  id: string;
  /**
   * The statement whose content defines this record's VALIDITY. Usually the same
   * object as `node`, but not always: when a proof is banked against a statement the
   * round is simultaneously re-opening, validity is measured against the statement as
   * written while the catalog stores the re-opened (`to-prove`) form.
   */
  snapshotOf: CoreStatement;
  proofTex: string;
  /**
   * Durable catalog node. Agent-added statements live nowhere else, so they must carry
   * one; frozen proto members omit it, since the proto is already their definition.
   */
  node?: CoreStatement;
  owner?: string;
  /**
   * An open obligation rather than a finished argument. The record and its `proof_tex`
   * are still carried forward as prior progress ("extend this, do not restart"), but
   * the node stays open and is not reusable for discharge.
   */
  partial?: boolean;
}

/** Record a proof, computing its snapshot against the frozen `proto`. */
export function recordProof(working: WorkingState, proto: Core, spec: ProofRecordSpec): void {
  const common = { proof_tex: spec.proofTex, snapshot: snapshotMember(proto, spec.snapshotOf) };
  const partial = spec.partial ? { partial: true as const } : {};
  // Built as one of the two arms rather than assigned field-by-field: `SolvedMember` is
  // a union discriminated on `node`, so an agent-authored record must carry its
  // statement and a frozen-member record must NOT pretend to.
  working.solved[spec.id] =
    spec.node !== undefined
      ? { ...common, ...partial, node: spec.node, ...(spec.owner !== undefined ? { owner: spec.owner } : {}) }
      : { ...common, ...partial };
}

/**
 * Re-snapshot every recorded proof against the CURRENT statement text in `core`.
 *
 * Run after any pass that rewrites statements in place — dependency auto-wiring, OEQ
 * id remapping, prose application. Without it a record keeps the snapshot it was
 * written with, and the next round reads the rewrite as a content change and re-opens
 * a finished proof.
 *
 * `skipPartial` leaves open obligations alone: a partial record's snapshot describes
 * what the agent was asked to extend, and refreshing it would quietly retarget the
 * obligation. Returns the ids whose snapshot actually moved, for logging.
 */
export function refreshSnapshots(
  working: WorkingState,
  proto: Core,
  core: Core,
  opts: { skipPartial?: boolean } = {},
): string[] {
  const byId = new Map(core.statements.map((s) => [s.id, s] as const));
  const moved: string[] = [];
  for (const [id, rec] of Object.entries(working.solved)) {
    if (opts.skipPartial && rec.partial) continue;
    const stmt = byId.get(id);
    if (!stmt) continue;
    const next = snapshotMember(proto, stmt);
    if (JSON.stringify(rec.snapshot) !== JSON.stringify(next)) moved.push(id);
    rec.snapshot = next;
    // The record's own copy of the node must track the rewrite too, or the durable
    // agent-node catalog drifts from what the core actually says.
    if (rec.node) rec.node = stmt;
  }
  return moved;
}
