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
// So: snapshots are computed HERE, against `proto`, and nowhere else — over the
// WIRED closure: the member's authored `depends_on` plus every LOCAL node id
// its claim/proof text cites (qualified cross-paper mentions excluded —
// `extractCitationRefs`). The refresh
// loops that used to re-sync snapshots from the mutated workspace core after
// dependency auto-wiring are gone; the wiring is applied AT THE WRITE, from the
// same text the render's canonical wiring pass reads, so the two can never
// disagree. (The record node's published edge set gets the cycle-guarded wiring
// at render; the snapshot closure deliberately skips the cycle guard — an extra
// closure edge only ever WIDENS invalidation, which is the safe direction.)

import type { Core, CoreStatement } from "./core/schema.js";
import { extractCitationRefs } from "./core/node_ids.js";
import { snapshotMember, type SolvedMember, type WorkingState } from "./stages/d0_working.js";

/** The member with its claim/proof-cited node ids unioned into `depends_on` —
 *  the closure `snapshotMember` walks, matching what dependency auto-wiring
 *  publishes. */
export function withWiredDeps(member: CoreStatement, proofTex: string): CoreStatement {
  const deps = new Set(member.depends_on ?? []);
  // CITATION refs only: a qualified `other_paper/lem:foo` is a mention of
  // another paper, never a local dependency — including its bare suffix
  // poisoned the closure with an id that exists nowhere and read the record
  // permanently stale (audit R2BB2).
  for (const ref of extractCitationRefs(`${member.statement ?? ""}\n${proofTex}`)) {
    if (ref !== member.id) deps.add(ref);
  }
  // SORTED: the snapshot's `depends_on` is provenance (validity walks the
  // defs/assumptions maps), and a canonical order makes writer and checker
  // byte-agree regardless of which surface (merge record, apply compose,
  // render-wired statement) supplied the base dep list.
  return { ...member, depends_on: [...deps].sort() };
}

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

/** The canonical snapshot computation: against the frozen `proto`, over the
 *  wired closure. ONE function shared by the writer (`recordProof`) and the
 *  `snapshot-basis` invariant checker, so they can never disagree about what a
 *  correct basis looks like. */
export function wiredSnapshot(proto: Core, member: CoreStatement, proofTex: string) {
  return snapshotMember(proto, withWiredDeps(member, proofTex));
}

/** Record a proof, computing its snapshot against the frozen `proto` over the
 *  wired closure (authored deps + claim/proof-cited ids). */
export function recordProof(working: WorkingState, proto: Core, spec: ProofRecordSpec): void {
  const common = {
    proof_tex: spec.proofTex,
    snapshot: wiredSnapshot(proto, spec.snapshotOf, spec.proofTex),
  };
  const partial = spec.partial ? { partial: true as const } : {};
  // Built as one of the two arms rather than assigned field-by-field: `SolvedMember` is
  // a union discriminated on `node`, so an agent-authored record must carry its
  // statement and a frozen-member record must NOT pretend to.
  working.solved[spec.id] =
    spec.node !== undefined
      ? {
          ...common,
          ...partial,
          node: spec.partial ? spec.node : { ...spec.node, proof_tex: spec.proofTex },
          ...(spec.owner !== undefined ? { owner: spec.owner } : {}),
        }
      : { ...common, ...partial };
}

// (Batch B: `refreshSnapshots` is gone. Snapshots are computed once, at the
// write, over the wired closure — there is no workspace core to re-sync from.
// The one remaining post-write snapshot mutation is the OEQ id remap in the
// merge, which rewrites `rec.snapshot.depends_on` in place: an id rename, not
// a basis retarget.)
