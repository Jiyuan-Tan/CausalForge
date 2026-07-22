// Cross-store coherence — every check that a D-stage round's stores agree,
// in one module with TIERED verdicts:
//
//   HARD  — `reconcileProofStores` (repairs the recoverable direction; THROWS on
//           the one unrepairable state) and the proposal-closure invariant
//           (`checkProposalClosure`): a violation means an atomic apply or the
//           next round would silently destroy real work.
//   WARN  — the round invariants (`checkRoundInvariants`): detect-and-warn by
//           policy; the danger they guard against is SILENCE, not survivable
//           damage, and aborting a paid round over a repairable inconsistency
//           is the worse trade.
//
// Consolidated 2026-07-20 (T4 of the framework-rewrite mechanical phase) from
// `core/closure.ts`, `core/round_invariants.ts` and
// `stages/d0_working.ts::reconcileProofStores`, each moved verbatim — the
// original per-check header commentary is kept inline below.

// ---------------------------------------------------------------------------
// HARD TIER 1/2 — proposal closure (formerly core/closure.ts)
//
// D0 keeps the same mathematics in several stores: the live `core.json`, the
// frozen `proto_core.json` that an atomic apply rebases onto, and the round's
// proposal payload (the `proposals` carrier in `d0_working.json`; the per-kind
// `proposed_*.json` mirror files are retired).
// `d0_apply_change` composes proto + proposals; it CANNOT see `core.json`.
//
// So the apply is sound only if
//
//     ids(core) ⊆ ids(proto) ∪ ids(proposals)
//
// When that fails, a node the solver genuinely emitted — with a complete proof —
// is invisible to the apply, and the resulting base carries a dangling
// dependency. On the 2026-07-18 run this happened three times to
// `lem:integrated-arm-path-differentiation`, and each time it was caught only by
// a `gpt-5.6-sol` adjudication AFTER a 20-60 minute solve round. This check is
// that same verdict as a set difference: no tokens, before dispatch.
//
// The reverse direction (proto nodes absent from core) is reported but not
// fatal: it is usually a deliberate removal, and nothing had ever surfaced it.
import { snapshotMember, type WorkingState } from "../stages/d0_working.js";
import type { Core } from "./schema.js";

/** The structural slice of a core this check needs. Deliberately loose so it can
 *  run against a partially-parsed store — a closure violation must still be
 *  reportable when the full `CoreSchema` parse is what is failing. */
export interface ClosureCoreView {
  statements?: Array<{ id?: string }>;
  assumptions?: Array<{ id?: string }>;
  definitions?: Array<{ id?: string }>;
}

export interface ClosureReport {
  ok: boolean;
  /** In `core` but in neither `proto` nor any proposal — the apply would drop these. */
  uncarried: string[];
  /** In `proto` but not in `core` — drift in the other direction; advisory. */
  protoOnly: string[];
}

export function nodeIds(view: ClosureCoreView | null | undefined): string[] {
  if (!view) return [];
  const out: string[] = [];
  for (const group of [view.statements, view.assumptions, view.definitions]) {
    for (const node of group ?? []) {
      if (typeof node?.id === "string" && node.id.length > 0) out.push(node.id);
    }
  }
  return out;
}

export function checkProposalClosure(args: {
  core: ClosureCoreView;
  proto: ClosureCoreView;
  /** Every id the proposal payload would carry into the atomic base. */
  proposalIds: Set<string>;
}): ClosureReport {
  const coreIds = nodeIds(args.core);
  const protoIds = new Set(nodeIds(args.proto));
  const uncarried = [...new Set(coreIds)]
    .filter((id) => !protoIds.has(id) && !args.proposalIds.has(id))
    .sort();
  const coreIdSet = new Set(coreIds);
  const protoOnly = [...protoIds].filter((id) => !coreIdSet.has(id)).sort();
  return { ok: uncarried.length === 0, uncarried, protoOnly };
}

/** Human-readable escalation body for a closure violation. Names the exact ids and
 *  the exact repair, so the orchestrator never has to re-derive it from a REJECT. */
export function formatClosureViolation(report: ClosureReport): string {
  const lines = [
    `D0 proposal closure violated: ${report.uncarried.length} node(s) exist in core.json but are carried ` +
      `by neither proto_core.json nor any proposal file, so an atomic apply would silently drop them ` +
      `and leave a dangling dependency.`,
    `UNCARRIED: ${report.uncarried.join(", ")}`,
    `REPAIR: emit a structured core edit (and, where the node is proved, its proof in the round's ` +
      `proposal payload — the \`proposals.proofs\` carrier in d0_working.json) for each id above, in the ` +
      `SAME bundle as any change that depends on it.`,
  ];
  if (report.protoOnly.length > 0) {
    lines.push(`ADVISORY — in proto but absent from core (verify the removal was intended): ${report.protoOnly.join(", ")}`);
  }
  return lines.join("\n");
}

// ---------------------------------------------------------------------------
// HARD TIER 2/2 — proof-store reconciliation (formerly stages/d0_working.ts)

/** Reconcile the two stores that redundantly record the same proofs: the assembled
 *  `core` (derived merge, what renders) and `working.solved` (what the NEXT round
 *  carries). Several carry branches in Stage 0-SOLVE write only one of them, and the
 *  asymmetry is silently fatal: every carry branch reads `prev.solved`, so a node
 *  present in the core with a proof but absent from `solved` renders this round and
 *  then disappears. TERMINAL results are the systematic victims — having no inbound
 *  edge, they never trigger the referenced-but-not-re-emitted repair.
 *
 *  Repairs the recoverable direction (core node is the authoritative proof) and
 *  returns the recovered ids for the caller to report. Mutates `working.solved`.
 *  Throws when a `resolved_oeqs` entry names a theorem present in NEITHER store:
 *  that state claims an open question is answered by a result that does not exist,
 *  and nothing in the core can reconstruct it. */
export function reconcileProofStores(core: Core, proto: Core, working: WorkingState): string[] {
  const recovered: string[] = [];
  for (const s of core.statements) {
    if (!s.proof_tex || working.solved[s.id]) continue;
    const { proof_tex, ...bare } = s;
    // Snapshot against `proto`, not `core` — `computeValidNodes` compares stored
    // snapshots to `snapshotMember(proto, …)`, so a core-derived snapshot would
    // read as permanently stale and re-open a finished proof every round.
    working.solved[s.id] = { node: bare, proof_tex, snapshot: snapshotMember(proto, bare) };
    recovered.push(s.id);
  }
  const dangling = Object.entries(working.resolved_oeqs ?? {})
    .map(([sourceId, r]) => [sourceId, typeof r === "string" ? r : r.theorem_id] as const)
    .filter(([, theoremId]) => !working.solved[theoremId]);
  if (dangling.length > 0) {
    throw new Error(
      `Stage 0-SOLVE resolved-OEQ points at an absent theorem: ` +
        `${dangling.map(([s, t]) => `${s}->${t}`).join(", ")}. ` +
        "The run would claim an open question is answered by a result present in no store; " +
        "refusing to persist an incoherent state.",
    );
  }
  return recovered;
}

// ---------------------------------------------------------------------------
// WARN TIER — round invariants (formerly core/round_invariants.ts)
//
// What a D-stage round must never leave behind.
//
// Each check below corresponds to a fault that ACTUALLY OCCURRED on 2026-07-19. None was
// caught by the ~1600 unit tests, because none is a property of a single function: they
// live where two code paths meet — two writers of one store, two builders of one payload,
// two guards that each work alone. Such a fault is visible only in the state a ROUND
// leaves behind, and several need more than one round to appear.
//
// This module DETECTS; it does not decide what to do. The D0 solve commit warns on every
// violation at commit time, so each real run checks itself, and the test suite asserts
// the same function so a scenario and a live run cannot disagree about what "broken"
// means. Detection is O(nodes) over a graph of tens of nodes — free at round scale.
//
// POLICY: warn, do not throw. Today's lesson was that the danger is SILENCE, not
// survivable damage; aborting an expensive round over a repairable inconsistency trades
// one failure mode for a worse one. The single exception is `reconcileProofStores`
// above, which throws when a resolution names a theorem present in no store — that
// state cannot be repaired and must not be persisted.

export interface RoundViolation {
  /** Stable, greppable identifier for the invariant that failed. */
  code:
    | "store-incoherent"
    | "dangling-resolution"
    | "oeq-answer-churn"
    | "snapshot-basis"
    | "hollow-proof"
    | "silent-node-loss"
    | "dependency-cycle";
  /** One line explaining what this means and why it matters. */
  detail: string;
  /** The offending node ids (or `source->answer` pairs), for a receipts-bearing log line. */
  ids: string[];
}

export interface RoundInvariantInput {
  proto: Core;
  core: Core;
  /** Previous round's working state. Omit on a first round; cross-round checks are skipped. */
  before?: WorkingState | null;
  after: WorkingState;
  /** Ids whose disappearance from `solved` is intended this round (explicit deletes, consumed OEQ sources). */
  allowedLoss?: Iterable<string>;
}

const resolutionTargetId = (r: unknown): string =>
  typeof r === "string" ? r : (r as { theorem_id: string }).theorem_id;

/** The two stores must agree in BOTH directions.
 *
 *  This checked only core -> working. The reverse is equally possible and was invisible:
 *  on 2026-07-19 two agent-authored lemmas sat in the working cursor carrying full proofs
 *  while absent from the assembled core, and this invariant — whose whole job is store
 *  divergence — stayed silent. An agent-authored node is defined NOWHERE ELSE, so its
 *  absence from core means the definition exists only in a store nothing renders from. */
function checkStoreCoherence({ proto, core, after }: RoundInvariantInput): RoundViolation | null {
  const coreIds = new Set(core.statements.map((s) => s.id));
  // SETTLED, not just proved-with-text. Requiring a non-empty proof_tex silently exempted
  // `cited` nodes — whose justification IS the citation, so they legitimately carry no
  // proof — and a cited leaf present in core but absent from the cursor renders once and
  // then vanishes, exactly like the proved case this was written for.
  //
  // ...but only for nodes that can actually be LOST. A frozen proto member is recreated
  // from proto_core.json on every assembly, so its absence from the cursor is not a
  // vanishing node. Including cited without that carve-out reported every frozen cited
  // leaf on a first round -- an over-broad rule of exactly the kind this sweep keeps
  // producing.
  const protoIds = new Set(proto.statements.map((s: { id: string }) => s.id));
  const settled = (s: { status?: string; proof_tex?: string }): boolean =>
    s.status === "cited" || (s.proof_tex ?? "").length > 0;
  const missingWorking = core.statements
    .filter((s) => settled(s) && !after.solved[s.id] && !protoIds.has(s.id))
    .map((s) => `core-only:${s.id}`);
  const missingCore = Object.entries(after.solved)
    .filter(([id, rec]) => rec.node !== undefined && !coreIds.has(id))
    .map(([id]) => `working-only:${id}`);
  const ids = [...missingWorking, ...missingCore];
  return ids.length === 0 ? null : {
    code: "store-incoherent",
    detail:
      "core.json and the working cursor disagree. `core-only` = a proved core node with no " +
      "working record: every carry branch reads prev.solved, so it renders this round and is " +
      "deleted the next. `working-only` = an agent-authored node carried in the cursor but " +
      "absent from core: it is defined nowhere else, so it renders nowhere and may be pruned",
    ids,
  };
}

/** Every resolution names a theorem that exists somewhere. */
function checkDanglingResolution({ core, after }: RoundInvariantInput): RoundViolation | null {
  const ids = Object.entries(after.resolved_oeqs ?? {})
    .map(([src, r]) => [src, resolutionTargetId(r)] as const)
    .filter(([, tid]) => !after.solved[tid] && !core.statements.some((s) => s.id === tid))
    .map(([src, tid]) => `${src}->${tid}`);
  return ids.length === 0 ? null : {
    code: "dangling-resolution",
    detail: "the run claims an open question is answered by a theorem present in no store",
    ids,
  };
}

/** An answered question keeps its answer id, unless the question itself changed. */
function checkOeqAnswerChurn({ proto, before, after }: RoundInvariantInput): RoundViolation | null {
  if (!before) return null;
  const protoIds = new Set(proto.statements.map((s: { id: string }) => s.id));
  const ids: string[] = [];
  for (const [sourceId, prevRes] of Object.entries(before.resolved_oeqs ?? {})) {
    const nextRes = (after.resolved_oeqs ?? {})[sourceId];
    if (nextRes === undefined) continue; // retracted — a different event
    if (!protoIds.has(sourceId)) continue; // the question left the proto
    const [a, b] = [resolutionTargetId(prevRes), resolutionTargetId(nextRes)];
    if (a !== b) ids.push(`${sourceId}: ${a} -> ${b}`);
  }
  return ids.length === 0 ? null : {
    code: "oeq-answer-churn",
    detail:
      "an answered question was re-answered under a NEW id although the question is unchanged; " +
      "a solve round was spent re-deriving a result that only needed its proof re-checked",
    ids,
  };
}

/** Snapshots are taken against the frozen proto — the basis `computeValidNodes` compares to. */
function checkSnapshotBasis({ proto, core, after }: RoundInvariantInput): RoundViolation | null {
  const byId = new Map(core.statements.map((s) => [s.id, s] as const));
  const ids: string[] = [];
  for (const [id, rec] of Object.entries(after.solved)) {
    if (rec.partial) continue; // a partial's snapshot describes the obligation, not current text
    // BASIS: an agent-authored record's authoritative statement is `rec.node`, not the
    // derived core copy. Comparing against core validated the snapshot against a view that
    // can itself have drifted — checking the derived artifact instead of the source.
    const stmt = rec.node ?? byId.get(id);
    if (!stmt) continue;
    if (JSON.stringify(rec.snapshot) !== JSON.stringify(snapshotMember(proto, stmt))) ids.push(id);
  }
  return ids.length === 0 ? null : {
    code: "snapshot-basis",
    detail:
      "snapshot(s) not taken against the frozen proto; a core-based snapshot has no valid " +
      "comparison basis, so the node reads as stale on every subsequent round",
    ids,
  };
}

/** Nothing is published as established over an empty proof. */
function checkHollowProofs({ core }: RoundInvariantInput): RoundViolation | null {
  const ids = core.statements
    .filter((s) => s.status === "proved" && (s.proof_tex ?? "").trim().length === 0)
    .map((s) => s.id);
  return ids.length === 0 ? null : {
    code: "hollow-proof",
    detail: "node(s) marked proved with an empty proof; they render as established with nothing behind them",
    ids,
  };
}

/** An agent-authored statement is defined ONLY in `solved`; losing the record deletes the statement. */
function checkSilentNodeLoss({ before, after, allowedLoss }: RoundInvariantInput): RoundViolation | null {
  if (!before) return null;
  const allowed = new Set(allowedLoss ?? []);
  const ids = Object.keys(before.solved).filter(
    (id) => before.solved[id].node && !after.solved[id] && !allowed.has(id),
  );
  return ids.length === 0 ? null : {
    code: "silent-node-loss",
    detail:
      "agent-authored statement(s) left the working state unexplained; `solved` is their only " +
      "definition, so this deletes the STATEMENT, not merely its proof",
    ids,
  };
}

/** The statement dependency graph is acyclic. */
function checkDependencyCycle({ core }: RoundInvariantInput): RoundViolation | null {
  const known = new Set(core.statements.map((s) => s.id));
  const edges = new Map(
    core.statements.map((s) => [s.id, (s.depends_on ?? []).filter((d) => known.has(d))] as const),
  );
  const mark = new Map<string, "open" | "done">();
  const ids: string[] = [];
  const walk = (id: string, trail: string[]): void => {
    if (mark.get(id) === "done") return;
    if (mark.get(id) === "open") {
      ids.push([...trail.slice(trail.indexOf(id)), id].join("->"));
      return;
    }
    mark.set(id, "open");
    for (const next of edges.get(id) ?? []) walk(next, [...trail, id]);
    mark.set(id, "done");
  };
  for (const id of known) walk(id, []);
  return ids.length === 0 ? null : {
    code: "dependency-cycle",
    detail:
      "dependency cycle(s) in the assembled core; the structural gate reports these as a defect " +
      "even when the mathematics is sound",
    ids,
  };
}

const CHECKS = [
  checkStoreCoherence,
  checkDanglingResolution,
  checkOeqAnswerChurn,
  checkSnapshotBasis,
  checkHollowProofs,
  checkSilentNodeLoss,
  checkDependencyCycle,
] as const;

/** Run every round-level invariant. Empty result means the round left a coherent state. */
export function checkRoundInvariants(input: RoundInvariantInput): RoundViolation[] {
  return CHECKS.map((check) => check(input)).filter((v): v is RoundViolation => v !== null);
}

/** One log line per violation, with receipts. */
export function formatRoundViolation(v: RoundViolation): string {
  const shown = v.ids.slice(0, 8).join(", ");
  const more = v.ids.length > 8 ? `, … (${v.ids.length - 8} more)` : "";
  return `[D0-SOLVE] INVARIANT ${v.code}: ${v.detail} — ${shown}${more}`;
}
