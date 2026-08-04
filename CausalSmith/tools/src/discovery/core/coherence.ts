// Round invariants — every check that a committed D-stage round left a sound
// state, in one module. All WARN-tier: detect-and-warn by policy; the danger
// they guard against is SILENCE, not survivable damage, and aborting a paid
// round over a repairable inconsistency is the worse trade.
//
// Consolidated 2026-07-20 (T4 of the framework-rewrite mechanical phase);
// REDUCED 2026-07-31 (Phase 1 of the store-consolidation migration): the
// published core.json became a pure render of (proto_core.json,
// d0_working.json) — `assembleCore` — so the cross-store contradiction checks
// this module used to carry became unrepresentable and were DELETED, each
// replaced by a construction-level test (test/discovery/assemble.test.ts):
//
//   `reconcileProofStores` (hard)  — repaired proved-in-core-but-not-in-cursor;
//                                    a rendered proof now only ever comes FROM
//                                    the cursor. Its throw case (a resolution
//                                    naming a theorem no store holds) moved to
//                                    `saveWorkingState` → `normalizeWorkingState`.
//   proposal closure (hard)        — ids(core) ⊆ ids(proto) ∪ ids(working) holds
//                                    by construction of the render.
//   `store-incoherent` (warn)      — both directions unrepresentable: a settled
//                                    core node exists only via its record, and a
//                                    recorded (unshelved) agent node always renders.
//   `proved-not-partial` (warn)    — published status is DERIVED from the record;
//                                    a partial record renders `to-prove`, never
//                                    `proved`.
//   `oeq-source-retired` (warn)    — the render filters answered sources.
//   `oeq-source-record-retired`    — auto-resolved at the single write boundary
//     (warn)                         (`normalizeWorkingState` retires the record).
//
// What remains guards the MATHEMATICS and the cross-round history, which no
// store layout can make unrepresentable.

import { type WorkingState } from "../stages/d0_working.js";
import { wiredSnapshot } from "../working_writer.js";
import type { Core } from "./schema.js";

export interface RoundViolation {
  /** Stable, greppable identifier for the invariant that failed. */
  code:
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
    // Compare against the CANONICAL basis computation (the wired closure the
    // writer uses) — recomputing with the bare closure here would flag every
    // correctly-written record whose proof cites an undeclared def/ass.
    if (JSON.stringify(rec.snapshot) !== JSON.stringify(wiredSnapshot(proto, stmt, rec.proof_tex ?? ""))) ids.push(id);
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
