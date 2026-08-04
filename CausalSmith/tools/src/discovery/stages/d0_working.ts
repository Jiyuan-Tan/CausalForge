// D0-SOLVE incremental working state — proof reuse across escalation rounds.
//
// Without this, every D0 round re-derives the whole core from the frozen proto
// (no proofs carried), so an agent re-proves unchanged lemmas every time the
// orchestrator applies one correction and re-runs. This module makes the loop
// INCREMENTAL: a previous round's proofs are carried forward, and a node is
// re-solved ONLY when a correction actually invalidated it.
//
// Granularity (two levels):
//   • DISPATCH is per weakly-connected GROUP (coherence — a group's shared objects
//     must be reconciled by one agent). A group with every member still valid is
//     SKIPPED entirely.
//   • VALIDITY is per MEMBER: a proved statement stays valid until its content
//     CLOSURE changes — its own statement text, or the construction/condition of a
//     `def`/assumption it references (via `depends_on`). An open group still carries
//     its valid members' proofs to the agent as GIVEN context (cite, don't re-prove);
//     only the invalidated / unsolved members are targets.
//
// Invalidation tracks `depends_on` def/assumption references and follows structured
// definition refs transitively where available; the post-solve gate remains the backstop.
import { createHash } from "node:crypto";
import { existsSync } from "node:fs";
import { readFile, writeFile, appendFile, rename, rm } from "node:fs/promises";
import path from "node:path";
import { artifactPath } from "../../paths.js";
import { archiveProofs, type ProofToArchive } from "../proof_archive.js";
import type { PipelineContext } from "../../types.js";
import { extractNodeRefs, extractCitationRefs } from "../core/node_ids.js";
import { normalizeSymbol } from "../core/preflight.js";
import type { Core, CoreStatement } from "../core/schema.js";
import { coreNodeIds } from "../core/schema.js";
import { writeJsonAtomic } from "../../shared/json_atomic.js";
import { repairLatexStringsDeep } from "../core/latex_serialization.js";
import type { ProseOverlay } from "../core/assemble.js";
import { ProposedCoreEditSchema } from "../solve/schemas.js";
import type { RawCoreEdit } from "./d0_apply.js";
import {
  assertMandateIntegrity,
  assertMandateCancellationIntegrity,
  RequiredCoreEditMandateCancellationSchema,
  RequiredCoreEditMandateSchema,
  type RequiredCoreEditMandateCancellation,
  type RequiredCoreEditMandate,
} from "../solve/mandates.js";

/** The content a member statement was last solved against — change ⟹ invalidate. */
export interface MemberSnapshot {
  stmt: string; // the member's own statement text
  /** Edge set at solve time. PROVENANCE ONLY — no longer part of validity: a proof's
   *  soundness rests on its statement plus the CONTENT it was solved against (`defs`/
   *  `assumptions` below, which are captured post-auto-wiring and therefore cover every
   *  def/ass the proof text cites), not on the edge list. Comparing the edge set made a
   *  pure dependency rewire re-derive a byte-identical theorem (observed ≥3× on one
   *  flagship: "dep change alone triggers re-derivation via snapshot invalidation").
   *  Upstream STATEMENT changes are handled separately by `computeValidNodes`'s
   *  staleness propagation over the CURRENT edges. */
  depends_on?: string[];
  defs: Record<string, string>; // referenced def id → construction
  assumptions: Record<string, string>; // referenced assumption id → condition
}

/** One proved node carried across rounds. Spec statements store just proof+snapshot;
 *  agent-added lemmas additionally store their `node` (they are not in the proto) and
 *  the `owner` group label that authored them. */
// A record's `node` is not an optional extra — it is the KIND distinction, and reading
// it without establishing which kind you hold is a live source of wrong answers. A
// frozen proto member's statement is defined in `proto_core.json`, so its record carries
// no `node`; an agent-authored statement is defined NOWHERE ELSE, so its record must.
// Written as an optional field, `rec.node.status` compiled fine and silently returned
// `undefined` for every frozen member — which counted six PROVED nodes as unproved and
// sent a real run down the wrong diagnosis (PIPELINE_NOTES 2026-07-19). As a union, that
// read is a compile error and the guard is forced.
interface ProtoMemberProof {
  proof_tex: string;
  snapshot: MemberSnapshot;
  node?: undefined;
  owner?: undefined;
  partial?: boolean;
  /** Never set on a frozen member: its render comes from the proto text, so there
   *  is nothing to shelve. Typed `undefined` so a union read is legal. */
  shelved?: undefined;
}
interface AgentNodeProof {
  proof_tex: string;
  snapshot: MemberSnapshot;
  node: CoreStatement;
  owner?: string;
  /** True when proof_tex is only a PARTIAL result (the node has an open obligation).
   *  A partial is carried forward as "extend, don't restart" context but is NOT a valid
   *  proof for reuse/discharge — the node stays open until fully proved. */
  partial?: boolean;
  /** A partial carried as debt that is deliberately NOT part of the published paper
   *  this round (e.g. a stale helper lemma that no live result consumes yet — the
   *  frontier logic re-opens it only when a root pulls it back in). `assembleCore`
   *  skips shelved records; a published partial (`shelved` absent/false) renders as
   *  an open `to-prove` target with its best-partial bytes. Meaningful only with
   *  `partial: true`. */
  shelved?: boolean;
}
export type SolvedMember = ProtoMemberProof | AgentNodeProof;

/** Durable D0-boundary replacement of a frozen OEQ by its answer theorem. */
export interface ResolvedOeq {
  theorem_id: string;
  /** Frozen OEQ claim/prose/dependency fingerprint at the moment it was answered. */
  source_fingerprint: string;
}

/** Persistent incremental state, parallel to the assembled core.json. */
export interface WorkingState {
  round: number;
  /** Number of parsed escalation-log entries delivered to a solver round.
   *  A newly appended standalone directive must invalidate reuse once so it
   *  reaches a real dispatch; after that, ordinary incremental reuse resumes. */
  escalation_entries_consumed?: number;
  /**
   * D-1.2 proposal revision that authored the frozen proto used for these
   * proofs.  Ordinary D0 corrections keep this key and use member-level
   * invalidation; a source rewind increments it and must rebuild from scratch
   * so removed source claims cannot survive as carried agent-added nodes.
   */
  proposal_revision?: string;
  /**
   * GLOBAL symbol basis these proofs were solved against: symbol name → hex
   * fingerprint of the symbol's SEMANTIC fields (`type`/`space`/`sig`/`def`/`role`/`ref`;
   * only `refs` is excluded — see `symbolBasis` for why each field is in or out).
   * Symbols are not `depends_on` edges (`sym` is absent
   * from `NODE_KINDS`) and appear in NO `MemberSnapshot` field, so an APPLIED symbol
   * re-definition (e.g. narrowing a space from ℝ to [0,1]) changed what every
   * statement quoting it CLAIMS while every statement's text stayed byte-identical —
   * `computeValidNodes` saw nothing and published proofs of materially different
   * claims as current. `merge.ts` already treats a PROPOSED symbol edit as globally
   * proof-invalidating; this is the applied-case counterpart. Values are hex hashes
   * so `repairLatexStringsDeep` (applied to the whole cursor on load) cannot mutate
   * them out from under the comparison.
   *
   * The basis is global; the INVALIDATION it triggers is scoped per node by the
   * declared `free_symbols` closure (`declaredSymbolScope`), so a symbol edit reopens
   * the statements that declare it and their dependents rather than the whole paper.
   * A node with no declaration still reopens on any change.
   */
  symbol_basis?: Record<string, string>;
  /** Every proved node (spec statements + agent-added lemmas), keyed by id. */
  solved: Record<string, SolvedMember>;
  /**
   * This round's proposal payload, adjudicated as a unit.
   *
   * Previously five sibling `proposed_*.json` files with no tie between them, so each
   * consumer read its own subset and the subsets disagreed (apply never read the
   * proofs; the D0.5 reviewers read none of it). The payload has exactly this state's
   * lifecycle — per round, cleared on apply, invalidated when D-1.2 advances the
   * proposal revision — so it lives here, and the closure invariant
   * `ids(core) ⊆ ids(proto) ∪ ids(working)` becomes structural.
   *
   * Access ONLY through `solve/proposals.ts`; it falls back to the legacy files for
   * runs that checkpointed before the fold. Typed as `unknown`-free but structurally,
   * to avoid a cycle with stage0_apply's raw edit types.
   */
  proposals?: {
    statements: unknown[];
    definitions: unknown[];
    assumptions: unknown[];
    coreEdits: unknown[];
    /** `argues_proposed`: the proof argues the same-round PROPOSED statement text for
     *  this id (see solve/proposals.ts `ProvisionalProof`); apply promotes it when that
     *  basis materializes. Kept structural here to avoid an import cycle. */
    proofs: Array<{ id: string; proof_tex: string; argues_proposed?: boolean }>;
  };
  /** Independently adjudicated exact edits remain authoritative across any number
   * of solve regenerations and are cleared only by a successful atomic apply or an
   * explicit, content-addressed cancellation journal event. */
  required_core_edit_mandates?: RequiredCoreEditMandate[];
  /**
   * Solved OEQs are not ordinary added theorems: their source `oeq:` node still
   * lives in the frozen proto used to rebuild later D0 rounds. This map makes
   * the D0-boundary replacement durable; the answer theorem itself is in `solved`.
   */
  /** String values from the first implementation are recognized and safely re-solved. */
  resolved_oeqs?: Record<string, ResolvedOeq | string>;
  /**
   * Cumulative directive-authorized prose overlay (Phase 1 of the 2026-07-30
   * store consolidation). `prose_updates` used to be applied to BOTH core.json
   * and the frozen proto mid-round (`applyProseUpdates` — the only
   * non-transactional proto writer); now the round merges them here and
   * `assembleCore` applies the overlay at render time. Absent on pre-migration
   * cursors (their prose is already baked into the proto by the old dual write).
   */
  prose_overlay?: ProseOverlay;
  /**
   * Proto-resident lemmas removed from the published paper by the maximality-
   * checkpoint orphan prune. The proto still defines them (only an orchestrator
   * proto edit deletes them there), so the pure render needs this durable filter
   * — without it every re-assembly would resurrect the pruned node. An entry
   * whose id later leaves the proto (the orchestrator applied the edit) is inert.
   */
  pruned_proto_orphans?: string[];
  /**
   * Store-format generation. `2` = written by post-consolidation code (core.json
   * is a pure render of (proto, working)); absent = pre-migration writer. The
   * replay harness keys its assemble-equivalence severity on this: divergence is
   * report-only on legacy cursors, a hard failure on format ≥ 2 (unless a D0.R
   * in-place edit is on record for the run).
   */
  store_format?: number;
}

/** The current writer's store-format generation (see `WorkingState.store_format`). */
export const WORKING_STORE_FORMAT = 2;

/** Stable identity of the D-1.2 source revision currently under D0. */
export function proposalRevision(state: {
  proposed_from?: { current_angle_index?: number; current_version?: number };
}): string | undefined {
  const angle = state.proposed_from?.current_angle_index;
  const version = state.proposed_from?.current_version;
  return typeof angle === "number" && typeof version === "number"
    ? `angle:${angle}/version:${version}`
    : undefined;
}

export function workingPath(ctx: PipelineContext): string {
  return artifactPath(ctx.repoRoot, ctx.qid, "discovery", "d0_working.json", [`${ctx.qid}_d0_working.json`]);
}
export function escalationLogPath(ctx: PipelineContext): string {
  return artifactPath(ctx.repoRoot, ctx.qid, "discovery", "d0_escalation_log.jsonl", [
    `${ctx.qid}_d0_escalation_log.jsonl`,
  ]);
}

function validateWorkingMandates(working: WorkingState): void {
  if (working.required_core_edit_mandates === undefined) return;
  working.required_core_edit_mandates = working.required_core_edit_mandates.map((raw) => {
    const mandate = RequiredCoreEditMandateSchema.parse(raw);
    assertMandateIntegrity(mandate);
    return mandate;
  });
}

export async function loadWorkingState(ctx: PipelineContext): Promise<WorkingState | null> {
  const p = workingPath(ctx);
  if (!existsSync(p)) return null;
  try {
    const working = JSON.parse(await readFile(p, "utf8")) as WorkingState;
    // Repair legacy decoded control-escape corruption carried in solved
    // proof_tex/snapshots from before the escape defense.
    repairLatexStringsDeep(working, new Set(["source_fingerprint", "required_core_edit_mandates"]));
    validateWorkingMandates(working);
    return working;
  } catch (err) {
    throw new Error(
      `D0 working cursor is corrupt at ${p}; refusing to discard carried nodes/proofs: ` +
        `${err instanceof Error ? err.message : String(err)}`,
    );
  }
}
/** Proof bytes present in `prev` (on disk) that `next` no longer holds anywhere.
 *  Exported for tests; the semantics are the whole point:
 *    • a solved record whose bytes changed → "displaced"
 *    • a solved record that vanished → "dropped"
 *    • a provisional proposal payload cleared without landing in `solved` → "proposal-cleared"
 *  Bytes still present under the same id (including a provisional payload promoted into
 *  `solved`) are NOT displaced — hot state keeps them and nothing is archived. */
export function displacedProofBytes(prev: WorkingState | null, next: WorkingState): ProofToArchive[] {
  if (!prev) return [];
  const out: ProofToArchive[] = [];
  for (const [id, rec] of Object.entries(prev.solved ?? {})) {
    const bytes = rec.proof_tex ?? "";
    if (bytes.trim().length === 0) continue;
    const now = next.solved?.[id];
    if (now === undefined) {
      out.push({ nodeId: id, proofTex: bytes, reason: `dropped/round-${next.round}`, snapshot: rec.snapshot });
    } else if ((now.proof_tex ?? "") !== bytes) {
      out.push({ nodeId: id, proofTex: bytes, reason: `displaced/round-${next.round}`, snapshot: rec.snapshot });
    }
  }
  for (const p of prev.proposals?.proofs ?? []) {
    const bytes = p.proof_tex ?? "";
    if (bytes.trim().length === 0) continue;
    const carried = next.proposals?.proofs?.some((q) => q.id === p.id && q.proof_tex === bytes);
    const promoted = (next.solved?.[p.id]?.proof_tex ?? "") === bytes;
    if (!carried && !promoted) {
      out.push({ nodeId: p.id, proofTex: bytes, reason: `proposal-cleared/round-${next.round}` });
    }
  }
  return out;
}

/** Every proof byte-string currently living in HOT state, by node id (solved records,
 *  their durable nodes, and the round's provisional proposal payloads). The raw-file
 *  archive sweeps consult this so bytes that remain hot are never recorded as archived
 *  — archiving live bytes would poison provenance ("archived" must mean "left hot
 *  state") and its dedup row would later suppress the record of a REAL displacement. */
export function hotProofBytes(w: WorkingState | null): Map<string, Set<string>> {
  const hot = new Map<string, Set<string>>();
  const add = (id: string, bytes: string | undefined): void => {
    if (bytes === undefined || bytes.trim().length === 0) return;
    let set = hot.get(id);
    if (!set) { set = new Set(); hot.set(id, set); }
    set.add(bytes);
  };
  if (!w) return hot;
  for (const [id, rec] of Object.entries(w.solved ?? {})) {
    add(id, rec.proof_tex);
    if (rec.node) add(id, rec.node.proof_tex);
  }
  for (const p of w.proposals?.proofs ?? []) add(p.id, p.proof_tex);
  return hot;
}

/** Single-store invariants enforced at the ONE write boundary (Phase 1 of the
 *  store consolidation — these replace the cross-store checks that policed the
 *  same states after the fact):
 *  - an answered OEQ's working record is retired (the answer lives under the
 *    theorem id; a surviving source record was the `oeq-source-record-retired`
 *    warn class — now auto-resolved at write);
 *  - a resolution must name a theorem the store holds (was the throw inside
 *    `reconcileProofStores`: that state claims an open question is answered by
 *    a result present in no store, and nothing can reconstruct it). */
export function normalizeWorkingState(w: WorkingState): void {
  const resolutions = Object.entries(w.resolved_oeqs ?? {});
  for (const [sourceId] of resolutions) {
    if (w.solved[sourceId] !== undefined) delete w.solved[sourceId];
  }
  const dangling = resolutions
    .map(([src, r]) => [src, typeof r === "string" ? r : r.theorem_id] as const)
    .filter(([, theoremId]) => !w.solved[theoremId]);
  if (dangling.length > 0) {
    throw new Error(
      `D0 working state resolved-OEQ points at an absent theorem: ` +
        `${dangling.map(([s, t]) => `${s}->${t}`).join(", ")}. ` +
        "The store would claim an open question is answered by a result it does not hold; " +
        "refusing to persist an incoherent state.",
    );
  }
}

export async function saveWorkingState(ctx: PipelineContext, w: WorkingState): Promise<void> {
  validateWorkingMandates(w);
  // `store_format` is deliberately NOT stamped here: a quiescent CLI that
  // mutates a legacy cursor without re-rendering core.json must not promote the
  // run to "post-consolidation" (the replay harness keys hard-fail severity on
  // it). The writers that render core.json through `assembleCore` stamp it.
  normalizeWorkingState(w);
  // Archive-on-displacement at the store boundary. Diffing against the ON-DISK previous
  // cursor (not whatever object the caller mutated) is what makes this immune to
  // call-site mistakes: any path that overwrites or deletes proof bytes — statement
  // reopen, OEQ resolution, proposal reset, auto-heal, or a future bug — passes through
  // this write, and the displaced bytes are already in the cold archive when it lands.
  // The archive is never read by dispatch/context assembly (see proof_archive.ts).
  //
  // ORDER IS DELIBERATE: archive first, then write. A crash in between leaves a
  // premature archive row for bytes that are in fact still hot (their later real
  // displacement is then dedup-suppressed — a provenance blemish, nothing lost). The
  // reverse order would open a window where displaced bytes are GONE from hot state
  // with no archive record, violating the module's core invariant.
  const displaced = displacedProofBytes(await loadWorkingState(ctx), w);
  if (displaced.length > 0) await archiveProofs(path.dirname(workingPath(ctx)), displaced);
  await writeJsonAtomic(workingPath(ctx), w);
}

/** One orchestrator resolution, appended when a proposed change is applied. */
export interface EscalationLogEntry {
  /** Idempotency key for a replayable multi-file D0 apply transaction. */
  transaction_id?: string;
  round: number;
  changed: Array<{ id: string; kind: "definition" | "statement" | "assumption" | "bibliography" | "symbol" | "metadata"; from: string; to: string; reason: string }>;
  note?: string;
  /** A standalone orchestrator directive to the next solve (no applied change) — e.g. a
   *  D0.5 review finding routed back for re-derivation. Rendered even when `changed` is empty. */
  directive?: string;
  /** Fail closed when the directive explicitly requires frozen-core/metadata edits.
   * The next solve must emit at least one structured proposal instead of merely
   * rewriting proofs/prose around a stale node. */
  require_core_changes?: boolean;
  /** Auditable retirement of a pending bare `require_core_changes` guard when review
   * determines that the requested repair is prose-only. Exact edit mandates have
   * their own content-addressed cancellation mechanism and are unaffected. */
  cancel_require_core_changes?: boolean;
  /** Exact structured-proposal targets required by this directive. */
  required_core_targets?: string[];
  /** Auditable retirement of bare required targets that later normalize to a
   * proven no-op. Exact edit mandates remain separately content-addressed. */
  cancelled_core_targets?: string[];
  /** Exact, already-adjudicated structured edits that the next atomic bundle must
   * carry. Unlike prose directives, these are typed operations: the solver may
   * provide surrounding mathematics, but cannot silently replace a required delete
   * with a fresh proof of the obsolete node. */
  required_core_edits?: RawCoreEdit[];
  /** Durable form written by the current CLI. Raw required_core_edits above is
   * parsed only so every live or consumed legacy row can fail closed. */
  required_core_edit_mandates?: RequiredCoreEditMandate[];
  /** Auditable retirement of an exact mandate rejected by subsequent mandatory
   * review. These events are journal-only and never authored by solve workers. */
  cancelled_core_edit_mandates?: RequiredCoreEditMandateCancellation[];
  /** PROVENANCE ONLY — record this verdict/critique in the journal, but do NOT treat it as
   *  a re-solve directive.
   *
   *  An untargeted pending directive makes D0 force EVERY statement open
   *  (`stage0_solve.ts`, `requiredCoreTargets.size === 0` branch), discarding the whole
   *  `d0_working.json` reuse cursor and re-deriving the entire paper. That is right for a
   *  real "fix the paper" directive and catastrophic for an entry whose only job is to stop
   *  a paid verdict from being lost (the citation-source halt, a non-salvageable
   *  below-floor tier). Such entries carry no targets by nature, so without this flag they
   *  silently select the most expensive possible behaviour. */
  provenance_only?: boolean;
}
export async function appendEscalationLog(ctx: PipelineContext, entry: EscalationLogEntry): Promise<void> {
  await appendFile(escalationLogPath(ctx), JSON.stringify(entry) + "\n", "utf8");
}
export async function readEscalationLog(ctx: PipelineContext): Promise<EscalationLogEntry[]> {
  const p = escalationLogPath(ctx);
  if (!existsSync(p)) return [];
  const txt = await readFile(p, "utf8");
  const entries: EscalationLogEntry[] = [];
  txt.split("\n").forEach((l, i) => {
    if (l.trim().length === 0) return;
    try {
      const entry = JSON.parse(l) as EscalationLogEntry;
      repairLatexStringsDeep(entry, new Set(["source_fingerprint", "from", "to", "required_core_edit_mandates"]));
      if (entry.required_core_edits !== undefined) {
        entry.required_core_edits = entry.required_core_edits.map((edit) => ProposedCoreEditSchema.parse(edit));
      }
      if (entry.required_core_edit_mandates !== undefined) {
        entry.required_core_edit_mandates = entry.required_core_edit_mandates.map((mandate) =>
          RequiredCoreEditMandateSchema.parse(mandate));
        entry.required_core_edit_mandates.forEach(assertMandateIntegrity);
      }
      if (entry.cancelled_core_edit_mandates !== undefined) {
        entry.cancelled_core_edit_mandates = entry.cancelled_core_edit_mandates.map((cancellation) =>
          RequiredCoreEditMandateCancellationSchema.parse(cancellation));
        entry.cancelled_core_edit_mandates.forEach(assertMandateCancellationIntegrity);
      }
      entries.push(entry);
    } catch (err) {
      // This journal carries accepted edits and directives. Skipping a torn row
      // silently loses an operator decision and may let the cursor advance on a
      // stale core. Fail before dispatch so recovery is explicit and token-free.
      // (Deliberate: tolerating even a torn FINAL row was considered and rejected —
      // an operator decision is worth an explicit repair, and this costs no tokens
      // because it fires in preflight, before any dispatch.)
      throw new Error(
        `D0 escalation journal is corrupt at ${p}:${i + 1}; refusing to skip an accepted edit/directive: ` +
          `${err instanceof Error ? err.message : String(err)}\n` +
          `REPAIR: this fires in resume PREFLIGHT, so no tokens have been spent and no stage has run. ` +
          `Inspect line ${i + 1}. If it is the LAST line and truncated mid-write, an append was interrupted ` +
          `and that entry never committed — delete that one line and resume. If it is mid-file, an operator ` +
          `decision is genuinely lost: reconstruct it from orchestrator/decision_log.jsonl before resuming.`,
      );
    }
  });
  return entries;
}

/**
 * Guarded repair for an ownership-overlap defect in an UNCONSUMED directive.
 *
 * A target-scoped directive occasionally names both an OEQ and the theorem that is
 * created when that OEQ is resolved. D0 then dispatches them as independent units,
 * although the OEQ unit legitimately owns both writes, and the capability gate stops
 * before merge. This operation narrows exactly one pending target list to a strict
 * subset. It does not alter the directive prose, cursor, core, or any consumed journal
 * entry. The journal replacement is atomic, so readers never observe a torn JSONL file.
 */
export async function narrowPendingDirectiveTargets(
  ctx: PipelineContext,
  args: { owner: string; dropTargets: string[] },
): Promise<{ entryIndex: number; before: string[]; after: string[] }> {
  if (!args.owner.trim()) throw new Error("pending-directive narrowing requires a nonempty owner target");
  const drops = new Set(args.dropTargets.filter((id) => id.trim().length > 0));
  if (drops.size === 0) throw new Error("pending-directive narrowing requires at least one drop target");
  if (drops.has(args.owner)) throw new Error(`refusing to drop owner target ${args.owner}`);

  const p = escalationLogPath(ctx);
  const original = await readFile(p, "utf8");
  const entries = await readEscalationLog(ctx);
  const working = await loadWorkingState(ctx);
  const consumed = Math.min(working?.escalation_entries_consumed ?? 0, entries.length);
  const matches = entries
    .map((entry, entryIndex) => ({ entry, entryIndex }))
    .filter(({ entry, entryIndex }) =>
      entryIndex >= consumed &&
      entry.required_core_targets?.includes(args.owner) === true &&
      [...drops].every((id) => entry.required_core_targets?.includes(id) === true),
    );
  if (matches.length !== 1) {
    throw new Error(
      `expected exactly one unconsumed directive containing owner ${args.owner} and drops ` +
        `${[...drops].join(", ")}; found ${matches.length}`,
    );
  }

  const { entry, entryIndex } = matches[0];
  const before = [...(entry.required_core_targets ?? [])];
  const after = before.filter((id) => !drops.has(id));
  if (after.length === 0 || after.length >= before.length || !after.includes(args.owner)) {
    throw new Error("replacement target list must be a nonempty strict subset retaining the owner");
  }
  entry.required_core_targets = after;

  const lines = original.split("\n");
  // Nonempty JSONL rows map one-to-one to readEscalationLog entries. Refuse exotic
  // blank-line layouts instead of risking a write to the wrong physical row.
  const nonemptyLineIndexes = lines
    .map((line, i) => ({ line, i }))
    .filter(({ line }) => line.trim().length > 0)
    .map(({ i }) => i);
  if (nonemptyLineIndexes.length !== entries.length) throw new Error("escalation journal row mapping changed during repair");
  lines[nonemptyLineIndexes[entryIndex]] = JSON.stringify(entry);
  const replacement = lines.join("\n");
  const temp = `${p}.tmp-${process.pid}-${Date.now()}`;
  try {
    await writeFile(temp, replacement, "utf8");
    // Parse the candidate before the atomic swap.
    for (const line of replacement.split("\n").filter((value) => value.trim().length > 0)) JSON.parse(line);
    await rename(temp, p);
  } finally {
    await rm(temp, { force: true });
  }
  return { entryIndex, before, after };
}

/** Fingerprint the proto's symbol table as the GLOBAL reuse basis for carried proofs:
 *  name → hex hash of the SEMANTIC fields. Hashing keeps the values immune to the
 *  LaTeX-escape repair applied to the loaded cursor, and the basis is order-independent
 *  by construction (`topologicallyOrderSymbols` reorders the array on every apply).
 *
 *  `ref` IS semantic and is included. It names the node a symbol denotes (`def:…` on a
 *  class symbol, occasionally `ass:…`), so re-pointing it swaps the symbol's referent
 *  while `type`/`space`/`sig`/`def`/`role` can stay byte-identical — the prose in `def`
 *  routinely describes the object generically ("Nonhomogeneous subclass of …") and does
 *  not name which definition carves it. Excluding it meant a statement quoting that
 *  symbol kept a proof about the OLD object. The two writers are `d0_apply`'s
 *  statement-delete-with-replacement (re-point) and definition-delete (clear), and both
 *  are cases where the referent genuinely vanished, so there is no spurious-rewire case
 *  to protect against. Narrow blast radius either way: 13 of the 2095 symbols in the 42
 *  real cores under doc/research carry `ref` at all.
 *
 *  `refs` stays EXCLUDED. It lists the other symbols this symbol's `def` mentions and
 *  exists for G1's defined-before-use ordering check — it is derived from `def`, which is
 *  already hashed, so it carries no meaning of its own and would only add invalidation on
 *  a pure re-ordering. 1287 symbols carry it. */
export function symbolBasis(proto: Core): Record<string, string> {
  const out: Record<string, string> = {};
  for (const sym of proto.symbols ?? []) {
    out[sym.name] = createHash("sha256")
      .update(
        JSON.stringify({
          type: sym.type, space: sym.space, sig: sym.sig, def: sym.def, role: sym.role, ref: sym.ref,
        }),
      )
      .digest("hex")
      .slice(0, 16);
  }
  return out;
}

/** Symbol names whose SEMANTIC definition changed (or that vanished) since the carried
 *  proofs were solved. A newly ADDED symbol invalidates nothing: no existing proof was
 *  solved against it. A legacy cursor with no recorded basis invalidates nothing (do
 *  not mass-invalidate existing runs on upgrade). */
export function changedSymbolNames(prev: WorkingState | null, proto: Core): Set<string> {
  const before = prev?.symbol_basis;
  if (!before) return new Set();
  const after = symbolBasis(proto);
  // Admitting `ref` to the fingerprint is not a corpus-wide re-baselining: `JSON.stringify`
  // omits an `undefined` value, so a symbol without `ref` hashes exactly as it did before
  // and a cursor checkpointed under the old scheme still matches. Only the 13 ref-bearing
  // symbols in the 42 real cores re-fingerprint, and those reclassify ONCE, in the safe
  // direction (their citing nodes re-derive). Excusing them by also comparing against the
  // old hashing would do the opposite — a `ref` that genuinely moved across the upgrade
  // boundary would go unnoticed, which is the exact failure this field was added to close.
  const changed = new Set<string>();
  for (const [name, fingerprint] of Object.entries(before)) {
    if (after[name] !== fingerprint) changed.add(name);
  }
  return changed;
}

/** The symbols a carried node's claim rests on, as DECLARED — its own `free_symbols`
 *  plus those of every definition/assumption in its snapshot closure — or `null` when
 *  the scope is UNDECLARED and must be read as "may use ANY symbol".
 *
 *  THE FAIL-SAFE IS THE WHOLE POINT. `StatementSchema`/`DefinitionSchema` spell
 *  `free_symbols` `.optional()` precisely so `undefined` survives parsing: real cores
 *  mix newer declarations with legacy nodes that predate the field, and a `.default([])`
 *  would present every legacy node as "declared, and uses no symbols" — scoping symbol
 *  changes to nothing and publishing proofs of materially different claims as current.
 *  `[]` is a real declaration and does scope; `undefined` never does. Any undeclared
 *  member of the closure poisons the whole scope, because a symbol can be used ONLY
 *  through a definition the statement cites.
 *
 *  The CURRENT declarations are read, not the ones stored at solve time: a declaration
 *  that grew must widen the scope immediately (a snapshot copy would keep watching the
 *  old, narrower list). Definitions/assumptions that vanished from the proto are skipped
 *  — `snapshotBasisValid` already fails such a node outright. */
export function declaredSymbolScope(
  proto: Core,
  member: CoreStatement,
  snapshot: MemberSnapshot,
): Set<string> | null {
  if (member.free_symbols === undefined) return null;
  const scope = new Set<string>(member.free_symbols.map(normalizeSymbol));
  const defById = new Map(proto.definitions.map((d) => [d.id, d] as const));
  const assById = new Map(proto.assumptions.map((a) => [a.id, a] as const));
  for (const id of Object.keys(snapshot.defs)) {
    const d = defById.get(id);
    if (!d) continue;
    if (d.free_symbols === undefined) return null;
    for (const s of d.free_symbols) scope.add(normalizeSymbol(s));
  }
  for (const id of Object.keys(snapshot.assumptions)) {
    const a = assById.get(id);
    if (!a) continue;
    // `AssumptionSchema.free_symbols` is `.optional()` like the other two, so an
    // assumption that never declared survives parsing as `undefined` and poisons the
    // scope here exactly as an undeclared definition does. (994 of the 996 real
    // assumptions declare, 80 of them legitimately `[]`, so this bites almost nothing.)
    if (a.free_symbols === undefined) return null;
    for (const s of a.free_symbols) scope.add(normalizeSymbol(s));
  }
  return scope;
}

/** Does a symbol change reach this node? `null` scope (never declared) is reached by
 *  ANY change — that is the fail-safe that keeps legacy cores sound. */
function symbolScopeStale(changed: Set<string>, scope: Set<string> | null): boolean {
  if (changed.size === 0) return false;
  if (scope === null) return true;
  for (const name of changed) if (scope.has(normalizeSymbol(name))) return true;
  return false;
}

/** Snapshot the content closure of a member against the CURRENT proto. */
export function snapshotMember(proto: Core, member: CoreStatement): MemberSnapshot {
  const defs: Record<string, string> = {};
  const assumptions: Record<string, string> = {};
  const defById = new Map(proto.definitions.map((d) => [d.id, d] as const));
  const assById = new Map(proto.assumptions.map((a) => [a.id, a] as const));
  const visitDef = (id: string): void => {
    if (defs[id] !== undefined) return;
    const d = defById.get(id);
    if (!d) return;
    defs[id] = d.construction;
    // why: structured definition refs are transitive dependencies for proof reuse.
    for (const r of d.by_member_properties ?? []) visitDep(r);
    for (const r of d.inputs ?? []) visitDep(r);
  };
  const visitDep = (dep: string): void => {
    if (dep.startsWith("def:")) {
      visitDef(dep);
    } else if (dep.startsWith("ass:")) {
      const a = assById.get(dep);
      if (a) assumptions[dep] = a.condition;
    }
  };
  for (const dep of member.depends_on ?? []) visitDep(dep);
  return { stmt: member.statement, depends_on: [...(member.depends_on ?? [])], defs, assumptions };
}

/** Is a stored snapshot still a valid REUSE BASIS against the current proto?
 *
 *  Valid iff the member's own statement text is unchanged AND every definition /
 *  assumption the proof was solved against (the STORED closure — captured after
 *  citation auto-wiring, so it includes everything the proof text cites) still exists
 *  with byte-identical content. The `depends_on` EDGE SET is deliberately NOT compared:
 *  an edge added or removed with all referenced content intact is dependency
 *  bookkeeping, not a change to what the proof established. Content NEWLY entering the
 *  closure via edge growth postdates the proof, which never used it; content leaving
 *  the closure is still checked through the stored map (a removed-AND-edited def
 *  invalidates). Upstream statement-node changes propagate separately in
 *  `computeValidNodes`. */
function snapshotBasisValid(snapshot: MemberSnapshot, proto: Core, member: CoreStatement): boolean {
  if (snapshot.stmt !== member.statement) return false;
  const defById = new Map(proto.definitions.map((d) => [d.id, d.construction] as const));
  const assById = new Map(proto.assumptions.map((a) => [a.id, a.condition] as const));
  for (const [id, construction] of Object.entries(snapshot.defs)) {
    if (defById.get(id) !== construction) return false;
  }
  for (const [id, condition] of Object.entries(snapshot.assumptions)) {
    if (assById.get(id) !== condition) return false;
  }
  return true;
}

/** A member is VALID (its prior proof may be reused) iff it was solved before AND
 *  its stored content basis is intact (see `snapshotBasisValid`). */
export function memberValid(prev: WorkingState | null, proto: Core, member: CoreStatement): boolean {
  const rec = prev?.solved[member.id];
  if (!rec || rec.partial) return false; // a partial result is not a reusable proof
  // Symbol basis, SCOPED by the node's declared symbol closure (see
  // `declaredSymbolScope`): a node that never declared its symbols is invalidated by
  // any symbol change, exactly as the earlier global rule did.
  if (symbolScopeStale(changedSymbolNames(prev, proto), declaredSymbolScope(proto, member, rec.snapshot))) {
    return false;
  }
  return snapshotBasisValid(rec.snapshot, proto, member);
}

/** The set of solved-node ids whose proofs may be REUSED this round. A node is
 *  reusable iff it was solved, its own content closure is byte-identical to what it
 *  was solved against, AND every node it depends on is also reusable — staleness
 *  propagates along `depends_on`, so correcting a `def` invalidates exactly the
 *  nodes that (transitively) consume it. Spec statements come from `proto`;
 *  agent-added lemmas come from the prior working state. */
export function computeValidNodes(prev: WorkingState | null, proto: Core): Set<string> {
  if (!prev) return new Set();
  // SYMBOL BASIS. A re-defined (or deleted) symbol changes what every statement quoting
  // it claims while all statement/def/assumption TEXT stays byte-identical, so no
  // content snapshot can see it. Symbols are not `depends_on` edges, so the reach of the
  // change has to come from a DECLARED edge — `free_symbols` — never from scanning the
  // prose for the symbol's name, which was measured unsound in both directions (bare
  // single-letter names like `d`/`n` match every statement through ordinary English;
  // `\(\pi_n\)`-wrapped names match nothing; use through a definition is invisible
  // either way). A node with no declaration is therefore treated as using EVERY symbol
  // and reopens on any change, which is exactly the old global rule and keeps every
  // pre-existing core sound. Directly-hit nodes enter `stale` below and the ordinary
  // `depends_on` fixpoint carries the change to their dependents — no second
  // propagation. (`merge.ts` keeps its whole-round rule for a PROPOSED symbol edit:
  // that is about the in-flight round, not about carried proofs.)
  const changedSymbols = changedSymbolNames(prev, proto);
  const specById = new Map(proto.statements.map((s) => [s.id, s] as const));
  const lemmaById = new Map(
    Object.entries(prev.solved)
      .filter(([, r]) => r.node)
      .map(([id, r]) => [id, r.node as CoreStatement] as const),
  );
  // PROTO WINS. The spread order used to let a same-id agent record override the frozen
  // proto statement, so a carried proof was validated — and reused — against the AGENT's
  // claim rather than the frozen one it is supposed to discharge.
  const nodeById = new Map<string, CoreStatement>([...lemmaById, ...specById]);
  const solvedIds = new Set(Object.keys(prev.solved));
  // An agent record colliding with a proto id is only reusable if it says the same thing;
  // otherwise it must be re-derived against the frozen claim.
  // Compare the whole node, not just the claim text: a same-id agent record that differs
  // in kind or dependencies is equally unusable against the frozen member. (Comparing
  // only `statement` also made the Map-order fix above untestable, because this check
  // alone caught the claim case.)
  const collidesWithProto = new Set<string>(
    [...lemmaById.keys()].filter((id) => {
      const spec = specById.get(id);
      if (spec === undefined) return false;
      const agent = lemmaById.get(id)!;
      const deps = (d?: string[]): string => [...new Set(d ?? [])].sort().join("\u0000");
      return spec.statement !== agent.statement ||
        spec.kind !== agent.kind ||
        deps(spec.depends_on) !== deps(agent.depends_on);
    }),
  );

  // Directly stale: unsolved, PARTIAL (open obligation — not a finished proof), or own
  // closure changed since it was solved.
  const stale = new Set<string>();
  for (const [id, node] of nodeById) {
    if (!solvedIds.has(id) || prev.solved[id].partial) {
      stale.add(id);
      continue;
    }
    // A record whose stored claim contradicts the frozen proto cannot be reused.
    if (collidesWithProto.has(id)) {
      stale.add(id);
      continue;
    }
    // A settled record with NO proof is not a finished result. `cited` is exempt: its
    // justification IS the citation, so it legitimately carries no proof_tex.
    if (node.status !== "cited" && (prev.solved[id].proof_tex ?? "").trim().length === 0) {
      stale.add(id);
      continue;
    }
    // A statement dependency that has VANISHED from both stores leaves nothing to
    // discharge it. The propagation below only reaches deps still present in nodeById, so
    // a deleted dependency silently left its consumer "valid". AUTHORED edges
    // only: a wired (prose-cited) ref that exists nowhere is the
    // cite-without-emit class, owned by the consistency gate — treating it as a
    // vanished dependency would read the record permanently stale (audit R2BB2).
    const missingDep = (node.depends_on ?? []).some(
      (d) => /^(thm|lem|prop|oeq|conj):/.test(d) && !nodeById.has(d),
    );
    if (missingDep) {
      stale.add(id);
      continue;
    }
    // A symbol this node DECLARES (directly, or through a def/assumption in its
    // snapshot closure) was re-defined — same text, different claim.
    if (symbolScopeStale(changedSymbols, declaredSymbolScope(proto, node, prev.solved[id].snapshot))) {
      stale.add(id);
      continue;
    }
    if (!snapshotBasisValid(prev.solved[id].snapshot, proto, node)) stale.add(id);
  }
  // Propagate along the WIRED edge set (authored deps ∪ the snapshot's cited
  // closure) to a fixpoint — an upstream change reaches every proof that cites
  // the node, declared or prose-cited.
  const propagationEdges = (id: string, node: CoreStatement): Iterable<string> =>
    new Set([
      ...(node.depends_on ?? []),
      ...(prev.solved[id]?.snapshot?.depends_on ?? []),
    ]);
  for (let changed = true; changed; ) {
    changed = false;
    for (const [id, node] of nodeById) {
      if (stale.has(id)) continue;
      for (const dep of propagationEdges(id, node)) {
        if (dep !== id && nodeById.has(dep) && stale.has(dep)) {
          stale.add(id);
          changed = true;
          break;
        }
      }
    }
  }
  const valid = new Set<string>();
  for (const id of solvedIds) if (nodeById.has(id) && !stale.has(id)) valid.add(id);
  return valid;
}

/** At the MAXIMALITY CHECKPOINT (clean discharge, stable graph), discard lemmas no
 *  longer reachable from any non-lemma claim (theorem / proposition / conjecture) via
 *  `depends_on`. Across escalation rounds an abandoned proof route leaves orphan helper
 *  lemmas in the working state + assembled core; without this they leak into the rendered
 *  paper and the downstream graph. Reachability is computed on the assembled `core` (the
 *  merged spec+agent graph). SAFE ONLY on a clean discharge — pruning mid-iteration would
 *  kill a lemma whose consumer is temporarily open. Mutates `core.statements` and
 *  `working.solved` in place; returns the pruned lemma ids and, separately, the subset
 *  that ALSO live in the frozen `proto` (those need a proto edit by the orchestrator —
 *  pruning the core alone lets a re-solve re-assemble them from the proto). */
export function pruneOrphanLemmas(
  core: Core,
  working: WorkingState,
  proto: Core,
): { pruned: string[]; protoOrphans: string[] } {
  // Reachability is over the UNION of the derived core and the durable agent-node catalog.
  // Refusing to prune when those stores diverged was safe but terminal: an unreferenced
  // partial lemma absent from core could never re-enter the clean core, so every later
  // checkpoint refused again and its proof accumulated forever. The cursor carries the
  // missing node's full statement and proof, which is enough to decide reachability without
  // guessing. A working-only non-lemma consumer remains a root and protects its helpers;
  // a working-only lemma with no such depender is a genuine orphan and can be removed.
  const byId = new Map<string, CoreStatement>(core.statements.map((s) => [s.id, s] as const));
  for (const [id, rec] of Object.entries(working.solved)) {
    if (!rec.node || byId.has(id)) continue;
    byId.set(id, { ...rec.node, proof_tex: rec.proof_tex || rec.node.proof_tex });
  }
  // Roots = every non-lemma claim plus every cited leaf. Cited comparator lemmas
  // are literature deliverables audited by D0.5, not abandoned internal proof
  // helpers; they often appear only in related-work prose and have no theorem
  // depends_on edge.
  const reachable = new Set<string>();
  const stack: string[] = [];
  for (const s of byId.values()) {
    if (s.kind !== "lemma" || s.status === "cited") {
      reachable.add(s.id);
      stack.push(s.id);
    }
  }
  // A node's reachability edges are its `depends_on` PLUS any node id referenced in its
  // proof / statement prose. The solver's `depends_on` is not always complete vs. the ids it
  // cites in prose (e.g. sentence-initial `Lem:foo`), so following depends_on alone prunes
  // lemmas a surviving proof actually uses — deleting load-bearing helpers (PIPELINE_NOTES
  // 2026-06-30, estimator-side linearization lemmas). Treating prose references as edges
  // keeps a genuinely-used lemma; an abandoned-route orphan, cited by no surviving result, is
  // still unreferenced and still pruned.
  // Go through `extractNodeRefs`, NOT a raw `nodeRefRegex()` matchAll — it is the extractor
  // that normalizes a LaTeX-escaped hyphen (`lem:beta\text{-}free`) back to the plain-`-` id
  // grammar. Lowercasing the raw match yields the truncated `lem:beta`, the real lemma loses
  // its last inbound prose edge, and THIS FUNCTION DELETES IT — while `findDanglingCitations`
  // below, which does use the extractor, resolves the same reference. Keep every reachability
  // consumer on the one extractor so the two can never disagree.
  const edgesOf = (s: CoreStatement | undefined): string[] => {
    if (!s) return [];
    const refs = new Set<string>(s.depends_on ?? []);
    const prose = `${s.proof_tex ?? ""} ${s.statement ?? ""}`;
    for (const r of extractNodeRefs(prose)) refs.add(r);
    return [...refs];
  };
  while (stack.length > 0) {
    const s = byId.get(stack.pop() as string);
    for (const dep of edgesOf(s)) {
      if (byId.has(dep) && !reachable.has(dep)) {
        reachable.add(dep);
        stack.push(dep);
      }
    }
  }
  const pruned = [...byId.values()].filter((s) => s.kind === "lemma" && !reachable.has(s.id)).map((s) => s.id);
  if (pruned.length === 0) return { pruned: [], protoOrphans: [] };
  const prunedSet = new Set(pruned);
  core.statements = core.statements.filter((s) => !prunedSet.has(s.id));
  for (const id of pruned) delete working.solved[id];
  const protoIds = new Set(proto.statements.map((s) => s.id));
  const protoOrphans = pruned.filter((id) => protoIds.has(id));
  return { pruned, protoOrphans };
}

/** Detect "cite-without-emit" dangling citations: a `proof_tex` / `statement` prose that
 *  references a `lem:/thm:/prop:/oeq:/conj:/def:/ass:` id which is NOT a defined member of
 *  the assembled core (statements ∪ definitions ∪ assumptions). The D0 solver sometimes
 *  writes a proof that INVOKES a helper lemma it never EMITS as a member — the reference is
 *  then silently dangling (`pruneOrphanLemmas` can keep a genuinely-emitted lemma reachable
 *  via prose, but it cannot resurrect one that was never emitted). Such a core reads as
 *  "fully proved" yet has an unproven step; it sails into the EXPENSIVE D0.5 panel, fails
 *  there, and triggers a full repair re-solve. This deterministic check catches it at the
 *  cheapest point (D0 discharge, ~0 cost). Returns `{node, ref}` pairs (node = the citing
 *  member, ref = the missing id), deduped. See PIPELINE_NOTES 2026-06-30. */
export function findDanglingCitations(
  core: Core,
  opts: { alsoKnown?: Iterable<string> } = {},
): Array<{ node: string; ref: string }> {
  const known = coreNodeIds(core);
  // A RESOLVED OEQ is not missing — it was ANSWERED, and the D0 boundary replaces the
  // question node with its answer theorem, so the `oeq:` id legitimately leaves the core
  // while proofs still name it as the question they settle. Without this the answer
  // theorem's own proof reads as citing an undefined member, and the auto-heal below
  // issues an UNSATISFIABLE directive: "emit the cited helper as a defined member" can
  // only be obeyed by re-authoring a node frozen at D-1, which the silent-alteration
  // guard then refuses. The two guards deadlock the run, and re-resuming reproduces it.
  for (const id of opts.alsoKnown ?? []) known.add(id.toLowerCase());
  const out: Array<{ node: string; ref: string }> = [];
  const seen = new Set<string>();
  for (const s of core.statements) {
    // `cited` leaves legitimately name def:/ass: notation they do not prove; skip them.
    if (s.status === "cited") continue;
    const prose = `${s.proof_tex ?? ""} ${s.statement ?? ""}`;
    // A node may also NAME another paper's result it does not depend on. Those are
    // declared in `external_refs`; honour the declaration by id as well, so a paper
    // credited in bare form (rather than as `<qid>/<node-id>`) is not a phantom defect.
    const declaredExternal = new Set(
      (s.external_refs ?? []).map((r) => r.slice(r.indexOf("/") + 1).toLowerCase()),
    );
    // Citations only: `<paper>/<node-id>` is a mention of another paper, not a claim
    // that THIS core proves it — see core/node_ids.ts.
    for (const ref of extractCitationRefs(prose)) {
      if (ref === s.id.toLowerCase()) continue; // self-reference
      if (known.has(ref)) continue;
      if (declaredExternal.has(ref)) continue;
      const key = `${s.id}|${ref}`;
      if (seen.has(key)) continue;
      seen.add(key);
      out.push({ node: s.id, ref });
    }
  }
  return out;
}

/** Format the escalation log as agent-prompt context (what the orchestrator changed
 *  and why, most recent last). Empty string when there is nothing to report. */
export function formatEscalationContext(log: EscalationLogEntry[]): string {
  if (log.length === 0) return "";
  const lines = log.flatMap((e) => {
    // A directive-only entry (review finding / orchestrator directive routed back) has
    // no `changed` array — guard so it renders the DIRECTIVE alone instead of crashing.
    const out = (e.changed ?? []).map(
      (c) => `  [round ${e.round}] ${c.kind} ${c.id} corrected: ${c.reason}${e.note ? ` — ${e.note}` : ""}`,
    );
    if (e.directive) {
      const targets = e.required_core_targets?.length
        ? ` [REQUIRED TARGETS: ${e.required_core_targets.join(", ")}]`
        : "";
      out.push(`  [round ${e.round}] DIRECTIVE${e.require_core_changes ? " [STRUCTURED CORE CHANGES REQUIRED]" : ""}${targets}: ${e.directive}`);
    }
    return out;
  });
  if (lines.length === 0) return "";
  return [
    "=== ORCHESTRATOR ESCALATION LOG (corrections applied + directives since the last solve — build on these, do not re-propose; act on every DIRECTIVE) ===",
    ...lines,
  ].join("\n");
}
