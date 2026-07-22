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
import { existsSync } from "node:fs";
import { readFile, writeFile, appendFile } from "node:fs/promises";
import path from "node:path";
import { artifactPath } from "../../paths.js";
import { archiveProofs, type ProofToArchive } from "../proof_archive.js";
import type { PipelineContext } from "../../types.js";
import { nodeRefRegex, extractCitationRefs } from "../core/node_ids.js";
import type { Core, CoreStatement } from "../core/schema.js";
import { coreNodeIds } from "../core/schema.js";
import { writeJsonAtomic } from "../../shared/json_atomic.js";
import { repairLatexStringsDeep } from "../core/latex_serialization.js";

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
  /**
   * Solved OEQs are not ordinary added theorems: their source `oeq:` node still
   * lives in the frozen proto used to rebuild later D0 rounds. This map makes
   * the D0-boundary replacement durable; the answer theorem itself is in `solved`.
   */
  /** String values from the first implementation are recognized and safely re-solved. */
  resolved_oeqs?: Record<string, ResolvedOeq | string>;
}

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

export async function loadWorkingState(ctx: PipelineContext): Promise<WorkingState | null> {
  const p = workingPath(ctx);
  if (!existsSync(p)) return null;
  try {
    const working = JSON.parse(await readFile(p, "utf8")) as WorkingState;
    // Repair legacy decoded control-escape corruption carried in solved
    // proof_tex/snapshots from before the escape defense.
    repairLatexStringsDeep(working);
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

export async function saveWorkingState(ctx: PipelineContext, w: WorkingState): Promise<void> {
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
  /** Exact structured-proposal targets required by this directive. */
  required_core_targets?: string[];
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
      repairLatexStringsDeep(entry);
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
    // a deleted dependency silently left its consumer "valid".
    const missingDep = (node.depends_on ?? []).some(
      (d) => /^(thm|lem|prop|oeq|conj):/.test(d) && !nodeById.has(d),
    );
    if (missingDep) {
      stale.add(id);
      continue;
    }
    if (!snapshotBasisValid(prev.solved[id].snapshot, proto, node)) stale.add(id);
  }
  // Propagate along depends_on to a fixpoint.
  for (let changed = true; changed; ) {
    changed = false;
    for (const [id, node] of nodeById) {
      if (stale.has(id)) continue;
      for (const dep of node.depends_on ?? []) {
        if (nodeById.has(dep) && stale.has(dep)) {
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
  const REF_RE = nodeRefRegex(); // shared definition — see core/node_ids.ts
  const edgesOf = (s: CoreStatement | undefined): string[] => {
    if (!s) return [];
    const refs = new Set<string>(s.depends_on ?? []);
    const prose = `${s.proof_tex ?? ""} ${s.statement ?? ""}`;
    for (const m of prose.matchAll(REF_RE)) refs.add(m[0].toLowerCase());
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
