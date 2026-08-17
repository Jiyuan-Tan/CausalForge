// Phase 1 of the 2026-07-30 store-consolidation migration: the pure render.
//
// `assembleCore(proto, working)` derives the published `core.json` from the two
// authoritative stores — the frozen `proto_core.json` and the mutable
// `d0_working.json` — with NO other input. It is the single writer-side source
// of the persisted core: `commitRound` (and the quiescent CLIs that used to
// dual-write core + working) render through this function, so the two stores
// can no longer disagree with the published artifact; disagreement is
// unrepresentable rather than policed (the retired checks: `store-incoherent`,
// `proved-not-partial`, `oeq-source-retired`, proposal closure,
// `reconcileProofStores`).
//
// Everything here is DERIVED and deterministic:
//   1. clone the frozen proto;
//   2. apply durable OEQ resolutions (drop answered sources, remap edges);
//   3. attach proofs / insert agent-authored nodes from `working.solved`,
//      DERIVING each published status from the record (cited / partial /
//      has-proof) — status is never stored twice;
//   4. auto-wire dependency edges from claim/proof citations (same
//      `wireStatementProofDependencies` the merge runs — deterministic over the
//      assembled statements, so re-running it here reproduces the wired edges);
//   5. apply the prose overlay (`working.prose_overlay`), the render-time home
//      of what `applyProseUpdates` used to write into BOTH core and proto;
//   6. prune dead assumptions, rebuild `assumption.used_by`, heal missing bib
//      cites, canonicalize LaTeX serialization.
//
// The published status derivation (step 3) is the one rule:
//   frozen member, no record ............ proto status as frozen
//   frozen member, partial record ....... proto status; best-partial proof bytes
//                                         attached when the node has none
//   frozen member, full record .......... proof attached; `solvedStatus`
//                                         (cited stays cited) — but never
//                                         `proved` over an empty proof
//   agent node, partial record .......... `cited` when it carries `source`,
//                                         else `to-prove`; best-partial bytes
//   agent node, full record ............. node published with `solvedStatus`
// A `proved`-published node with a `partial` cursor record is therefore
// impossible by construction.
import type { Core, CoreStatement } from "./schema.js";
import { solvedStatus } from "./status.js";
import { repairCoreLatexSerialization } from "./latex_serialization.js";
import { wireStatementProofDependencies, rebuildAssumptionUsedBy } from "./dependencies.js";
import { pruneDeadAssumptions } from "./gate.js";
import type { WorkingState, SolvedMember } from "../stages/d0_working.js";

/** Cumulative prose overlay carried in `d0_working.json` (Phase 1). The solver's
 *  directive-authorized `prose_updates` accumulate here instead of being written
 *  into core.json AND proto_core.json mid-round; assembly applies the overlay at
 *  render time. `statement_notes` is keyed by node id so later rounds replace
 *  earlier notes per field. */
export interface ProseOverlay {
  tldr?: string;
  project_justification?: Record<string, unknown>;
  sampling_model?: Record<string, string>;
  related_work?: string;
  interpretation?: string;
  technical_internal_limitation?: string;
  honest_scope?: string;
  statement_notes?: Record<string, { justification?: string; gap?: string; consumer?: string }>;
}

/** One prose-only update bundle, shared by D0-SOLVE and the D0.R transaction
 * boundary. Keeping this shape named lets a panel-cleared D0.R metadata repair
 * move into the durable working overlay without copying formal/proof edits. */
export interface ProseUpdates {
  tldr?: string;
  project_justification?: Record<string, unknown>;
  sampling_model?: Record<string, string>;
  related_work?: string;
  interpretation?: string;
  technical_internal_limitation?: string;
  honest_scope?: string;
  statement_notes?: Array<{ id: string; justification?: string; gap?: string; consumer?: string }>;
}

const OVERLAY_SCALAR_FIELDS = [
  "tldr",
  "related_work",
  "interpretation",
  "technical_internal_limitation",
  "honest_scope",
] as const;

/** Merge one round's prose updates into the cumulative overlay (last write wins
 *  per field; `sampling_model` and `statement_notes` merge per key). */
export function mergeProseOverlay(
  overlay: ProseOverlay | undefined,
  updates: ProseUpdates,
): ProseOverlay {
  const next: ProseOverlay = { ...(overlay ?? {}) };
  for (const field of OVERLAY_SCALAR_FIELDS) {
    if (updates[field] !== undefined) next[field] = updates[field];
  }
  if (updates.project_justification) {
    next.project_justification = { ...(next.project_justification ?? {}), ...updates.project_justification };
  }
  if (updates.sampling_model) {
    next.sampling_model = { ...(next.sampling_model ?? {}), ...updates.sampling_model };
  }
  for (const note of updates.statement_notes ?? []) {
    const prior = next.statement_notes?.[note.id] ?? {};
    next.statement_notes = {
      ...(next.statement_notes ?? {}),
      [note.id]: {
        ...prior,
        ...(note.justification !== undefined ? { justification: note.justification } : {}),
        ...(note.gap !== undefined ? { gap: note.gap } : {}),
        ...(note.consumer !== undefined ? { consumer: note.consumer } : {}),
      },
    };
  }
  return next;
}

/** Extract only prose/positioning replacements from an edited core. Formal
 * claims, proofs, dependencies, definitions and assumptions are deliberately
 * absent: those remain provisional until the complete D0.5 gate passes. */
export function diffCoreProse(before: Core, after: Core): ProseUpdates | null {
  const updates: ProseUpdates = {};
  for (const field of OVERLAY_SCALAR_FIELDS) {
    if (after[field] !== undefined && after[field] !== before[field]) updates[field] = after[field];
  }
  for (const [field, value] of Object.entries(after.project_justification ?? {})) {
    if (value !== undefined && value !== before.project_justification?.[field as keyof NonNullable<Core["project_justification"]>]) {
      updates.project_justification = { ...(updates.project_justification ?? {}), [field]: value };
    }
  }
  for (const [field, value] of Object.entries(after.sampling_model ?? {})) {
    if (value !== undefined && value !== before.sampling_model?.[field]) {
      updates.sampling_model = { ...(updates.sampling_model ?? {}), [field]: value };
    }
  }
  const beforeStatements = new Map(before.statements.map((statement) => [statement.id, statement]));
  for (const statement of after.statements) {
    const prior = beforeStatements.get(statement.id);
    if (!prior) continue;
    const note: { id: string; justification?: string; gap?: string; consumer?: string } = { id: statement.id };
    for (const field of ["justification", "gap", "consumer"] as const) {
      if (statement[field] !== undefined && statement[field] !== prior[field]) note[field] = statement[field];
    }
    if (Object.keys(note).length > 1) (updates.statement_notes ??= []).push(note);
  }
  return Object.keys(updates).length > 0 ? updates : null;
}

function applyProseOverlay(core: Core, overlay: ProseOverlay | undefined): void {
  if (!overlay) return;
  for (const field of OVERLAY_SCALAR_FIELDS) {
    if (overlay[field] !== undefined) core[field] = overlay[field];
  }
  if (overlay.project_justification) {
    core.project_justification = {
      ...(core.project_justification ?? {}),
      ...overlay.project_justification,
    } as Core["project_justification"];
  }
  if (overlay.sampling_model) {
    core.sampling_model = { ...(core.sampling_model ?? {}), ...overlay.sampling_model };
  }
  for (const [id, note] of Object.entries(overlay.statement_notes ?? {})) {
    const stmt = core.statements.find((s) => s.id === id);
    if (!stmt) continue; // out-of-round note: metadata only, dropping is safe (same policy as the old applyProseUpdates)
    for (const field of ["justification", "gap", "consumer"] as const) {
      if (note[field] !== undefined) stmt[field] = note[field];
    }
  }
}

/** The theorem id an OEQ resolution names (legacy string form stored only the id). */
const resolutionTheoremId = (r: NonNullable<WorkingState["resolved_oeqs"]>[string]): string =>
  typeof r === "string" ? r : r.theorem_id;

/** Render one agent-authored record as a published statement, or `null` when the
 *  record is SHELVED debt (a partial carried as "extend later" context that is
 *  deliberately not part of the paper this round — see `SolvedMember.shelved`).
 *
 *  A published partial is an OPEN TARGET: `to-prove`, `source` dropped (the
 *  solver must re-emit it to discharge — same rule as `openSolveTarget`), with
 *  its best-partial proof bytes attached as prior progress. A full record
 *  publishes via `solvedStatus`. */
function renderAgentNode(rec: SolvedMember & { node: CoreStatement }): CoreStatement | null {
  const proof = (rec.proof_tex ?? "").trim();
  if (rec.partial) {
    if (rec.shelved) return null;
    return {
      ...rec.node,
      status: "to-prove",
      proof_tex: proof.length > 0 ? rec.proof_tex : undefined,
      source: undefined,
    };
  }
  // A full record with an empty proof publishes like the recovery tool: keep the
  // node's own status rather than manufacturing a `proved` over nothing (which
  // the schema rejects). `cited` nodes legitimately carry no proof.
  if (proof.length === 0 && rec.node.status !== "cited") {
    return { ...rec.node, proof_tex: rec.node.proof_tex };
  }
  return { ...rec.node, proof_tex: proof.length > 0 ? rec.proof_tex : rec.node.proof_tex, status: solvedStatus(rec.node) };
}

/** Derive the published `core.json` from the two authoritative stores. Pure:
 *  never reads or writes disk, never mutates its inputs. The caller validates
 *  (`CoreSchema.parse`) and persists. */
export function assembleCore(proto: Core, working: WorkingState): Core {
  const core: Core = structuredClone(proto);

  // Proto-resident lemmas pruned as orphans at a maximality checkpoint. The proto
  // still holds them (only an orchestrator proto edit removes them there), so a
  // pure re-render would resurrect them; the durable prune record filters them.
  // REVIVAL (audit F3): a live non-partial record means a later round proved the
  // node again (e.g. an exact-target directive re-opened it) — the fresh proof
  // outranks the stale prune record, or the directive's work would render nowhere.
  const prunedOrphans = new Set(
    (working.pruned_proto_orphans ?? []).filter((id) => {
      const rec = working.solved?.[id];
      return rec === undefined || rec.partial === true;
    }),
  );
  if (prunedOrphans.size > 0) {
    core.statements = core.statements.filter((s) => !prunedOrphans.has(s.id));
  }

  // -- 2. durable OEQ resolutions ------------------------------------------------
  const resolutions = Object.entries(working.resolved_oeqs ?? {});
  const answeredSources = new Set(resolutions.map(([src]) => src));
  if (resolutions.length > 0) {
    const replacement = new Map(resolutions.map(([src, r]) => [src, resolutionTheoremId(r)] as const));
    core.statements = core.statements
      .filter((s) => !(s.kind === "openendedquestion" && answeredSources.has(s.id)))
      .map((s) => ({ ...s, depends_on: s.depends_on.map((d) => replacement.get(d) ?? d) }));
  }

  // -- 3. attach proofs / insert agent nodes, deriving status --------------------
  const byId = new Map(core.statements.map((s, i) => [s.id, i] as const));
  for (const [id, rec] of Object.entries(working.solved ?? {})) {
    // An ANSWERED question never publishes, whatever store holds it (audit R3F1):
    // a legacy cursor can still carry the historical source record beside its
    // resolution — the state `normalizeWorkingState` retires at the next write —
    // and rendering it would republish a question the run already answered.
    if (answeredSources.has(id)) continue;
    const at = byId.get(id);
    if (rec.node === undefined) {
      // Frozen proto member. Its statement text is the proto's; only proof bytes
      // and derived status come from the record.
      if (at === undefined) continue; // e.g. record for a node an apply deleted
      const stmt = core.statements[at];
      const proof = (rec.proof_tex ?? "").trim();
      if (rec.partial) {
        // Best-partial preservation: bytes attached, status stays frozen-open.
        if (proof.length > 0 && (stmt.proof_tex ?? "").trim().length === 0) stmt.proof_tex = rec.proof_tex;
        // Defensive (audit F1): the partial record wins over an anomalous settled
        // `proved` in the proto — stale mathematics must not publish as
        // established. (Unreachable through current writers: GP2 forces
        // all-to-prove at D-1.2 and apply composes `prior.status`; `cited` is the
        // deliberate awaiting-revalidation state and stays.)
        if (stmt.status === "proved") stmt.status = "to-prove";
        continue;
      }
      if (proof.length === 0 && stmt.status !== "cited") continue; // never publish proved over nothing
      if (proof.length > 0) stmt.proof_tex = rec.proof_tex;
      stmt.status = solvedStatus(stmt);
    } else {
      if (at !== undefined) {
        // Same-id collision with a frozen member: the proto stays authoritative
        // for the claim. Attach the proof only when the record argues the exact
        // frozen text (mirror of the packet-rebuild recovery rule).
        const stmt = core.statements[at];
        const proof = (rec.proof_tex ?? "").trim();
        if (!rec.partial && proof.length > 0 && rec.node.statement === stmt.statement) {
          stmt.proof_tex = rec.proof_tex;
          stmt.status = solvedStatus(stmt);
        }
      } else {
        const rendered = renderAgentNode(rec as SolvedMember & { node: CoreStatement });
        if (rendered !== null) {
          byId.set(id, core.statements.length);
          core.statements.push(rendered);
        }
      }
    }
  }

  // -- 4./6. derived passes, in the merge's order --------------------------------
  wireStatementProofDependencies(core);
  applyProseOverlay(core, (working as { prose_overlay?: ProseOverlay }).prose_overlay);
  {
    const res = pruneDeadAssumptions(core);
    if (res && res.pruned.length > 0) core.assumptions = res.core.assumptions;
  }
  rebuildAssumptionUsedBy(core);
  {
    // Missing-bib heal (same rule as solve/gates.ts): a `standard.cite` or cited
    // `source.cite` naming no bibliography key gets a stub entry.
    const bibKeys = new Set((core.bibliography ?? []).map((b) => b.key));
    const healed = Array.from(
      new Set(
        [
          ...core.assumptions.map((a) => a.standard?.cite),
          ...core.statements.filter((s) => s.status === "cited").map((s) => s.source?.cite),
        ].filter((c): c is string => !!c && !bibKeys.has(c)),
      ),
    );
    if (healed.length > 0) core.bibliography = [...(core.bibliography ?? []), ...healed.map((key) => ({ key }))];
  }
  repairCoreLatexSerialization(core);
  return core;
}
