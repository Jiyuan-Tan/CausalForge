// D0-SOLVE step 3/5 — parseOutputs/merge (spec §Stage kernel).
//
// Everything between the raw unit outputs and the fully assembled core, moved
// verbatim from stage0_solve.ts in the T1 carve: write-capability projection,
// cross-unit emission-conflict resolution, directive/prose-ownership
// enforcement, the proof/lemma merge with its collision withholding, proposal
// collection, OEQ resolution application, prose application, LaTeX repair, id
// auto-heal, citation wiring, and the self-containment repair + dangling-edge
// check at the merge boundary.
import { retargetDeletedDependency } from "../core/oeq_edges.js";
import { remapResolvedDependencies } from "../core/oeq_edges.js";
import { ProjectJustificationSchema, type Core, type CoreStatement } from "../core/schema.js";
import {
  proofContentClosureIntersects,
  rebuildAssumptionUsedBy,
  } from "../core/dependencies.js";

import { assertCanonicalAlignedRowTerminators, repairLatexStringsDeep } from "../core/latex_serialization.js";
import { extractCitationRefs, healStatementId } from "../core/node_ids.js";
import { mergeProseOverlay, assembleCore } from "../core/assemble.js";
import { isUnfinishedCarriedRecord } from "../core/status.js";
import { type ProofToArchive } from "../proof_archive.js";
import { recordProof } from "../working_writer.js";
import { validateSolveManifest } from "../semantic_manifest.js";
import {
  coreEditTarget,
  declarationNarrowed,
  describeEchoMismatch,
  describeRevisionMismatch,
  findUnsafeDeleteTextReferences,
  type RawCoreEdit,
} from "../stages/d0_apply.js";
import { normalizeSymbol } from "../core/preflight.js";
import type {
  ProposedStatementChange,
  ProposedDefinitionChange,
  ProposedAssumption,
  OpenObligation,
} from "./schemas.js";
import {
  projectOutputsToWriteCapabilities,
  selectLiveDurableProofOwners,
  collectConflictingSolveEmissions,
  dropConflictingSolveEmissions,
  type SolveEmissionConflict,
} from "./ownership.js";
import { oeqSourceFingerprint, openSolveTarget, type SolveRoundContext } from "./context.js";
import type { SolveDispatchResult } from "./dispatch.js";
import { coreEditOperationKey } from "./mandates.js";
import { pinWhitespaceEquivalentCurrent } from "./proposals.js";
import { normalizeTexWhitespace } from "../../shared/tex_text.js";
import { definitionRevision, statementRevision } from "../core/revision.js";
import type { WorkingState } from "../stages/d0_working.js";
import { computeValidNodes, symbolBasis } from "../stages/d0_working.js";
import {
  agentOeqSourceFromFingerprint,
  authoritativeStatementCatalog,
  resolvedStatementReplacementEndpoint,
} from "./oeq_source.js";

// (Records only: `applyProseUpdates` is gone. The prose channel's ONE durable
// carrier is `working.prose_overlay` (merged below via `mergeProseOverlay`);
// `assembleCore` applies it on every render — the same-round packet and the
// committed core.json both see it, and no workspace copy can drift from it.
// Cross-unit conflict detection and the ProjectJustification schema check are
// kept below at the merge boundary.)

// (Batch B: `silentAlterationViolations` is deleted — see the construction
// note at its former call site.)

/** Split emitted proofs into those naming a real core statement and those that do not.
 *
 *  The attach loop used to be `const stmt = core.statements.find(s => s.id === pr.id)`
 *  guarded by `if (stmt && ...)` with NO else — so a hallucinated or typo'd
 *  `proofs[].id` was discarded without a counter, `solved` stayed flat, and the round
 *  emitted "zero new proofs this round — the agent may be stuck or under-scoping",
 *  attributing an id-mapping fault to solver weakness. `o.proofs.length` was never
 *  compared against the number actually attached. */
export function partitionProofsByTarget<T extends { id: string }>(
  proofs: T[],
  statementIds: Set<string>,
): { matched: T[]; unmatched: string[] } {
  const matched: T[] = [];
  const unmatched: string[] = [];
  for (const proof of proofs) {
    if (statementIds.has(proof.id)) matched.push(proof);
    else unmatched.push(proof.id);
  }
  return { matched, unmatched };
}

/** Remove resolved-OEQ edges whose source or answer is deleted in one reviewed
 * statement transaction.  The apply path removes the same edge; merge previews
 * must do so too or stale source→answer metadata makes an atomic deletion bundle
 * look inapplicable. */
export function removeAtomicallyDeletedOeqResolutionEdges(
  resolved: Record<string, string | { theorem_id: string }> | undefined,
  deletedIds: ReadonlySet<string>,
): void {
  if (resolved === undefined) return;
  for (const [sourceId, resolution] of Object.entries(resolved)) {
    const theoremId = typeof resolution === "string" ? resolution : resolution.theorem_id;
    if (deletedIds.has(sourceId) || deletedIds.has(theoremId)) delete resolved[sourceId];
  }
}

/** Whether an already-carried theorem is the same proof-relevant OEQ answer an
 * OEQ solver just emitted. Motivation prose may differ because recovery always
 * keeps the prior durable node; changing it requires the statement-note channel. */
/** Dependencies are a SET for claim identity (depsKey, computeValidNodes,
 *  oeqSourceFingerprint); LLM re-emission order is not stable, so the duplicate-
 *  discharge check canonicalizes order/duplicates. NOT used by
 *  `reusableOeqAnswerMatches` below: reuse VALIDITY stays byte-conservative on
 *  purpose (a false reuse silently carries a stale answer; a false mismatch only
 *  costs a re-verification) — pinned by oeq_reopen_lifecycle.test.ts. */
function sameDependencySet(a: string[] | undefined, b: string[] | undefined): boolean {
  const key = (xs: string[] | undefined): string => [...new Set(xs ?? [])].sort().join("\n");
  return key(a) === key(b);
}

export function reusableOeqAnswerMatches(existing: CoreStatement, emitted: CoreStatement): boolean {
  return existing.id === emitted.id &&
    existing.kind === emitted.kind &&
    existing.statement === emitted.statement &&
    JSON.stringify(existing.depends_on ?? []) === JSON.stringify(emitted.depends_on ?? []) &&
    existing.status === emitted.status &&
    (existing.proof_tex ?? "") === (emitted.proof_tex ?? "") &&
    JSON.stringify(existing.source ?? null) === JSON.stringify(emitted.source ?? null) &&
    JSON.stringify(existing.free_symbols) === JSON.stringify(emitted.free_symbols) &&
    existing.route === emitted.route &&
    JSON.stringify(existing.external_refs) === JSON.stringify(emitted.external_refs);
}

// Moved to core/dependencies.ts so d0_apply can use it for paired-proof promotion
// without a merge↔apply value-import cycle; imported back here for local use and
// re-exported for existing consumers.
export { proofContentClosureIntersects };

export interface SolveMergeResult {
  emissionConflicts: SolveEmissionConflict[];
  /** Same-round statements/proofs withheld because their emitted dependency closure
   *  reaches an emission-conflicted id. Quarantining the closure lets unrelated
   *  units commit without publishing consumers of content that was withheld. */
  withheldConflictConsumers: string[];
  /** Ownership/capability-rejected payloads. They are auditable checkpoint content,
   *  not a reason to discard unrelated units from the round. */
  withheldCapabilityEmissions: string[];
  /** Complete raw bytes for every withheld structured carrier. The diagnostic
   *  summaries above are intentionally compact; this is the durable adjudication
   *  record before per-round solve files may be overwritten. */
  withheldPayloads: Array<{
    category: string;
    target: string;
    unit: string;
    reason: string;
    payload: unknown;
  }>;
  /** Exact directive targets for which no substantive accepted carrier survived
   * normalization.  Commit uses this explicit postimage result instead of
   * mistaking quarantined sibling noise for failure of a canonical mandate. */
  unfulfilledExactTargets: string[];
  /** The round consumed a STRUCTURED CORE CHANGES REQUIRED directive but no
   * substantive structured change landed. Commit must keep the directive pending
   * (rewind the escalation cursor) even when the directive names no exact target. */
  structuredDirectiveUnfulfilled: boolean;
  addedLemmaCollisions: Array<{ id: string; owner: string }>;
  oeqAnswerCollisions: string[];
  /** Resolutions withheld because their source is not a live OEQ in the frozen
   *  core ("source→theorem"). Paid output was discarded (bytes archived), so the
   *  proposal checkpoint must surface these — a console warning alone lets the
   *  round advance as if nothing was dropped. */
  withheldInvalidResolutions: string[];
  /** Identical-claim re-emissions of settled nodes, skipped as no-op discharges. */
  duplicateReproofIds: string[];
  /** `statement-replace` edits whose post-image equalled the node the worker was shown,
   *  dropped before capability projection so an echo cannot seed quarantine/closure. */
  duplicateEchoEditIds: string[];
  /** Proof bytes refused by this merge (withheld/unmatched/duplicate) — installed
   *  nowhere in hot state, so commitRound must copy them to the cold archive before
   *  the next dispatch can overwrite the raw solve files that hold them. */
  withheldProofBytes: ProofToArchive[];
  unmatchedProofIds: string[];
  /** Proofs withheld because the emitter lacked ownership of an EXISTING id. */
  quarantinedProofs: Array<{ id: string; unit: string; owner: string }>;
  proposedChanges: ProposedStatementChange[];
  defChanges: ProposedDefinitionChange[];
  proposedAssumptions: ProposedAssumption[];
  proposedCoreEdits: RawCoreEdit[];
  deferredProofs: Array<{ id: string; proof_tex: string; argues_proposed?: boolean }>;
  deferredCitationRevalidations: CoreStatement[];
  openObligations: OpenObligation[];
  illegalDefTargets: string[];
  solved: number;
  addedLemmas: number;
}

/** Remove note-overlay entries that no longer decorate any durable statement.
 *
 * The published render is intentionally not the catalog: resolved OEQ sources
 * and partial+shelved agent nodes can be absent from it while remaining
 * reversible authoritative records.  Frozen proto statements and agent-node
 * records are therefore the two liveness stores. */
export function pruneOrphanStatementNotes(
  proto: Pick<Core, "statements">,
  working: Pick<WorkingState, "solved" | "resolved_oeqs" | "prose_overlay">,
): string[] {
  const notes = working.prose_overlay?.statement_notes;
  if (notes === undefined) return [];

  const durableStatementIds = new Set(authoritativeStatementCatalog(proto.statements, working).keys());
  const orphanNoteIds = Object.keys(notes)
    .filter((id) => !durableStatementIds.has(id))
    .sort();
  for (const id of orphanNoteIds) delete notes[id];
  if (Object.keys(notes).length === 0) delete working.prose_overlay!.statement_notes;
  return orphanNoteIds;
}

/** Withheld-record reasons that never carry the directive's mathematics. */
export const NOISE_WITHHELD_REASONS: ReadonlySet<string> = new Set([
  "unsolicited-prose",
  "unauthorized-prose-owner",
  "unmatched-id",
  "duplicate-reproof",
  "mandate-shadowed",
  "dropped-nonexistent-obligation",
  "proof-on-resolved-oeq",
]);

/** Completion identity of a statement carrier: every field except `status` and
 *  `proof_tex`, with the dependency set order-normalized. Two carriers with equal
 *  identity are the same completion, never competing versions. */
function completionIdentity(statement: CoreStatement): string {
  const { status: _status, proof_tex: _proofTex, ...identity } = statement;
  return JSON.stringify({ ...identity, depends_on: [...new Set(statement.depends_on)].sort() });
}

export function mergeSolveOutputs(args: {
  sctx: SolveRoundContext;
  dr: SolveDispatchResult;
}): SolveMergeResult {
  const { sctx, dr } = args;
  const {
    proto,
    core,
    prev,
    next,
    sourceById,
    pendingSupersessionEdits,
    hasPendingDirective,
    requiresCoreChanges,
    requiredCoreTargets,
    requiredCoreEdits: requiredCoreEditsSealed,
    semanticManifest,
    validIds,
    droppedCarryIds,
  } = sctx;
  // `next` already contains this round's validity/shelving decisions. Proof merge
  // mutates it below, so correction revocation must restore this exact basis rather
  // than `prev`, whose formerly full record may have just been invalidated.
  const preMergeSolved = structuredClone(next.solved);
  const preMergeProseOverlay = structuredClone(next.prose_overlay);
  // Work with mandate payloads under the SAME LaTeX repair the proposal store
  // gets on every load. Mandates keep their sealed bytes (opaque on load), so an
  // operation on which `repairSerializedLatex` is not a no-op would otherwise
  // never key-match the repaired copy of its own seeded proposal — the same
  // cross-store asymmetry fixed at the d0_apply mandate echo check.
  const requiredCoreEdits = structuredClone(requiredCoreEditsSealed);
  repairLatexStringsDeep(requiredCoreEdits);
  // Exact sealed mandates are already content-addressed and basis-checked. Keep
  // their object identity so only the canonical seeded operation (never a
  // same-target worker substitute) may use the narrow mandate exception below.
  const isRequiredCoreEdit = (edit: RawCoreEdit): boolean => requiredCoreEdits.includes(edit);
  const { dispatch, rawOutputs, proseOwnerIndex, directiveOwnerLabel, semanticTargetOwners } = dr;
  // Revision provenance is a pipeline fact, not a prompt-compliance burden.
  // Statement revisions preserve a worker-supplied stamp and validate it. A
  // definition correction instead binds both pair members to this round's exact
  // frozen semantic basis here, so a whole-node post-image cannot carry a
  // construction-only or otherwise incomplete worker stamp into apply.
  const contextDefinitionById = new Map(core.definitions.map((definition) => [definition.id, definition] as const));
  const contextStatementById = new Map(core.statements.map((statement) => [statement.id, statement] as const));
  const revisionBoundRawOutputs = rawOutputs.map((output, index) => {
    const targetById = new Map(
      (dispatch[index]?.targets ?? []).map((target) => [target.id, target] as const),
    );
    return {
      ...output,
      proposed_statement_changes: output.proposed_statement_changes.map((change) => {
        const target = targetById.get(change.id);
        return change.based_on_revision === undefined && target
          ? { ...change, based_on_revision: statementRevision(target) }
          : change;
      }),
      proposed_definition_changes: output.proposed_definition_changes.map((change) => {
        const target = contextDefinitionById.get(change.id);
        return target
          ? { ...change, based_on_revision: definitionRevision(target, core) }
          : change;
      }),
      proposed_core_edits: output.proposed_core_edits.map((edit) => {
        if (edit.kind === "definition-replace") {
          const authoredView = contextDefinitionById.get(edit.id);
          return authoredView
            ? { ...edit, based_on_revision: definitionRevision(authoredView, core) }
            : edit;
        }
        if (edit.kind !== "statement-replace" || edit.based_on_revision !== undefined) return edit;
        // A local statement edit was authored against its stamped target block.
        // A directive-owner metadata edit may instead address a non-target node
        // shown only in the shared frozen core. Both views are pipeline-owned, so
        // attach their revision here instead of relying on a fragile status echo.
        const authoredView = targetById.get(edit.id) ?? contextStatementById.get(edit.id);
        return authoredView
          ? { ...edit, based_on_revision: statementRevision(authoredView) }
          : edit;
      }),
    };
  });
  // A settled AGENT-AUTHORED node may be redundantly re-emitted through
  // `added_lemmas` by a consumer that merely cites it. This is not a competing
  // write: merge already treats the exact same completion as a no-op and archives
  // the alternative proof. Frozen/source-backed nodes deliberately stay on the
  // stricter collision/revalidation path: an apparent re-proof can also alter a
  // citation, status, symbol declaration, route, or other source metadata.
  // Remove that harmless carrier before capability quarantine/conflict discovery,
  // otherwise ownership turns duplicate work into an avoidable checkpoint before
  // the existing no-op discharge can run. Keep every payload in rounds carrying a
  // semantic edit/resolution, and every exact required target, because those may be
  // post-image proof or citation-revalidation receipts rather than duplicates.
  const hasReviewCarrier = requiredCoreEdits.length > 0 || pendingSupersessionEdits.length > 0 ||
    revisionBoundRawOutputs.some((output) =>
      output.resolved_oeqs.length > 0 ||
      output.proposed_statement_changes.length > 0 ||
      output.proposed_definition_changes.length > 0 ||
      output.proposed_assumptions.length > 0 ||
      output.proposed_core_edits.length > 0
    );
  const preCapabilityDuplicateReproofs: Array<{ id: string; proofTex: string }> = [];
  const isSettledBeforeMerge = (id: string, statement: CoreStatement): boolean => {
    const record = next.solved[id];
    if (record !== undefined) {
      return record.partial !== true && (record.proof_tex ?? "").trim().length > 0;
    }
    return statement.status === "cited" ||
      (statement.status === "proved" && (statement.proof_tex ?? "").trim().length > 0);
  };
  // A `statement-replace` whose post-image is byte-identical to the node the worker
  // was shown is a pure echo: it cannot be a competing version, whoever emitted it.
  // Left in, an echo on a non-owned node is capability-quarantined and the conflict
  // closure then withholds the emitter's OWN target work as a dependency consumer
  // (a single-unit round lost its target proof this way). Drop echoes here, before
  // capability projection and conflict discovery. Kept: an exact required target
  // (a deliberate receipt), a sealed/carried mandate, and the structural half of a
  // same-unit claim-only correction pair (its claim field differs by contract).
  const preCapabilityEchoEdits: Array<{ id: string; unit: string }> = [];
  const echoIdentity = (statement: CoreStatement): string => JSON.stringify({
    kind: statement.kind,
    statement: statement.statement,
    status: statement.status,
    depends_on: [...new Set(statement.depends_on)].sort(),
    free_symbols: statement.free_symbols === undefined ? null : [...new Set(statement.free_symbols)].sort(),
    source: statement.source ?? null,
    route: statement.route ?? null,
    justification: statement.justification ?? null,
    gap: statement.gap ?? null,
    consumer: statement.consumer ?? null,
    // Provenance and adjudication context are identity-bearing too: an edit that
    // only adds a cross-run reference is a real change, not an echo.
    external_refs: statement.external_refs === undefined ? null : [...new Set(statement.external_refs)].sort(),
    partial_result: (statement as { partial_result?: string }).partial_result ?? null,
  });
  const sealedOperationKeys = new Set(
    [...requiredCoreEdits, ...pendingSupersessionEdits].map((edit) => coreEditOperationKey(edit)),
  );
  // A same-unit claim change whose proposed text equals the shown claim is the
  // no-op half of a no-op correction pair (merge already discards it late); with
  // it gone, its paired statement-replace is an ordinary echo and both halves drop.
  const isNoOpStatementChange = (change: { id: string; proposed: string }): boolean => {
    if (requiredCoreTargets.has(change.id)) return false;
    const current = contextStatementById.get(change.id);
    return current !== undefined && change.proposed === current.statement;
  };
  const isStatementReplaceEcho = (
    edit: RawCoreEdit,
    liveStatementChanges: ReadonlyArray<{ id: string }>,
  ): edit is Extract<RawCoreEdit, { kind: "statement-replace" }> => {
    if (edit.kind !== "statement-replace") return false;
    if (requiredCoreTargets.has(edit.id)) return false;
    if (sealedOperationKeys.has(coreEditOperationKey(edit))) return false;
    if (liveStatementChanges.some((change) => change.id === edit.id)) return false;
    const current = contextStatementById.get(edit.id);
    if (current === undefined) return false;
    return echoIdentity(current) === echoIdentity(edit.proposed as CoreStatement);
  };
  // A statement note that changes no field is not a write; drop it before the
  // ownership census so it can neither be quarantined nor contest a real note.
  const noteChangesNothing = (note: { id: string; justification?: string; gap?: string; consumer?: string }): boolean => {
    const target = contextStatementById.get(note.id);
    if (target === undefined) return false;
    return !((note.justification !== undefined && note.justification !== target.justification) ||
      (note.gap !== undefined && note.gap !== target.gap) ||
      (note.consumer !== undefined && note.consumer !== target.consumer));
  };
  const capabilityInputOutputs = revisionBoundRawOutputs.map((output, index) => {
    const unitLabel = dispatch[index]?.label ?? String(index);
    const liveStatementChanges = output.proposed_statement_changes.filter((change) => {
      if (!isNoOpStatementChange(change)) return true;
      preCapabilityEchoEdits.push({ id: change.id, unit: unitLabel });
      return false;
    });
    let proseUpdates = output.prose_updates;
    if (proseUpdates?.statement_notes !== undefined) {
      const liveNotes = proseUpdates.statement_notes.filter((note) => !noteChangesNothing(note));
      if (liveNotes.length !== proseUpdates.statement_notes.length) {
        const { statement_notes: _dropped, ...rest } = proseUpdates;
        proseUpdates = liveNotes.length > 0 || Object.keys(rest).length > 0
          ? { ...rest, statement_notes: liveNotes }
          : undefined;
      }
    }
    return {
      ...output,
      prose_updates: proseUpdates,
      added_lemmas: output.added_lemmas.filter((emitted) => {
        if (hasReviewCarrier || requiredCoreTargets.has(emitted.id)) return true;
        const existing = contextStatementById.get(emitted.id);
        if (existing === undefined || sourceById.has(emitted.id) ||
            !isSettledBeforeMerge(emitted.id, existing)) return true;
        if (completionIdentity(existing) !== completionIdentity(emitted)) return true;
        preCapabilityDuplicateReproofs.push({ id: emitted.id, proofTex: emitted.proof_tex ?? "" });
        return false;
      }),
      proposed_statement_changes: liveStatementChanges,
      proposed_core_edits: output.proposed_core_edits.filter((edit) => {
        if (!isStatementReplaceEcho(edit, liveStatementChanges)) return true;
        preCapabilityEchoEdits.push({ id: edit.id, unit: unitLabel });
        return false;
      }),
    };
  });
  const mandatedStatementIds = new Set(
    requiredCoreEdits
      .filter((edit) => edit.kind === "statement-delete" || edit.kind === "statement-replace")
      .map((edit) => edit.id),
  );
  const mandatedDeleteIds = new Set(
    requiredCoreEdits.filter((edit) => edit.kind === "statement-delete").map((edit) => edit.id),
  );
  const mandatedDefinitionIds = new Set(
    requiredCoreEdits
      .filter((edit) => edit.kind.startsWith("definition-"))
      .map((edit) => coreEditTarget(edit)),
  );
  const mandatedAssumptionIds = new Set(
    requiredCoreEdits
      .filter((edit) => edit.kind.startsWith("assumption-"))
      .map((edit) => coreEditTarget(edit)),
  );
  const mandatedTargetOperations = new Map(
    requiredCoreEdits.map((edit) => [coreEditTarget(edit), coreEditOperationKey(edit)]),
  );
  type TerminalDispositionReceipt = {
    index: number;
    category: "proof" | "oeq-resolution" | "added-node" | "statement-mutation" |
      "statement-delete" | "open-obligation";
    payload: unknown;
  };
  const hasTerminalContradiction = (receipts: TerminalDispositionReceipt[]): boolean => {
    const categories = new Set(receipts.map((receipt) => receipt.category));
    const settled = ["proof", "oeq-resolution", "added-node"]
      .some((category) => categories.has(category as TerminalDispositionReceipt["category"]));
    return (categories.has("open-obligation") && settled) ||
      (categories.has("statement-delete") &&
        [...categories].some((category) => category !== "statement-delete"));
  };
  const preProjectionDispositionReceipts = new Map<string, TerminalDispositionReceipt[]>();
  const addPreProjectionDisposition = (
    id: string,
    receipt: TerminalDispositionReceipt,
  ): void => {
    if (mandatedStatementIds.has(id)) return;
    const receipts = preProjectionDispositionReceipts.get(id) ?? [];
    receipts.push(receipt);
    preProjectionDispositionReceipts.set(id, receipts);
  };
  // Reject a worker that asserts mutually exclusive terminal states before
  // capability projection can erase its unauthorized sibling-target carriers.
  // A sealed mandate is the sole exception: every worker disposition on that
  // target is intentionally shadowed by the authoritative operation below.
  capabilityInputOutputs.forEach((output, index) => {
    for (const payload of output.proofs) {
      addPreProjectionDisposition(payload.id, { index, category: "proof", payload });
    }
    for (const payload of output.resolved_oeqs) {
      // Mandating either endpoint shadows the whole atomic Q→T transaction.
      if (mandatedStatementIds.has(payload.source_id) ||
          mandatedStatementIds.has(payload.theorem.id)) continue;
      addPreProjectionDisposition(payload.source_id, { index, category: "oeq-resolution", payload });
      addPreProjectionDisposition(payload.theorem.id, { index, category: "oeq-resolution", payload });
    }
    for (const payload of output.added_lemmas) {
      const settled = payload.status === "cited" ||
        (payload.status === "proved" && (payload.proof_tex ?? "").trim().length > 0);
      if (settled && contextStatementById.get(payload.id)?.kind !== "openendedquestion") {
        addPreProjectionDisposition(payload.id, { index, category: "added-node", payload });
      }
    }
    for (const payload of output.proposed_core_edits) {
      if (payload.kind === "statement-delete") {
        addPreProjectionDisposition(payload.id, { index, category: "statement-delete", payload });
      } else if (payload.kind === "statement-replace") {
        addPreProjectionDisposition(payload.id, { index, category: "statement-mutation", payload });
      }
    }
    for (const payload of output.proposed_statement_changes) {
      addPreProjectionDisposition(payload.id, { index, category: "statement-mutation", payload });
    }
    for (const payload of output.open_obligations) {
      addPreProjectionDisposition(payload.node_id, { index, category: "open-obligation", payload });
    }
    // INVARIANT: this raw, pre-projection check is the ONLY self-contradiction gate.
    // Every later projection stage must stay filter-only (and exclude mandated ids),
    // so a contradiction visible after projection was already visible here.
    for (const [id, receipts] of preProjectionDispositionReceipts) {
      const local = receipts.filter((receipt) => receipt.index === index);
      if (hasTerminalContradiction(local)) {
        throw new Error(
          `Stage 0-SOLVE emitted mutually exclusive terminal dispositions for ${id}: ` +
            [...new Set(local.map((receipt) => receipt.category))].sort().join(", "),
        );
      }
    }
  });
  // Conflict discovery must see incompatible mathematical versions before
  // capability projection erases unauthorized sibling carriers.  Apply only the
  // authoritative mandate shadow here; every other raw carrier remains evidence.
  const preCapabilityConflictOutputs = capabilityInputOutputs.map((output) => ({
    ...output,
    proofs: output.proofs.filter((payload) => !mandatedStatementIds.has(payload.id)),
    added_lemmas: output.added_lemmas.filter((payload) => !mandatedStatementIds.has(payload.id)),
    resolved_oeqs: output.resolved_oeqs.filter((payload) =>
      !mandatedStatementIds.has(payload.source_id) && !mandatedStatementIds.has(payload.theorem.id)
    ),
    proposed_statement_changes: output.proposed_statement_changes.filter(
      (payload) => !mandatedStatementIds.has(payload.id),
    ),
    proposed_definition_changes: output.proposed_definition_changes.filter(
      (payload) => !mandatedDefinitionIds.has(payload.id),
    ),
    proposed_assumptions: output.proposed_assumptions.filter(
      (payload) => !mandatedAssumptionIds.has(payload.id),
    ),
    proposed_core_edits: output.proposed_core_edits.filter(
      (payload) => !mandatedTargetOperations.has(coreEditTarget(payload)),
    ),
    open_obligations: output.open_obligations.filter(
      (payload) => !mandatedStatementIds.has(payload.node_id),
    ),
    ...(output.prose_updates ? {
      prose_updates: {
        ...output.prose_updates,
        statement_notes: (output.prose_updates.statement_notes ?? [])
          .filter((payload) => !mandatedStatementIds.has(payload.id)),
      },
    } : {}),
  }));
  const {
    outputs: projectedOutputs,
    quarantined: capabilityQuarantines,
    durableCorrectionTargetOwners,
    postimageProofOwners,
    ownershipPostimages,
    ownershipDurableRecords,
    ownershipRequiredIds,
    ownershipWritableIds,
  } = (() => {
    // A solver may need to refresh a proof on an agent-authored node that it owns
    // even when that node is not an open dispatch target: a settled node can need a
    // syntax-only proof refresh, and a shelved partial can carry the statement being
    // narrowed in this same bundle. Limit the fallback to current published nodes,
    // exact targets, and same-round statement-edit targets so unrelated shelved debt
    // remains unwritable.
    const durableCorrectionTargetOwners = new Map<string, string>();
    const durableRecords = new Map<string, { owner: string; node: CoreStatement; proofDependencies?: string[] }>();
    const publishedNodeById = new Map([
      ...proto.statements.map((statement) => [statement.id, statement] as const),
      ...core.statements.map((statement) => [statement.id, statement] as const),
    ]);
    for (const records of [prev?.solved ?? {}, next.solved]) {
      for (const [id, record] of Object.entries(records)) {
        const node = record.node ?? publishedNodeById.get(id);
        if (node === undefined || typeof record.owner !== "string" || record.owner.trim().length === 0) continue;
        durableRecords.set(id, {
          owner: record.owner,
          node,
          ...(record.snapshot.depends_on !== undefined ? { proofDependencies: record.snapshot.depends_on } : {}),
        });
      }
    }
    const recoveryTargetIds = new Set(requiredCoreTargets);
    const writableDurableIds = new Set<string>([
      ...pendingSupersessionEdits.map(coreEditTarget),
      ...requiredCoreEdits.map(coreEditTarget),
    ]);
    for (const output of capabilityInputOutputs) {
      for (const proof of output.proofs) writableDurableIds.add(proof.id);
      for (const statement of output.added_lemmas) {
        writableDurableIds.add(statement.id);
        // Narrow exception for a same-round completion of an existing durable
        // node. Its recorded owner still controls the channel; unrelated shelved
        // records are not added to the writable set.
        if (durableRecords.has(statement.id)) recoveryTargetIds.add(statement.id);
      }
      for (const change of output.proposed_statement_changes) writableDurableIds.add(change.id);
      for (const edit of output.proposed_core_edits) writableDurableIds.add(coreEditTarget(edit));
      for (const resolution of output.resolved_oeqs) {
        writableDurableIds.add(resolution.source_id);
        writableDurableIds.add(resolution.theorem.id);
      }
    }
    const pairedCandidates = new Map<string, Array<{ emitter: string; postimage: CoreStatement; complete: boolean }>>();
    for (let index = 0; index < capabilityInputOutputs.length; index += 1) {
      const unit = dispatch[index];
      const output = capabilityInputOutputs[index];
      for (const edit of output.proposed_core_edits) {
        const paired = edit.kind === "statement-replace" && output.proposed_statement_changes.some((change) =>
          change.id === edit.id && change.proposed === edit.proposed.statement
        );
        const completeProofTransaction =
          paired &&
          output.proofs.some((proof) => proof.id === edit.id && proof.argues_proposed === true);
        if (!paired || edit.kind !== "statement-replace") continue;
        const candidates = pairedCandidates.get(edit.id) ?? [];
        if (!candidates.some((candidate) => candidate.emitter === unit.label)) {
          candidates.push({ emitter: unit.label, postimage: edit.proposed, complete: completeProofTransaction });
          pairedCandidates.set(edit.id, candidates);
        }
      }
    }
    const deniedCorrectionTargets = new Set<string>();
    const postimageCandidates = new Map<string, { emitter: string; postimage: CoreStatement }>();
    for (const [id, candidates] of pairedCandidates) {
      const complete = candidates.filter((candidate) => candidate.complete);
      if (complete.length > 1) {
        deniedCorrectionTargets.add(id);
        continue;
      }
      // A statement postimage is proof-authorizing state, so even the semantic
      // owner must supply the complete argues_proposed transaction before it can
      // participate in reachability.
      const candidate = complete[0];
      if (candidate) postimageCandidates.set(id, candidate);
    }
    // Candidate postimages affect ownership, but ownership must also authorize the
    // candidate's emitter. Recompute to a fixed point after deleting every mismatch;
    // this prevents a rejected sibling postimage from minting reachability for a
    // downstream proof.
    const statementPostimages = new Map(
      [...postimageCandidates].map(([id, candidate]) => [id, candidate.postimage] as const),
    );
    const assignSharedUpstreamOwners = (owners: Map<string, string>): Map<string, string> => {
      if (dr.sharedUpstreamLabel === null || dr.sharedUpstreamLabel === undefined) return owners;
      for (const id of dr.sharedTargetIds ?? []) {
        // Only explicit cross-cutting directive targets acquire the staged owner.
        // Shared immutable reads and unpredictable local helpers do not.
        if (writableDurableIds.has(id)) owners.set(id, dr.sharedUpstreamLabel);
      }
      return owners;
    };
    let durableTargetOwners: Map<string, string>;
    while (true) {
      durableTargetOwners = assignSharedUpstreamOwners(selectLiveDurableProofOwners({
        coreStatements: core.statements,
        requiredIds: recoveryTargetIds,
        durableRecords,
        activeTargetOwners: semanticTargetOwners,
        statementPostimages,
        writableIds: writableDurableIds,
      }));
      const rejected = [...postimageCandidates].filter(([id, candidate]) =>
        statementPostimages.has(id) &&
        (semanticTargetOwners.get(id) ?? durableTargetOwners.get(id)) !== candidate.emitter
      );
      if (rejected.length === 0) break;
      for (const [id] of rejected) statementPostimages.delete(id);
    }
    const baselineDurableTargetOwners = assignSharedUpstreamOwners(selectLiveDurableProofOwners({
      coreStatements: core.statements,
      requiredIds: recoveryTargetIds,
      durableRecords,
      activeTargetOwners: semanticTargetOwners,
      writableIds: writableDurableIds,
    }));
    const postimageProofOwners = new Map(
      [...durableTargetOwners].filter(([id, owner]) => baselineDurableTargetOwners.get(id) !== owner),
    );
    // A shelved node may join the proof fallback only through a complete correction
    // pair emitted by its own recorded owner. A sibling's raw, later-quarantined edit
    // cannot bootstrap the proof into scope.
    for (let index = 0; index < capabilityInputOutputs.length; index += 1) {
      const output = capabilityInputOutputs[index];
      const unit = dispatch[index];
      for (const change of output.proposed_statement_changes) {
        const record = durableRecords.get(change.id);
        if (record === undefined) continue;
        const effectiveOwner = durableTargetOwners.get(change.id) ?? record.owner;
        if (change.current !== record.node.statement || change.proposed === record.node.statement) continue;
        const paired = output.proposed_core_edits.some((edit) =>
          edit.kind === "statement-replace" && edit.id === change.id &&
          edit.proposed.statement === change.proposed
        );
        if (!paired) continue;
        durableCorrectionTargetOwners.set(change.id, effectiveOwner);
        if (effectiveOwner === unit.label) durableTargetOwners.set(change.id, unit.label);
      }
    }
    return {
      ...projectOutputsToWriteCapabilities({
        outputs: capabilityInputOutputs,
        dispatch,
        semanticTargetOwners,
        durableTargetOwners,
        durableCorrectionTargetOwners,
        deniedCorrectionTargets,
        directiveOwnerLabel,
        strictSharedOwner: dr.sharedUpstreamLabel !== null && dr.sharedUpstreamLabel !== undefined,
        requiredCoreTargets,
        sharedTargetIds: new Set(dr.sharedTargetIds ?? []),
        existingStatementIds: new Set([
          ...proto.statements.map((statement) => statement.id),
          ...core.statements.map((statement) => statement.id),
          ...Object.keys(prev?.solved ?? {}),
        ]),
      }),
      durableCorrectionTargetOwners,
      postimageProofOwners,
      ownershipPostimages: statementPostimages,
      ownershipDurableRecords: durableRecords,
      ownershipRequiredIds: recoveryTargetIds,
      ownershipWritableIds: writableDurableIds,
    };
  })();
  const mandateWithheldProofBytes: ProofToArchive[] = [];
  const withheldPayloads: SolveMergeResult["withheldPayloads"] = [];
  const mandateRejectedOeqEndpoints = new Set<string>();
  const capabilityRejectedOeqEndpoints = new Set<string>();
  for (const receipt of capabilityQuarantines) {
    if (receipt.category !== "oeq-resolution") continue;
    const index = dispatch.findIndex((unit) => unit.label === receipt.unit);
    if (index < 0) continue;
    for (const resolution of revisionBoundRawOutputs[index].resolved_oeqs) {
      if (resolution.source_id !== receipt.target) continue;
      capabilityRejectedOeqEndpoints.add(resolution.source_id);
      capabilityRejectedOeqEndpoints.add(resolution.theorem.id);
      withheldPayloads.push({
        category: "oeq-resolution", target: resolution.theorem.id, unit: receipt.unit,
        reason: "capability-quarantine", payload: structuredClone(resolution),
      });
    }
  }
  const dispatchUnitsByTarget = new Map<string, Set<string>>();
  for (const unit of dispatch) for (const target of unit.targets) {
    const labels = dispatchUnitsByTarget.get(target.id) ?? new Set<string>();
    labels.add(unit.label);
    dispatchUnitsByTarget.set(target.id, labels);
  }
  const contestedDispatchTargets = new Set(
    [...dispatchUnitsByTarget].filter(([, labels]) => labels.size > 1).map(([id]) => id),
  );
  for (let index = 0; index < dispatch.length; index += 1) {
    for (const target of dispatch[index].targets) {
      if (!contestedDispatchTargets.has(target.id)) continue;
      withheldPayloads.push({
        category: "dispatch-ownership", target: target.id, unit: dispatch[index].label,
        reason: "contested-dispatch-ownership", payload: structuredClone(target),
      });
    }
  }
  const recordMandateShadow = (output: typeof projectedOutputs[number], unit: string): void => {
    const add = (category: string, target: string, payload: unknown): void => {
      withheldPayloads.push({
        category, target, unit, reason: "mandate-shadowed", payload: structuredClone(payload),
      });
    };
    for (const payload of output.proofs) if (mandatedStatementIds.has(payload.id)) add("proof", payload.id, payload);
    for (const payload of output.added_lemmas) if (mandatedStatementIds.has(payload.id)) add("statement", payload.id, payload);
    for (const payload of output.resolved_oeqs) {
      if (mandatedStatementIds.has(payload.source_id) || mandatedStatementIds.has(payload.theorem.id)) {
        add("oeq-resolution", payload.source_id, payload);
        add("oeq-resolution", payload.theorem.id, payload);
        mandateRejectedOeqEndpoints.add(payload.source_id);
        mandateRejectedOeqEndpoints.add(payload.theorem.id);
      }
    }
    for (const payload of output.proposed_statement_changes) if (mandatedStatementIds.has(payload.id)) add("statement-change", payload.id, payload);
    for (const payload of output.proposed_definition_changes) if (mandatedDefinitionIds.has(payload.id)) add("definition-change", payload.id, payload);
    for (const payload of output.proposed_assumptions) if (mandatedAssumptionIds.has(payload.id)) add("assumption", payload.id, payload);
    for (const payload of output.open_obligations) if (mandatedStatementIds.has(payload.node_id)) add("open-obligation", payload.node_id, payload);
    for (const payload of output.prose_updates?.statement_notes ?? []) if (mandatedStatementIds.has(payload.id)) add("statement-note", payload.id, payload);
    for (const payload of output.proposed_core_edits) {
      const target = coreEditTarget(payload);
      if (mandatedTargetOperations.has(target)) add("core-edit", target, payload);
    }
  };
  projectedOutputs.forEach((output, index) => recordMandateShadow(output, dispatch[index].label));
  // Orchestrator mandates outrank solver output. Quarantine all same-target worker
  // mutations (including semantically identical copies with different rationale), and
  // archive any proof bytes for a node that is already mandated for deletion.
  const mandateProjectedOutputs = projectedOutputs.map((output) => ({
    ...output,
    proofs: output.proofs.filter((proof) => {
      if (!mandatedStatementIds.has(proof.id)) return true;
      mandateWithheldProofBytes.push({
        nodeId: proof.id,
        proofTex: proof.proof_tex ?? "",
        reason: mandatedDeleteIds.has(proof.id) ? "mandated-delete" : "mandated-statement-replace",
      });
      return false;
    }),
    added_lemmas: output.added_lemmas.filter((statement) => {
      if (!mandatedStatementIds.has(statement.id)) return true;
      mandateWithheldProofBytes.push({
        nodeId: statement.id,
        proofTex: statement.proof_tex ?? "",
        reason: mandatedDeleteIds.has(statement.id) ? "mandated-delete" : "mandated-statement-replace",
      });
      return false;
    }),
    resolved_oeqs: output.resolved_oeqs.filter((replacement) => {
      const blocked = mandatedStatementIds.has(replacement.source_id) || mandatedStatementIds.has(replacement.theorem.id);
      if (blocked) mandateWithheldProofBytes.push({
        nodeId: replacement.theorem.id,
        proofTex: replacement.theorem.proof_tex ?? "",
        reason: mandatedDeleteIds.has(replacement.source_id) || mandatedDeleteIds.has(replacement.theorem.id)
          ? "mandated-delete"
          : "mandated-statement-replace",
      });
      return !blocked;
    }),
    proposed_statement_changes: output.proposed_statement_changes.filter((change) => !mandatedStatementIds.has(change.id)),
    proposed_definition_changes: output.proposed_definition_changes.filter((change) => !mandatedDefinitionIds.has(change.id)),
    proposed_assumptions: output.proposed_assumptions.filter((assumption) => !mandatedAssumptionIds.has(assumption.id)),
    open_obligations: output.open_obligations.filter((obligation) => !mandatedStatementIds.has(obligation.node_id)),
    ...(output.prose_updates ? {
      prose_updates: {
        ...output.prose_updates,
        statement_notes: (output.prose_updates.statement_notes ?? [])
          .filter((note) => !mandatedStatementIds.has(note.id)),
      },
    } : {}),
    proposed_core_edits: output.proposed_core_edits.filter((edit) => {
      const target = coreEditTarget(edit);
      if (!mandatedTargetOperations.has(target)) return true;
      return false; // identical or conflicting: mandate remains canonical either way.
    }),
  }));
  // If multiple OEQ transactions claim the same answer theorem id, none is
  // canonical: first-wins would make dispatch order observable. Quarantine every
  // endpoint before any transaction mutates the core, while preserving unrelated
  // work and the complete bytes for adjudication.
  const oeqSourcesByAnswer = new Map<string, Set<string>>();
  for (const output of mandateProjectedOutputs) for (const resolution of output.resolved_oeqs) {
    const sources = oeqSourcesByAnswer.get(resolution.theorem.id) ?? new Set<string>();
    sources.add(resolution.source_id);
    oeqSourcesByAnswer.set(resolution.theorem.id, sources);
  }
  const contestedOeqAnswerIds = new Set(
    [...oeqSourcesByAnswer].filter(([, sources]) => sources.size > 1).map(([id]) => id),
  );
  const contestedOeqSourceIds = new Set<string>();
  const contestedOeqWithheld: ProofToArchive[] = [];
  const oeqAnswerCollisions: string[] = [];
  mandateProjectedOutputs.forEach((output, index) => {
    for (const resolution of output.resolved_oeqs) {
      if (!contestedOeqAnswerIds.has(resolution.theorem.id)) continue;
      contestedOeqSourceIds.add(resolution.source_id);
      oeqAnswerCollisions.push(`${resolution.source_id}->${resolution.theorem.id}`);
      contestedOeqWithheld.push({
        nodeId: resolution.theorem.id, proofTex: resolution.theorem.proof_tex ?? "", reason: "oeq-answer-id-collision",
      });
      for (const target of [resolution.source_id, resolution.theorem.id]) {
        withheldPayloads.push({
          category: "oeq-resolution", target, unit: dispatch[index].label,
          reason: "oeq-answer-id-collision", payload: structuredClone(resolution),
        });
      }
    }
  });
  const oeqProjectedOutputs = mandateProjectedOutputs.map((output) => ({
    ...output,
    resolved_oeqs: output.resolved_oeqs.filter((resolution) =>
      !contestedOeqAnswerIds.has(resolution.theorem.id)
    ),
  }));
  const crossDispositionTargets = (receiptsById: Map<string, TerminalDispositionReceipt[]>): string[] =>
    [...receiptsById].filter(([, receipts]) => {
      return receipts.some((left, index) => receipts.slice(index + 1).some((right) =>
        left.index !== right.index && hasTerminalContradiction([left, right])
      ));
    }).map(([id]) => id);
  const crossDispositionConflictIds = new Set([
    ...crossDispositionTargets(preProjectionDispositionReceipts),
  ]);
  // An OEQ resolution is one source→answer transaction. If open(Q) conflicts
  // with Q→T, blocking Q alone strands every same-round consumer of T after the
  // resolution is removed. Seed both endpoints so ordinary semantic closure
  // quarantines T-targeted companions and downstream consumers too.
  for (const id of [...crossDispositionConflictIds]) {
    const endpointReceipts = preProjectionDispositionReceipts.get(id) ?? [];
    for (const receipt of endpointReceipts) {
      if (receipt.category !== "oeq-resolution") continue;
      const resolution = receipt.payload as { source_id: string; theorem: { id: string } };
      crossDispositionConflictIds.add(resolution.source_id);
      crossDispositionConflictIds.add(resolution.theorem.id);
    }
  }
  const crossDispositionWithheld: ProofToArchive[] = [];
  for (const id of crossDispositionConflictIds) {
    for (const receipt of preProjectionDispositionReceipts.get(id) ?? []) {
      withheldPayloads.push({
        category: receipt.category,
        target: id,
        unit: dispatch[receipt.index].label,
        reason: "cross-unit-terminal-disposition",
        payload: structuredClone(receipt.payload),
      });
      const proofTex = receipt.category === "proof"
        ? (receipt.payload as { proof_tex?: string }).proof_tex
        : receipt.category === "added-node"
          ? (receipt.payload as { proof_tex?: string }).proof_tex
          : receipt.category === "oeq-resolution"
            ? (receipt.payload as { theorem?: { proof_tex?: string } }).theorem?.proof_tex
            : receipt.category === "open-obligation"
              ? (receipt.payload as { partial_result?: string }).partial_result
              : undefined;
      if ((proofTex ?? "").trim().length > 0) {
        crossDispositionWithheld.push({
          nodeId: receipt.category === "oeq-resolution"
            ? (receipt.payload as { theorem: { id: string } }).theorem.id
            : id,
          proofTex: proofTex!, reason: "cross-unit-terminal-disposition",
        });
      }
    }
  }
  const terminalProjectedOutputs = oeqProjectedOutputs.map((output) => ({
    ...output,
    proofs: output.proofs.filter((payload) => !crossDispositionConflictIds.has(payload.id)),
    resolved_oeqs: output.resolved_oeqs.filter((payload) =>
      !crossDispositionConflictIds.has(payload.source_id) &&
      !crossDispositionConflictIds.has(payload.theorem.id)),
    added_lemmas: output.added_lemmas.filter((payload) => !crossDispositionConflictIds.has(payload.id)),
    proposed_core_edits: output.proposed_core_edits.filter((payload) =>
      payload.kind !== "statement-delete" || !crossDispositionConflictIds.has(payload.id)),
    open_obligations: output.open_obligations.filter((payload) =>
      !crossDispositionConflictIds.has(payload.node_id)),
  }));
  const invalidProjectedOeqEndpoints = new Set<string>();
  const precomputedInvalidResolutionReceipts: string[] = [];
  mandateProjectedOutputs.forEach((output, index) => {
    for (const resolution of output.resolved_oeqs) {
      if (contextStatementById.get(resolution.source_id)?.kind === "openendedquestion") continue;
      invalidProjectedOeqEndpoints.add(resolution.source_id);
      invalidProjectedOeqEndpoints.add(resolution.theorem.id);
      precomputedInvalidResolutionReceipts.push(`${resolution.source_id}→${resolution.theorem.id}`);
      for (const target of [resolution.source_id, resolution.theorem.id]) {
        withheldPayloads.push({
          category: "oeq-resolution", target, unit: dispatch[index].label,
          reason: "invalid-oeq-source", payload: structuredClone(resolution),
        });
      }
    }
  });
  // A cross-unit id collision withholds ONLY the colliding payloads. Dropping every
  // variant (never picking one) keeps the assembled core independent of dispatch
  // order, which is what the previous hard abort was protecting — but the rest of
  // the round now survives instead of being discarded wholesale.
  const emissionConflicts = collectConflictingSolveEmissions(
    terminalProjectedOutputs,
    dispatch.map((u) => u.label),
  );
  const conflictProjectedOutputs = dropConflictingSolveEmissions(terminalProjectedOutputs, emissionConflicts);
  const crossCategoryResolutionConflictSources = new Set<string>();
  const statementConflictIds = new Set(
    emissionConflicts.filter((conflict) => conflict.category === "statement").map((conflict) => conflict.id),
  );
  terminalProjectedOutputs.forEach((output, index) => {
    for (const resolution of output.resolved_oeqs) {
      if (!statementConflictIds.has(resolution.theorem.id)) continue;
      crossCategoryResolutionConflictSources.add(resolution.source_id);
      for (const target of [resolution.source_id, resolution.theorem.id]) {
        withheldPayloads.push({
          category: "oeq-resolution", target, unit: dispatch[index].label,
          reason: "cross-unit-conflict-transaction", payload: structuredClone(resolution),
        });
      }
    }
  });
  const preexistingCollisionIds = new Set<string>();
  const preexistingOeqCollisionSources = new Set<string>();
  // `preCapabilityConflictOutputs` is a superset of the projected view; ids collect into a Set.
  for (const output of preCapabilityConflictOutputs) {
    for (const statement of output.added_lemmas) {
      const existing = contextStatementById.get(statement.id);
      if (existing === undefined) continue;
      const sameMathematicalClaim = existing.kind === statement.kind &&
        existing.statement === statement.statement &&
        sameDependencySet(existing.depends_on, statement.depends_on);
      const sameAgentCompletion = !sourceById.has(statement.id) &&
        completionIdentity(existing) === completionIdentity(statement);
      const sameFrozenCitation = sourceById.has(statement.id) && sameMathematicalClaim &&
        existing.status === "cited" && statement.status === "cited" &&
        JSON.stringify(existing.source ?? null) === JSON.stringify(statement.source ?? null);
      const frozenCitedReceipt = sameFrozenCitation && requiredCoreTargets.has(statement.id);
      // A byte-identical re-emission of a SETTLED frozen citation is the same no-op
      // discharge the install pass below records as a duplicate re-proof; it is not
      // a competing version and must not quarantine the consumers citing it.
      const frozenCitedNoOp = sameFrozenCitation && !requiredCoreTargets.has(statement.id) &&
        next.solved[statement.id]?.partial !== true;
      if (!sameAgentCompletion && !frozenCitedReceipt && !frozenCitedNoOp) preexistingCollisionIds.add(statement.id);
    }
  }
  const projectedResolutions = conflictProjectedOutputs.flatMap((output) => output.resolved_oeqs);
  const liveProjectedResolutionSources = new Set(
    projectedResolutions
      .filter((resolution) => contextStatementById.get(resolution.source_id)?.kind === "openendedquestion")
      .map((resolution) => resolution.source_id),
  );
  for (const resolution of projectedResolutions) {
    const existing = contextStatementById.get(resolution.theorem.id);
    if (existing === undefined || liveProjectedResolutionSources.has(existing.id)) continue;
    const durable = prev?.solved[resolution.theorem.id]?.node;
    const statementChange = conflictProjectedOutputs.flatMap((output) => output.proposed_statement_changes)
      .find((change) => change.id === resolution.theorem.id && change.proposed === resolution.theorem.statement);
    const proposalBacked = durable !== undefined && statementChange !== undefined &&
      reusableOeqAnswerMatches(durable, { ...resolution.theorem, statement: durable.statement });
    if (!reusableOeqAnswerMatches(existing, resolution.theorem) &&
        !(durable !== undefined && reusableOeqAnswerMatches(durable, resolution.theorem)) &&
        !proposalBacked) {
      preexistingCollisionIds.add(resolution.theorem.id);
      preexistingOeqCollisionSources.add(resolution.source_id);
    }
  }
  // Withholding a newly emitted helper/definition must also withhold every same-round
  // consumer whose carrier would otherwise become dangling. Do this to a fixpoint so
  // a consumer-of-a-consumer cannot leak through, but leave unrelated units intact.
  // Proof text is included because dependency auto-wiring happens later in merge.
  const transactionBlockedIds = new Set([
    ...emissionConflicts.map((conflict) => conflict.id),
    ...contestedOeqAnswerIds,
    ...contestedOeqSourceIds,
    ...contestedDispatchTargets,
    ...preexistingCollisionIds,
    ...preexistingOeqCollisionSources,
    ...capabilityRejectedOeqEndpoints,
    ...crossCategoryResolutionConflictSources,
    ...mandateRejectedOeqEndpoints,
    ...invalidProjectedOeqEndpoints,
    ...crossDispositionConflictIds,
  ]);
  const conflictConsumerIds = new Set<string>(transactionBlockedIds);
  // An open obligation is an attestation, not a mutation: a quarantined non-owned
  // obligation keeps its receipt but must not withhold the emitter's own proofs.
  const blockedConflictIds = new Set([
    ...transactionBlockedIds,
    ...capabilityQuarantines
      .filter((receipt) => receipt.category !== "open-obligation")
      .map((receipt) => receipt.target),
  ]);
  // Closure propagation scope. A withheld carrier for an id with NO surviving
  // canonical version (a same-round helper/answer/definition) leaves every
  // consumer dangling, so it propagates to every unit. A withheld edit/echo of an
  // EXISTING canonical node (a frozen `def:`/`sym:`/`bib:` a unit merely re-emitted
  // without authorization, or a contested existing statement) leaves the canonical
  // node intact: only the emitting unit's own dependents on it are in doubt.
  // Propagating those globally emptied rounds on one stray echo of a central def.
  const canonicalDeclarationIds = new Set<string>([
    ...core.statements.map((value) => value.id),
    ...core.definitions.map((value) => value.id),
    ...core.assumptions.map((value) => value.id),
    ...core.symbols.map((value) => `sym:${value.name}`),
    ...core.bibliography.map((value) => `bib:${value.key}`),
    ...ownershipDurableRecords.keys(),
  ]);
  const rawCarrierTargets = (output: typeof capabilityInputOutputs[number]): Set<string> => new Set<string>([
    ...output.proofs.map((payload) => payload.id),
    ...output.added_lemmas.map((payload) => payload.id),
    ...output.resolved_oeqs.flatMap((payload) => [payload.source_id, payload.theorem.id]),
    ...output.proposed_statement_changes.map((payload) => payload.id),
    ...output.proposed_definition_changes.map((payload) => payload.id),
    ...output.proposed_assumptions.map((payload) => payload.id),
    ...output.proposed_core_edits.map(coreEditTarget),
    ...output.open_obligations.map((payload) => payload.node_id),
    ...(output.prose_updates?.statement_notes ?? []).map((payload) => payload.id),
  ]);
  const rawTargetsByUnit = capabilityInputOutputs.map(rawCarrierTargets);
  const propagatingBlockedIds = new Set<string>();
  const blockedEmitters = new Map<string, Set<number>>();
  const noteBlocked = (id: string, index: number | null): void => {
    if (!canonicalDeclarationIds.has(id)) {
      propagatingBlockedIds.add(id);
      return;
    }
    const emitters = blockedEmitters.get(id) ?? new Set<number>();
    if (index !== null) emitters.add(index);
    else rawTargetsByUnit.forEach((targets, unitIndex) => { if (targets.has(id)) emitters.add(unitIndex); });
    blockedEmitters.set(id, emitters);
  };
  for (const id of blockedConflictIds) noteBlocked(id, null);
  const blockedIdsForUnit = (index: number): ReadonlySet<string> => new Set<string>([
    ...propagatingBlockedIds,
    ...[...blockedEmitters].filter(([, emitters]) => emitters.has(index)).map(([id]) => id),
  ]);
  const referencesBlocked = (payload: unknown, blockedIds: ReadonlySet<string>): boolean => {
    const text = JSON.stringify(payload);
    if (extractCitationRefs(text).some((id) => blockedIds.has(id))) return true;
    const structuredValues = new Set<string>();
    const authoredStrings = new Set<string>();
    const visit = (value: unknown, key = ""): void => {
      if (Array.isArray(value)) {
        if (["free_symbols", "inputs", "depends_on", "refs"].includes(key)) {
          for (const item of value) if (typeof item === "string") structuredValues.add(item);
        }
        for (const item of value) visit(item, key);
      } else if (value !== null && typeof value === "object") {
        for (const [childKey, child] of Object.entries(value)) visit(child, childKey);
      } else if (typeof value === "string") {
        authoredStrings.add(value);
        if (["cite", "ref", "key"].includes(key)) structuredValues.add(value);
      }
    };
    visit(payload);
    return [...blockedIds].some((blocked) => {
      if (blocked.startsWith("sym:")) return structuredValues.has(blocked.slice(4));
      if (blocked.startsWith("bib:")) {
        const key = blocked.slice(4);
        if (structuredValues.has(key)) return true;
        for (const authored of authoredStrings) {
          for (const match of authored.matchAll(/\\cite\w*(?:\[[^\]]*\])*\{([^}]*)\}/g)) {
            if (match[1].split(",").map((part) => part.trim()).includes(key)) return true;
          }
        }
        return false;
      }
      return structuredValues.has(blocked);
    });
  };
  const sameRoundStatementById = new Map<string, CoreStatement>();
  for (const candidate of conflictProjectedOutputs) {
    for (const statement of candidate.added_lemmas) sameRoundStatementById.set(statement.id, statement);
    for (const resolution of candidate.resolved_oeqs) sameRoundStatementById.set(resolution.theorem.id, resolution.theorem);
  }
  const semanticDeclarationById = new Map<string, unknown>([
    ...core.statements.map((value) => [value.id, value] as const),
    ...sameRoundStatementById,
    ...core.definitions.map((value) => [value.id, value] as const),
    ...core.assumptions.map((value) => [value.id, value] as const),
    ...core.symbols.map((value) => [`sym:${value.name}`, value] as const),
    ...core.bibliography.map((value) => [`bib:${value.key}`, value] as const),
  ]);
  const semanticRefs = (payload: unknown): Set<string> => {
    const refs = new Set(extractCitationRefs(JSON.stringify(payload) ?? ""));
    const visit = (value: unknown, key = ""): void => {
      if (Array.isArray(value)) {
        for (const item of value) {
          if (typeof item === "string") {
            if (key === "free_symbols" || key === "refs") refs.add(`sym:${item}`);
            if (key === "depends_on" || key === "inputs") refs.add(item);
          }
          visit(item, key);
        }
      } else if (value !== null && typeof value === "object") {
        for (const [childKey, child] of Object.entries(value)) visit(child, childKey);
      } else if (typeof value === "string") {
        if (key === "cite" || key === "key") refs.add(`bib:${value}`);
        if (key === "ref") refs.add(value.includes(":") ? value : `sym:${value}`);
      }
    };
    visit(payload);
    return refs;
  };
  const enrichedSemanticCarrier = (targetId: string, payload: unknown): unknown => {
    const target = sameRoundStatementById.get(targetId) ??
      contextStatementById.get(targetId) ?? ownershipDurableRecords.get(targetId)?.node ??
      semanticDeclarationById.get(targetId);
    const closure: unknown[] = [];
    const queued = [...new Set([...semanticRefs(payload), ...semanticRefs(target)])];
    const seen = new Set<string>();
    while (queued.length > 0) {
      const id = queued.shift()!;
      if (seen.has(id)) continue;
      seen.add(id);
      const declaration = semanticDeclarationById.get(id);
      if (declaration === undefined) continue;
      closure.push(declaration);
      for (const ref of semanticRefs(declaration)) if (!seen.has(ref)) queued.push(ref);
    }
    return { carrier: payload, target_declaration: target, semantic_closure: closure };
  };
  for (;;) {
    let changed = false;
    for (let outputIndex = 0; outputIndex < conflictProjectedOutputs.length; outputIndex += 1) {
      const output = conflictProjectedOutputs[outputIndex];
      const unitBlockedIds = blockedIdsForUnit(outputIndex);
      const carriers: Array<{ target: string; payload: unknown }> = [
        ...output.proofs.map((payload) => ({
          target: payload.id,
          payload: enrichedSemanticCarrier(payload.id, payload),
        })),
        ...output.added_lemmas.map((payload) => ({
          target: payload.id, payload: enrichedSemanticCarrier(payload.id, payload),
        })),
        ...output.resolved_oeqs.map((payload) => ({
          target: payload.theorem.id,
          payload: enrichedSemanticCarrier(payload.theorem.id, payload),
        })),
        ...output.proposed_statement_changes.map((payload) => ({
          target: payload.id, payload: enrichedSemanticCarrier(payload.id, payload),
        })),
        ...output.proposed_definition_changes.map((payload) => ({
          target: payload.id, payload: enrichedSemanticCarrier(payload.id, payload),
        })),
        ...output.proposed_assumptions.map((payload) => ({
          target: payload.id, payload: enrichedSemanticCarrier(payload.id, payload),
        })),
        ...output.proposed_core_edits.map((payload) => {
          const target = coreEditTarget(payload);
          return { target, payload: enrichedSemanticCarrier(target, payload) };
        }),
        ...output.open_obligations.map((payload) => ({
          target: payload.node_id, payload: enrichedSemanticCarrier(payload.node_id, payload),
        })),
        ...(output.prose_updates ? [{
          target: "prose:paper-wide",
          payload: enrichedSemanticCarrier("prose:paper-wide", output.prose_updates),
        }] : []),
        ...(output.prose_updates?.statement_notes ?? []).map((payload) => ({
          target: payload.id, payload: enrichedSemanticCarrier(payload.id, payload),
        })),
      ];
      for (const carrier of carriers) {
        if (!blockedConflictIds.has(carrier.target) && referencesBlocked(carrier.payload, unitBlockedIds)) {
          blockedConflictIds.add(carrier.target);
          conflictConsumerIds.add(carrier.target);
          noteBlocked(carrier.target, outputIndex);
          changed = true;
        }
      }
      // Q→T is one semantic transaction.  The generic carrier above is rooted at
      // T so that T's theorem/dependency closure is inspected, but once either
      // endpoint is blocked the other endpoint must be quarantined too.  Otherwise
      // filtering removes the resolution while an exact Q directive still looks
      // unaccounted-for and aborts unrelated accepted work.
      for (const resolution of output.resolved_oeqs) {
        if (!blockedConflictIds.has(resolution.source_id) &&
            !blockedConflictIds.has(resolution.theorem.id)) continue;
        for (const endpoint of [resolution.source_id, resolution.theorem.id]) {
          if (!blockedConflictIds.has(endpoint)) {
            blockedConflictIds.add(endpoint);
            noteBlocked(endpoint, outputIndex);
            changed = true;
          }
          conflictConsumerIds.add(endpoint);
        }
      }
    }
    if (!changed) break;
  }
  const conflictConsumerWithheld: ProofToArchive[] = [];
  const outputsAfterConflictClosure = conflictProjectedOutputs.map((output) => {
    for (const proof of output.proofs) {
      if (conflictConsumerIds.has(proof.id)) conflictConsumerWithheld.push({
        nodeId: proof.id,
        proofTex: proof.proof_tex ?? "",
        reason: "conflicted-dependency-consumer",
      });
    }
    for (const statement of output.added_lemmas) {
      if (conflictConsumerIds.has(statement.id)) conflictConsumerWithheld.push({
        nodeId: statement.id,
        proofTex: statement.proof_tex ?? "",
        reason: "conflicted-dependency-consumer",
      });
    }
    for (const resolution of output.resolved_oeqs) {
      if (conflictConsumerIds.has(resolution.theorem.id)) conflictConsumerWithheld.push({
        nodeId: resolution.theorem.id,
        proofTex: resolution.theorem.proof_tex ?? "",
        reason: "conflicted-dependency-consumer",
      });
    }
    return {
      ...output,
      proofs: output.proofs.filter((proof) => !conflictConsumerIds.has(proof.id)),
      added_lemmas: output.added_lemmas.filter((statement) => !conflictConsumerIds.has(statement.id)),
      resolved_oeqs: output.resolved_oeqs.filter((resolution) =>
        !conflictConsumerIds.has(resolution.source_id) && !conflictConsumerIds.has(resolution.theorem.id)
      ),
      proposed_statement_changes: output.proposed_statement_changes.filter((change) => !conflictConsumerIds.has(change.id)),
      proposed_definition_changes: output.proposed_definition_changes.filter((change) => !conflictConsumerIds.has(change.id)),
      proposed_assumptions: output.proposed_assumptions.filter((assumption) => !conflictConsumerIds.has(assumption.id)),
      proposed_core_edits: output.proposed_core_edits.filter((edit) => !conflictConsumerIds.has(coreEditTarget(edit))),
      open_obligations: output.open_obligations.filter((obligation) => !conflictConsumerIds.has(obligation.node_id)),
      prose_updates: output.prose_updates && !conflictConsumerIds.has("prose:paper-wide")
        ? {
          ...output.prose_updates,
          statement_notes: (output.prose_updates.statement_notes ?? [])
            .filter((note) => !conflictConsumerIds.has(note.id)),
        }
        : undefined,
    };
  });
  const withheldCapabilityEmissions = capabilityQuarantines.map((receipt) =>
    `${receipt.category}:${receipt.target}@${receipt.unit}`
  );
  const payloadsFor = (output: typeof revisionBoundRawOutputs[number], category: string, target: string): unknown[] => {
    if (category === "proof") return output.proofs.filter((payload) => payload.id === target);
    if (category === "statement") {
      return [
        ...output.added_lemmas.filter((payload) => payload.id === target),
        ...output.resolved_oeqs.filter((payload) => payload.theorem.id === target).map((payload) => payload.theorem),
      ];
    }
    if (category === "added-node" || category === "cited-added-node") {
      return output.added_lemmas.filter((payload) => payload.id === target);
    }
    if (category === "oeq-resolution") {
      // Preserve the complete atomic resolution receipt under either endpoint.
      // This is intentionally broader than the source-keyed durable map: a
      // transitive conflict discovered through theorem T must retain Q→T bytes.
      return output.resolved_oeqs.filter((payload) =>
        payload.source_id === target || payload.theorem.id === target
      );
    }
    if (category === "statement-change") return output.proposed_statement_changes.filter((payload) => payload.id === target);
    if (category === "definition-change") return output.proposed_definition_changes.filter((payload) => payload.id === target);
    if (category === "assumption") return output.proposed_assumptions.filter((payload) => payload.id === target);
    if (category === "core-edit") return output.proposed_core_edits.filter((payload) => coreEditTarget(payload) === target);
    if (category === "open-obligation") return output.open_obligations.filter((payload) => payload.node_id === target);
    if (category === "statement-note") return (output.prose_updates?.statement_notes ?? []).filter((payload) => payload.id === target);
    if (category === "prose-updates") {
      return target === "prose:paper-wide" && output.prose_updates ? [output.prose_updates] : [];
    }
    return [];
  };
  for (const conflict of emissionConflicts) {
    for (let index = 0; index < mandateProjectedOutputs.length; index += 1) {
      for (const payload of payloadsFor(mandateProjectedOutputs[index], conflict.category, conflict.id)) {
        withheldPayloads.push({
          category: conflict.category,
          target: conflict.id,
          unit: dispatch[index].label,
          reason: "cross-unit-conflict",
          payload: structuredClone(payload),
        });
      }
    }
  }
  for (const receipt of capabilityQuarantines) {
    const index = dispatch.findIndex((unit) => unit.label === receipt.unit);
    if (index < 0) continue;
    for (const payload of payloadsFor(revisionBoundRawOutputs[index], receipt.category, receipt.target)) {
      withheldPayloads.push({
        category: receipt.category,
        target: receipt.target,
        unit: receipt.unit,
        reason: "capability-quarantine",
        payload: structuredClone(payload),
      });
    }
  }
  for (let index = 0; index < conflictProjectedOutputs.length; index += 1) {
    for (const target of conflictConsumerIds) {
      for (const category of [
        "proof", "statement", "oeq-resolution", "statement-change", "definition-change",
        "assumption", "core-edit", "open-obligation", "statement-note", "prose-updates",
      ]) {
        for (const payload of payloadsFor(conflictProjectedOutputs[index], category, target)) {
          withheldPayloads.push({
            category,
            target,
            unit: dispatch[index].label,
            reason: "conflicted-dependency-consumer",
            payload: structuredClone(
              category === "proof" ? enrichedSemanticCarrier(target, payload) : payload,
            ),
          });
        }
      }
    }
  }
  const capabilityWithheldProofBytes: ProofToArchive[] = [];
  const capabilityInvalidResolutions: string[] = [];
  const liveOeqIdsBeforeProjection = new Set(
    core.statements.filter((statement) => statement.kind === "openendedquestion").map((statement) => statement.id),
  );
  for (const receipt of capabilityQuarantines) {
    const unitIndex = dispatch.findIndex((unit) => unit.label === receipt.unit);
    if (unitIndex < 0) continue;
    const raw = revisionBoundRawOutputs[unitIndex];
    if (receipt.category === "proof") {
      for (const proof of raw.proofs.filter((candidate) => candidate.id === receipt.target)) {
        capabilityWithheldProofBytes.push({
          nodeId: proof.id,
          proofTex: proof.proof_tex ?? "",
          reason: "unauthorized-target",
        });
      }
    }
    if (receipt.category === "added-node" || receipt.category === "cited-added-node") {
      for (const statement of raw.added_lemmas.filter((candidate) => candidate.id === receipt.target)) {
        capabilityWithheldProofBytes.push({
          nodeId: statement.id,
          proofTex: statement.proof_tex ?? "",
          reason: "unauthorized-target",
        });
      }
    }
    if (receipt.category === "oeq-resolution") {
      for (const resolution of raw.resolved_oeqs.filter((candidate) => candidate.source_id === receipt.target)) {
        capabilityWithheldProofBytes.push({
          nodeId: resolution.theorem.id,
          proofTex: resolution.theorem.proof_tex ?? "",
          reason: "unauthorized-target",
        });
        if (!liveOeqIdsBeforeProjection.has(resolution.source_id)) {
          capabilityInvalidResolutions.push(`${resolution.source_id}→${resolution.theorem.id}`);
        }
      }
    }
  }
  // A proof that declares it argues proposed claim bytes is one member of an atomic
  // transaction. Capability/mandate/conflict filtering may remove a different member
  // after the raw unit passed validation, so recheck the transaction here. The same
  // rule also preserves the narrower durable-owner recovery invariant below.
  const revokedDurableProofs: ProofToArchive[] = [];
  const outputs = outputsAfterConflictClosure.map((output, outputIndex) => ({
    ...output,
    proofs: output.proofs.filter((proof) => {
      const currentClaim = contextStatementById.get(proof.id) ??
        ownershipDurableRecords.get(proof.id)?.node;
      const rawChangedClaimEdit = currentClaim !== undefined &&
        revisionBoundRawOutputs[outputIndex].proposed_core_edits.some((edit) =>
          edit.kind === "statement-replace" && edit.id === proof.id &&
          edit.proposed.statement !== currentClaim.statement
        );
      if (rawChangedClaimEdit) {
        const changes = output.proposed_statement_changes.filter((candidate) => candidate.id === proof.id);
        const completePairs = changes.filter((change) => output.proposed_core_edits.some((edit) =>
          edit.kind === "statement-replace" && edit.id === proof.id &&
          edit.proposed.statement === change.proposed
        ));
        if (completePairs.length !== 1) {
          revokedDurableProofs.push({
            nodeId: proof.id,
            proofTex: proof.proof_tex ?? "",
            reason: "claim-transaction-revoked",
          });
          withheldPayloads.push({
            category: "proof", target: proof.id, unit: dispatch[outputIndex].label,
            reason: "claim-transaction-revoked", payload: structuredClone(proof),
          });
          return false;
        }
      }
      if (proof.argues_proposed === true) {
        const changes = output.proposed_statement_changes.filter((candidate) => candidate.id === proof.id);
        const completePairs = changes.filter((change) => output.proposed_core_edits.some((edit) =>
          edit.kind === "statement-replace" && edit.id === proof.id &&
          edit.proposed.statement === change.proposed
        ));
        if (completePairs.length === 1) return true;
        revokedDurableProofs.push({
          nodeId: proof.id,
          proofTex: proof.proof_tex ?? "",
          reason: "proposed-claim-transaction-revoked",
        });
        withheldPayloads.push({
          category: "proof", target: proof.id, unit: dispatch[outputIndex].label,
          reason: "proposed-claim-transaction-revoked", payload: structuredClone(proof),
        });
        return false;
      }
      if (!durableCorrectionTargetOwners.has(proof.id) ||
          core.statements.some((statement) => statement.id === proof.id) ||
          requiredCoreTargets.has(proof.id)) return true;
      const change = output.proposed_statement_changes.find((candidate) => candidate.id === proof.id);
      const pairSurvives = change !== undefined && output.proposed_core_edits.some((edit) =>
        edit.kind === "statement-replace" && edit.id === proof.id &&
        edit.proposed.statement === change.proposed
      );
      if (pairSurvives) return true;
      revokedDurableProofs.push({
        nodeId: proof.id,
        proofTex: proof.proof_tex ?? "",
        reason: "durable-correction-pair-revoked",
      });
      withheldPayloads.push({
        category: "proof", target: proof.id, unit: dispatch[outputIndex].label,
        reason: "durable-correction-pair-revoked", payload: structuredClone(proof),
      });
      return false;
    }),
  }));
  // A resolution whose source is not a live open-ended question in the frozen core
  // cannot transition anything: the source may be sealed as an acknowledged residual,
  // already resolved, or plain mis-addressed. This used to abort the WHOLE round
  // (eid_periodic 2026-08-30), discarding every unit's paid work over one
  // mis-addressed entry. Withhold just that resolution (its replacement theorem with
  // it, archived below) and any stray proof attached to a resolved source, and keep
  // the round.
  const invalidResolutionWithheld: ProofToArchive[] = [];
  const withheldInvalidResolutions: string[] = [
    ...capabilityInvalidResolutions,
    ...precomputedInvalidResolutionReceipts,
  ];
  {
    const liveOeqIds = new Set(
      core.statements.filter((s) => s.kind === "openendedquestion").map((s) => s.id),
    );
    const acceptedResolutionSources = new Set<string>();
    for (const output of outputs) {
      const kept: typeof output.resolved_oeqs = [];
      for (const resolution of output.resolved_oeqs) {
        if (!liveOeqIds.has(resolution.source_id)) {
          console.warn(
            `[D0-SOLVE] withheld resolution for '${resolution.source_id}': not an open-ended question ` +
              `in the frozen core; its replacement theorem '${resolution.theorem.id}' was withheld with it.`,
          );
          invalidResolutionWithheld.push({
            nodeId: resolution.theorem.id,
            proofTex: resolution.theorem.proof_tex ?? "",
            reason: "invalid-resolution-source",
          });
          withheldInvalidResolutions.push(`${resolution.source_id}→${resolution.theorem.id}`);
          withheldPayloads.push({
            category: "oeq-resolution",
            target: resolution.source_id,
            unit: dispatch[outputs.indexOf(output)]?.label ?? "unknown",
            reason: "invalid-resolution-source",
            payload: structuredClone(resolution),
          });
          continue;
        }
        if (acceptedResolutionSources.has(resolution.source_id)) {
          // A differing duplicate was already dropped by the cross-unit conflict
          // guard; a survivor here is byte-identical and harmless — keep one.
          console.warn(
            `[D0-SOLVE] deduplicated identical resolution for '${resolution.source_id}'.`,
          );
          continue;
        }
        acceptedResolutionSources.add(resolution.source_id);
        kept.push(resolution);
      }
      output.resolved_oeqs = kept;
    }
    for (const output of outputs) {
      output.proofs = output.proofs.filter((proof) => {
        if (!acceptedResolutionSources.has(proof.id)) return true;
        console.warn(
          `[D0-SOLVE] withheld stray proof attached to resolved OEQ '${proof.id}'; ` +
            `the resolution's replacement theorem is the only sanctioned carrier.`,
        );
        invalidResolutionWithheld.push({
          nodeId: proof.id,
          proofTex: proof.proof_tex ?? "",
          reason: "proof-on-resolved-oeq",
        });
        return false;
      });
    }
  }
  // Helper ids the solver re-used for a DIFFERENT claim than the core already holds, and
  // OEQ answers that collide on one theorem id. Both are withheld rather than guessed.
  const addedLemmaCollisions: Array<{ id: string; owner: string }> = [];
  // Identical-claim re-emissions of settled nodes, skipped as no-ops (canonical kept).
  // Reported informationally so emitted-vs-persisted reconciliation stays possible.
  const duplicateReproofIds: string[] = preCapabilityDuplicateReproofs.map(({ id }) => id);
  // Shared tail for every directive abort: a required target that is ALREADY
  // settled cannot yield a structural change (its re-emitted proof/metadata is
  // discharged as a duplicate), so re-dispatching the same directive only burns
  // rounds — the correct move is to cancel the mandate.
  const settledRequiredTargetsHint = (): string => {
    const settled = [...requiredCoreTargets].filter((id) => {
      const record = next.solved[id];
      const shown = contextStatementById.get(id);
      return (record !== undefined && record.partial !== true && (record.proof_tex ?? "").trim().length > 0) ||
        shown?.status === "proved" || shown?.status === "cited";
    });
    if (settled.length === 0) return "";
    const discharged = [...new Set([...duplicateReproofIds, ...preCapabilityEchoEdits.map(({ id }) => id)])]
      .filter((id) => requiredCoreTargets.has(id));
    return `. Required target(s) already settled in the rendered core: ${settled.join(", ")}` +
      (discharged.length > 0 ? ` (this round's re-emissions on ${discharged.join(", ")} were discharged as duplicates)` : "") +
      ". A settled node cannot satisfy a structured-change directive; cancel the mandate (d0_cancel_mandate) instead of re-dispatching.";
  };
  // Proof bytes this merge refuses to install ANYWHERE in hot state (withheld
  // collisions, unmatched ids, duplicate re-proofs, cross-unit conflict variants).
  // They exist only in this round's raw solve files, which the NEXT dispatch may
  // overwrite without a sweep — so commitRound copies these to the cold archive.
  const withheldProofBytes: ProofToArchive[] = [
    ...preCapabilityDuplicateReproofs.map(({ id, proofTex }) => ({
      nodeId: id,
      proofTex,
      reason: "duplicate-reproof",
    })),
    ...mandateWithheldProofBytes,
    ...revokedDurableProofs,
    ...invalidResolutionWithheld,
    ...conflictConsumerWithheld,
    ...capabilityWithheldProofBytes,
    ...contestedOeqWithheld,
    ...crossDispositionWithheld,
  ];
  // Conflict withholding is CATEGORY-specific (`dropConflictingSolveEmissions` keys on
  // category:id) — collect exactly what that drop removes, or a live payload sharing an
  // id with a conflicted OTHER-category emission would be falsely archived as withheld.
  {
    const droppedKeys = new Set(emissionConflicts.map((c) => `${c.category}:${c.id}`));
    const droppedBy = (category: string, id: string): boolean => droppedKeys.has(`${category}:${id}`);
    for (const output of projectedOutputs) {
      for (const pr of output.proofs) {
        if (droppedBy("proof", pr.id)) withheldProofBytes.push({ nodeId: pr.id, proofTex: pr.proof_tex ?? "", reason: "cross-unit-conflict" });
      }
      for (const lem of output.added_lemmas) {
        if (droppedBy("statement", lem.id)) withheldProofBytes.push({ nodeId: lem.id, proofTex: lem.proof_tex ?? "", reason: "cross-unit-conflict" });
      }
      for (const r of output.resolved_oeqs) {
        if (droppedBy("oeq-resolution", r.source_id) || droppedBy("statement", r.theorem.id)) {
          withheldProofBytes.push({ nodeId: r.theorem.id, proofTex: r.theorem.proof_tex ?? "", reason: "cross-unit-conflict" });
        }
      }
    }
  }
  let emittedStatementNoteChanges = outputs.some((output) =>
    (output.prose_updates?.statement_notes ?? []).some((note) => {
      const target = core.statements.find((statement) => statement.id === note.id);
      return target !== undefined &&
        ((note.justification !== undefined && note.justification !== target.justification) ||
          (note.gap !== undefined && note.gap !== target.gap) ||
          (note.consumer !== undefined && note.consumer !== target.consumer));
    })
  );
  const emittedStructuredChanges = requiredCoreEdits.length > 0 || emittedStatementNoteChanges || outputs.some((output) =>
    output.proposed_statement_changes.length > 0 ||
    output.proposed_definition_changes.length > 0 ||
    output.proposed_assumptions.length > 0 ||
    output.added_lemmas.length > 0 ||
    output.resolved_oeqs.length > 0 ||
    output.proposed_core_edits.some((edit) => edit.kind !== "rebuild-reverse-dependencies"),
  );
  // These are the immutable pre-merge echo/applicability views. Proof installation
  // below mutates `core` in place; retaining live object references here would make a
  // valid structural edit against a to-prove node look stale merely because this same
  // transaction also supplied its proof.
  const statementById = new Map(
    core.statements.map((statement) => [statement.id, structuredClone(statement)] as const),
  );
  // Capability projection above has already established that only the durable owner
  // may emit these bytes. Make its carried statement definition available to the
  // ordinary proof/provisional-proof merge even when a shelved partial is absent from
  // the assembled current core. Without this second half of the repair, ownership
  // accepts the proof but the id matcher still reports the same false PLUMBING FAULT.
  const authorizedExistingNodeIds = new Set(outputs.flatMap((output) => [
    ...output.proofs.map((proof) => proof.id),
    ...output.added_lemmas.map((statement) => statement.id),
  ]));
  for (const records of [prev?.solved ?? {}, next.solved]) {
    for (const [id, record] of Object.entries(records)) {
      if (authorizedExistingNodeIds.has(id) && record.node !== undefined && !statementById.has(id)) {
        statementById.set(id, structuredClone(record.node));
      }
    }
  }
  for (const [id, statement] of authoritativeStatementCatalog(proto.statements, next)) {
    if (!statementById.has(id)) statementById.set(id, structuredClone(statement));
  }
  // An open obligation may legitimately attest a node introduced in this same
  // solve transaction. Keep the pre-merge map above for applicability decisions,
  // but include same-round additions for the obligation identity/kind check.
  const obligationStatementById = new Map(statementById);
  for (const output of outputs) {
    for (const statement of output.added_lemmas) {
      if (!obligationStatementById.has(statement.id)) {
        obligationStatementById.set(statement.id, structuredClone(statement));
      }
    }
    for (const resolution of output.resolved_oeqs) {
      if (!obligationStatementById.has(resolution.theorem.id)) {
        obligationStatementById.set(resolution.theorem.id, structuredClone(resolution.theorem));
      }
    }
  }
  const definitionById = new Map(
    core.definitions.map((definition) => [definition.id, structuredClone(definition)] as const),
  );
  const initialSettledProofs = new Map(
    core.statements
      .filter((statement) => statement.status === "proved" && (statement.proof_tex ?? "").trim().length > 0)
      .map((statement) => [statement.id, statement.proof_tex!] as const),
  );
  const initialResolvedOeqs = structuredClone(next.resolved_oeqs ?? {});
  for (const output of outputs) {
    output.open_obligations = output.open_obligations.filter((obligation) => {
      const target = obligationStatementById.get(obligation.node_id);
      if (!target) {
        // An obligation naming no existing node attests nothing real. Drop just
        // this entry instead of aborting every sibling unit's paid work: a
        // mistyped REQUIRED target still fails the exact-target coverage check
        // below with a precise message naming the missing id. Its partial-result
        // bytes are archived like every other refused payload class.
        if ((obligation.partial_result ?? "").trim().length > 0) {
          withheldProofBytes.push({
            nodeId: obligation.node_id,
            proofTex: obligation.partial_result!,
            reason: "dropped-nonexistent-obligation",
          });
        }
        console.warn(`[D0-SOLVE] open obligation names no current statement (${obligation.node_id}); dropped`);
        return false;
      }
      // The id/kind mismatch stays fail-closed: it references a REAL node the
      // worker misidentified, so dropping it would hide an openness attestation.
      const hasOeqId = obligation.node_id.startsWith("oeq:");
      const hasOeqKind = target.kind === "openendedquestion";
      if (hasOeqId !== hasOeqKind) {
        throw new Error(
          `Stage 0-SOLVE open obligation has inconsistent OEQ id/kind for ${obligation.node_id}`,
        );
      }
      return true;
    });
  }
  const terminalDisposition = new Map<string, Set<string>>();
  const noteDisposition = (id: string, disposition: string): void => {
    const dispositions = terminalDisposition.get(id) ?? new Set<string>();
    dispositions.add(disposition);
    terminalDisposition.set(id, dispositions);
  };
  for (const output of outputs) {
    for (const proof of output.proofs) noteDisposition(proof.id, "proof");
    for (const resolution of output.resolved_oeqs) noteDisposition(resolution.source_id, "oeq-resolution");
    for (const statement of output.added_lemmas) {
      const settled = statement.status === "cited" ||
        (statement.status === "proved" && (statement.proof_tex ?? "").trim().length > 0);
      if (settled) {
        const existing = statementById.get(statement.id);
        if (existing?.kind === "openendedquestion") {
          throw new Error(
            `Stage 0-SOLVE attempted to settle OEQ ${statement.id} in added_lemmas; ` +
              "solved OEQs must use resolved_oeqs",
          );
        }
        noteDisposition(statement.id, "added-node");
      }
    }
    for (const edit of output.proposed_core_edits) {
      if (edit.kind === "statement-delete") noteDisposition(edit.id, "statement-delete");
    }
    for (const obligation of output.open_obligations) noteDisposition(obligation.node_id, "open-obligation");
  }
  for (const [id, dispositions] of terminalDisposition) {
    if (dispositions.has("open-obligation") && dispositions.size > 1) {
      throw new Error(
        `Stage 0-SOLVE emitted mutually exclusive terminal dispositions for ${id}: ` +
          [...dispositions].sort().join(", "),
      );
    }
  }
  if (requiredCoreTargets.size > 0) {
    const emittedTargets = new Set<string>(requiredCoreEdits.map(coreEditTarget));
    const noteIsSubstantive = (note: { id: string; justification?: string; gap?: string; consumer?: string }): boolean => {
      const target = statementById.get(note.id);
      return target !== undefined &&
        ((note.justification !== undefined && note.justification !== target.justification) ||
          (note.gap !== undefined && note.gap !== target.gap) ||
          (note.consumer !== undefined && note.consumer !== target.consumer));
    };
    for (const output of outputs) {
      // Exact theorem/lemma repair targets are legitimately discharged by a new
      // proof payload. Structural requirements are checked independently below.
      for (const proof of output.proofs) {
        if (statementById.has(proof.id)) emittedTargets.add(proof.id);
      }
      for (const change of output.proposed_statement_changes) {
        const target = statementById.get(change.id);
        if (target && target.kind !== "openendedquestion") emittedTargets.add(change.id);
      }
      for (const change of output.proposed_definition_changes) {
        const target = definitionById.get(change.id);
        if (target && target.by_member_properties === undefined) emittedTargets.add(change.id);
      }
      for (const assumption of output.proposed_assumptions) {
        if (assumption.id.startsWith("ass:")) emittedTargets.add(assumption.id);
      }
      for (const statement of output.added_lemmas) emittedTargets.add(statement.id);
      for (const replacement of output.resolved_oeqs) {
        // A resolved OEQ is the structured answer to its SOURCE target. Credit
        // both ends of the replacement: directives naturally name the frozen
        // oeq: node, while later consumers name the emitted thm: node.
        emittedTargets.add(replacement.source_id);
        emittedTargets.add(replacement.theorem.id);
      }
      for (const edit of output.proposed_core_edits) emittedTargets.add(coreEditTarget(edit));
      // Statement notes are the first-class channel for justification/gap/consumer
      // metadata. Credit only a note that directly names the required statement and
      // changes at least one supplied field; unrelated or byte-identical prose cannot
      // consume an exact target directive.
      for (const note of output.prose_updates?.statement_notes ?? []) {
        if (noteIsSubstantive(note)) emittedTargets.add(note.id);
      }
      // A required `oeq:` target the solver leaves genuinely open is attested through
      // an open obligation — the prompt's OEQ contract forbids a proof or resolution
      // entry for it, so silence was the only alternative and the whole round was
      // discarded as "omitted". Credit the attestation: commit routes an oeq-only
      // obligation to D0.5 as an acknowledged residual. Only `oeq:` ids get this
      // credit — an obligation on a theorem/lemma target is a gap, not a discharge.
      for (const obligation of output.open_obligations) {
        const target = statementById.get(obligation.node_id);
        if (target?.kind === "openendedquestion" && obligation.node_id.startsWith("oeq:")) {
          emittedTargets.add(obligation.node_id);
        }
      }
    }
    // Exact means direct. A shared dependency edit may be useful, but it cannot
    // consume several requested targets without emitting those targets themselves.
    // If dependency-first work is needed, the orchestrator keeps the original
    // targets pending and issues a separate directive after that edit commits.
    const withheldTargets = new Set([
      ...emissionConflicts.map((conflict) => conflict.id),
      ...conflictConsumerIds,
      ...capabilityQuarantines.map((receipt) => receipt.target),
      ...contestedOeqSourceIds,
      ...contestedOeqAnswerIds,
      ...contestedDispatchTargets,
    ]);
    const missing = [...requiredCoreTargets].filter((target) =>
      !emittedTargets.has(target) && !withheldTargets.has(target)
    );
    if (missing.length > 0) {
      throw new Error(
        `Stage 0-SOLVE directive required exact structured target(s) ${[...requiredCoreTargets].join(", ")}, ` +
          `but the solver omitted ${missing.join(", ")}; unrelated proposals cannot satisfy this directive` +
          settledRequiredTargetsHint(),
      );
    }
  }
  if (requiresCoreChanges && !emittedStructuredChanges &&
      emissionConflicts.length === 0 && conflictConsumerIds.size === 0 && capabilityQuarantines.length === 0) {
    throw new Error(
      "Stage 0-SOLVE consumed a STRUCTURED CORE CHANGES REQUIRED directive but emitted no proposed changes; " +
        "refusing to persist proofs/prose around stale frozen nodes" + settledRequiredTargetsHint(),
    );
  }
  // Prose is a narrative overlay, never load-bearing mathematics. Non-owner or
  // unsolicited prose used to abort the whole round (exp_mixed 2026-08-09: "the
  // canonical prose owner is none" discarded every unit's proofs over a stray
  // tldr). Withhold the prose, keep the round.
  for (let i = 0; i < outputs.length; i += 1) {
    const output = outputs[i];
    if (output.prose_updates === undefined) continue;
    if (i !== proseOwnerIndex) {
      console.warn(
        `[D0-SOLVE] withheld prose_updates from unit '${dispatch[i].label}': canonical prose owner is ` +
          `${proseOwnerIndex === null ? "none" : `'${dispatch[proseOwnerIndex].label}'`}.`,
      );
      withheldPayloads.push({
        category: "prose-updates", target: "prose:paper-wide", unit: dispatch[i].label,
        reason: "unauthorized-prose-owner", payload: structuredClone(output.prose_updates),
      });
      output.prose_updates = undefined;
    } else if (!hasPendingDirective) {
      console.warn(
        `[D0-SOLVE] withheld prose_updates from unit '${dispatch[i].label}': no pending orchestrator ` +
          `directive solicited narrative changes.`,
      );
      withheldPayloads.push({
        category: "prose-updates", target: "prose:paper-wide", unit: dispatch[i].label,
        reason: "unsolicited-prose", payload: structuredClone(output.prose_updates),
      });
      output.prose_updates = undefined;
    }
  }
  const proseUpdates = outputs.flatMap((o) => o.prose_updates ? [o.prose_updates] : []);
  // Fail before assembly/persistence if a run-scoped semantic contract detects a
  // forbidden replacement theorem or a regressed emitted proof interface.
  validateSolveManifest(semanticManifest, outputs);

  // A solved open-ended question changes mathematical type: its answer (especially a
  // negative or partial answer) is not the interrogative proposition originally posed.
  // Require the solver to supply the actual answer as a replacement theorem instead of
  // attaching proof text to an `oeq:` node that F2 must treat as an open Prop definition.
  const resolvedOeqEntries = outputs.flatMap((o) => o.resolved_oeqs);
  const resolvedOeqSources = new Set(resolvedOeqEntries.map((r) => r.source_id));
  const duplicateResolution = resolvedOeqEntries.find(
    (r, i) => resolvedOeqEntries.findIndex((x) => x.source_id === r.source_id) !== i,
  );
  if (duplicateResolution) {
    throw new Error(`Stage 0-SOLVE emitted multiple resolutions for ${duplicateResolution.source_id}`);
  }
  for (const r of resolvedOeqEntries) {
    const source = core.statements.find((s) => s.id === r.source_id);
    if (!source || source.kind !== "openendedquestion") {
      throw new Error(`Stage 0-SOLVE resolution source ${r.source_id} is not an open-ended question in the frozen core`);
    }
    if (outputs.some((o) => o.proofs.some((p) => p.id === r.source_id))) {
      throw new Error(`Stage 0-SOLVE must not also attach a proof to resolved OEQ ${r.source_id}; emit only its replacement theorem`);
    }
  }
  // Validate every same-id answer before proof/lemma merge mutates the in-memory core.
  // A failed collision therefore cannot partially install any sibling output, even
  // transiently. Exact reuse is permitted only for a settled durable agent theorem;
  // frozen, partial and proofless records must still fail closed.
  const resolvedOeqReplacement = new Map(resolvedOeqEntries.map((r) => [r.source_id, r.theorem.id] as const));
  const reusableResolutionSources = new Set<string>();
  // Sources admitted ONLY because the existing node is the open projection of a stale
  // agent target (`status:"to-prove"`, proof cleared). These are NOT no-ops like an exact
  // settled re-emission: the projection must be REPLACED by the proved answer, or the
  // core keeps the unproved placeholder and the emitted proof is persisted nowhere.
  const projectionResolutionSources = new Set<string>();
  const projectionDurableAnswers = new Map<string, CoreStatement>();
  const staleAgentTargetIds = new Set(sctx.staleAgentTargets.map((statement) => statement.id));
  for (const r of resolvedOeqEntries) {
    const emitted = {
      ...r.theorem,
      depends_on: remapResolvedDependencies(r.theorem.id, r.theorem.depends_on, resolvedOeqReplacement,
        (id) => core.statements.find((s) => s.id === id)?.depends_on),
    };
    const existing = core.statements.find((s) => s.id === emitted.id && !resolvedOeqSources.has(s.id));
    if (!existing) continue;
    const priorCarried = prev?.solved[emitted.id];
    // `next` deliberately projects an invalidated agent theorem to a partial,
    // `to-prove` target before dispatch. Comparing the fresh proved answer with
    // that projection makes an exact re-derivation look non-identical. The durable
    // identity being reverified is the settled PRIOR record; the open projection is
    // only a dispatch vehicle and must never become the comparison authority.
    const durable = priorCarried?.node
      ? { ...priorCarried.node, proof_tex: priorCarried.proof_tex }
      : null;
    // A solver may re-emit the same OEQ answer with a same-round, explicitly gated
    // statement cleanup (for example removing serialization debris). Collision
    // validation runs before proposal adjudication, so compare the re-emission to
    // the durable theorem WITH ONLY that declared statement overlay. Marking the
    // source reusable keeps the current durable theorem in the assembled core; it
    // does not install the unaccepted overlay. The proposal checkpoint remains the
    // sole path by which the new text can land.
    const statementChanges = [...new Map(
      outputs.flatMap((output) => output.proposed_statement_changes)
        .filter((change) => change.id === emitted.id)
        .map((change) => [JSON.stringify(change), change] as const),
    ).values()];
    const proposalBackedReemission = durable !== null &&
      statementChanges.length === 1 &&
      statementChanges[0].current === durable.statement &&
      statementChanges[0].proposed === emitted.statement &&
      reusableOeqAnswerMatches(
        { ...durable, statement: statementChanges[0].proposed },
        emitted,
      );
    const reusableDurableRecord =
      priorCarried?.node !== undefined &&
      priorCarried.partial !== true &&
      priorCarried.proof_tex.trim().length > 0 &&
      durable !== null &&
      (reusableOeqAnswerMatches(durable, emitted) || proposalBackedReemission);
    const existingIsExact = reusableOeqAnswerMatches(existing, emitted);
    const existingIsOpenProjection = staleAgentTargetIds.has(emitted.id);
    if ((!existingIsExact && !existingIsOpenProjection) || !reusableDurableRecord) {
      throw new Error(
        `Stage 0-SOLVE OEQ resolution theorem id collides with non-identical existing node ${emitted.id} ` +
        `(existing_exact=${existingIsExact}, stale_projection=${existingIsOpenProjection}, ` +
        `settled_prior=${priorCarried?.node !== undefined && priorCarried.partial !== true && priorCarried.proof_tex.trim().length > 0}, ` +
        `statement_overlays=${statementChanges.length}, proposal_backed=${proposalBackedReemission})`,
      );
    }
    reusableResolutionSources.add(r.source_id);
    // ONLY when the emitted theorem matches the DURABLE settled answer. A
    // proposal-backed re-emission also lands here with an open projection, but it carries
    // UNADJUDICATED overlay text — installing that would launder a proposal past review,
    // which apply owns. Such a source keeps the old no-op behaviour.
    if (!existingIsExact && existingIsOpenProjection && durable !== null && reusableOeqAnswerMatches(durable, emitted)) {
      projectionResolutionSources.add(r.source_id);
      projectionDurableAnswers.set(r.source_id, durable);
    }
  }
  const unnormalizedOeqProof = outputs
    .flatMap((o) => o.proofs)
    .find((p) => core.statements.some((s) => s.id === p.id && s.kind === "openendedquestion") && !resolvedOeqSources.has(p.id));
  if (unnormalizedOeqProof) {
    throw new Error(
      `Stage 0-SOLVE proved ${unnormalizedOeqProof.id} in place; solved OEQs must be emitted in resolved_oeqs as replacement thm: nodes`,
    );
  }

  // Merge new proofs + lemmas; snapshot each into the next working state so a later
  // round can decide reuse; collect proposed changes.
  const proposedChanges: ProposedStatementChange[] = [];
  const proposedDefChanges: ProposedDefinitionChange[] = [];
  const proposedAssumptions: ProposedAssumption[] = [];
  const proposedCoreEdits: RawCoreEdit[] = [];
  // Operation identity excludes rationale prose. A carried supersession and a newly
  // mandated copy of the same A→B delete may legitimately have different reasons; keep
  // exactly one operation, with the mandate (the current adjudicated record) winning.
  const seededByOperation = new Map<string, RawCoreEdit>();
  for (const edit of pendingSupersessionEdits) seededByOperation.set(coreEditOperationKey(edit), edit);
  for (const edit of requiredCoreEdits) seededByOperation.set(coreEditOperationKey(edit), edit);
  for (const edit of seededByOperation.values()) {
    proposedCoreEdits.push(edit);
  }
  const openObligations: OpenObligation[] = [];
  const openObligationIds = new Set<string>();
  const normalizedProposalText = (value: string): string => normalizeTexWhitespace(value);
  // A proposal invalidates only proofs whose mathematical content closure touches it.
  // The former round-wide boolean made one local narrowing turn EVERY proof and added
  // theorem from every solve unit into partial debt, spending another full D0 round on
  // results that were independent of the edit. Track the edited ids and walk the same
  // declared statement/definition closure used by incremental reuse. Authored literal
  // references are included as a backstop before citation auto-wiring runs below.
  const proofInvalidatingIds = new Set<string>();
  let hasGlobalProofInvalidation = false;
  for (const output of outputs) {
    for (const change of output.proposed_statement_changes) {
      const current = core.statements.find((statement) => statement.id === change.id);
      // Claim identity is byte-exact. TeX comments and literal environments make
      // ordinary whitespace normalization semantic, and a false no-op classification
      // can attach a proof of the proposed claim to the old frozen bytes.
      if (current && current.statement !== change.proposed) {
        proofInvalidatingIds.add(change.id);
      }
    }
    for (const change of output.proposed_definition_changes) {
      const current = core.definitions.find((definition) => definition.id === change.id);
      if (current && current.by_member_properties === undefined &&
          normalizedProposalText(current.construction) !== normalizedProposalText(change.proposed)) {
        proofInvalidatingIds.add(change.id);
      }
    }
    // A newly proposed assumption may be used semantically without its fresh id being
    // declared yet. Keep this channel fail-closed rather than certifying any same-round
    // proof before the assumption is adjudicated and applied. An assumption the core
    // already holds with identical (normalized) condition is a restatement of an applied
    // add, not new semantics — mirroring the no-op text checks above; without this the
    // echo deferred EVERY proof in the round and it discharged "proved 0".
    const echoAssumption = (a: { id: string; condition: string }): boolean => {
      const current = core.assumptions.find((x) => x.id === a.id);
      return current !== undefined &&
        normalizedProposalText(current.condition) === normalizedProposalText(a.condition);
    };
    if ((output.proposed_assumptions ?? []).some((a) => !echoAssumption(a))) hasGlobalProofInvalidation = true;
    for (const edit of output.proposed_core_edits ?? []) {
      if (edit.kind === "rebuild-reverse-dependencies") continue;
      // Symbol and bibliography meaning are global metadata rather than declared
      // `depends_on` edges, so keep their previous whole-round treatment.
      if (edit.kind === "symbol-add" || edit.kind === "symbol-replace" || edit.kind === "symbol-delete" ||
          edit.kind === "bibliography-replace") {
        hasGlobalProofInvalidation = true;
      } else if (edit.kind === "statement-replace") {
        const current = core.statements.find((statement) => statement.id === edit.id);
        // Deliberately NOT comparing `depends_on`: statement-replace is the
        // dependency/metadata rewire channel (statement text must echo byte-for-byte),
        // and an edge rewire with all referenced CONTENT intact does not change what a
        // proof established. Content changes travel through their own tracked channels
        // (def/assumption changes, definition-add/delete), whose ids the closure walk
        // below already sees. Mirrors `snapshotBasisValid` in stages/d0_working.ts —
        // dep-only echoes used to convert every same-round proof into partial debt.
        const proofInterfaceMoved = !current ||
          current.kind !== edit.proposed.kind ||
          JSON.stringify(current.source ?? null) !== JSON.stringify(edit.proposed.source ?? null);
        if (proofInterfaceMoved) proofInvalidatingIds.add(edit.id);
      } else {
        proofInvalidatingIds.add(coreEditTarget(edit));
      }
    }
  }
  for (const edit of pendingSupersessionEdits) proofInvalidatingIds.add(coreEditTarget(edit));
  for (const edit of requiredCoreEdits) proofInvalidatingIds.add(coreEditTarget(edit));

  const extraStatements = [
    ...outputs.flatMap((output) => output.added_lemmas.map((statement) => [statement.id, statement] as const)),
    ...outputs.flatMap((output) => output.resolved_oeqs.map((r) => [r.theorem.id, r.theorem] as const)),
  ].map(([, statement]) => statement);
  const proofNeedsPostEditRevalidation = (node: CoreStatement, proofText = ""): boolean => {
    if (hasGlobalProofInvalidation) return true;
    return proofContentClosureIntersects({
      core, node, proofText, changedIds: proofInvalidatingIds, extraStatements,
    });
  };
  const deferredProofs: Array<{ id: string; proof_tex: string; argues_proposed?: boolean }> = [];
  const deferredCitationRevalidations: CoreStatement[] = [];
  const deferCitationRevalidation = (statement: CoreStatement): void => {
    const prior = deferredCitationRevalidations.find((candidate) => candidate.id === statement.id);
    if (prior !== undefined && !reusableOeqAnswerMatches(prior, statement)) {
      throw new Error(`Stage 0-SOLVE emitted conflicting cited revalidation receipts for ${statement.id}`);
    }
    if (prior === undefined) deferredCitationRevalidations.push(structuredClone(statement));
  };
  const deferProof = (id: string, proofTex: string, arguesProposed?: boolean): void => {
    const prior = deferredProofs.find((proof) => proof.id === id);
    if (prior && prior.proof_tex !== proofTex) {
      throw new Error(`Stage 0-SOLVE emitted conflicting provisional proof payloads for ${id}`);
    }
    if (!prior) deferredProofs.push({ id, proof_tex: proofTex, ...(arguesProposed ? { argues_proposed: true } : {}) });
  };
  let addedLemmas = 0;
  let solved = 0;
  // Every emitted proof id that names no core statement. Collected so the round can
  // report an id-mapping fault AS an id-mapping fault, instead of silently dropping
  // the proof and then blaming the solver for making no progress.
  const unmatchedProofIds: string[] = [];
  const quarantinedProofs: Array<{ id: string; unit: string; owner: string }> = [];
  for (const receipt of capabilityQuarantines.filter((item) => item.category === "proof")) {
    const unitIndex = dispatch.findIndex((unit) => unit.label === receipt.unit);
    const proof = unitIndex < 0
      ? undefined
      : rawOutputs[unitIndex].proofs.find((candidate) => candidate.id === receipt.target);
    if (!proof) continue;
    // The id exists; the emitter lacked ownership. Report it as such, never as an
    // id-mapping fault (which told operators to reconcile ids that were fine).
    quarantinedProofs.push({ id: proof.id, unit: receipt.unit, owner: receipt.owner });
    withheldProofBytes.push({
      nodeId: proof.id,
      proofTex: proof.proof_tex ?? "",
      reason: "unauthorized-target",
    });
  }
  // A proof emitted in `proofs[]` for a node this SAME round adds (added_lemmas /
  // resolved_oeqs) has no core statement while the per-unit loop runs — the prompt
  // licenses that split ("<target or lemma id>"), and cross-unit splits made matching
  // dispatch-order-dependent. Park such proofs and apply them AFTER every unit's
  // nodes are installed; only a target still absent then is a real unmatched-id fault.
  const roundEmittedIds = new Set(extraStatements.map((s) => s.id));
  // RECORDS-ONLY MERGE (Batch B): the workspace core is a READ-ONLY dispatch
  // view after context assembly. "What statements exist right now" = that view
  // plus this round's installs, tracked here; every install is simultaneously a
  // working RECORD, so the persisted render can never disagree with the merge's
  // own view of the round.
  const installedNodes = new Map<string, CoreStatement>();
  const statementExists = (id: string): boolean => statementById.has(id) || installedNodes.has(id);
  const currentStatement = (id: string): CoreStatement | undefined =>
    installedNodes.get(id) ?? statementById.get(id);
  /** Is this node settled RIGHT NOW (carried-in settled, or recorded full this round)? */
  const settledNow = (id: string): boolean => {
    const rec = next.solved[id];
    if (rec !== undefined && rec.partial !== true && (rec.proof_tex ?? "").trim().length > 0) return true;
    return initialSettledProofs.has(id) && next.solved[id] === undefined;
  };
  const pendingSameRoundProofs: Array<{
    proof: { id: string; proof_tex?: string; argues_proposed?: boolean }; ownerLabel: string;
  }> = [];
  const roundHasReviewBundle = outputs.some((output) =>
    output.proposed_statement_changes.length > 0 ||
    output.proposed_definition_changes.length > 0 ||
    output.proposed_assumptions.length > 0 ||
    output.proposed_core_edits.length > 0
  );
  const reviewDeferredRecoveredPartials = new Map<string, { statement: CoreStatement; owner: string }>();
  for (let i = 0; i < outputs.length; i++) {
    const o = outputs[i];
    const ownerLabel = dispatch[i].label;
    const statementIds = new Set([...statementById.keys(), ...installedNodes.keys()]);
    const unmatchedHere = new Set(
      partitionProofsByTarget(o.proofs, statementIds).unmatched.filter((id) => !roundEmittedIds.has(id)),
    );
    unmatchedProofIds.push(...unmatchedHere);
    for (const pr of o.proofs) {
      if (mandatedDeleteIds.has(pr.id)) {
        withheldProofBytes.push({ nodeId: pr.id, proofTex: pr.proof_tex ?? "", reason: "mandated-delete" });
        continue;
      }
      if (unmatchedHere.has(pr.id)) withheldProofBytes.push({ nodeId: pr.id, proofTex: pr.proof_tex ?? "", reason: "unmatched-id" });
      else if (!statementIds.has(pr.id)) pendingSameRoundProofs.push({ proof: pr, ownerLabel });
    }
    for (const pr of o.proofs) {
      if (mandatedDeleteIds.has(pr.id)) continue;
      const stmt = currentStatement(pr.id);
      // AUDIT-B: if the same round proposes changing the statement, do not attach its proof to the old frozen claim.
      // AUDIT-R3: if the round proposes a new assumption, leave proofs for the re-solve after it is applied.
      const needsPostEditRevalidation = stmt
        ? proofNeedsPostEditRevalidation(stmt, pr.proof_tex ?? "")
        : false;
      if (stmt && !needsPostEditRevalidation && typeof pr.proof_tex === "string" && pr.proof_tex.trim().length > 0) {
        // (Records only: no workspace-core write — the render derives the
        // published `proved` status from the record.)
        // A node ADDED this round was already counted at install (`addedLemmas`), so
        // counting it again here made the discharge count depend on which channel —
        // and, cross-unit, on which ORDER — the solver happened to use. Mirrors the
        // parked-proof drain, which deliberately does not increment.
        if (!roundEmittedIds.has(stmt.id)) solved += 1;
        // `prev` is the PREVIOUS round: for a lemma this round installed (a sibling unit
        // emitting its proof through `proofs[]` — the ordering the parking mechanism does
        // NOT cover, because the id is already in `statementIds` by then) it holds
        // nothing, so recordProof replaced the node-carrying record with a node-less one
        // and the next round's carryPlan dropped the lemma entirely. Consult the
        // same-round install, and let its owner win over the proof-emitting unit.
        const installed = !sourceById.has(stmt.id) ? next.solved[stmt.id] : undefined;
        const priorAgent = !sourceById.has(stmt.id) ? prev?.solved[stmt.id] : undefined;
        recordProof(next, proto, {
          id: stmt.id,
          snapshotOf: stmt,
          proofTex: pr.proof_tex,
          ...(installed?.node || priorAgent?.node
            ? { node: stmt, owner: installed?.owner ?? priorAgent?.owner }
            : {}),
        });
      } else if (
        stmt &&
        needsPostEditRevalidation &&
        typeof pr.proof_tex === "string" &&
        pr.proof_tex.trim().length > 0
      ) {
        // A structured edit makes this same-round proof provisional, but dropping
        // it from core.json without a separate artifact makes proposal reviewers
        // inspect the stale carried proof. Bank the exact emitted payload for
        // review and as partial context for the post-apply revalidation round.
        // `argues_proposed` travels with it so apply can promote in the same
        // adjudication when the declared basis materializes verbatim.
        deferProof(pr.id, pr.proof_tex, pr.argues_proposed);
        // Same ownership rule as the applied branch above: the INSTALLING unit owns an
        // agent-added node, not whichever sibling unit emitted its proof.
        const installedOwner = (next.solved[stmt.id] as { owner?: string } | undefined)?.owner;
        const priorAgent = prev?.solved[stmt.id];
        recordProof(next, proto, {
          id: stmt.id,
          snapshotOf: stmt,
          proofTex: pr.proof_tex,
          ...(!sourceById.has(stmt.id)
            ? { node: { ...stmt, status: "to-prove" as const, proof_tex: undefined }, owner: installedOwner ?? priorAgent?.owner ?? ownerLabel }
            : {}),
          partial: true,
        });
      }
    }
    for (const lem of o.added_lemmas) {
      const existing = currentStatement(lem.id);
      const sameMathematicalClaim = existing !== undefined &&
        existing.kind === lem.kind &&
        existing.statement === lem.statement &&
        sameDependencySet(existing.depends_on, lem.depends_on);
      const sameClaim = existing !== undefined &&
        (sourceById.has(lem.id)
          ? sameMathematicalClaim
          : completionIdentity(existing) === completionIdentity(lem));
      const recoveredPartial = preMergeSolved[lem.id];
      const mustReviewRecoveredPartial =
        roundHasReviewBundle &&
        sameClaim &&
        recoveredPartial?.node !== undefined &&
        recoveredPartial.partial === true &&
        lem.status === "proved" &&
        (lem.proof_tex ?? "").trim().length > 0;
      const needsPostEditRevalidation =
        proofNeedsPostEditRevalidation(lem, lem.proof_tex ?? "") && lem.status === "proved";
      if ((needsPostEditRevalidation || mustReviewRecoveredPartial) && (existing === undefined || sameClaim)) {
        if ((lem.proof_tex ?? "").trim().length > 0) deferProof(lem.id, lem.proof_tex!);
        if (mustReviewRecoveredPartial) {
          reviewDeferredRecoveredPartials.set(lem.id, {
            statement: structuredClone(lem),
            owner: ownerLabel,
          });
        }
        // Proved agent-added results whose content closure touches a proposed edit
        // wait for the post-apply re-solve. Their exact proof is also part of the
        // proposal-review artifact; otherwise an emitted prerequisite can exist
        // only in core/working and disappear from adjudication.
        // The same rule applies to a live partial helper recovered through
        // `added_lemmas`: settling it immediately would bypass the atomic review
        // bundle and leave apply with no provisional proof to promote.
        lem.status = "to-prove";
      }
      if (lem.status === "proved" && (lem.proof_tex ?? "").trim().length === 0) {
        // why: a proofless proved lemma is undischarged at the solve boundary, not reusable proof debt.
        lem.status = "to-prove";
      }
      if (existing !== undefined) {
        // Preserve an exact cited receipt before the ordinary settled-node no-op
        // branch. The preimage may still be settled here even though a same-round
        // symbol/catalog edit will reopen it during apply.
        const bundledCitedReceipt =
          roundHasReviewBundle &&
          sourceById.has(lem.id) &&
          requiredCoreTargets.has(lem.id) &&
          existing.status === "cited" &&
          lem.status === "cited" &&
          reusableOeqAnswerMatches(existing, lem);
        if (bundledCitedReceipt) deferCitationRevalidation(lem);
        // Proof prose is not part of a node's identity — only the claim is. A re-emission
        // whose claim is byte-identical to an already-SETTLED node is a no-op discharge:
        // keep the canonical proof/citation, skip the emission. Before this branch, a
        // prose-only re-derivation of a proved helper fell through to the collision path
        // and cost a withheld-helper checkpoint plus a full recovery round. The
        // alternative payload is not lost — it stays in this round's solve_*.json, which
        // the round-clear sweep archives.
        const settled =
          (existing.status === "cited" &&
            !requiredCoreTargets.has(lem.id) &&
            next.solved[lem.id]?.partial !== true) ||
          settledNow(lem.id);
        if (sameClaim && settled) {
          duplicateReproofIds.push(lem.id);
          withheldProofBytes.push({ nodeId: lem.id, proofTex: lem.proof_tex ?? "", reason: "duplicate-reproof" });
          continue;
        }
        // FROZEN cited member: the only accepted re-emission is the byte-faithful
        // citation-revalidation receipt — claim AND source identical to the displayed
        // leaf. The reopen (d0_apply) leaves the same schema-valid cited leaf a
        // carried node gets, and no other channel can refresh a frozen member's
        // snapshot (a statement-replace echo is filtered as a no-op below), so without
        // this branch the receipt the solve prompt mandates was withheld as a
        // collision and the reopened leaf could never be revalidated. Source equality
        // is REQUIRED here because the discharge below keeps the proto copy canonical:
        // accepting a different source would silently drop the solver's correction — a
        // frozen source fix must travel the adjudicated statement-replace channel.
        // AGENT-authored nodes (the branch after it) stay wholesale-replaceable under
        // an exact required directive: that requiredness IS the authorization a
        // directed source refresh relies on.
        const frozenCitedReceipt =
          sourceById.has(lem.id) &&
          existing.status === "cited" &&
          requiredCoreTargets.has(lem.id) &&
          lem.status === "cited" &&
          JSON.stringify(existing.source ?? null) === JSON.stringify(lem.source ?? null);
        const sameFrozenClaim =
          sameClaim &&
          (frozenCitedReceipt ||
            (!sourceById.has(lem.id) &&
              (existing.status === "to-prove" ||
                (existing.status === "cited" &&
                  (requiredCoreTargets.has(lem.id) || next.solved[lem.id]?.partial === true)))));
        if (!sameFrozenClaim) {
          // The solver emitted a helper under an id the core already uses for a DIFFERENT
          // claim. Discarding it silently is unsafe: the proof that cites this id was
          // recorded above meaning the NEW claim, while the graph resolves the id to the
          // OLD one — the proof then rests on a statement it never argued. Withhold the
          // node (taking either would be a guess) and report it, exactly as a cross-unit
          // collision is handled.
          addedLemmaCollisions.push({ id: lem.id, owner: ownerLabel });
          withheldProofBytes.push({ nodeId: lem.id, proofTex: lem.proof_tex ?? "", reason: "collision-withheld" });
          withheldPayloads.push({
            category: "added-node", target: lem.id, unit: ownerLabel,
            reason: "existing-node-collision", payload: structuredClone(lem),
          });
          continue;
        }
        // A cited receipt emitted beside a proposal must survive until the proposal's
        // postimage exists. Consuming it only against the preimage loses the explicit
        // solver assertion when a symbol/definition edit reopens this leaf during
        // apply, stranding every reviewed consumer behind an apparently stale citation.
        if (
          !bundledCitedReceipt &&
          roundHasReviewBundle && lem.status === "cited" && existing.status === "cited"
        ) deferCitationRevalidation(lem);

        if (sourceById.has(lem.id)) {
          // FROZEN cited member revalidated: the proto copy stays canonical (the
          // re-emission may omit authored prose fields such as justification/gap), so
          // only the working record moves — a fresh non-partial snapshot of the CURRENT
          // claim replaces the old-basis partial one and clears the reopen. No `node`:
          // a frozen member must not enter the agent-node catalog.
          recordProof(next, proto, { id: lem.id, snapshotOf: existing, proofTex: "" });
          solved += 1;
          continue;
        }
        // A directed post-edit re-solve recovers an agent-authored node from the
        // previous core as an explicit to-prove target. Solvers legitimately emit
        // cited/agent-authored nodes through `added_lemmas`, even though that target
        // id is already present in the assembled frontier. Treat an exact claim
        // match as discharge of the recovered target; otherwise the old
        // `existingIds` guard leaves it permanently to-prove and the D0 cursor loops.
        installedNodes.set(lem.id, lem);
        recordProof(next, proto, {
          id: lem.id,
          snapshotOf: lem,
          proofTex: lem.proof_tex ?? "",
          node: lem.status === "to-prove" ? { ...lem, proof_tex: undefined } : lem,
          owner: ownerLabel,
          ...(lem.status === "to-prove" ? { partial: true } : {}),
        });
        if (lem.status !== "to-prove") solved += 1;
        continue;
      }
      if (!statementExists(lem.id)) {
        installedNodes.set(lem.id, lem);
        addedLemmas += 1;
        // A cited node needs no proof of ours, and a proved one carries its own; both
        // are recorded as-is. Anything else (including `proved` with an empty body) is
        // an open obligation, stored re-opened so the next round re-derives it.
        const settled = lem.status === "cited" || (lem.status === "proved" && (lem.proof_tex ?? "").trim().length > 0);
        recordProof(next, proto, {
          id: lem.id,
          snapshotOf: lem,
          proofTex: lem.proof_tex ?? "",
          node: settled ? lem : { ...lem, status: "to-prove", proof_tex: undefined },
          owner: ownerLabel,
          ...(settled ? {} : { partial: true }),
        });
      }
    }
    proposedChanges.push(...o.proposed_statement_changes.map((change) => {
      const target = statementById.get(change.id);
      return pinWhitespaceEquivalentCurrent(
        change,
        target?.statement,
        target ? [statementRevision(target), statementRevision(openSolveTarget(target))] : [],
      );
    }));
    proposedDefChanges.push(...o.proposed_definition_changes.map((change) => {
      const target = definitionById.get(change.id);
      // Class definitions are rejected by the A6 firewall below; their payload is
      // intentionally never publishable, so do not let its irrelevant echo abort
      // otherwise-valid work before that filter runs.
      return target?.by_member_properties === undefined
        ? pinWhitespaceEquivalentCurrent(
            change,
            target?.construction,
            target ? [definitionRevision(target, core)] : [],
          )
        : change;
    }));
    proposedAssumptions.push(...(o.proposed_assumptions ?? []));
    for (const edit of o.proposed_core_edits ?? []) {
      const repeatsRequiredEdit = requiredCoreEdits.some((required) =>
        coreEditOperationKey(required) === coreEditOperationKey(edit),
      );
      const repeatsPendingSupersession = edit.kind === "statement-delete" &&
        pendingSupersessionEdits.some((pending) =>
          pending.id === edit.id && pending.replacement_id === edit.replacement_id,
        );
      if (!repeatsPendingSupersession && !repeatsRequiredEdit) proposedCoreEdits.push(edit);
    }
    for (const obligation of o.open_obligations) {
      if (openObligationIds.has(obligation.node_id)) continue;
      openObligationIds.add(obligation.node_id);
      openObligations.push(obligation);
    }
  }

  // Apply the parked same-round proofs in TWO drains: now (every unit's added_lemmas
  // nodes are installed), and again after the OEQ transition below installs the
  // resolved-OEQ answer theorems — `roundEmittedIds` includes those theorem ids, so a
  // proofs[] re-emission for a replacement theorem drained here would be misfiled as
  // an unmatched-id PLUMBING FAULT on a clean round. Only after the FINAL drain is a
  // still-absent target (withheld by collision/quarantine, or never emitted) a real
  // unmatched-id fault. A target already settled with its own inline proof makes the
  // proofs[]-channel copy a duplicate re-proof (canonical kept).
  const drainParkedProofs = (final: boolean): void => {
    for (let i = pendingSameRoundProofs.length - 1; i >= 0; i--) {
      const { proof, ownerLabel } = pendingSameRoundProofs[i];
      const stmt = currentStatement(proof.id);
      if (!stmt) {
        if (final) {
          pendingSameRoundProofs.splice(i, 1);
          unmatchedProofIds.push(proof.id);
          withheldProofBytes.push({ nodeId: proof.id, proofTex: proof.proof_tex ?? "", reason: "unmatched-id" });
          withheldPayloads.push({
            category: "proof", target: proof.id, unit: ownerLabel,
            reason: "unmatched-id", payload: structuredClone(proof),
          });
        }
        continue;
      }
      pendingSameRoundProofs.splice(i, 1);
      if (typeof proof.proof_tex !== "string" || proof.proof_tex.trim().length === 0) continue;
      if (settledNow(proof.id)) {
        duplicateReproofIds.push(proof.id);
        withheldProofBytes.push({ nodeId: proof.id, proofTex: proof.proof_tex, reason: "duplicate-reproof" });
        continue;
      }
      // recordProof REPLACES the record: an agent-added target (recorded partial with
      // node+owner at install) must keep its agent-node catalog entry, with the
      // INSTALLING unit's ownership preserved over the proof-emitting unit's label.
      const installOwner = (next.solved[stmt.id] as { owner?: string } | undefined)?.owner;
      const priorAgent = !sourceById.has(stmt.id) ? prev?.solved[stmt.id] : undefined;
      if (proofNeedsPostEditRevalidation(stmt, proof.proof_tex)) {
        // Mirrors the in-loop provisional branch: bank the payload for adjudication and
        // as partial context for the post-apply revalidation round.
        deferProof(proof.id, proof.proof_tex, proof.argues_proposed);
        recordProof(next, proto, {
          id: stmt.id,
          snapshotOf: stmt,
          proofTex: proof.proof_tex,
          ...(!sourceById.has(stmt.id)
            ? { node: { ...stmt, status: "to-prove" as const, proof_tex: undefined }, owner: installOwner ?? priorAgent?.owner ?? ownerLabel }
            : {}),
          partial: true,
        });
        continue;
      }
      // (Records only: the render derives `proved` from the record.)
      // NOT `solved += 1`: parked targets are always round-added nodes, whose inline-
      // proved twin increments only `addedLemmas` (at install). Counting them as solved
      // too made the discharge message depend on which channel the solver used and
      // double-represented the node in finalizeRound's derived lemma count.
      recordProof(next, proto, {
        id: stmt.id,
        snapshotOf: stmt,
        proofTex: proof.proof_tex,
        ...(!sourceById.has(stmt.id)
          ? { node: stmt, owner: installOwner ?? priorAgent?.owner ?? ownerLabel }
          : {}),
      });
    }
  };
  drainParkedProofs(false);

  // No-op re-proposal filter: the solver sometimes re-derives a narrowing/correction that
  // is ALREADY applied (proposed text == the node's current text), which would spuriously
  // checkpoint and stall the loop (re-proposing the same applied benchmark every round).
  // Drop these — an already-applied change is not a change.
  const norm = (s: string) => normalizeTexWhitespace(s); // paragraph breaks (\par) stay significant
  {
    const stmtNow = new Map([
      ...[...statementById.values()].map((s) => [s.id, s.statement] as const),
      ...[...installedNodes.values()].map((s) => [s.id, s.statement] as const),
    ]);
    const defNow = new Map(core.definitions.map((d) => [d.id, norm(d.construction)]));
    const beforeS = proposedChanges.length, beforeD = proposedDefChanges.length;
    for (let i = proposedChanges.length - 1; i >= 0; i--) {
      if (stmtNow.get(proposedChanges[i].id) === proposedChanges[i].proposed) proposedChanges.splice(i, 1);
    }
    for (let i = proposedDefChanges.length - 1; i >= 0; i--) {
      if (defNow.get(proposedDefChanges[i].id) === norm(proposedDefChanges[i].proposed)) proposedDefChanges.splice(i, 1);
    }
    // Same rule for assumptions: a proposed_assumption whose id the core already holds
    // with an identical (normalized) condition is a restatement of an applied add, not a
    // change. Without this drop it re-checkpointed every round, and the apply-side
    // existing-id skip then turned an apply-all into an undiagnosable partial-apply
    // refusal. An existing id with a DIFFERENT condition still surfaces (that conflict
    // is the orchestrator's to adjudicate).
    const assNow = new Map(core.assumptions.map((a) => [a.id, norm(a.condition)]));
    const beforeA = proposedAssumptions.length;
    for (let i = proposedAssumptions.length - 1; i >= 0; i--) {
      if (assNow.get(proposedAssumptions[i].id) === norm(proposedAssumptions[i].condition)) proposedAssumptions.splice(i, 1);
    }
    const dropped = beforeS - proposedChanges.length + (beforeD - proposedDefChanges.length) +
      (beforeA - proposedAssumptions.length);
    if (dropped > 0) void dropped; // (no-op count; could be logged)

  }

  // Best-partial preservation: an open obligation may carry the strongest partial result
  // the solver reached for that node. Record it on the core node (status STAYS to-prove —
  // it is partial, not discharged) and save it in the working state flagged `partial`, so
  // the next round EXTENDS it (carried as context) instead of restarting. Reduces the
  // apply→re-run back-and-forth: each round banks its best partial.
  for (const ob of openObligations) {
    const partial = ob.partial_result;
    if (partial && partial.trim().length > 0) {
      // (Records only: the render attaches best-partial bytes to the published
      // node from the record — the old direct `stmt.proof_tex = partial`
      // workspace write is gone.)
      const stmt = currentStatement(ob.node_id);
      const prior = next.solved[ob.node_id] ?? prev?.solved[ob.node_id];
      const activeNode = stmt && !sourceById.has(ob.node_id)
        ? { ...stmt, status: "to-prove" as const, proof_tex: undefined }
        : prior?.node;
      recordProof(next, proto, {
        id: ob.node_id,
        // An obligation can name a node the core does not hold; an empty stand-in
        // snapshots to "no content", which correctly reads as stale next round.
        snapshotOf: stmt ?? ({ id: ob.node_id, statement: "", depends_on: [] } as unknown as CoreStatement),
        proofTex: partial,
        ...(activeNode ? { node: activeNode, owner: prior?.owner } : {}),
        partial: true,
      });
      // Publication state is data (Phase 1): an obligation on a node the round's
      // paper does not hold is carried as shelved debt, not rendered.
      const written = next.solved[ob.node_id];
      if (stmt === undefined && written?.node !== undefined) written.shelved = true;
    }
  }

  // Auto-wire dependency edges from claim/proof citations. Authored math cites nodes by
  // literal id (e.g. `lem:foo`, `def:bar`); the agent does not always
  // also list them in `depends_on`, but D0.5 discharges each node from its DECLARED
  // depends_on only, so an undeclared-but-used node is a review finding. Union every
  // real node id the claim or proof cites into the node's depends_on (growth is allowed by the
  // frozen-claim guard; this never removes or reorders existing edges).
  // Wiring grows core.json's depends_on (for the gate / reviewer / render) and the reuse
  // snapshots below, so later changes to an auto-wired def/assumption invalidate stale proofs.
  //
  // (Records only: the citation auto-wiring pass over the workspace is gone —
  // the RENDER wires the published edge set with the canonical cycle guard, and
  // `recordProof` wires each record's snapshot closure from the same text, so
  // neither can drift from the other.)
  // No-op statement-replace echo filter — the dependency comparison must see the
  // same wired edge set the solver was shown in the previous round's published
  // core.json, so echo views are WIRED on the fly below.
  {
    // Same filter for statement-replace CORE EDITS that echo the node wholesale — kind,
    // statement, dependency SET and source all byte-identical to the current node.
    // Solvers re-emit these as "confirmations" (observed shape: status echoed as
    // `to-prove` while the SAME round supplies the proof through the proofs channel);
    // each one spuriously flips the round into a proposal checkpoint
    // (emittedStructuredChanges), costing an adjudication + apply + re-solve cycle that
    // changes nothing. A rewire (any field actually moving) passes through untouched,
    // and a `to-prove` echo WITHOUT a same-round proof is a genuine reopen request.
    const depsKey = (xs: string[] | undefined): string => [...new Set(xs ?? [])].sort().join("\n");
    // `free_symbols` MUST be part of the no-op comparison, or this filter contradicts the
    // contract stated three lines above it ("a rewire — any field actually moving — passes
    // through untouched"). It is not a cosmetic omission: `free_symbols` on a proto-frozen
    // statement is writable through exactly ONE channel, `statement-replace`, and apply
    // REQUIRES that channel to echo the statement byte-for-byte. So a payload whose only
    // delta is `free_symbols` matched every condition here and was spliced as a no-op,
    // while any payload altered enough to survive this filter was then refused by apply's
    // echo check. The two rules together made the field unwritable by construction, and
    // the deletion happens upstream of apply's `skipped` ledger, so it left NO receipt —
    // the round simply reported fewer edits than the model emitted.
    // `undefined` (never declared) and `[]` (authored empty) are DISTINCT declarations
    // that scope symbol invalidation differently, so they must not collapse to one key.
    const symbolsKey = (xs: string[] | undefined): string =>
      xs === undefined ? "\u0000undeclared" : [...new Set(xs)].sort().join("\n");
    // The solver echoes the WIRED published view it was shown; the render is
    // that view (records hold every install by this point).
    const stmtById = new Map(assembleCore(proto, next).statements.map((s) => [s.id, s]));
    const provedThisRound = new Set(
      outputs.flatMap((o) => o.proofs)
        .filter((p) => typeof p.proof_tex === "string" && p.proof_tex.trim().length > 0)
        .map((p) => p.id),
    );
  for (let i = proposedCoreEdits.length - 1; i >= 0; i--) {
    const edit = proposedCoreEdits[i];
    if (requiredCoreEdits.some((required) =>
      coreEditOperationKey(required) === coreEditOperationKey(edit))) continue;
      if (edit.kind !== "statement-replace") continue;
      const current = stmtById.get(edit.id);
      if (current === undefined) continue;
      const statusIsNoOp =
        current.status === edit.proposed.status ||
        (edit.proposed.status === "to-prove" && current.status === "proved" && provedThisRound.has(edit.id));
      if (
        statusIsNoOp &&
        current.kind === edit.proposed.kind &&
        current.statement === edit.proposed.statement &&
        depsKey(current.depends_on) === depsKey(edit.proposed.depends_on) &&
        symbolsKey(current.free_symbols) === symbolsKey(edit.proposed.free_symbols) &&
        JSON.stringify(current.source ?? null) === JSON.stringify(edit.proposed.source ?? null)
      ) {
        proposedCoreEdits.splice(i, 1);
      }
    }
  }

  // Dedup proposed DEFINITION changes by id (the WCC unit, or sibling units, may
  // each surface the same mis-specified shared object — e.g. an envelope a thm and
  // a downstream prop both reference). Reject a change that targets a CLASS
  // definition (by_member_properties): correcting class membership is an
  // assumption/scope move, not a constructed-object formula fix (A6 firewall).
  const defById = new Map(core.definitions.map((d) => [d.id, d]));
  const seenDef = new Set<string>();
  const defChanges: ProposedDefinitionChange[] = [];
  const illegalDefTargets: string[] = [];
  for (const c of proposedDefChanges) {
    if (seenDef.has(c.id)) continue;
    seenDef.add(c.id);
    const d = defById.get(c.id);
    if (!d || d.by_member_properties !== undefined) {
      illegalDefTargets.push(c.id);
      continue;
    }
    defChanges.push(c);
  }
  if (illegalDefTargets.length > 0) {
    const illegal = new Set(illegalDefTargets);
    for (let i = proposedCoreEdits.length - 1; i >= 0; i--) {
      const edit = proposedCoreEdits[i];
      if (edit.kind === "definition-replace" && illegal.has(edit.id)) proposedCoreEdits.splice(i, 1);
    }
  }
  // Conflict filtering can discard one member of a definition correction pair.
  // Recheck the surviving post-image here so merge never publishes an orphaned
  // construction change or a different replacement for the same target.
  for (let i = defChanges.length - 1; i >= 0; i--) {
    const change = defChanges[i];
    const pairs = proposedCoreEdits.filter(
      (edit) => edit.kind === "definition-replace" && edit.id === change.id &&
        edit.proposed.construction === change.proposed,
    );
    if (pairs.length === 1) continue;
    defChanges.splice(i, 1);
    for (let j = proposedCoreEdits.length - 1; j >= 0; j--) {
      const edit = proposedCoreEdits[j];
      if (edit.kind === "definition-replace" && edit.id === change.id) proposedCoreEdits.splice(j, 1);
    }
  }
  for (let i = proposedCoreEdits.length - 1; i >= 0; i--) {
    const edit = proposedCoreEdits[i];
    if (edit.kind !== "definition-replace") continue;
    if (isRequiredCoreEdit(edit)) continue;
    const authored = definitionById.get(edit.id);
    if (authored === undefined || edit.proposed.construction === authored.construction) continue;
    const paired = defChanges.some(
      (change) => change.id === edit.id && change.proposed === edit.proposed.construction &&
        change.based_on_revision === edit.based_on_revision,
    );
    if (!paired) proposedCoreEdits.splice(i, 1);
  }
  for (let i = proposedChanges.length - 1; i >= 0; i--) {
    const change = proposedChanges[i];
    const pairs = proposedCoreEdits.filter(
      (edit) => edit.kind === "statement-replace" && edit.id === change.id &&
        edit.proposed.statement === change.proposed,
    );
    if (pairs.length === 1) continue;
    proposedChanges.splice(i, 1);
    for (let j = proposedCoreEdits.length - 1; j >= 0; j--) {
      const edit = proposedCoreEdits[j];
      if (edit.kind === "statement-replace" && edit.id === change.id) proposedCoreEdits.splice(j, 1);
    }
  }
  for (let i = proposedCoreEdits.length - 1; i >= 0; i--) {
    const edit = proposedCoreEdits[i];
    if (edit.kind !== "statement-replace") continue;
    const authored = statementById.get(edit.id);
    if (authored === undefined || edit.proposed.statement === authored.statement) continue;
    const paired = proposedChanges.some(
      (change) => change.id === edit.id && change.proposed === edit.proposed.statement &&
        (change.based_on_revision === undefined || edit.based_on_revision === undefined ||
          change.based_on_revision === edit.based_on_revision),
    );
    if (!paired) proposedCoreEdits.splice(i, 1);
  }

  // (Records only: the silent-alteration guard is unrepresentable. A frozen
  // member has no record `node`, so no channel can alter its claim/kind/prose —
  // an agent emission under a frozen id is either the byte-faithful receipt or
  // a withheld collision, and the render always republishes the proto text.
  // Construction test: stage0_solve.test.ts ("records-only merge" describe).)

  // Apply the one-node OEQ -> theorem transition only after the frozen-content guard has
  // verified that the solver did not silently rewrite the original question. Remap every
  // dependency so consumers follow the answer theorem, then remove the obsolete OEQ node.
  if (resolvedOeqEntries.length > 0) {
    // Snapshot each resolution's SOURCE node BEFORE the transition below removes it from
    // `core.statements` and from `next.solved`. The fingerprint is computed after that
    // removal, and `sourceById` is built from the FROZEN proto only — so an AGENT-ADDED
    // oeq (one a previous round created in working state, never frozen at D-1) is absent
    // from every surviving lookup by then. The old `source!` assertion turned that into
    // `TypeError: Cannot read properties of undefined (reading 'kind')` at fingerprint
    // time, after a full ~40-minute solve had already been paid for. The validation at
    // "resolution source is not an open-ended question" guarantees the node IS present
    // here, so this map always resolves.
    const resolvedSourceById = new Map(
      [...resolvedOeqSources]
        .map((id) => currentStatement(id))
        .filter((s): s is CoreStatement => s !== undefined)
        .map((s) => [s.id, s] as const),
    );
    const replacement = resolvedOeqReplacement;
    // (Records only: the render filters answered sources and remaps depends_on /
    // assumption.used_by from `resolved_oeqs` — no workspace rewrite.)
    for (const sourceId of resolvedOeqSources) delete next.solved[sourceId];
    // Propagate the replacement into EVERY working record's edges, exactly as the id
    // auto-heal below does for renames. The records used to be remapped only as a side
    // effect of `refreshSnapshots`, which now (correctly) skips partials to preserve the
    // basis they argued — so a partial's catalog node kept the dead `oeq:` edge, the next
    // round re-opened it through `openSolveTarget` carrying that edge, and merge's
    // dangling-edge check threw AFTER a full paid dispatch, every round, with the source
    // record already deleted so self-containment could not repair it. An id remap is NOT
    // a basis retarget: it must reach partials too.
    // Shared Q→T rule (oeq_edges.ts): the answer's own citation of its question
    // inherits the question's upstream edges; a self-edge would fail G4 at the
    // post-solve gate and discard the whole paid round.
    const questionDepsOf = (id: string): readonly string[] | undefined =>
      core.statements.find((s) => s.id === id)?.depends_on;
    for (const [recId, rec] of Object.entries(next.solved)) {
      if (rec.node && Array.isArray(rec.node.depends_on)) {
        rec.node.depends_on = remapResolvedDependencies(recId, rec.node.depends_on, replacement, questionDepsOf);
      }
      if (Array.isArray(rec.snapshot?.depends_on)) {
        // Sorted-unique: a proof citing BOTH the question and its answer would
        // otherwise remap to a duplicate entry, and the canonical recomputation
        // in the snapshot-basis check would flag a clean resolution (audit R2BB3).
        rec.snapshot.depends_on = remapResolvedDependencies(recId, rec.snapshot.depends_on, replacement, questionDepsOf).sort();
      }
    }
    for (const r of resolvedOeqEntries) {
      const theorem = {
        ...r.theorem,
        depends_on: remapResolvedDependencies(r.theorem.id, r.theorem.depends_on, replacement, questionDepsOf),
      };
      // Two resolutions may name the SAME answer theorem id. Pushing both puts duplicate
      // statement ids in the core, where every consumer keys by id and silently resolves
      // to one record while `recordProof` overwrites the single working entry. Withhold
      // the second and report it rather than persisting an incoherent core.
      if (statementExists(theorem.id)) {
        if (!reusableResolutionSources.has(r.source_id)) {
          oeqAnswerCollisions.push(`${r.source_id}->${theorem.id}`);
          withheldProofBytes.push({ nodeId: theorem.id, proofTex: theorem.proof_tex ?? "", reason: "collision-withheld" });
          withheldPayloads.push({
            category: "oeq-resolution", target: theorem.id, unit: r.source_id,
            reason: "oeq-answer-id-collision", payload: structuredClone(r),
          });
          withheldPayloads.push({
            category: "oeq-resolution", target: r.source_id, unit: r.source_id,
            reason: "oeq-answer-id-collision", payload: structuredClone(r),
          });
          continue;
        }
        // The id is present as the OPEN PROJECTION, not as a settled answer. Skipping here
        // (the exact-re-emission no-op) would keep the `to-prove` placeholder in the core,
        // leave the working record `partial`, and drop the emitted proof bytes into neither
        // the archive nor `withheldProofBytes` — the round then reports the node still open
        // even though the solver proved it, and re-running reproduces the same state.
        if (projectionResolutionSources.has(r.source_id)) {
          const canonical = projectionDurableAnswers.get(r.source_id) ?? theorem;
          installedNodes.set(theorem.id, canonical);
          solved += 1;
          recordProof(next, proto, {
            id: canonical.id,
            snapshotOf: canonical,
            proofTex: canonical.proof_tex ?? "",
            node: canonical,
            owner: r.source_id,
          });
        }
      } else {
        installedNodes.set(theorem.id, theorem);
        solved += 1;
        addedLemmas += 1;
        recordProof(next, proto, {
          id: theorem.id,
          snapshotOf: theorem,
          proofTex: theorem.proof_tex ?? "",
          node: theorem,
          owner: r.source_id,
        });
      }
      const source = resolvedSourceById.get(r.source_id) ?? sourceById.get(r.source_id);
      if (!source) {
        // Fail with the id rather than a bare TypeError from inside the fingerprint.
        throw new Error(
          `Stage 0-SOLVE resolved ${r.source_id}, but its source node is absent from the assembled ` +
            `core — cannot fingerprint the resolution`,
        );
      }
      next.resolved_oeqs![r.source_id] = {
        theorem_id: theorem.id,
        source_fingerprint: oeqSourceFingerprint(source),
      };
    }
    const effectiveSymbolBasis = symbolBasis(
      proto,
      Object.values(next.solved).flatMap((record) => record.node ? [record.node] : []),
      next.resolved_oeqs,
    );
    if (JSON.stringify(effectiveSymbolBasis) !== JSON.stringify(next.symbol_basis ?? {})) {
      // The source→answer transition can change a symbol's semantic referent
      // without changing its raw proto row. Reopen the declared free-symbol
      // closure before adopting the new basis; otherwise those proofs become
      // falsely current under the answer endpoint.
      const validUnderEffectiveBasis = computeValidNodes(next, proto);
      for (const [id, record] of Object.entries(next.solved)) {
        if (!validUnderEffectiveBasis.has(id)) record.partial = true;
      }
      next.symbol_basis = effectiveSymbolBasis;
    }
  }
  // (Records only: the "answered source must not remain a live node" sweep is
  // structural now — `assembleCore` filters every `resolved_oeqs` source at
  // render, whichever channel answered it.)
  // FINAL drain: the resolved-OEQ answer theorems are installed now, so any parked
  // proof still unresolved has a genuinely absent target and reports as unmatched.
  drainParkedProofs(true);

  // Apply prose only after OEQ replacement so statement notes may target the
  // resolved theorem id. Durability: the updates merge into the working state's
  // `prose_overlay` (rendered by `assembleCore` on every later assembly); the
  // in-memory workspace gets them too so this round's gates/packet see the same
  // paper the commit will publish. The proto is no longer written.
  if (proseUpdates.length > 0) {
    const seen = new Map<string, string>();
    for (const updates of proseUpdates) {
      const claims: Array<[string, string]> = [];
      for (const field of [
        "tldr", "related_work", "interpretation", "technical_internal_limitation", "honest_scope",
      ] as const) {
        if (updates[field] !== undefined) claims.push([field, updates[field] as string]);
      }
      for (const [field, value] of Object.entries(updates.project_justification ?? {})) {
        if (value !== undefined) claims.push([`project_justification.${field}`, value]);
      }
      for (const [field, value] of Object.entries(updates.sampling_model ?? {})) {
        if (value !== undefined) claims.push([`sampling_model.${field}`, value]);
      }
      for (const note of updates.statement_notes) {
        for (const field of ["justification", "gap", "consumer"] as const) {
          if (note[field] !== undefined) claims.push([`statement_notes.${note.id}.${field}`, note[field] as string]);
        }
      }
      for (const [field, value] of claims) {
        const prior = seen.get(field);
        if (prior !== undefined && prior !== value) {
          throw new Error(`Stage 0-SOLVE conflicting prose_updates for ${field}`);
        }
        seen.set(field, value);
      }
      // A paper-wide prose owner can see durable prior-round statements that are
      // intentionally absent this round (most notably an OEQ answer invalidated
      // for re-solve). Notes are metadata only: warn-and-keep is safer than
      // aborting structured changes; the render simply has no node to decorate.
      for (const note of updates.statement_notes) {
        const known = sourceById.has(note.id) || next.solved[note.id] !== undefined ||
          resolvedOeqEntries.some((r) => r.theorem.id === note.id);
        if (!known) {
          console.warn(`[D0-SOLVE] prose sync: statement note targets out-of-round node '${note.id}'.`);
        }
      }
      next.prose_overlay = mergeProseOverlay(next.prose_overlay, updates);
    }
    // The merged project_justification must still parse — the schema check the
    // old workspace application performed, now at the one durable carrier.
    if (next.prose_overlay?.project_justification !== undefined) {
      ProjectJustificationSchema.parse({
        ...(proto.project_justification ?? {}),
        ...next.prose_overlay.project_justification,
      });
    }
  }

  // (Records only: the writer-side LaTeX canonicalization lives in the render —
  // `assembleCore` repairs the published bytes deterministically. The records
  // keep the solver's raw bytes for archive fidelity; assert the one invariant
  // that must hold at the boundary over THEM.)
  for (const [recId, rec] of Object.entries(next.solved)) {
    if (rec.proof_tex) assertCanonicalAlignedRowTerminators(rec.proof_tex, `${recId}.proof_tex`);
  }
  for (const proof of deferredProofs) {
    assertCanonicalAlignedRowTerminators(proof.proof_tex, `${proof.id}.proof_tex (deferred)`);
  }

  // Auto-heal statement ids that violate the lowercase-kebab schema
  // `(thm|lem|prop|conj):[a-z0-9-]+` — the solver tends to name an added lemma
  // after a capital-letter symbol (e.g. `lem:Ghat-envelope-valid` for an
  // estimator Ĝ_n). Lowercase + map any invalid char to '-', then propagate the
  // rename through every statement's `depends_on` so the dependency graph stays
  // resolvable. Done BEFORE the write so the persisted core.json (re-parsed by
  // CoreSchema downstream — gate, render) is already valid; a trivial id-format
  // slip must not abort an otherwise-clean discharge. (Frozen thm/prop/conj ids
  // are already lowercase, so this only ever touches agent-introduced lemmas.)
  const idRename = new Map<string, string>();
  const reservedIds = new Set([...statementById.keys(), ...installedNodes.keys(), ...Object.keys(next.solved)]);
  for (const id of [...installedNodes.keys(), ...Object.keys(next.solved)]) {
    const healed = healStatementId(id);
    if (healed === null || healed === id || idRename.has(id)) continue;
    // AUDIT-B: collision would merge two statements under one id; stop instead of silently retargeting deps.
    if (reservedIds.has(healed)) throw new Error(`Stage 0-SOLVE auto-heal collision: '${id}' would rename onto existing statement id '${healed}'`);
    reservedIds.delete(id);
    reservedIds.add(healed);
    idRename.set(id, healed);
  }
  if (idRename.size > 0) {
    // The rename reaches every id-keyed RECORD store (the render republishes
    // from them, so the published graph follows automatically).
    const renameKeys = <T>(rec: Record<string, T>): Record<string, T> =>
      Object.fromEntries(Object.entries(rec).map(([k, v]) => [idRename.get(k) ?? k, v]));
    for (const [oldId, newId] of idRename) {
      const node = installedNodes.get(oldId);
      if (node) { installedNodes.delete(oldId); node.id = newId; installedNodes.set(newId, node); }
    }
    for (const node of installedNodes.values()) {
      if (Array.isArray(node.depends_on)) node.depends_on = node.depends_on.map((d) => idRename.get(d) ?? d);
    }

    next.solved = renameKeys(next.solved);
    for (const rec of Object.values(next.solved)) {
      if (rec.node) {
        rec.node.id = idRename.get(rec.node.id) ?? rec.node.id;
        if (Array.isArray(rec.node.depends_on)) {
          rec.node.depends_on = rec.node.depends_on.map((d) => idRename.get(d) ?? d);
        }
      }
      if (Array.isArray(rec.snapshot?.depends_on)) {
        rec.snapshot.depends_on = rec.snapshot.depends_on.map((d) => idRename.get(d) ?? d);
      }
    }
    if (next.resolved_oeqs) {
      next.resolved_oeqs = renameKeys(next.resolved_oeqs);
      for (const [src, r] of Object.entries(next.resolved_oeqs)) {
        if (typeof r !== "string") {
          next.resolved_oeqs[src] = { ...r, theorem_id: idRename.get(r.theorem_id) ?? r.theorem_id };
        }
      }
    }
    for (const proof of deferredProofs) proof.id = idRename.get(proof.id) ?? proof.id;

    console.warn(
      `[D0-SOLVE] auto-healed ${idRename.size} non-kebab statement id(s) across the working ` +
        `cursor, resolutions and deferred proofs: ` +
        `${[...idRename].map(([a, b]) => `${a}->${b}`).join(", ")}`,
    );
  }

  // SELF-CONTAINMENT REPAIR, over the RENDER (the published graph). A lemma
  // reused from a prior round (referenced by a freshly-added consumer this
  // round but not re-emitted, and dropped by the validIds carry) would leave a
  // dangling published `depends_on` → a spurious G4. Recover records to a
  // FIXPOINT — a recovered node may itself reference further recoverable nodes,
  // and each recovery changes the render (audit BB2) — then judge dangling
  // edges against the FINAL render.
  const selfContainmentRecoveredIds = new Set<string>();
  let finalRendered = assembleCore(proto, next);
  {
    // A sealed statement deletion is part of this round's reviewed postimage even
    // when the worker correctly emits no copy of the mandated edit.  Do not inspect
    // that soon-to-be-deleted node's dependency closure before the structural-edit
    // receipt/apply pass below: doing so makes an obsolete carried answer with a
    // dependency on a simultaneously rejected declaration impossible to remove.
    //
    // We skip only the deletion TARGETS here.  Other nodes that still point at a
    // target remain visible, so statementDeleteApplicable/d0_apply continue to fail
    // closed on unsafe inbound references or missing replacement endpoints.
    const preValidationDeleteIds = new Set(
      [...pendingSupersessionEdits, ...requiredCoreEdits]
        .filter((edit) => edit.kind === "statement-delete")
        .map((edit) => edit.id),
    );
    const prospectiveKnown = new Set<string>([
      ...proposedAssumptions.map((a) => a.id),
      ...proposedCoreEdits
        .filter((edit) => edit.kind === "definition-add")
        .map((edit) => edit.id),
    ]);
    const knownOf = (rendered: Core): Set<string> =>
      new Set<string>([
        ...rendered.assumptions.map((a) => a.id),
        ...rendered.definitions.map((d) => d.id),
        ...rendered.statements.map((st) => st.id),
      ]);
    for (let pass = 0; pass < 50; pass++) {
      const known = knownOf(finalRendered);
      let repaired = false;
      for (const st of finalRendered.statements) {
        if (preValidationDeleteIds.has(st.id)) continue;
        for (const dep of st.depends_on ?? []) {
          if (!known.has(dep) && !droppedCarryIds.has(dep) &&
              prev?.solved[dep]?.node && next.solved[dep] === undefined) {
            const rec = prev.solved[dep];
            // Recover it HONESTLY: an unfinished record (partial / empty
            // non-cited proof — see isUnfinishedCarriedRecord) re-enters as an
            // open partial, never as an established result; the render derives
            // the status.
            next.solved[dep] = !validIds.has(dep) || isUnfinishedCarriedRecord(rec)
              ? { ...rec, partial: true }
              : rec;
            selfContainmentRecoveredIds.add(dep);
            repaired = true;
            console.warn(
              `[D0-SOLVE] self-containment repair: carried reused node '${dep}' (referenced but not re-emitted this round).`,
            );
          }
        }
      }
      if (!repaired) break;
      finalRendered = assembleCore(proto, next);
    }
    // A still-dangling edge is ambiguous: it may be a spurious label, or it may be
    // a load-bearing assumption/helper the worker forgot to emit. Erasing it here
    // silently changes the declared proof interface and defers discovery to the
    // expensive D0.5 panel. Fail at the cheap merge boundary with exact receipts.
    const known = knownOf(finalRendered);
    const dangling: string[] = [];
    for (const st of finalRendered.statements) {
      if (preValidationDeleteIds.has(st.id)) continue;
      if (!Array.isArray(st.depends_on)) continue;
      for (const dep of st.depends_on) {
        if (!known.has(dep) && !prospectiveKnown.has(dep)) dangling.push(`${st.id}->${dep}`);
      }
    }
    if (dangling.length > 0) {
      throw new Error(
        `Stage 0-SOLVE unresolved dependency target(s): ${dangling.join(", ")}. ` +
          "The solver must emit the missing node or remove the edge explicitly in a reviewed core edit; " +
          "refusing to erase a possibly load-bearing dependency.",
      );
    }
  }

  // Re-check exact directives against the FINAL accepted carrier, after collision,
  // no-op, illegal-target, and mandate filtering. The earlier check is a cheap
  // emitted-shape diagnostic; it must not let a payload that is later discarded
  // consume a durable exact-target directive.
  const normalizedText = (value: string): string => normalizeTexWhitespace(value); // paragraph breaks stay significant
  let applicableAnyStatementChanges = proposedChanges.filter((change) => {
    const target = statementById.get(change.id);
    return target !== undefined &&
      change.current === target.statement &&
      change.proposed !== target.statement;
  });
  // OEQ claim narrowings are supported apply-time detach transitions, but only
  // the obligation/resolution channel may consume an exact OEQ directive.
  let applicableStatementChanges = applicableAnyStatementChanges.filter(
    (change) => statementById.get(change.id)?.kind !== "openendedquestion",
  );
  let applicableDefinitionChanges = defChanges.filter((change) => {
    const target = definitionById.get(change.id);
    return target !== undefined &&
      target.by_member_properties === undefined &&
      change.current === target.construction &&
      normalizedText(change.proposed) !== normalizedText(target.construction);
  });
  const existingAssumptionIds = new Set(core.assumptions.map((assumption) => assumption.id));
  const applicableAssumptions = proposedAssumptions.filter((assumption) =>
    assumption.id.startsWith("ass:") && !existingAssumptionIds.has(assumption.id)
  );
  const applicableStatementChangeById = new Map(
    applicableAnyStatementChanges.map((change) => [change.id, change] as const),
  );
  const statementPostClaim = (current: CoreStatement, change: ProposedStatementChange): CoreStatement => ({
    ...current,
    statement: change.proposed,
    ...(current.status === "proved"
      ? { status: "to-prove" as const, proof_tex: undefined }
      : current.status === "cited"
        ? { proof_tex: undefined }
        : {}),
  });
  const statementReplacementEchoesApplyView = (
    edit: Extract<RawCoreEdit, { kind: "statement-replace" }>,
    current: CoreStatement,
  ): boolean => {
    const paired = applicableStatementChangeById.get(edit.id);
    // Phase 2: a revision-bearing edit pins its view by hash — mirror the
    // apply's rule here so the merge's no-op/echo filter and the apply agree.
    if (edit.based_on_revision !== undefined) {
      const views = paired ? [current, statementPostClaim(current, paired)] : [current];
      return describeRevisionMismatch(edit.based_on_revision, edit.proposed, views, edit.id) === null;
    }
    if (!paired) return describeEchoMismatch(edit.proposed, current, edit.id) === null;
    const after = statementPostClaim(current, paired);
    const echoesBefore =
      edit.proposed.id === current.id &&
      edit.proposed.kind === current.kind &&
      edit.proposed.statement === current.statement &&
      edit.proposed.status === current.status;
    const echoesAfter =
      edit.proposed.id === after.id &&
      edit.proposed.kind === after.kind &&
      edit.proposed.statement === after.statement &&
      edit.proposed.status === after.status;
    return echoesBefore || echoesAfter;
  };
  const effectiveDefinitionReplacement = (
    edit: Extract<RawCoreEdit, { kind: "definition-replace" }>,
    current: Core["definitions"][number],
  ): Core["definitions"][number] => {
    const original = definitionById.get(edit.id) ?? current;
    const completed = { ...current, ...edit.proposed };
    completed.free_symbols = edit.proposed.free_symbols;
    if (original.construction !== completed.construction ||
        !declarationNarrowed(original, completed)) return completed;
    const proposedNames = new Set((completed.free_symbols ?? []).map(normalizeSymbol));
    const retained = (original.free_symbols ?? []).filter((name) => !proposedNames.has(normalizeSymbol(name)));
    return retained.length === 0
      ? completed
      : { ...completed, free_symbols: [...(completed.free_symbols ?? []), ...retained] };
  };
  const coreEditsInApplyOrder = [...new Map([
    ...pendingSupersessionEdits,
    ...requiredCoreEdits,
    ...proposedCoreEdits,
  ].map((edit) => [coreEditOperationKey(edit), edit] as const)).values()].sort((a, b) => {
    const rank = (edit: RawCoreEdit): number =>
      edit.kind === "statement-replace" ? 0 :
      edit.kind === "statement-delete" ? 1 :
      edit.kind === "definition-delete" ? 3 :
      edit.kind === "assumption-delete" ? 4 :
      edit.kind === "rebuild-reverse-dependencies" ? 5 : 2;
    return rank(a) - rank(b);
  });
  const atomicSymbolPostimage = (symbols: Core["symbols"]): Core["symbols"] => {
    const projected = structuredClone(symbols);
    for (const edit of coreEditsInApplyOrder) {
      if (edit.kind === "symbol-add") {
        if (!projected.some((symbol) => symbol.name === edit.name) &&
            edit.proposed.name === edit.name) projected.push(structuredClone(edit.proposed));
      } else if (edit.kind === "symbol-replace") {
        const index = projected.findIndex((symbol) => symbol.name === edit.name);
        if (index >= 0 && edit.proposed.name === edit.name) {
          projected[index] = structuredClone(edit.proposed);
        }
      } else if (edit.kind === "symbol-delete") {
        const index = projected.findIndex((symbol) => symbol.name === edit.name);
        if (index >= 0) projected.splice(index, 1);
      }
    }
    return projected;
  };
  const receiptCore = structuredClone(proto);
  // Apply runs only after this round commits `next`; replay against that exact
  // durable cursor, not the pre-round `prev`, so same-round nodes/edges participate
  // in delete/replacement applicability exactly as they will transactionally.
  const receiptWorking = structuredClone(next);
  const transactionStatementCatalog = authoritativeStatementCatalog(
    receiptCore.statements,
    receiptWorking,
  );
  const atomicStatementDeleteIds = new Set(
    coreEditsInApplyOrder
      .filter((edit) => edit.kind === "statement-delete")
      .map((edit) => edit.id),
  );
  const atomicDefinitionDeleteIds = new Set(
    coreEditsInApplyOrder
      .filter((edit) => edit.kind === "definition-delete")
      .map((edit) => edit.id),
  );
  // A mutation of a recovered agent-authored OEQ must first detach the old
  // source→answer resolution and install the question as a real partial working
  // node. Otherwise claim/dependency edits mutate only a detached catalog object
  // and APPLY cannot reproduce the receipt postimage.
  const recoveredMutationIds = new Set([
    ...applicableAnyStatementChanges.map((change) => change.id),
    ...coreEditsInApplyOrder
      .filter((edit) => edit.kind === "statement-replace")
      .map((edit) => edit.id),
  ]);
  for (const id of recoveredMutationIds) {
    if (receiptCore.statements.some((statement) => statement.id === id) || receiptWorking.solved[id]?.node) continue;
    const recovered = transactionStatementCatalog.get(id);
    const resolution = receiptWorking.resolved_oeqs?.[id];
    if (recovered?.kind !== "openendedquestion" || resolution === undefined || typeof resolution === "string") continue;
    recordProof(receiptWorking, receiptCore, {
      id,
      snapshotOf: recovered,
      proofTex: "",
      node: structuredClone(recovered),
      owner: id,
      partial: true,
    });
    delete receiptWorking.resolved_oeqs![id];
    if (Object.keys(receiptWorking.resolved_oeqs!).length === 0) delete receiptWorking.resolved_oeqs;
    if (receiptWorking.sealed_open_oeqs !== undefined) {
      delete receiptWorking.sealed_open_oeqs[id];
      if (Object.keys(receiptWorking.sealed_open_oeqs).length === 0) delete receiptWorking.sealed_open_oeqs;
    }
  }
  // Claim/definition proposal channels apply before structural core edits.
  for (const change of applicableAnyStatementChanges) {
    const frozen = receiptCore.statements.find((statement) => statement.id === change.id);
    if (frozen) frozen.statement = change.proposed;
    const carried = receiptWorking?.solved[change.id]?.node;
    if (carried) carried.statement = change.proposed;
  }
  for (const change of applicableDefinitionChanges) {
    const definition = receiptCore.definitions.find((candidate) => candidate.id === change.id);
    if (definition) definition.construction = change.proposed;
  }
  const receiptBefore = new Map<RawCoreEdit, {
    core: Core;
    working: typeof receiptWorking;
  }>();
  const receiptStatement = (
    preview: Core,
    working: typeof receiptWorking,
    id: string,
  ): CoreStatement | undefined =>
    authoritativeStatementCatalog(preview.statements, working).get(id);
  const statementDeleteApplicable = (
    edit: Extract<RawCoreEdit, { kind: "statement-delete" }>,
    preview: Core,
    working: typeof receiptWorking,
  ): boolean => {
    // Deletion existence is judged against the stable reviewed transaction
    // preimage, so answer-first deletion cannot erase the only recovery carrier
    // before a later source deletion is evaluated. Replacement endpoints, by
    // contrast, must still exist in the current sequential preview.
    if (!transactionStatementCatalog.has(edit.id) || edit.replacement_id === edit.id) return false;
    if (edit.replacement_id !== undefined &&
        (!receiptStatement(preview, working, edit.replacement_id) ||
          atomicStatementDeleteIds.has(edit.replacement_id))) return false;
    // Judge a reviewed deletion bundle against its atomic postimage.  A helper's
    // only consumer may itself be deleted later in apply order; treating that
    // consumer as live here drops the helper edit before the bundle can land.
    const validationCore = {
      ...preview,
      // Structural edits are one reviewed transaction.  A selected symbol
      // delete/replacement can retire the only inbound ref or authored symbol
      // prose even though statement deletions execute first operationally.
      symbols: atomicSymbolPostimage(preview.symbols),
      statements: preview.statements.filter(
        (statement) => statement.id === edit.id || !atomicStatementDeleteIds.has(statement.id),
      ),
    };
    const validationWorking = working === null ? null : structuredClone(working);
    if (validationWorking) {
      for (const id of atomicStatementDeleteIds) if (id !== edit.id) delete validationWorking.solved[id];
      // A resolved OEQ is one atomic source→answer transaction.  When both ends
      // are selected for deletion, the apply step removes the resolution mapping;
      // leaving that stale mapping in this preview makes the answer deletion look
      // text-referenced and then makes every downstream definition deletion look
      // live.  Judge the reviewed bundle against the same atomic post-image.
      removeAtomicallyDeletedOeqResolutionEdges(
        validationWorking.resolved_oeqs,
        atomicStatementDeleteIds,
      );
    }
    if (findUnsafeDeleteTextReferences(validationCore, validationWorking, edit.id).length > 0) return false;
    if (edit.replacement_id !== undefined) return true;
    const structuredInbound = validationCore.statements.some(
      (statement) => statement.id !== edit.id && statement.depends_on.includes(edit.id),
    );
    const carriedInbound = Object.entries(validationWorking?.solved ?? {}).some(
      ([id, record]) => id !== edit.id && record.node?.depends_on.includes(edit.id),
    );
    const symbolInbound = validationCore.symbols.some((symbol) => symbol.ref === edit.id);
    return !structuredInbound && !carriedInbound && !symbolInbound;
  };
  // Build the same ordered post-image views that d0_apply exposes to each later
  // core edit. This is especially load-bearing for a statement deletion, whose
  // internal reverse-edge rebuild may make a later exact assumption restoration
  // substantive even when that restoration equalled the round's original preimage.
  for (const edit of coreEditsInApplyOrder) {
    receiptBefore.set(edit, {
      core: structuredClone(receiptCore),
      working: structuredClone(receiptWorking),
    });
    if (edit.kind === "statement-delete" &&
        statementDeleteApplicable(edit, receiptCore, receiptWorking)) {
      const replacement = edit.replacement_id;
      const durableReplacement = resolvedStatementReplacementEndpoint(
        replacement,
        receiptWorking,
        atomicStatementDeleteIds,
      );
      receiptCore.statements = receiptCore.statements
        .filter((statement) => statement.id !== edit.id)
        .map((statement) => ({
          ...statement,
          depends_on: retargetDeletedDependency(statement.id, statement.depends_on, edit.id, durableReplacement),
        }));
      for (const symbol of receiptCore.symbols) {
        if (symbol.ref !== edit.id) continue;
        if (durableReplacement === undefined) delete symbol.ref;
        else symbol.ref = durableReplacement;
      }
      if (receiptWorking) {
        delete receiptWorking.solved[edit.id];
        if (receiptWorking.prose_overlay?.statement_notes !== undefined) {
          delete receiptWorking.prose_overlay.statement_notes[edit.id];
          if (Object.keys(receiptWorking.prose_overlay.statement_notes).length === 0) {
            delete receiptWorking.prose_overlay.statement_notes;
          }
        }
        if (receiptWorking.sealed_open_oeqs !== undefined) {
          delete receiptWorking.sealed_open_oeqs[edit.id];
          if (Object.keys(receiptWorking.sealed_open_oeqs).length === 0) {
            delete receiptWorking.sealed_open_oeqs;
          }
        }
        for (const record of Object.values(receiptWorking.solved)) {
          if (!record.node) continue;
          record.node.depends_on = retargetDeletedDependency(record.node.id, record.node.depends_on, edit.id, durableReplacement);
        }
        // Match APPLY's answer-retirement transition before judging later edits:
        // deleting a resolved answer reopens an agent-authored source from its
        // fingerprint unless the same atomic bundle also deletes that source.
        for (const [sourceId, resolution] of Object.entries(receiptWorking.resolved_oeqs ?? {})) {
          const theoremId = typeof resolution === "string" ? resolution : resolution.theorem_id;
          if (sourceId === edit.id || theoremId !== edit.id || atomicStatementDeleteIds.has(sourceId)) continue;
          if (!receiptCore.statements.some((statement) => statement.id === sourceId) &&
              receiptWorking.solved[sourceId] === undefined && typeof resolution !== "string") {
            const restored = agentOeqSourceFromFingerprint(sourceId, resolution.source_fingerprint);
            if (restored !== null) {
              recordProof(receiptWorking, receiptCore, {
                id: sourceId,
                snapshotOf: restored,
                proofTex: "",
                node: restored,
                owner: sourceId,
                partial: true,
              });
            }
          }
          const reopened = receiptCore.statements.find((statement) => statement.id === sourceId) ??
            receiptWorking.solved[sourceId]?.node;
          if (reopened?.kind === "openendedquestion") {
            receiptWorking.sealed_open_oeqs ??= {};
            receiptWorking.sealed_open_oeqs[sourceId] = oeqSourceFingerprint(reopened);
          }
        }
        removeAtomicallyDeletedOeqResolutionEdges(receiptWorking.resolved_oeqs, new Set([edit.id]));
        if (receiptWorking.resolved_oeqs !== undefined &&
            Object.keys(receiptWorking.resolved_oeqs).length === 0) {
          delete receiptWorking.resolved_oeqs;
        }
      }
      rebuildAssumptionUsedBy(
        receiptCore,
        Object.values(receiptWorking?.solved ?? {}).flatMap((record) => record.node ? [record.node] : []),
      );
    } else if (edit.kind === "statement-replace" &&
        statementById.get(edit.id) !== undefined &&
        statementReplacementEchoesApplyView(edit, statementById.get(edit.id)!)) {
      const frozen = receiptCore.statements.find((statement) => statement.id === edit.id);
      const carried = receiptWorking?.solved[edit.id]?.node;
      const target = frozen ?? carried;
      if (target && edit.proposed.id === edit.id) {
        const { partial_result: _partial, ...proposed } = edit.proposed;
        const composed = {
          ...target,
          ...proposed,
          statement: target.statement,
          status: target.status,
          free_symbols: proposed.free_symbols,
          proof_tex: target.proof_tex,
        };
        if (frozen) Object.assign(frozen, composed);
        if (carried) Object.assign(carried, composed);
      }
    } else if (edit.kind === "assumption-replace") {
      const index = receiptCore.assumptions.findIndex((assumption) => assumption.id === edit.id);
      if (index >= 0 && edit.proposed.id === edit.id) receiptCore.assumptions[index] = structuredClone(edit.proposed);
    } else if (edit.kind === "assumption-delete") {
      const safe =
        receiptCore.assumptions.some((assumption) => assumption.id === edit.id) &&
        findUnsafeDeleteTextReferences(receiptCore, receiptWorking, edit.id).length === 0 &&
        !receiptCore.statements.some((statement) => statement.depends_on.includes(edit.id)) &&
        !Object.values(receiptWorking?.solved ?? {})
          .some((record) => record.node?.depends_on.includes(edit.id));
      if (safe) {
        receiptCore.assumptions = receiptCore.assumptions.filter((assumption) => assumption.id !== edit.id);
      }
    } else if (edit.kind === "definition-add") {
      if (!receiptCore.definitions.some((definition) => definition.id === edit.id) &&
          edit.proposed.id === edit.id) receiptCore.definitions.push(structuredClone(edit.proposed));
    } else if (edit.kind === "definition-replace") {
      const index = receiptCore.definitions.findIndex((definition) => definition.id === edit.id);
      if (index >= 0 && edit.proposed.id === edit.id) {
        receiptCore.definitions[index] = effectiveDefinitionReplacement(edit, receiptCore.definitions[index]);
      }
    } else if (edit.kind === "definition-delete") {
      // Judge a reviewed deletion bundle against its atomic postimage. A deleted
      // definition may be referenced only by another definition deleted later in
      // emitter order; that transient edge must not make the first deletion a no-op.
      const validationCore = {
        ...receiptCore,
        definitions: receiptCore.definitions.filter(
          (definition) => definition.id === edit.id || !atomicDefinitionDeleteIds.has(definition.id),
        ),
      };
      const safe =
        receiptCore.definitions.some((definition) => definition.id === edit.id) &&
        findUnsafeDeleteTextReferences(validationCore, receiptWorking, edit.id).length === 0 &&
        !validationCore.statements.some((statement) => statement.depends_on.includes(edit.id)) &&
        !Object.values(receiptWorking?.solved ?? {})
          .some((record) => record.node?.depends_on.includes(edit.id)) &&
        !validationCore.symbols.some((symbol) => symbol.ref === edit.id);
      if (safe) {
        receiptCore.definitions = receiptCore.definitions.filter((definition) => definition.id !== edit.id);
      }
    } else if (edit.kind === "bibliography-replace" && edit.proposed.key === edit.key) {
      const index = receiptCore.bibliography.findIndex((entry) => entry.key === edit.key);
      if (index < 0) receiptCore.bibliography.push(structuredClone(edit.proposed));
      else receiptCore.bibliography[index] = structuredClone(edit.proposed);
    } else if (edit.kind === "target-estimand-replace" &&
        edit.current === receiptCore.target_estimand) {
      receiptCore.target_estimand = edit.proposed;
    } else if (edit.kind === "estimand-functional-replace" &&
        edit.current === (receiptCore.estimand_functional ?? "")) {
      receiptCore.estimand_functional = edit.proposed;
    } else if (edit.kind === "comparator-promise-table-replace") {
      receiptCore.comparator_promise_table = structuredClone(edit.proposed);
    } else if (edit.kind === "symbol-add" &&
        edit.proposed.name === edit.name &&
        !receiptCore.symbols.some((symbol) => symbol.name === edit.name)) {
      receiptCore.symbols.push(structuredClone(edit.proposed));
    } else if (edit.kind === "symbol-replace" && edit.proposed.name === edit.name) {
      const index = receiptCore.symbols.findIndex((symbol) => symbol.name === edit.name);
      if (index >= 0) receiptCore.symbols[index] = structuredClone(edit.proposed);
    } else if (edit.kind === "symbol-delete") {
      receiptCore.symbols = receiptCore.symbols.filter((symbol) => symbol.name !== edit.name);
    } else if (edit.kind === "rebuild-reverse-dependencies") {
      rebuildAssumptionUsedBy(
        receiptCore,
        Object.values(receiptWorking.solved).flatMap((record) => record.node ? [record.node] : []),
      );
    }
  }
  const coreEditApplicable = (edit: RawCoreEdit): boolean => {
    const preview = receiptBefore.get(edit)?.core ?? proto;
    const previewWorking = receiptBefore.get(edit)?.working ?? next;
    if (edit.kind === "assumption-replace") {
      const current = preview.assumptions.find((assumption) => assumption.id === edit.id);
      return current !== undefined &&
        edit.proposed.id === edit.id &&
        JSON.stringify(edit.proposed) !== JSON.stringify(current);
    }
    if (edit.kind === "assumption-delete") {
      const exists = preview.assumptions.some((assumption) => assumption.id === edit.id);
      if (!exists || findUnsafeDeleteTextReferences(preview, previewWorking, edit.id).length > 0) return false;
      const structured = preview.statements.some((statement) => statement.depends_on.includes(edit.id));
      const carried = Object.values(previewWorking?.solved ?? {})
        .some((record) => record.node?.depends_on.includes(edit.id));
      return !structured && !carried;
    }
    if (edit.kind === "statement-replace") {
      const current = statementById.get(edit.id);
      if (!current || !statementReplacementEchoesApplyView(edit, current)) return false;
      // A claim correction is an atomic two-channel transaction: the
      // statement-change owns the new claim bytes and statement-replace is its
      // mandatory typed postimage.  That postimage remains substantive even
      // when every non-claim field is byte-identical.  Revision/echo validation
      // above still rejects stale views, and the exact pair check below prevents
      // an unrelated or incomplete replacement from using this exception.
      const paired = applicableStatementChangeById.get(edit.id);
      if (paired !== undefined && edit.proposed.statement === paired.proposed) return true;
      const {
        proof_tex: _proof,
        statement: _currentStatement,
        status: _currentStatus,
        ...currentStructural
      } = current;
      const {
        partial_result: _partial,
        statement: _proposedStatement,
        status: _proposedStatus,
        ...proposedStructural
      } = edit.proposed;
      return JSON.stringify(proposedStructural) !== JSON.stringify(currentStructural);
    }
    if (edit.kind === "statement-delete") return statementDeleteApplicable(edit, preview, previewWorking);
    if (edit.kind === "definition-add") {
      return !preview.definitions.some((definition) => definition.id === edit.id) &&
        edit.proposed.id === edit.id;
    }
    if (edit.kind === "definition-replace") {
      const current = preview.definitions.find((definition) => definition.id === edit.id);
      const authored = definitionById.get(edit.id);
      return current !== undefined &&
        authored !== undefined &&
        (isRequiredCoreEdit(edit) || edit.based_on_revision === definitionRevision(authored, core)) &&
        edit.proposed.id === edit.id &&
        JSON.stringify(effectiveDefinitionReplacement(edit, current)) !== JSON.stringify(current);
    }
    if (edit.kind === "definition-delete") {
      const exists = preview.definitions.some((definition) => definition.id === edit.id);
      const validationCore = {
        ...preview,
        definitions: preview.definitions.filter(
          (definition) => definition.id === edit.id || !atomicDefinitionDeleteIds.has(definition.id),
        ),
      };
      return exists &&
        findUnsafeDeleteTextReferences(validationCore, previewWorking, edit.id).length === 0 &&
        !validationCore.statements.some((statement) => statement.depends_on.includes(edit.id)) &&
        !Object.values(previewWorking?.solved ?? {})
          .some((record) => record.node?.depends_on.includes(edit.id)) &&
        !validationCore.symbols.some((symbol) => symbol.ref === edit.id);
    }
    if (edit.kind === "bibliography-replace") {
      const current = preview.bibliography.find((entry) => entry.key === edit.key);
      return edit.proposed.key === edit.key &&
        (current === undefined || JSON.stringify(edit.proposed) !== JSON.stringify(current));
    }
    if (edit.kind === "target-estimand-replace") {
      return edit.current === preview.target_estimand && edit.proposed !== edit.current;
    }
    if (edit.kind === "estimand-functional-replace") {
      return edit.current === (core.estimand_functional ?? "") && edit.proposed !== edit.current;
    }
    if (edit.kind === "comparator-promise-table-replace") {
      return JSON.stringify(edit.proposed) !== JSON.stringify(core.comparator_promise_table ?? []);
    }
    const symbols = new Map(preview.symbols.map((symbol) => [symbol.name, symbol]));
    if (edit.kind === "symbol-add") {
      return !symbols.has(edit.name) && edit.proposed.name === edit.name;
    }
    if (edit.kind === "symbol-replace") {
      return symbols.has(edit.name) &&
        edit.proposed.name === edit.name &&
        JSON.stringify(edit.proposed) !== JSON.stringify(symbols.get(edit.name));
    }
    if (edit.kind === "symbol-delete") return symbols.has(edit.name);
    return false; // a reverse-dependency rebuild alone is derived metadata, not an exact repair.
  };
  let applicableCoreEdits = proposedCoreEdits.filter(coreEditApplicable);
  // Claim/construction corrections are atomic two-channel transactions.  The
  // raw pair check above proves both halves were emitted, but revision and
  // applicability normalization can still drop the structural postimage later.
  // Record that as quarantined exact-target debt rather than surfacing an orphan
  // that APPLY must reject after the journal cursor has advanced.
  const inapplicableCorrectionTargets = new Set<string>();
  for (const change of applicableAnyStatementChanges) {
    const pairSurvives = applicableCoreEdits.some((edit) =>
      edit.kind === "statement-replace" && edit.id === change.id &&
      edit.proposed.statement === change.proposed
    );
    if (!pairSurvives) inapplicableCorrectionTargets.add(change.id);
  }
  for (const change of applicableDefinitionChanges) {
    const pairSurvives = applicableCoreEdits.some((edit) =>
      edit.kind === "definition-replace" && edit.id === change.id &&
      edit.proposed.construction === change.proposed
    );
    if (!pairSurvives) inapplicableCorrectionTargets.add(change.id);
  }
  for (const id of inapplicableCorrectionTargets) {
    for (let index = 0; index < revisionBoundRawOutputs.length; index += 1) {
      const raw = revisionBoundRawOutputs[index];
      for (const payload of raw.proposed_statement_changes.filter((candidate) => candidate.id === id)) {
        withheldPayloads.push({
          category: "statement-change", target: id, unit: dispatch[index].label,
          reason: "correction-pair-inapplicable", payload: structuredClone(payload),
        });
      }
      for (const payload of raw.proposed_definition_changes.filter((candidate) => candidate.id === id)) {
        withheldPayloads.push({
          category: "definition-change", target: id, unit: dispatch[index].label,
          reason: "correction-pair-inapplicable", payload: structuredClone(payload),
        });
      }
      for (const payload of raw.proposed_core_edits.filter((candidate) => coreEditTarget(candidate) === id)) {
        withheldPayloads.push({
          category: "core-edit", target: id, unit: dispatch[index].label,
          reason: "correction-pair-inapplicable", payload: structuredClone(payload),
        });
      }
      for (const payload of raw.proofs.filter((candidate) => candidate.id === id)) {
        withheldPayloads.push({
          category: "proof", target: id, unit: dispatch[index].label,
          reason: "correction-pair-inapplicable", payload: structuredClone(payload),
        });
      }
    }
  }
  // Definitions have no installed proof carrier to roll back here; remove both
  // proposal halves immediately. Statement corrections use the full rollback
  // helper below because their provisional proof may already be in `next`.
  const inapplicableDefinitionCorrectionTargets = new Set(
    [...inapplicableCorrectionTargets].filter((id) =>
      applicableDefinitionChanges.some((change) => change.id === id)
    ),
  );
  if (inapplicableDefinitionCorrectionTargets.size > 0) {
    applicableDefinitionChanges = applicableDefinitionChanges.filter(
      (change) => !inapplicableDefinitionCorrectionTargets.has(change.id),
    );
    for (let index = defChanges.length - 1; index >= 0; index -= 1) {
      if (inapplicableDefinitionCorrectionTargets.has(defChanges[index].id)) defChanges.splice(index, 1);
    }
    for (let index = proposedCoreEdits.length - 1; index >= 0; index -= 1) {
      const edit = proposedCoreEdits[index];
      if (edit.kind === "definition-replace" && inapplicableDefinitionCorrectionTargets.has(edit.id)) {
        proposedCoreEdits.splice(index, 1);
      }
    }
    applicableCoreEdits = applicableCoreEdits.filter((edit) =>
      !(edit.kind === "definition-replace" && inapplicableDefinitionCorrectionTargets.has(edit.id))
    );
  }
  const survivingStructuredReviewBundle =
    applicableAnyStatementChanges.length > 0 ||
    applicableDefinitionChanges.length > 0 ||
    applicableAssumptions.length > 0 ||
    applicableCoreEdits.some((edit) => edit.kind !== "rebuild-reverse-dependencies");
  if (!survivingStructuredReviewBundle) {
    for (const [id, recovered] of reviewDeferredRecoveredPartials) {
      for (let index = deferredProofs.length - 1; index >= 0; index -= 1) {
        if (deferredProofs[index].id === id) deferredProofs.splice(index, 1);
      }
      recordProof(next, proto, {
        id,
        snapshotOf: recovered.statement,
        proofTex: recovered.statement.proof_tex ?? "",
        node: recovered.statement,
        owner: recovered.owner,
      });
      for (const output of outputs) {
        output.added_lemmas = output.added_lemmas.map((statement) =>
          statement.id === id ? structuredClone(recovered.statement) : statement
        );
      }
      solved += 1;
    }
    if (reviewDeferredRecoveredPartials.size > 0) finalRendered = assembleCore(proto, next);
  }
  const durableCorrectionPairSurvives = (id: string): boolean => {
    if (!durableCorrectionTargetOwners.has(id)) return false;
    const change = applicableAnyStatementChanges.find((candidate) => candidate.id === id);
    return change !== undefined && applicableCoreEdits.some((edit) =>
      edit.kind === "statement-replace" && edit.id === id && edit.proposed.statement === change.proposed
    );
  };
  // A same-round root postimage may be the only edge that makes a shelved helper
  // live. Projection must see that edge early enough to retain the helper bytes,
  // but the root edit can still fail later applicability checks. Revoke every proof
  // capability minted solely by rejected postimages before publishing the carrier.
  const survivingOwnershipPostimages = new Map(
    [...ownershipPostimages].filter(([id, postimage]) =>
      applicableAnyStatementChanges.some((change) =>
        change.id === id && change.proposed === postimage.statement
      ) && applicableCoreEdits.some((edit) =>
        edit.kind === "statement-replace" && edit.id === id &&
        JSON.stringify(edit.proposed) === JSON.stringify(postimage)
      )
    ),
  );
  const survivingPostimageOwners = selectLiveDurableProofOwners({
    coreStatements: core.statements,
    requiredIds: ownershipRequiredIds,
    durableRecords: ownershipDurableRecords,
    activeTargetOwners: semanticTargetOwners,
    statementPostimages: survivingOwnershipPostimages,
    writableIds: ownershipWritableIds,
  });
  const revokePostimageMintedTarget = (id: string, reason: string): void => {
    const currentRecord = next.solved[id];
    const priorRecord = preMergeSolved[id];
    const removedInstalledSettlement = currentRecord !== undefined &&
      JSON.stringify(currentRecord) !== JSON.stringify(priorRecord);
    let removedAddedNode = false;
    const revokedResolutionSources = new Set<string>();
    for (const output of outputs) {
      for (const proof of output.proofs.filter((candidate) => candidate.id === id)) {
        withheldProofBytes.push({ nodeId: id, proofTex: proof.proof_tex ?? "", reason });
      }
      removedAddedNode ||= output.added_lemmas.some((candidate) => candidate.id === id);
      for (const resolution of output.resolved_oeqs) {
        if (resolution.source_id === id || resolution.theorem.id === id) {
          revokedResolutionSources.add(resolution.source_id);
          removedAddedNode = true;
        }
      }
      output.proofs = output.proofs.filter((candidate) => candidate.id !== id);
      output.added_lemmas = output.added_lemmas.filter((candidate) => candidate.id !== id);
      output.proposed_statement_changes = output.proposed_statement_changes.filter((candidate) => candidate.id !== id);
      output.proposed_core_edits = output.proposed_core_edits.filter((candidate) => coreEditTarget(candidate) !== id);
      output.resolved_oeqs = output.resolved_oeqs.filter((candidate) =>
        candidate.source_id !== id && candidate.theorem.id !== id
      );
      output.open_obligations = output.open_obligations.filter((candidate) => candidate.node_id !== id);
      if (output.prose_updates !== undefined) {
        output.prose_updates = {
          ...output.prose_updates,
          statement_notes: output.prose_updates.statement_notes.filter((note) => note.id !== id),
        };
      }
    }
    for (let index = proposedChanges.length - 1; index >= 0; index -= 1) {
      if (proposedChanges[index].id === id) proposedChanges.splice(index, 1);
    }
    for (let index = proposedCoreEdits.length - 1; index >= 0; index -= 1) {
      if (coreEditTarget(proposedCoreEdits[index]) === id) proposedCoreEdits.splice(index, 1);
    }
    applicableAnyStatementChanges = applicableAnyStatementChanges.filter((candidate) => candidate.id !== id);
    applicableStatementChanges = applicableStatementChanges.filter((candidate) => candidate.id !== id);
    applicableCoreEdits = applicableCoreEdits.filter((candidate) => coreEditTarget(candidate) !== id);
    applicableStatementChangeById.delete(id);
    for (let index = resolvedOeqEntries.length - 1; index >= 0; index -= 1) {
      const candidate = resolvedOeqEntries[index];
      if (candidate.source_id === id || candidate.theorem.id === id) resolvedOeqEntries.splice(index, 1);
    }
    for (let index = openObligations.length - 1; index >= 0; index -= 1) {
      if (openObligations[index].node_id === id) openObligations.splice(index, 1);
    }
    for (const sourceId of revokedResolutionSources) {
      const prior = initialResolvedOeqs[sourceId];
      if (prior === undefined) delete next.resolved_oeqs?.[sourceId];
      else (next.resolved_oeqs ??= {})[sourceId] = structuredClone(prior);
    }
    const priorNote = preMergeProseOverlay?.statement_notes?.[id];
    if (priorNote === undefined) {
      if (next.prose_overlay?.statement_notes !== undefined) {
        delete next.prose_overlay.statement_notes[id];
      }
    } else {
      (next.prose_overlay ??= {}).statement_notes ??= {};
      next.prose_overlay.statement_notes[id] = structuredClone(priorNote);
    }
    installedNodes.delete(id);
    if (priorRecord === undefined) delete next.solved[id];
    else next.solved[id] = structuredClone(priorRecord);
    if (removedInstalledSettlement) solved = Math.max(0, solved - 1);
    if (removedAddedNode) addedLemmas = Math.max(0, addedLemmas - 1);
  };
  const inapplicableStatementCorrectionTargets = [...inapplicableCorrectionTargets]
    .filter((id) => applicableAnyStatementChanges.some((change) => change.id === id));
  for (const id of inapplicableStatementCorrectionTargets) {
    revokePostimageMintedTarget(id, "correction-pair-inapplicable");
    for (let index = deferredProofs.length - 1; index >= 0; index -= 1) {
      if (deferredProofs[index].id === id) deferredProofs.splice(index, 1);
    }
    finalRendered = assembleCore(proto, next);
  }
  let revokedPostimageProof = false;
  for (const [id, expectedOwner] of postimageProofOwners) {
    if (survivingPostimageOwners.get(id) === expectedOwner) continue;
    revokedPostimageProof = true;
    revokePostimageMintedTarget(id, "enabling-statement-postimage-inapplicable");
    for (let index = deferredProofs.length - 1; index >= 0; index -= 1) {
      if (deferredProofs[index].id === id) deferredProofs.splice(index, 1);
    }
    finalRendered = assembleCore(proto, next);
  }
  // Final fail-closed check for correction-only durable proofs. Eligibility was
  // established before ordinary normalization so projection could authorize the
  // pair, but a no-op/revision/applicability filter may still remove it later. Roll
  // back the proof record and rendered node unless the exact pair remains applicable.
  let revokedDurableCorrection = false;
  for (const id of durableCorrectionTargetOwners.keys()) {
    if (core.statements.some((statement) => statement.id === id) || requiredCoreTargets.has(id)) continue;
    if (durableCorrectionPairSurvives(id)) continue;
    revokedDurableCorrection = true;
    revokePostimageMintedTarget(id, "durable-correction-pair-inapplicable");
    for (let index = deferredProofs.length - 1; index >= 0; index -= 1) {
      if (deferredProofs[index].id === id) deferredProofs.splice(index, 1);
    }
    finalRendered = assembleCore(proto, next);
  }
  if ((revokedDurableCorrection || revokedPostimageProof) && selfContainmentRecoveredIds.size > 0) {
    // Some records may have been recovered solely because the now-revoked target
    // transiently referenced them. Restore every such slot to the round-current
    // pre-merge state, then rebuild the closure from the surviving graph only.
    for (const id of selfContainmentRecoveredIds) {
      const prior = preMergeSolved[id];
      if (prior === undefined) delete next.solved[id];
      else next.solved[id] = structuredClone(prior);
    }
    finalRendered = assembleCore(proto, next);
    const deletedStatementIds = new Set(
      [...pendingSupersessionEdits, ...requiredCoreEdits]
        .filter((edit) => edit.kind === "statement-delete")
        .map((edit) => edit.id),
    );
    for (let pass = 0; pass < 50; pass += 1) {
      const known = new Set([
        ...finalRendered.assumptions.map((assumption) => assumption.id),
        ...finalRendered.definitions.map((definition) => definition.id),
        ...finalRendered.statements.map((statement) => statement.id),
      ]);
      let repaired = false;
      for (const statement of finalRendered.statements) {
        if (deletedStatementIds.has(statement.id)) continue;
        for (const dependency of statement.depends_on ?? []) {
          const record = prev?.solved[dependency];
          if (known.has(dependency) || droppedCarryIds.has(dependency) ||
              record?.node === undefined || next.solved[dependency] !== undefined) continue;
          next.solved[dependency] = !validIds.has(dependency) || isUnfinishedCarriedRecord(record)
            ? { ...record, partial: true }
            : record;
          repaired = true;
        }
      }
      if (!repaired) break;
      finalRendered = assembleCore(proto, next);
    }
    const known = new Set([
      ...finalRendered.assumptions.map((assumption) => assumption.id),
      ...finalRendered.definitions.map((definition) => definition.id),
      ...finalRendered.statements.map((statement) => statement.id),
      ...proposedAssumptions.map((assumption) => assumption.id),
      ...proposedCoreEdits
        .filter((edit) => edit.kind === "definition-add")
        .map((edit) => edit.id),
    ]);
    const dangling: string[] = [];
    for (const statement of finalRendered.statements) {
      if (deletedStatementIds.has(statement.id)) continue;
      for (const dependency of statement.depends_on ?? []) {
        if (!known.has(dependency)) dangling.push(`${statement.id}->${dependency}`);
      }
    }
    if (dangling.length > 0) {
      throw new Error(
        `Stage 0-SOLVE unresolved dependency target(s) after durable-correction rollback: ${dangling.join(", ")}`,
      );
    }
  }

  // `statement_notes` decorates the durable statement catalog, not only the
  // currently published render.  The overlay is cumulative, so a note can outlive
  // a node removed in an earlier transaction (most notably legacy OEQ/answer ids
  // whose statement deletion predated overlay cleanup).  Conversely, resolved OEQ
  // sources and partial+shelved agent nodes are deliberately absent from
  // `finalRendered` but remain revivable authoritative records.  Prune only keys
  // absent from BOTH stores after the complete postimage/rollback closure is known:
  // frozen proto statements (including resolved OEQs) and agent-authored catalog
  // records (including shelved nodes).  Explicit statement deletion removes its
  // proto/record and note transactionally in d0_apply.
  const orphanNoteIds = pruneOrphanStatementNotes(proto, next);
  if (orphanNoteIds.length > 0) {
    console.warn(
      `[D0-SOLVE] pruned ${orphanNoteIds.length} orphan statement-note key(s) from the final postimage: ` +
        orphanNoteIds.join(", "),
    );
  }
  const substantiveNoteIds = new Set<string>();
  for (const output of outputs) {
    for (const note of output.prose_updates?.statement_notes ?? []) {
      const target = core.statements.find((statement) => statement.id === note.id);
      if (target !== undefined &&
        ((note.justification !== undefined && note.justification !== target.justification) ||
          (note.gap !== undefined && note.gap !== target.gap) ||
          (note.consumer !== undefined && note.consumer !== target.consumer))) {
        substantiveNoteIds.add(note.id);
      }
    }
  }
  emittedStatementNoteChanges = substantiveNoteIds.size > 0;
  // A structured directive forbids a prose-only response: a note counts toward it
  // only when it edits metadata of one of the directive's EXACT targets.
  const noteChangeOnRequiredTarget = [...substantiveNoteIds].some((id) => requiredCoreTargets.has(id));
  // A worker-proposed rebuild is derived metadata and cannot satisfy a mathematical
  // exact target. A sealed orchestrator mandate for that exact operation is different:
  // mandate integrity and basis checks have already adjudicated it, and apply supports
  // it as a real required transaction step.
  const applicableRequiredCoreEdits = requiredCoreEdits.filter(
    (edit) => edit.kind === "rebuild-reverse-dependencies" || coreEditApplicable(edit),
  );
  const applicableAllCoreEdits = [
    ...pendingSupersessionEdits.filter(coreEditApplicable),
    ...applicableRequiredCoreEdits,
    ...applicableCoreEdits,
  ];
  const applicableDeletes = new Set(
    applicableAllCoreEdits
      .filter((edit) => edit.kind === "statement-delete")
      .map((edit) => edit.id),
  );
  const dependencySet = (values: string[]): string =>
    [...new Set(values)].sort().join("\u0000");
  const structurallyInvalidatedSettled = new Set(
    applicableAllCoreEdits
      .filter((edit): edit is Extract<RawCoreEdit, { kind: "statement-replace" }> =>
        edit.kind === "statement-replace"
      )
      .filter((edit) => {
        const current = statementById.get(edit.id);
        if (!current) return false;
        // Frozen members keep their settlement in the working overlay. d0_apply
        // deliberately preserves that proof/citation across structural metadata
        // repairs (including declaration narrowing); only an agent-authored carried
        // node takes the immediate reopen branch here.
        const proposedDeps = new Set(edit.proposed.depends_on);
        return current.depends_on.some((dep) => !proposedDeps.has(dep)) ||
          declarationNarrowed(current, edit.proposed);
      })
      .map((edit) => edit.id),
  );
  // Only dispositions that survived mandate/capability/conflict projection may
  // constrain the final transaction. A worker obligation shadowed by an
  // authoritative delete is already preserved in withheld content and must not
  // resurrect the old whole-round abort here.
  for (const obligation of outputs.flatMap((output) => output.open_obligations)) {
    const target = statementById.get(obligation.node_id);
    const durable = initialResolvedOeqs[obligation.node_id];
    const answerId = typeof durable === "string" ? durable : durable?.theorem_id;
    if (answerId !== undefined) {
      const sourceClaimNarrowed = applicableAnyStatementChanges.some(
        (change) => change.id === obligation.node_id && change.direction === "narrow",
      );
      const sourceDependenciesChanged = applicableAllCoreEdits.some(
        (edit) => edit.kind === "statement-replace" &&
          edit.id === obligation.node_id &&
          target !== undefined &&
          dependencySet(edit.proposed.depends_on) !== dependencySet(target.depends_on),
      );
      if (!applicableDeletes.has(obligation.node_id) &&
          !applicableDeletes.has(answerId) &&
          !sourceClaimNarrowed &&
          !sourceDependenciesChanged) {
        throw new Error(
          `Stage 0-SOLVE cannot leave already-resolved OEQ ${obligation.node_id} open while durable answer ` +
            `${answerId} remains; delete its source/answer or narrow/rewire the source in the same reviewed transaction`,
        );
      }
    }
    const settled = target?.status === "cited" ||
      (target?.status === "proved" && (target.proof_tex ?? "").trim().length > 0);
    if (settled &&
        !applicableStatementChangeById.has(obligation.node_id) &&
        !structurallyInvalidatedSettled.has(obligation.node_id)) {
      throw new Error(
        `Stage 0-SOLVE cannot mark settled statement ${obligation.node_id} open without a same-transaction proof-relevant invalidation`,
      );
    }
  }
  const finalStructuredTargets = new Set<string>(applicableRequiredCoreEdits.map(coreEditTarget));
  for (const change of applicableStatementChanges) finalStructuredTargets.add(change.id);
  for (const change of applicableDefinitionChanges) finalStructuredTargets.add(change.id);
  for (const assumption of applicableAssumptions) finalStructuredTargets.add(assumption.id);
  for (const edit of applicableCoreEdits) finalStructuredTargets.add(coreEditTarget(edit));
  for (const output of outputs) {
    for (const note of output.prose_updates?.statement_notes ?? []) {
      const target = statementById.get(note.id);
      if (target !== undefined &&
          ((note.justification !== undefined && note.justification !== target.justification) ||
            (note.gap !== undefined && note.gap !== target.gap) ||
            (note.consumer !== undefined && note.consumer !== target.consumer))) {
        finalStructuredTargets.add(note.id);
      }
    }
  }
  for (const obligation of openObligations) {
    const target = statementById.get(obligation.node_id);
    if (target?.kind === "openendedquestion" && obligation.node_id.startsWith("oeq:")) {
      finalStructuredTargets.add(obligation.node_id);
    }
  }
  for (const resolution of resolvedOeqEntries) {
    const durable = next.resolved_oeqs?.[resolution.source_id];
    const theoremId = typeof durable === "string" ? durable : durable?.theorem_id;
    if (theoremId === resolution.theorem.id) {
      finalStructuredTargets.add(resolution.source_id);
      finalStructuredTargets.add(resolution.theorem.id);
    }
  }
  const deferredProofIds = new Set(deferredProofs.map((proof) => proof.id));
  const duplicateReproofSet = new Set(duplicateReproofIds);
  const unmatchedProofSet = new Set(unmatchedProofIds);
  const acceptedAddedNodeIds = new Set<string>();
  for (const output of outputs) {
    for (const proof of output.proofs) {
      // Credit requires the PUBLISHED node to be proved with these bytes — a
      // bare proofs[] emission cannot clear a reopened CITED target, whose
      // sanctioned discharge is the byte-faithful added_lemmas receipt
      // (audit BB3; render status `cited` refuses the credit exactly as the
      // old workspace-status test did).
      const published = finalRendered.statements.find((st) => st.id === proof.id);
      const installed = published?.status === "proved" && published.proof_tex === proof.proof_tex;
      if (
        initialSettledProofs.get(proof.id) !== proof.proof_tex &&
        !duplicateReproofSet.has(proof.id) &&
        !unmatchedProofSet.has(proof.id) &&
        // The deferral arm carries the same publishability bar as the install
        // arm (audit R2BB1): a deferred proof of a reopened CITED target must
        // not consume the directive — the sanctioned discharge is the
        // byte-faithful added_lemmas receipt.
        (installed ||
          (deferredProofIds.has(proof.id) &&
            finalRendered.statements.find((st) => st.id === proof.id)?.status !== "cited"))
      ) {
        finalStructuredTargets.add(proof.id);
      }
    }
    for (const statement of output.added_lemmas) {
      const record = next.solved[statement.id];
      const settled = statement.status === "cited" ||
        (statement.status === "proved" && (statement.proof_tex ?? "").trim().length > 0);
      const accepted = settled &&
        record !== undefined &&
        record.partial !== true &&
        !duplicateReproofSet.has(statement.id) &&
        !addedLemmaCollisions.some((collision) => collision.id === statement.id);
      if (accepted) {
        acceptedAddedNodeIds.add(statement.id);
        finalStructuredTargets.add(statement.id);
      } else if (
        record?.partial === true &&
        record.node?.id === statement.id &&
        deferredProofIds.has(statement.id) &&
        !duplicateReproofSet.has(statement.id) &&
        !addedLemmaCollisions.some((collision) => collision.id === statement.id)
      ) {
        // A new node whose proof depends on a same-round gated edit is deliberately
        // staged as durable partial progress. Credit that concrete carrier for the
        // exact-target emission check so the proposal checkpoint can persist both
        // halves of the transaction. This does NOT accept the proof: apply reopens
        // the dependency closure and the next D0 round must revalidate the node.
        finalStructuredTargets.add(statement.id);
      }
    }
  }
  // A cited-source receipt is intentionally deferred until apply has constructed
  // the reviewed postimage. It is still a concrete structured payload for the
  // exact-target and structured-change gates; otherwise a required cited target
  // is paradoxically rejected precisely because it took the safe deferred path.
  for (const receipt of deferredCitationRevalidations) {
    finalStructuredTargets.add(receipt.id);
  }
  // Projection's first exact-target check sees raw authorized emissions.  A raw
  // owner payload can still disappear here because it is stale, a no-op, or
  // otherwise inapplicable.  Do not let that transient receipt mask a sibling's
  // quarantined mathematical correction: the same capability must exist in the
  // final accepted carrier.  Proof credit alone is intentionally insufficient.
  const unfulfilledExactTargets = [...requiredCoreTargets]
    .filter((target) => !finalStructuredTargets.has(target));
  if (requiredCoreTargets.size > 0) {
    const missing = unfulfilledExactTargets;
    const collisionWithheld = new Set([
      ...addedLemmaCollisions.map((collision) => collision.id),
      ...emissionConflicts.map((conflict) => conflict.id),
      ...conflictConsumerIds,
      ...capabilityQuarantines.map((receipt) => receipt.target),
      ...contestedOeqSourceIds,
      ...contestedOeqAnswerIds,
      ...contestedDispatchTargets,
      ...inapplicableCorrectionTargets,
    ]);
    const hardMissing = missing.filter((target) => !collisionWithheld.has(target));
    if (hardMissing.length > 0) {
      throw new Error(
        `Stage 0-SOLVE directive required exact structured target(s) ${[...requiredCoreTargets].join(", ")}, ` +
          `but no accepted substantive payload remained for ${hardMissing.join(", ")} after normalization` +
          settledRequiredTargetsHint(),
      );
    }
  }
  const finalHasStructuredChanges =
    applicableRequiredCoreEdits.length > 0 ||
    applicableStatementChanges.length > 0 ||
    applicableDefinitionChanges.length > 0 ||
    applicableAssumptions.length > 0 ||
    applicableCoreEdits.some((edit) => edit.kind !== "rebuild-reverse-dependencies") ||
    // A directive that REQUIRES core changes forbids a prose-only response, so
    // statement-note edits count as structure only for ordinary rounds.
    (requiresCoreChanges ? noteChangeOnRequiredTarget : emittedStatementNoteChanges) ||
    acceptedAddedNodeIds.size > 0 ||
    deferredCitationRevalidations.length > 0 ||
    resolvedOeqEntries.some((resolution) => finalStructuredTargets.has(resolution.source_id));
  // Withheld records that carry no mathematics for the directive (stray prose, an
  // unmatched id, a duplicate re-proof, a shadowed mandate echo) must not disarm
  // this abort: a directive would otherwise be consumed by a round that changed
  // nothing, and commit would advance the cursor past it.
  const structuredDirectiveDisarmed = withheldPayloads.some((record) =>
    requiredCoreTargets.has(record.target) || !NOISE_WITHHELD_REASONS.has(record.reason));
  const structuredDirectiveUnfulfilled = requiresCoreChanges && !finalHasStructuredChanges;
  if (structuredDirectiveUnfulfilled &&
      emissionConflicts.length === 0 && conflictConsumerIds.size === 0 && capabilityQuarantines.length === 0 &&
      !structuredDirectiveDisarmed) {
    throw new Error(
      "Stage 0-SOLVE consumed a STRUCTURED CORE CHANGES REQUIRED directive but no accepted substantive " +
        "structured change remained after normalization" + settledRequiredTargetsHint(),
    );
  }

  // `used_by` is derived metadata. Ordinary worker rebuild requests must not buy
  // an adjudication checkpoint; apply normalizes it transactionally after any
  // accepted bundle. Preserve only a sealed orchestrator-required rebuild, whose
  // mandate/basis has already been verified and must remain explicitly auditable.
  const requiredCoreEditOperations = new Set(requiredCoreEdits.map(coreEditOperationKey));
  const applicableDeleteEdits = new Set(applicableCoreEdits.filter(
    (edit) => edit.kind === "statement-delete" || edit.kind === "definition-delete" ||
      edit.kind === "assumption-delete" || edit.kind === "symbol-delete",
  ));
  // A carried supersession delete (or a sealed mandate) is the gated half of an
  // already-installed A→A' replacement. It is routinely inapplicable on the retry
  // round that still names A, yet dropping it here erases the only record of that
  // relation and lets a later clean round publish both chains as proved. Keep it
  // surfaced; apply revalidates applicability transactionally.
  const carriedDeleteOperations = new Set(
    [...pendingSupersessionEdits, ...requiredCoreEdits].map(coreEditOperationKey),
  );
  const surfacedCoreEdits = proposedCoreEdits.filter(
    (edit) =>
      (!(edit.kind === "statement-delete" || edit.kind === "definition-delete" ||
          edit.kind === "assumption-delete" || edit.kind === "symbol-delete") ||
        applicableDeleteEdits.has(edit) ||
        carriedDeleteOperations.has(coreEditOperationKey(edit))) &&
      (edit.kind !== "rebuild-reverse-dependencies" ||
        requiredCoreEditOperations.has(coreEditOperationKey(edit))),
  );

  return {
    emissionConflicts,
    withheldConflictConsumers: [...conflictConsumerIds]
      .filter((id) => !transactionBlockedIds.has(id))
      .sort(),
    withheldCapabilityEmissions: [...new Set(withheldCapabilityEmissions)].sort(),
    withheldPayloads,
    unfulfilledExactTargets,
    structuredDirectiveUnfulfilled,
    addedLemmaCollisions,
    oeqAnswerCollisions,
    withheldInvalidResolutions,
    duplicateReproofIds,
    duplicateEchoEditIds: preCapabilityEchoEdits.map(({ id }) => id),
    withheldProofBytes,
    unmatchedProofIds,
    quarantinedProofs,
    proposedChanges,
    defChanges,
    proposedAssumptions,
    proposedCoreEdits: surfacedCoreEdits,
    deferredProofs,
    deferredCitationRevalidations,
    openObligations,
    illegalDefTargets,
    solved,
    addedLemmas,
  };
}
