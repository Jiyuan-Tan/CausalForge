// D0-SOLVE step 3/5 — parseOutputs/merge (spec §Stage kernel).
//
// Everything between the raw unit outputs and the fully assembled core, moved
// verbatim from stage0_solve.ts in the T1 carve: write-capability projection,
// cross-unit emission-conflict resolution, directive/prose-ownership
// enforcement, the proof/lemma merge with its collision withholding, proposal
// collection, OEQ resolution application, prose application, LaTeX repair, id
// auto-heal, citation wiring, and the self-containment repair + dangling-edge
// check at the merge boundary.
import { CoreSchema, ProjectJustificationSchema, type Core, type CoreStatement } from "../core/schema.js";
import {
  proofContentClosureIntersects,
  rebuildAssumptionUsedBy,
  wireStatementProofDependencies,
} from "../core/dependencies.js";
import { assertCanonicalAlignedRowTerminators, repairCoreLatexSerialization, repairLatexStringsDeep } from "../core/latex_serialization.js";
import { extractNodeRefs, healStatementId } from "../core/node_ids.js";
import { mergeProseOverlay, assembleCore } from "../core/assemble.js";
import { solvedStatus, isUnfinishedCarriedRecord } from "../core/status.js";
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
  ProseUpdates,
} from "./schemas.js";
import {
  projectOutputsToWriteCapabilities,
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

/** Whether an already-carried theorem is exactly the same mathematical answer an
 * OEQ solver just emitted. Motivation/provenance prose may move independently; the
 * theorem identity, claim, proof interface, proof state and proof body may not. */
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
    JSON.stringify(existing.source ?? null) === JSON.stringify(emitted.source ?? null);
}

// Moved to core/dependencies.ts so d0_apply can use it for paired-proof promotion
// without a merge↔apply value-import cycle; imported back here for local use and
// re-exported for existing consumers.
export { proofContentClosureIntersects };

export interface SolveMergeResult {
  emissionConflicts: SolveEmissionConflict[];
  addedLemmaCollisions: Array<{ id: string; owner: string }>;
  oeqAnswerCollisions: string[];
  /** Identical-claim re-emissions of settled nodes, skipped as no-op discharges. */
  duplicateReproofIds: string[];
  /** Proof bytes refused by this merge (withheld/unmatched/duplicate) — installed
   *  nowhere in hot state, so commitRound must copy them to the cold archive before
   *  the next dispatch can overwrite the raw solve files that hold them. */
  withheldProofBytes: ProofToArchive[];
  unmatchedProofIds: string[];
  proposedChanges: ProposedStatementChange[];
  defChanges: ProposedDefinitionChange[];
  proposedAssumptions: ProposedAssumption[];
  proposedCoreEdits: RawCoreEdit[];
  deferredProofs: Array<{ id: string; proof_tex: string; argues_proposed?: boolean }>;
  openObligations: OpenObligation[];
  illegalDefTargets: string[];
  solved: number;
  addedLemmas: number;
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
    persistedOeqReplacements,
    pendingSupersessionEdits,
    hasPendingDirective,
    requiresCoreChanges,
    requiredCoreTargets,
    requiredCoreEdits: requiredCoreEditsSealed,
    semanticManifest,
  } = sctx;
  // Work with mandate payloads under the SAME LaTeX repair the proposal store
  // gets on every load. Mandates keep their sealed bytes (opaque on load), so an
  // operation on which `repairSerializedLatex` is not a no-op would otherwise
  // never key-match the repaired copy of its own seeded proposal — the same
  // cross-store asymmetry fixed at the d0_apply mandate echo check.
  const requiredCoreEdits = structuredClone(requiredCoreEditsSealed);
  repairLatexStringsDeep(requiredCoreEdits);
  const { dispatch, rawOutputs, proseOwnerIndex, directiveOwnerLabel, semanticTargetOwners } = dr;
  // Revision provenance is a pipeline fact, not a prompt-compliance burden.
  // Attach the exact view stamped into each unit's target block and the shared
  // frozen-definition context whenever the worker omitted it. A worker-supplied
  // revision is preserved and validated normally, so a false/stale value still
  // fails closed instead of being overwritten.
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
        return change.based_on_revision === undefined && target
          ? { ...change, based_on_revision: definitionRevision(target) }
          : change;
      }),
      proposed_core_edits: output.proposed_core_edits.map((edit) => {
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
  const {
    outputs: projectedOutputs,
    quarantined: capabilityQuarantines,
  } = projectOutputsToWriteCapabilities({
    outputs: revisionBoundRawOutputs,
    dispatch,
    semanticTargetOwners,
    directiveOwnerLabel,
    requiredCoreTargets,
    existingStatementIds: new Set([
      ...proto.statements.map((statement) => statement.id),
      ...core.statements.map((statement) => statement.id),
      ...Object.keys(prev?.solved ?? {}),
    ]),
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
  const mandateWithheldProofBytes: ProofToArchive[] = [];
  const mandatedTargetOperations = new Map(requiredCoreEdits.map((edit) => [coreEditTarget(edit), coreEditOperationKey(edit)]));
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
  // A cross-unit id collision withholds ONLY the colliding payloads. Dropping every
  // variant (never picking one) keeps the assembled core independent of dispatch
  // order, which is what the previous hard abort was protecting — but the rest of
  // the round now survives instead of being discarded wholesale.
  const emissionConflicts = collectConflictingSolveEmissions(mandateProjectedOutputs, dispatch.map((u) => u.label));
  const outputs = dropConflictingSolveEmissions(mandateProjectedOutputs, emissionConflicts);
  // Helper ids the solver re-used for a DIFFERENT claim than the core already holds, and
  // OEQ answers that collide on one theorem id. Both are withheld rather than guessed.
  const addedLemmaCollisions: Array<{ id: string; owner: string }> = [];
  const oeqAnswerCollisions: string[] = [];
  // Identical-claim re-emissions of settled nodes, skipped as no-ops (canonical kept).
  // Reported informationally so emitted-vs-persisted reconciliation stays possible.
  const duplicateReproofIds: string[] = [];
  // Proof bytes this merge refuses to install ANYWHERE in hot state (withheld
  // collisions, unmatched ids, duplicate re-proofs, cross-unit conflict variants).
  // They exist only in this round's raw solve files, which the NEXT dispatch may
  // overwrite without a sweep — so commitRound copies these to the cold archive.
  const withheldProofBytes: ProofToArchive[] = [...mandateWithheldProofBytes];
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
  const emittedStatementNoteChanges = outputs.some((output) =>
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
  const preMandateObligations = projectedOutputs.flatMap((output) => output.open_obligations);
  for (const edit of [...pendingSupersessionEdits, ...requiredCoreEdits]) {
    if (
      edit.kind === "statement-delete" &&
      preMandateObligations.some((obligation) => obligation.node_id === edit.id)
    ) {
      throw new Error(
        `Stage 0-SOLVE transaction both deletes and leaves open ${edit.id}`,
      );
    }
  }
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
    const missing = [...requiredCoreTargets].filter((target) => !emittedTargets.has(target));
    if (missing.length > 0) {
      throw new Error(
        `Stage 0-SOLVE directive required exact structured target(s) ${[...requiredCoreTargets].join(", ")}, ` +
          `but the solver omitted ${missing.join(", ")}; unrelated proposals cannot satisfy this directive`,
      );
    }
  }
  if (requiresCoreChanges && !emittedStructuredChanges) {
    throw new Error(
      "Stage 0-SOLVE consumed a STRUCTURED CORE CHANGES REQUIRED directive but emitted no proposed changes; " +
        "refusing to persist proofs/prose around stale frozen nodes",
    );
  }
  const unauthorizedProseIndex = outputs.findIndex(
    (output, i) => output.prose_updates !== undefined && i !== proseOwnerIndex,
  );
  if (unauthorizedProseIndex !== -1) {
    throw new Error(
      `Stage 0-SOLVE unit ${dispatch[unauthorizedProseIndex].label} emitted prose_updates but ` +
        `the canonical prose owner is ${proseOwnerIndex === null ? "none" : dispatch[proseOwnerIndex].label}`,
    );
  }
  const proseUpdates = outputs.flatMap((o) => o.prose_updates ? [o.prose_updates] : []);
  if (proseUpdates.length > 0 && !hasPendingDirective) {
    throw new Error(
      "Stage 0-SOLVE emitted prose_updates without a pending orchestrator directive; refusing unsolicited narrative drift",
    );
  }
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
  const duplicateResolutionTarget = resolvedOeqEntries.find(
    (r, i) => resolvedOeqEntries.findIndex((x) => x.theorem.id === r.theorem.id) !== i,
  );
  if (duplicateResolutionTarget) {
    throw new Error(
      `Stage 0-SOLVE emitted multiple OEQ resolutions claiming theorem id ${duplicateResolutionTarget.theorem.id}`,
    );
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
  const staleAgentTargetIds = new Set(sctx.staleAgentTargets.map((statement) => statement.id));
  for (const r of resolvedOeqEntries) {
    const emitted = {
      ...r.theorem,
      depends_on: r.theorem.depends_on.map((d) => resolvedOeqReplacement.get(d) ?? d),
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
      if (current && normalizedProposalText(current.statement) !== normalizedProposalText(change.proposed)) {
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
  for (const receipt of capabilityQuarantines.filter((item) => item.category === "proof")) {
    const unitIndex = dispatch.findIndex((unit) => unit.label === receipt.unit);
    const proof = unitIndex < 0
      ? undefined
      : rawOutputs[unitIndex].proofs.find((candidate) => candidate.id === receipt.target);
    if (!proof) continue;
    unmatchedProofIds.push(proof.id);
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
  const settledProofBytes = (id: string): string | undefined => {
    const rec = next.solved[id];
    if (rec !== undefined && rec.partial !== true && (rec.proof_tex ?? "").trim().length > 0) return rec.proof_tex;
    return initialSettledProofs.get(id);
  };
  const pendingSameRoundProofs: Array<{
    proof: { id: string; proof_tex?: string; argues_proposed?: boolean }; ownerLabel: string;
  }> = [];
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
      const needsPostEditRevalidation =
        proofNeedsPostEditRevalidation(lem, lem.proof_tex ?? "") && lem.status === "proved";
      if (needsPostEditRevalidation) {
        if ((lem.proof_tex ?? "").trim().length > 0) deferProof(lem.id, lem.proof_tex!);
        // Proved agent-added results whose content closure touches a proposed edit
        // wait for the post-apply re-solve. Their exact proof is also part of the
        // proposal-review artifact; otherwise an emitted prerequisite can exist
        // only in core/working and disappear from adjudication.
        lem.status = "to-prove";
      }
      if (lem.status === "proved" && (lem.proof_tex ?? "").trim().length === 0) {
        // why: a proofless proved lemma is undischarged at the solve boundary, not reusable proof debt.
        lem.status = "to-prove";
      }
      const existing = currentStatement(lem.id);
      if (existing !== undefined) {
        const sameClaim =
          existing.kind === lem.kind &&
          existing.statement === lem.statement &&
          sameDependencySet(existing.depends_on, lem.depends_on);
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
          continue;
        }

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
            target ? [definitionRevision(target)] : [],
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
      ...[...statementById.values()].map((s) => [s.id, norm(s.statement)] as const),
      ...[...installedNodes.values()].map((s) => [s.id, norm(s.statement)] as const),
    ]);
    const defNow = new Map(core.definitions.map((d) => [d.id, norm(d.construction)]));
    const beforeS = proposedChanges.length, beforeD = proposedDefChanges.length;
    for (let i = proposedChanges.length - 1; i >= 0; i--) {
      if (stmtNow.get(proposedChanges[i].id) === norm(proposedChanges[i].proposed)) proposedChanges.splice(i, 1);
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
    for (const rec of Object.values(next.solved)) {
      if (rec.node && Array.isArray(rec.node.depends_on)) {
        rec.node.depends_on = [...new Set(rec.node.depends_on.map((d) => replacement.get(d) ?? d))];
      }
      if (Array.isArray(rec.snapshot?.depends_on)) {
        // Sorted-unique: a proof citing BOTH the question and its answer would
        // otherwise remap to a duplicate entry, and the canonical recomputation
        // in the snapshot-basis check would flag a clean resolution (audit R2BB3).
        rec.snapshot.depends_on = [...new Set(rec.snapshot.depends_on.map((d) => replacement.get(d) ?? d))].sort();
      }
    }
    for (const r of resolvedOeqEntries) {
      const theorem = {
        ...r.theorem,
        depends_on: r.theorem.depends_on.map((d) => replacement.get(d) ?? d),
      };
      // Two resolutions may name the SAME answer theorem id. Pushing both puts duplicate
      // statement ids in the core, where every consumer keys by id and silently resolves
      // to one record while `recordProof` overwrites the single working entry. Withhold
      // the second and report it rather than persisting an incoherent core.
      if (statementExists(theorem.id)) {
        if (!reusableResolutionSources.has(r.source_id)) {
          oeqAnswerCollisions.push(`${r.source_id}->${theorem.id}`);
          withheldProofBytes.push({ nodeId: theorem.id, proofTex: theorem.proof_tex ?? "", reason: "collision-withheld" });
          continue;
        }
        // The id is present as the OPEN PROJECTION, not as a settled answer. Skipping here
        // (the exact-re-emission no-op) would keep the `to-prove` placeholder in the core,
        // leave the working record `partial`, and drop the emitted proof bytes into neither
        // the archive nor `withheldProofBytes` — the round then reports the node still open
        // even though the solver proved it, and re-running reproduces the same state.
        if (projectionResolutionSources.has(r.source_id)) {
          installedNodes.set(theorem.id, theorem);
          solved += 1;
          recordProof(next, proto, {
            id: theorem.id,
            snapshotOf: theorem,
            proofTex: theorem.proof_tex ?? "",
            node: theorem,
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
  let finalRendered = assembleCore(proto, next);
  {
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
        for (const dep of st.depends_on ?? []) {
          if (!known.has(dep) && prev?.solved[dep]?.node && next.solved[dep] === undefined) {
            const rec = prev.solved[dep];
            // Recover it HONESTLY: an unfinished record (partial / empty
            // non-cited proof — see isUnfinishedCarriedRecord) re-enters as an
            // open partial, never as an established result; the render derives
            // the status.
            next.solved[dep] = isUnfinishedCarriedRecord(rec) ? { ...rec, partial: true } : rec;
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
  const applicableAnyStatementChanges = proposedChanges.filter((change) => {
    const target = statementById.get(change.id);
    return target !== undefined &&
      change.current === target.statement &&
      normalizedText(change.proposed) !== normalizedText(target.statement);
  });
  // OEQ claim narrowings are supported apply-time detach transitions, but only
  // the obligation/resolution channel may consume an exact OEQ directive.
  const applicableStatementChanges = applicableAnyStatementChanges.filter(
    (change) => statementById.get(change.id)?.kind !== "openendedquestion",
  );
  const applicableDefinitionChanges = defChanges.filter((change) => {
    const target = definitionById.get(change.id);
    return target !== undefined &&
      target.by_member_properties === undefined &&
      change.current === target.construction &&
      normalizedText(change.proposed) !== normalizedText(target.construction);
  });
  const existingAssumptionIds = new Set(core.assumptions.map((assumption) => assumption.id));
  const assumptionById = new Map(core.assumptions.map((assumption) => [assumption.id, assumption]));
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
    if (current.construction !== edit.proposed.construction ||
        !declarationNarrowed(current, edit.proposed)) return edit.proposed;
    const proposedNames = new Set((edit.proposed.free_symbols ?? []).map(normalizeSymbol));
    const retained = (current.free_symbols ?? []).filter((name) => !proposedNames.has(normalizeSymbol(name)));
    return retained.length === 0
      ? edit.proposed
      : { ...edit.proposed, free_symbols: [...(edit.proposed.free_symbols ?? []), ...retained] };
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
  const receiptCore = structuredClone(proto);
  // Apply runs only after this round commits `next`; replay against that exact
  // durable cursor, not the pre-round `prev`, so same-round nodes/edges participate
  // in delete/replacement applicability exactly as they will transactionally.
  const receiptWorking = structuredClone(next);
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
    preview.statements.find((statement) => statement.id === id) ?? working?.solved[id]?.node;
  const statementDeleteApplicable = (
    edit: Extract<RawCoreEdit, { kind: "statement-delete" }>,
    preview: Core,
    working: typeof receiptWorking,
  ): boolean => {
    if (!receiptStatement(preview, working, edit.id) || edit.replacement_id === edit.id) return false;
    if (edit.replacement_id !== undefined &&
        !receiptStatement(preview, working, edit.replacement_id)) return false;
    if (findUnsafeDeleteTextReferences(preview, working, edit.id).length > 0) return false;
    if (edit.replacement_id !== undefined) return true;
    const structuredInbound = preview.statements.some(
      (statement) => statement.id !== edit.id && statement.depends_on.includes(edit.id),
    );
    const carriedInbound = Object.entries(working?.solved ?? {}).some(
      ([id, record]) => id !== edit.id && record.node?.depends_on.includes(edit.id),
    );
    const symbolInbound = preview.symbols.some((symbol) => symbol.ref === edit.id);
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
      receiptCore.statements = receiptCore.statements
        .filter((statement) => statement.id !== edit.id)
        .map((statement) => ({
          ...statement,
          depends_on: replacement === undefined
            ? statement.depends_on.filter((dep) => dep !== edit.id)
            : statement.depends_on.map((dep) => dep === edit.id ? replacement : dep),
        }));
      for (const symbol of receiptCore.symbols) {
        if (symbol.ref !== edit.id) continue;
        if (replacement === undefined) delete symbol.ref;
        else symbol.ref = replacement;
      }
      if (receiptWorking) {
        delete receiptWorking.solved[edit.id];
        for (const record of Object.values(receiptWorking.solved)) {
          if (!record.node) continue;
          record.node.depends_on = replacement === undefined
            ? record.node.depends_on.filter((dep) => dep !== edit.id)
            : record.node.depends_on.map((dep) => dep === edit.id ? replacement : dep);
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
          ...proposed,
          statement: target.statement,
          status: target.status,
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
      const safe =
        receiptCore.definitions.some((definition) => definition.id === edit.id) &&
        findUnsafeDeleteTextReferences(receiptCore, receiptWorking, edit.id).length === 0;
      if (safe) {
        receiptCore.definitions = receiptCore.definitions.filter((definition) => definition.id !== edit.id);
        for (const statement of receiptCore.statements) {
          statement.depends_on = statement.depends_on.filter((dep) => dep !== edit.id);
        }
        for (const symbol of receiptCore.symbols) if (symbol.ref === edit.id) delete symbol.ref;
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
    const previewStatements = new Map(
      [
        ...preview.statements,
        ...Object.values(previewWorking?.solved ?? {}).flatMap((record) => record.node ? [record.node] : []),
      ].map((statement) => [statement.id, statement] as const),
    );
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
      return current !== undefined &&
        edit.proposed.id === edit.id &&
        JSON.stringify(effectiveDefinitionReplacement(edit, current)) !== JSON.stringify(current);
    }
    if (edit.kind === "definition-delete") {
      const exists = preview.definitions.some((definition) => definition.id === edit.id);
      return exists && findUnsafeDeleteTextReferences(preview, previewWorking, edit.id).length === 0;
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
  const applicableCoreEdits = proposedCoreEdits.filter(coreEditApplicable);
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
  for (const obligation of preMandateObligations) {
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
      }
    }
  }
  if (requiredCoreTargets.size > 0) {
    const missing = [...requiredCoreTargets].filter((target) => !finalStructuredTargets.has(target));
    const collisionWithheld = new Set(addedLemmaCollisions.map((collision) => collision.id));
    const hardMissing = missing.filter((target) => !collisionWithheld.has(target));
    if (hardMissing.length > 0) {
      throw new Error(
        `Stage 0-SOLVE directive required exact structured target(s) ${[...requiredCoreTargets].join(", ")}, ` +
          `but no accepted substantive payload remained for ${hardMissing.join(", ")} after normalization`,
      );
    }
  }
  const finalHasStructuredChanges =
    applicableRequiredCoreEdits.length > 0 ||
    applicableStatementChanges.length > 0 ||
    applicableDefinitionChanges.length > 0 ||
    applicableAssumptions.length > 0 ||
    applicableCoreEdits.some((edit) => edit.kind !== "rebuild-reverse-dependencies") ||
    emittedStatementNoteChanges ||
    acceptedAddedNodeIds.size > 0 ||
    resolvedOeqEntries.some((resolution) => finalStructuredTargets.has(resolution.source_id));
  if (requiresCoreChanges && !finalHasStructuredChanges) {
    throw new Error(
      "Stage 0-SOLVE consumed a STRUCTURED CORE CHANGES REQUIRED directive but no accepted substantive " +
        "structured change remained after normalization",
    );
  }

  // `used_by` is derived metadata. Ordinary worker rebuild requests must not buy
  // an adjudication checkpoint; apply normalizes it transactionally after any
  // accepted bundle. Preserve only a sealed orchestrator-required rebuild, whose
  // mandate/basis has already been verified and must remain explicitly auditable.
  const requiredCoreEditOperations = new Set(requiredCoreEdits.map(coreEditOperationKey));
  const surfacedCoreEdits = proposedCoreEdits.filter(
    (edit) => edit.kind !== "rebuild-reverse-dependencies" ||
      requiredCoreEditOperations.has(coreEditOperationKey(edit)),
  );

  return {
    emissionConflicts,
    addedLemmaCollisions,
    oeqAnswerCollisions,
    duplicateReproofIds,
    withheldProofBytes,
    unmatchedProofIds,
    proposedChanges,
    defChanges,
    proposedAssumptions,
    proposedCoreEdits: surfacedCoreEdits,
    deferredProofs,
    openObligations,
    illegalDefTargets,
    solved,
    addedLemmas,
  };
}
