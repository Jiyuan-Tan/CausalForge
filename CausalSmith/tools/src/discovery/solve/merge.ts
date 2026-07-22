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
import { proofContentClosureIntersects, wireStatementProofDependencies } from "../core/dependencies.js";
import { assertCanonicalAlignedRowTerminators, repairCoreLatexSerialization } from "../core/latex_serialization.js";
import { extractNodeRefs, healStatementId } from "../core/node_ids.js";
import { solvedStatus, isUnfinishedCarriedRecord } from "../core/status.js";
import { type ProofToArchive } from "../proof_archive.js";
import { recordProof, refreshSnapshots } from "../working_writer.js";
import { validateSolveManifest } from "../semantic_manifest.js";
import { coreEditTarget, type RawCoreEdit } from "../stages/d0_apply.js";
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
import { oeqSourceFingerprint, type SolveRoundContext } from "./context.js";
import type { SolveDispatchResult } from "./dispatch.js";

/** Apply directive-authorized narrative replacements to both the live solved core
 * and its frozen proto source. This channel cannot touch mathematical content. */
function applyProseUpdates(core: Core, proto: Core, updates: ProseUpdates): void {
  const targets = [core, proto];
  const scalarFields = [
    "tldr",
    "related_work",
    "interpretation",
    "technical_internal_limitation",
    "honest_scope",
  ] as const;
  for (const field of scalarFields) {
    const value = updates[field];
    if (value === undefined) continue;
    for (const target of targets) target[field] = value;
  }
  if (updates.project_justification) {
    for (const target of targets) {
      const prior = target.project_justification;
      const merged = { ...prior, ...updates.project_justification };
      target.project_justification = ProjectJustificationSchema.parse(merged);
    }
  }
  for (const note of updates.statement_notes) {
    const protoStmt = proto.statements.find((s) => s.id === note.id);
    const coreStmt = core.statements.find((s) => s.id === note.id);
    // A paper-wide prose owner can see durable prior-round statements that are
    // intentionally absent from this round's assembled core (most notably an OEQ
    // answer invalidated for re-solve by a new directive).  Statement notes are
    // metadata only: dropping such a stale/out-of-round note is safer than aborting
    // structured mathematical changes that will rebuild the node on the next pass.
    // Fresh OEQ replacements emitted in this round are present here because prose
    // application happens after the replacement merge below.
    if (!coreStmt) {
      console.warn(
        `[D0-SOLVE] prose sync: dropped statement note for out-of-round node '${note.id}'.`,
      );
      continue;
    }
    for (const field of ["justification", "gap", "consumer"] as const) {
      const value = note[field];
      if (value === undefined) continue;
      coreStmt[field] = value;
      if (protoStmt) protoStmt[field] = value;
    }
  }
}

/** Statements the solver may NOT alter in place (claim/kind/prose are frozen at
 *  D-1; a change goes through the proposed_statement_change escalation, not a
 *  silent edit). Status/route/proof_tex/depends_on-growth ARE allowed. */
function silentAlterationViolations(proto: Core, core: Core, allowedDropped = new Set<string>()): string[] {
  const v: string[] = [];
  const byId = new Map(core.statements.map((s) => [s.id, s]));
  for (const p of proto.statements) {
    const c = byId.get(p.id);
    if (!c) {
      if (!allowedDropped.has(p.id)) v.push(`statement ${p.id} dropped (frozen at D-1)`);
      continue;
    }
    if (c.kind !== p.kind) v.push(`statement ${p.id}: kind changed silently (use proposed_statement_change)`);
    if (c.statement !== p.statement) v.push(`statement ${p.id}: claim changed silently (use proposed_statement_change)`);
    if ((c.justification ?? "") !== (p.justification ?? "") || (c.gap ?? "") !== (p.gap ?? "") || (c.consumer ?? "") !== (p.consumer ?? ""))
      v.push(`statement ${p.id}: prose changed silently (frozen at D-1)`);
  }
  return v;
}

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
  protoChangedByProse: boolean;
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
    semanticManifest,
  } = sctx;
  const { dispatch, rawOutputs, proseOwnerIndex, directiveOwnerLabel, semanticTargetOwners } = dr;
  const { outputs: projectedOutputs } = projectOutputsToWriteCapabilities({
    outputs: rawOutputs,
    dispatch,
    semanticTargetOwners,
    directiveOwnerLabel,
    requiredCoreTargets,
  });
  // A cross-unit id collision withholds ONLY the colliding payloads. Dropping every
  // variant (never picking one) keeps the assembled core independent of dispatch
  // order, which is what the previous hard abort was protecting — but the rest of
  // the round now survives instead of being discarded wholesale.
  const emissionConflicts = collectConflictingSolveEmissions(projectedOutputs, dispatch.map((u) => u.label));
  const outputs = dropConflictingSolveEmissions(projectedOutputs, emissionConflicts);
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
  const withheldProofBytes: ProofToArchive[] = [];
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
  const emittedStructuredChanges = outputs.some((output) =>
    output.proposed_statement_changes.length > 0 ||
    output.proposed_definition_changes.length > 0 ||
    output.proposed_assumptions.length > 0 ||
    output.added_lemmas.length > 0 ||
    output.resolved_oeqs.length > 0 ||
    output.proposed_core_edits.some((edit) => edit.kind !== "rebuild-reverse-dependencies"),
  );
  if (requiredCoreTargets.size > 0) {
    const emittedTargets = new Set<string>();
    for (const output of outputs) {
      // Exact theorem/lemma repair targets are legitimately discharged by a new
      // proof payload. Structural requirements are checked independently below.
      for (const proof of output.proofs) emittedTargets.add(proof.id);
      for (const change of output.proposed_statement_changes) emittedTargets.add(change.id);
      for (const change of output.proposed_definition_changes) emittedTargets.add(change.id);
      for (const assumption of output.proposed_assumptions) emittedTargets.add(assumption.id);
      for (const statement of output.added_lemmas) emittedTargets.add(statement.id);
      for (const replacement of output.resolved_oeqs) {
        // A resolved OEQ is the structured answer to its SOURCE target. Credit
        // both ends of the replacement: directives naturally name the frozen
        // oeq: node, while later consumers name the emitted thm: node.
        emittedTargets.add(replacement.source_id);
        emittedTargets.add(replacement.theorem.id);
      }
      for (const edit of output.proposed_core_edits) emittedTargets.add(coreEditTarget(edit));
      // A required `oeq:` target the solver leaves genuinely open is attested through
      // an open obligation — the prompt's OEQ contract forbids a proof or resolution
      // entry for it, so silence was the only alternative and the whole round was
      // discarded as "omitted". Credit the attestation: commit routes an oeq-only
      // obligation to D0.5 as an acknowledged residual. Only `oeq:` ids get this
      // credit — an obligation on a theorem/lemma target is a gap, not a discharge.
      for (const obligation of output.open_obligations) {
        if (obligation.node_id.startsWith("oeq:")) emittedTargets.add(obligation.node_id);
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
  for (const r of resolvedOeqEntries) {
    const emitted = {
      ...r.theorem,
      depends_on: r.theorem.depends_on.map((d) => resolvedOeqReplacement.get(d) ?? d),
    };
    const existing = core.statements.find((s) => s.id === emitted.id && !resolvedOeqSources.has(s.id));
    if (!existing) continue;
    const carried = next.solved[emitted.id];
    const priorCarried = prev?.solved[emitted.id];
    const durable = carried?.node
      ? { ...carried.node, proof_tex: carried.proof_tex }
      : null;
    const reusableDurableRecord =
      priorCarried?.node !== undefined &&
      priorCarried.partial !== true &&
      priorCarried.proof_tex.trim().length > 0 &&
      carried?.node !== undefined &&
      carried.partial !== true &&
      carried.proof_tex.trim().length > 0 &&
      durable !== null &&
      reusableOeqAnswerMatches(durable, emitted);
    if (!reusableOeqAnswerMatches(existing, emitted) || !reusableDurableRecord) {
      throw new Error(
        `Stage 0-SOLVE OEQ resolution theorem id collides with non-identical existing node ${emitted.id}`,
      );
    }
    reusableResolutionSources.add(r.source_id);
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
  const proposedCoreEdits: RawCoreEdit[] = [...pendingSupersessionEdits];
  const openObligations: OpenObligation[] = [];
  const existingIds = new Set(core.statements.map((s) => s.id));
  const normalizedProposalText = (value: string): string => value.replace(/\s+/g, " ").trim();
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
  // A proof emitted in `proofs[]` for a node this SAME round adds (added_lemmas /
  // resolved_oeqs) has no core statement while the per-unit loop runs — the prompt
  // licenses that split ("<target or lemma id>"), and cross-unit splits made matching
  // dispatch-order-dependent. Park such proofs and apply them AFTER every unit's
  // nodes are installed; only a target still absent then is a real unmatched-id fault.
  const roundEmittedIds = new Set(extraStatements.map((s) => s.id));
  const pendingSameRoundProofs: Array<{
    proof: { id: string; proof_tex?: string; argues_proposed?: boolean }; ownerLabel: string;
  }> = [];
  for (let i = 0; i < outputs.length; i++) {
    const o = outputs[i];
    const ownerLabel = dispatch[i].label;
    const statementIds = new Set(core.statements.map((s) => s.id));
    const unmatchedHere = new Set(
      partitionProofsByTarget(o.proofs, statementIds).unmatched.filter((id) => !roundEmittedIds.has(id)),
    );
    unmatchedProofIds.push(...unmatchedHere);
    for (const pr of o.proofs) {
      if (unmatchedHere.has(pr.id)) withheldProofBytes.push({ nodeId: pr.id, proofTex: pr.proof_tex ?? "", reason: "unmatched-id" });
      else if (!statementIds.has(pr.id)) pendingSameRoundProofs.push({ proof: pr, ownerLabel });
    }
    for (const pr of o.proofs) {
      const stmt = core.statements.find((s) => s.id === pr.id);
      // AUDIT-B: if the same round proposes changing the statement, do not attach its proof to the old frozen claim.
      // AUDIT-R3: if the round proposes a new assumption, leave proofs for the re-solve after it is applied.
      const needsPostEditRevalidation = stmt
        ? proofNeedsPostEditRevalidation(stmt, pr.proof_tex ?? "")
        : false;
      if (stmt && !needsPostEditRevalidation && typeof pr.proof_tex === "string" && pr.proof_tex.trim().length > 0) {
        stmt.proof_tex = pr.proof_tex;
        stmt.status = solvedStatus(stmt);
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
      const existingIndex = core.statements.findIndex((statement) => statement.id === lem.id);
      if (existingIndex >= 0) {
        const existing = core.statements[existingIndex];
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
          (existing.status === "proved" && (existing.proof_tex ?? "").trim().length > 0) ||
          (existing.status === "cited" && !requiredCoreTargets.has(lem.id));
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
                (existing.status === "cited" && requiredCoreTargets.has(lem.id)))));
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
        core.statements[existingIndex] = lem;
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
      if (!existingIds.has(lem.id)) {
        core.statements.push(lem);
        existingIds.add(lem.id);
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
    proposedChanges.push(...o.proposed_statement_changes);
    proposedDefChanges.push(...o.proposed_definition_changes);
    proposedAssumptions.push(...(o.proposed_assumptions ?? []));
    for (const edit of o.proposed_core_edits ?? []) {
      const repeatsPendingSupersession = edit.kind === "statement-delete" &&
        pendingSupersessionEdits.some((pending) =>
          pending.id === edit.id && pending.replacement_id === edit.replacement_id,
        );
      if (!repeatsPendingSupersession) proposedCoreEdits.push(edit);
    }
    openObligations.push(...o.open_obligations);
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
      const stmt = core.statements.find((s) => s.id === proof.id);
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
      if (stmt.status === "proved" && (stmt.proof_tex ?? "").trim().length > 0) {
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
      stmt.proof_tex = proof.proof_tex;
      stmt.status = solvedStatus(stmt);
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
  const norm = (s: string) => s.replace(/\s+/g, " ").trim();
  {
    const stmtNow = new Map(core.statements.map((s) => [s.id, norm(s.statement)]));
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
      const stmt = core.statements.find((s) => s.id === ob.node_id);
      if (stmt && (stmt.proof_tex ?? "").trim().length === 0) stmt.proof_tex = partial; // keep to-prove
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
  // This was an inline copy of `wireStatementProofDependencies` MINUS its cycle guard,
  // running before the real one. Two lemmas that merely MENTION each other in prose
  // ("the dual of lem:b") got a mutual edge here; the later canonical pass only declines
  // to ADD a cycling edge, so it could not undo one, and the cycle reached the gate as a
  // phantom G4 on a core that was actually fine. Same call, both places — it unions into
  // existing edges and is safe to run twice.
  wireStatementProofDependencies(core);
  // why: reuse snapshots must include dependencies auto-wired from claim/proof citations.
  refreshSnapshots(next, proto, core, { skipPartial: true });
  // No-op statement-replace echo filter (placed AFTER citation auto-wiring so the
  // dependency comparison sees the same wired edge set the solver was shown in the
  // previous round's core.json, not the bare proto assembly).
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
    const stmtById = new Map(core.statements.map((s) => [s.id, s]));
    const provedThisRound = new Set(
      outputs.flatMap((o) => o.proofs)
        .filter((p) => typeof p.proof_tex === "string" && p.proof_tex.trim().length > 0)
        .map((p) => p.id),
    );
    for (let i = proposedCoreEdits.length - 1; i >= 0; i--) {
      const edit = proposedCoreEdits[i];
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

  // Guard: the solver must not have silently altered a frozen D-1 claim/kind/prose
  // (a real change goes through proposed_statement_changes, escalated below).
  const silent = silentAlterationViolations(proto, core, new Set(persistedOeqReplacements.keys()));
  if (silent.length > 0) {
    throw new Error(
      `Stage 0-SOLVE silently altered frozen D-1 content (changes must be PROPOSED, not applied):\n` +
        silent.map((m) => `  - ${m}`).join("\n"),
    );
  }

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
      core.statements.filter((s) => resolvedOeqSources.has(s.id)).map((s) => [s.id, s] as const),
    );
    const replacement = resolvedOeqReplacement;
    core.statements = core.statements
      .filter((s) => !resolvedOeqSources.has(s.id))
      .map((s) => ({ ...s, depends_on: s.depends_on.map((d) => replacement.get(d) ?? d) }));
    // `assumption.used_by` is the reverse edge of `depends_on` and the only other field
    // that addresses a statement id, so it must follow the same remap — otherwise it keeps
    // naming the removed `oeq:` node and reaches F1 (which is told the core's edges are
    // structural ground truth) as a dangling reference.
    core.assumptions = core.assumptions.map((a) =>
      a.used_by ? { ...a, used_by: a.used_by.map((u) => replacement.get(u) ?? u) } : a,
    );
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
        rec.node.depends_on = rec.node.depends_on.map((d) => replacement.get(d) ?? d);
      }
      if (Array.isArray(rec.snapshot?.depends_on)) {
        rec.snapshot.depends_on = rec.snapshot.depends_on.map((d) => replacement.get(d) ?? d);
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
      if (core.statements.some((st) => st.id === theorem.id)) {
        if (!reusableResolutionSources.has(r.source_id)) {
          oeqAnswerCollisions.push(`${r.source_id}->${theorem.id}`);
          withheldProofBytes.push({ nodeId: theorem.id, proofTex: theorem.proof_tex ?? "", reason: "collision-withheld" });
          continue;
        }
      } else {
        core.statements.push(theorem);
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
    // Snapshot against `proto`, not `core`: this loop used the assembled core, which
    // has no valid comparison basis in `computeValidNodes`. skipPartial: a partial's
    // snapshot is the basis the agent argued — refreshing it retargets the obligation.
    refreshSnapshots(next, proto, core, { skipPartial: true });
  }
  // FINAL drain: the resolved-OEQ answer theorems are installed now, so any parked
  // proof still unresolved has a genuinely absent target and reports as unmatched.
  drainParkedProofs(true);

  // Apply prose only after OEQ replacement so statement notes may target the
  // resolved theorem id. Top-level and frozen-member prose also persists to the
  // proto; replacement-theorem prose persists through its working-state node.
  let protoChangedByProse = false;
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
      applyProseUpdates(core, proto, updates);
    }
    CoreSchema.parse(proto);
    protoChangedByProse = true;
    // skipPartial for the same reason as the two calls above: prose application must
    // not silently retarget a partial's argued basis.
    refreshSnapshots(next, proto, core, { skipPartial: true });
  }

  // Model JSON can legally decode an under-escaped `\ne`/`\notin` as a newline
  // plus text. Repair the narrow recurrent patterns in the typed core itself so
  // core.json and its deterministic TeX rendering cannot diverge.
  repairCoreLatexSerialization(core);
  for (const statement of core.statements) {
    if (statement.proof_tex) assertCanonicalAlignedRowTerminators(statement.proof_tex, `${statement.id}.proof_tex`);
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
  const reservedIds = new Set(core.statements.map((s) => s.id));
  for (const s of core.statements) {
    const healed = healStatementId(s.id);
    if (healed === null) continue;
    if (healed !== s.id) {
      // AUDIT-B: collision would merge two statements under one id; stop instead of silently retargeting deps.
      if (reservedIds.has(healed)) throw new Error(`Stage 0-SOLVE auto-heal collision: '${s.id}' would rename onto existing statement id '${healed}'`);
      reservedIds.delete(s.id);
      reservedIds.add(healed);
      idRename.set(s.id, healed);
    }
  }
  if (idRename.size > 0) {
    for (const s of core.statements) {
      const renamed = idRename.get(s.id);
      if (renamed) s.id = renamed;
      if (Array.isArray(s.depends_on)) {
        s.depends_on = s.depends_on.map((d) => idRename.get(d) ?? d);
      }
    }
    // The rename must reach EVERY id-keyed store, not just core.statements. It used to
    // touch only the core, so the working cursor kept the OLD key while the core carried
    // the NEW one — the two stores disagreed the moment a heal fired, the next round
    // carried both, and reconciliation could persist a duplicate node.
    const renameKeys = <T>(rec: Record<string, T>): Record<string, T> =>
      Object.fromEntries(Object.entries(rec).map(([k, v]) => [idRename.get(k) ?? k, v]));

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
      `[D0-SOLVE] auto-healed ${idRename.size} non-kebab statement id(s) across core, working ` +
        `cursor, resolutions and deferred proofs: ` +
        `${[...idRename].map(([a, b]) => `${a}->${b}`).join(", ")}`,
    );
  }

  // The first citation-wiring pass precedes OEQ replacement. Reconcile once more
  // after all replacement theorems and id repairs exist, before self-containment
  // and dead-assumption pruning inspect the final direct graph.
  wireStatementProofDependencies(core);

  // SELF-CONTAINMENT REPAIR. A lemma reused from a prior round (referenced by a
  // freshly-added consumer this round but not re-emitted, and dropped by the validIds
  // carry) would leave a dangling `depends_on` → a spurious G4. Carry any such referenced
  // node forward from the prior working state so the assembled core stays self-contained.
  {
    const known = new Set<string>([
      ...core.assumptions.map((a) => a.id),
      ...core.definitions.map((d) => d.id),
      ...core.statements.map((s) => s.id),
    ]);
    // A dependency on a node surfaced in this same round as an explicit typed
    // add proposal is not dangling: the checkpoint intentionally publishes the
    // proof together with the proposal, then re-proves after adjudication.  Keep
    // it visible in core.json, but count the proposed node as prospective for
    // this merge-boundary integrity check.
    const prospectiveKnown = new Set<string>([
      ...proposedAssumptions.map((a) => a.id),
      ...proposedCoreEdits
        .filter((edit) => edit.kind === "definition-add")
        .map((edit) => edit.id),
    ]);
    for (const s of core.statements) {
      for (const dep of s.depends_on ?? []) {
        if (!known.has(dep) && prev?.solved[dep]?.node) {
          const rec = prev.solved[dep];
          // `solvedStatus` returns "proved" for everything non-cited, so this repair used
          // to publish a carried node as PROVED regardless of its state — including a
          // record flagged `partial` (which means "re-derive; the stored proof is prior
          // partial progress, not a finished proof") and one whose proof is empty. Either
          // way the node rendered as established with nothing established behind it.
          // Recover it honestly: keep the node visible so the core stays self-contained,
          // but carry it as an open obligation rather than a result.
          // A `cited` node legitimately has NO proof — its justification is the citation —
          // so an emptiness test alone marks every cited record unfinished, and rewriting
          // it to `to-prove` while it still carries `source` produces a node the schema
          // rejects (cited <=> source). Cited nodes are never "unfinished" here.
          // See isUnfinishedCarriedRecord: `partial` outranks `cited`, and a reopened
          // cited node must shed `source` or the schema rejects it.
          const unfinished = isUnfinishedCarriedRecord(rec);
          core.statements.push(
            unfinished
              ? { ...rec.node!, proof_tex: undefined, status: "to-prove", source: undefined }
              : { ...rec.node!, proof_tex: rec.proof_tex, status: solvedStatus(rec.node!) },
          );
          known.add(dep);
          next.solved[dep] = rec;
          console.warn(
            `[D0-SOLVE] self-containment repair: carried reused node '${dep}' (referenced but not re-emitted this round).`,
          );
        }
      }
    }
    // A still-dangling edge is ambiguous: it may be a spurious label, or it may be
    // a load-bearing assumption/helper the worker forgot to emit. Erasing it here
    // silently changes the declared proof interface and defers discovery to the
    // expensive D0.5 panel. Fail at the cheap merge boundary with exact receipts.
    const dangling: string[] = [];
    for (const s of core.statements) {
      if (!Array.isArray(s.depends_on)) continue;
      for (const dep of s.depends_on) {
        if (!known.has(dep) && !prospectiveKnown.has(dep)) dangling.push(`${s.id}->${dep}`);
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
    proposedCoreEdits,
    deferredProofs,
    openObligations,
    illegalDefTargets,
    solved,
    addedLemmas,
    protoChangedByProse,
  };
}
