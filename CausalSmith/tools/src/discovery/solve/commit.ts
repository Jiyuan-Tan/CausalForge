// D0-SOLVE step 5/5 — persist/commit (spec §Stage kernel).
//
// The round's terminal paths, moved verbatim from stage0_solve.ts in the T1
// carve: the atomic commit closure (publish artifacts first, rename the working
// cursor LAST), the proposal/withheld-content checkpoint with its review packet
// and closure/preflight receipts, the open-obligation and incomplete-round
// checkpoints, and the clean-discharge result.
import { rm } from "node:fs/promises";
import path from "node:path";
import type { PipelineContext, StageResult, StateJson } from "../../types.js";
import { writeJsonAtomic } from "../../shared/json_atomic.js";
import { buildReviewPacket } from "../review_packet.js";
import { formatClosureViolation } from "../core/coherence.js";
import { formatPreflightViolations } from "../core/preflight.js";
import {
  proposalReviewPacketPath,
  openObligationsPath,
} from "../discovery_paths.js";
import { archiveProofs, type ProofToArchive } from "../proof_archive.js";
import { workingPath, saveWorkingState } from "../stages/d0_working.js";
import type { ProposedStatementChange } from "./schemas.js";
import { formatSolveEmissionConflicts } from "./ownership.js";
import type { SolveRoundContext } from "./context.js";
import type { SolveMergeResult } from "./merge.js";
import {
  reconcileAndWarnRound,
  checkpointClosure,
  checkpointPreflight,
  healMissingBibCites,
  runPostSolveGate,
} from "./gates.js";

export interface Stage0SolveResult {
  message: string;
  coreJsonPath: string;
  solved: number;
  addedLemmas: number;
  proposedChanges: ProposedStatementChange[];
}

/** Build the round's atomic commit closure over the shared round state. */
export function makeCommitRound(args: {
  ctx: PipelineContext;
  sctx: SolveRoundContext;
  protoChangedByProse: boolean;
  /** Proof bytes the merge refused to install anywhere in hot state. They live only in
   *  this round's raw solve files, which the next dispatch may overwrite — so the
   *  commit copies them to the cold archive first. */
  withheldProofBytes?: ProofToArchive[];
}): () => Promise<void> {
  const { ctx, sctx, protoChangedByProse, withheldProofBytes = [] } = args;
  const { proto, core, protoPath, corePath, next } = sctx;
  // `d0_working.json` is the round commit record: it marks escalation rows as
  // consumed. Publish every round artifact first and rename the cursor LAST.
  // A crash before that final rename safely replays the directive; after it,
  // core/proposal artifacts are already durable.
  // STORE-COHERENCE INVARIANT. `core.json` (the derived merge) and the working
  // state's `solved` map record the same proofs through different code paths, and
  // several carry branches write only one of them. A node present in the core with
  // a proof but ABSENT from `solved` still renders this round, then silently
  // vanishes next round: every carry branch reads `prev.solved`, so the working
  // state — not the core — is what survives. This preferentially destroys TERMINAL
  // results, which have no inbound edge to trigger the self-containment repair.
  // Repair from the core node (the authoritative proof) and report receipts; a
  // resolution pointing at a theorem in NEITHER store is unrepairable, so throw.
  const commitRound = async (): Promise<void> => {
    reconcileAndWarnRound(sctx);
    if (withheldProofBytes.length > 0) await archiveProofs(path.dirname(corePath), withheldProofBytes);
    await writeJsonAtomic(corePath, core);
    if (protoChangedByProse) await writeJsonAtomic(protoPath, proto);
    await saveWorkingState(ctx, next);
  };
  return commitRound;
}


/** The proposal / withheld-content checkpoint. Returns the checkpoint StageResult
 *  when this round must halt for orchestrator adjudication, or null when the
 *  round has nothing to surface and may continue toward discharge. */
export async function surfaceProposalCheckpoint(args: {
  ctx: PipelineContext;
  sctx: SolveRoundContext;
  mr: SolveMergeResult;
  commitRound: () => Promise<void>;
}): Promise<StageResult | null> {
  const { ctx, sctx, mr, commitRound } = args;
  const { proto, core, corePath, next } = sctx;
  const {
    emissionConflicts,
    addedLemmaCollisions,
    oeqAnswerCollisions,
    unmatchedProofIds,
    proposedChanges,
    defChanges,
    proposedAssumptions,
    proposedCoreEdits,
    deferredProofs,
    illegalDefTargets,
  } = mr;
  // SURFACE PROPOSALS for the D0 revise loop (runStage0Typed). The solver's
  // statement narrowings, definition corrections, new assumptions, and structured
  // edits are written to canonical proposed_*.json files and the run CHECKPOINTS.
  // The orchestrator adjudicates every proposal, explicitly applies accepted ids
  // with d0_apply_change (which records the escalation), and then re-solves.
  // `emissionConflicts` must trigger this checkpoint on its OWN. When a collision drops
  // the round's only proposals, every list below is empty, and gating solely on them
  // skipped the checkpoint entirely — the conflict went unreported and the run advanced
  // as if nothing had happened. That is strictly worse than the abort this replaced,
  // which at least failed loudly. A withheld collision must always reach the orchestrator.
  // EVERY withheld-content collector must appear here, not just the proposal lists. This
  // guard was already widened once for `emissionConflicts`; the two collision collectors
  // added afterwards were pushed into `blocks` but NOT into this condition, so a round
  // whose ONLY defect was a withheld helper or OEQ answer skipped the checkpoint entirely
  // and advanced silently — the identical bug, one commit later. Anything that withholds
  // content belongs in this list.
  if (proposedChanges.length > 0 || defChanges.length > 0 || proposedAssumptions.length > 0 ||
      proposedCoreEdits.length > 0 || emissionConflicts.length > 0 ||
      addedLemmaCollisions.length > 0 || oeqAnswerCollisions.length > 0 ||
      unmatchedProofIds.length > 0) {
    // The payload's ONE carrier is `working.proposals` (set below, committed by
    // commitRound). The five per-kind mirror files are retired — every consumer
    // (apply, reviewers, packet rebuild) reads through `solve/proposals.ts`.
    const artifacts = [corePath, workingPath(ctx)];
    const blocks: string[] = [];
    if (proposedChanges.length > 0) {
      blocks.push(`${proposedChanges.length} STATEMENT change(s): ` + proposedChanges.map((c) => `${c.id}[${c.direction}]`).join(", "));
    }
    if (defChanges.length > 0) {
      blocks.push(`${defChanges.length} DEFINITION change(s): ` + defChanges.map((c) => `${c.id}[${c.direction}]`).join(", "));
    }
    if (proposedAssumptions.length > 0) {
      blocks.push(`${proposedAssumptions.length} NEW ASSUMPTION(s): ` + proposedAssumptions.map((a) => a.id).join(", "));
    }
    if (proposedCoreEdits.length > 0) {
      blocks.push(`${proposedCoreEdits.length} STRUCTURED CORE edit(s): ` + proposedCoreEdits.map((e) => e.kind).join(", "));
    }
    if (deferredProofs.length > 0) {
      blocks.push(`${deferredProofs.length} PROVISIONAL proof payload(s) preserved for adjudication`);
    }
    // Obligations isolated in the SAME round as a proposal used to be dropped here
    // (only finalizeRound wrote them), so the orchestrator adjudicated the proposals
    // never knowing an obstruction had been isolated, and the next round re-paid the
    // solver to re-derive it. Persist and announce them; deliberately NOT pushed into
    // `artifacts`, so runStage0Typed still routes this halt as a proposal checkpoint
    // (its open-gap branch keys on the artifact list).
    if (mr.openObligations.length > 0) {
      const obPath = openObligationsPath(ctx);
      await writeJsonAtomic(obPath, mr.openObligations);
      blocks.push(
        `${mr.openObligations.length} OPEN OBLIGATION(s) also isolated this round (kept in open_obligations.json): ` +
          mr.openObligations.map((o) => `${o.node_id} — ${o.what_is_open}`).join("; "),
      );
    }
    // One canonical adjudication input prevents reviewers from seeing only the
    // pre-proposal paper or only a pile of deltas. It contains the complete paper
    // rendered from this round's assembled core plus every same-round proposal and
    // every proof payload that supersedes stale core proof text for review.
    const reviewPacketPath = proposalReviewPacketPath(ctx);
    await writeJsonAtomic(
      reviewPacketPath,
      buildReviewPacket({
        core,
        working: next,
        proposedStatementChanges: proposedChanges,
        proposedDefinitionChanges: defChanges,
        proposedAssumptions,
        proposedCoreEdits,
        provisionalProofs: deferredProofs,
      }),
    );
    artifacts.push(reviewPacketPath);
    const closure = checkpointClosure(sctx, mr);
    const preflight = checkpointPreflight(core);
    if (preflight.length > 0) {
      blocks.push(formatPreflightViolations(preflight));
    }
    // Withheld cross-unit collisions. Surfaced here rather than thrown, so the round's
    // other work reaches the orchestrator and only the colliding ids need re-solving.
    if (emissionConflicts.length > 0) {
      blocks.push(formatSolveEmissionConflicts(emissionConflicts));
    }
    if (addedLemmaCollisions.length > 0) {
      blocks.push(
        `${addedLemmaCollisions.length} added helper(s) WITHHELD — the id already names a different claim (or a ` +
          `different citation source) in the core, so keeping either would leave a proof resting on a statement ` +
          `it did not argue. Rename the helper, change the existing node through proposed_statement_changes, or — ` +
          `for a reopened cited target — re-emit it byte-faithfully INCLUDING its exact source payload: ` +
          addedLemmaCollisions.map((c) => `${c.id} (from ${c.owner})`).join(", "),
      );
    }
    if (oeqAnswerCollisions.length > 0) {
      blocks.push(
        `${oeqAnswerCollisions.length} OEQ answer(s) WITHHELD — two resolutions claimed the same theorem id, ` +
          `which would duplicate a statement id in the core: ` + oeqAnswerCollisions.join(", "),
      );
    }
    // Informational only (never a checkpoint trigger): identical-claim re-proofs of
    // settled nodes skipped as no-ops, so emitted-vs-persisted counts reconcile.
    if (mr.duplicateReproofIds.length > 0) {
      blocks.push(
        `${mr.duplicateReproofIds.length} duplicate re-proof(s) of settled node(s) skipped as no-ops ` +
          `(canonical kept, alternative archived): ${[...new Set(mr.duplicateReproofIds)].join(", ")}`,
      );
    }
    if (!closure.ok) {
      blocks.push(formatClosureViolation(closure));
    } else if (closure.protoOnly.length > 0) {
      blocks.push(
        `ADVISORY — ${closure.protoOnly.length} node(s) in proto_core but absent from core ` +
          `(confirm the removal was intended): ${closure.protoOnly.join(", ")}`,
      );
    }
    // AUTHORITY: the payload lives in the working state, which every consumer reads
    // through `solve/proposals.ts`. Five independent per-kind mirror files were what
    // let `d0_apply_change` approve a statement change while discarding the proof
    // written for it, and let the D0.5 reviewers see none of the payload at all;
    // they are retired (operators inspect the payload in `d0_working.json` or the
    // review packet).
    next.proposals = {
      statements: proposedChanges,
      definitions: defChanges,
      assumptions: proposedAssumptions,
      coreEdits: proposedCoreEdits,
      proofs: deferredProofs,
    };
    blocks.push("canonical full-paper proposal review packet written");
    if (illegalDefTargets.length > 0) {
      blocks.push(`IGNORED ${illegalDefTargets.length} illegal class/unknown def change(s): ${illegalDefTargets.join(", ")}`);
    }
    if (unmatchedProofIds.length > 0) {
      blocks.push(
        `PLUMBING FAULT — ${unmatchedProofIds.length} emitted proof(s) named no core statement and were ` +
          `DROPPED: ${[...new Set(unmatchedProofIds)].join(", ")}. Reconcile the ids before re-dispatching; ` +
          `re-solving will not fix this.`,
      );
    }
    // The OUTER loop (runStage0Typed) decides whether to continue by re-reading the four
    // PROPOSAL arrays. A round whose only defect is WITHHELD content leaves all four
    // empty, so this checkpoint was swallowed and the loop continued — the fix inside this
    // function never reached the orchestrator. Drop a marker artifact, exactly as
    // open_obligations.json does, so the caller can see it without parsing the message.
    const withheld = {
      emission_conflicts: emissionConflicts,
      added_lemma_collisions: addedLemmaCollisions,
      oeq_answer_collisions: oeqAnswerCollisions,
      // Proofs emitted against ids present in NO core store. These were reported only
      // inside the incomplete-round checkpoint, so a round that discharged every target
      // AND dropped a proof completed clean with the drop invisible. That is the silent
      // id-mapping drop the project's own debugging rule calls out: what the agent EMITTED
      // must be reconciled against what was PERSISTED, and a count mismatch IS the bug.
      unmatched_proof_ids: [...new Set(unmatchedProofIds)],
    };
    // NOT included: `illegalDefTargets`. The audit read its absence from the guard as the
    // same accidental omission as the two collectors above, but the A6 class-definition
    // firewall is DELIBERATE and tested: a class-targeted def change is rejected, the run
    // discharges cleanly, and the completion message says it was ignored. That is a
    // documented contract, not a silent drop.
    if (Object.values(withheld).some((v) => v.length > 0)) {
      const wp = path.join(path.dirname(corePath), "withheld_content.json");
      await writeJsonAtomic(wp, withheld);
      artifacts.push(wp);
    }
    await commitRound();
    return {
      stage: "0",
      status: "checkpoint",
      advance: false,
      message:
        `Stage 0-SOLVE surfaced proposed change(s) for the D0 revise loop — ${blocks.join("; ")}. ` +
        `No proposal is auto-applied; the orchestrator must adjudicate and explicitly apply accepted ids before re-solving. ` +
        `Proposals written under ${path.dirname(corePath)}.`,
      artifacts,
    };
  }
  return null;
}


/** The round's terminal decision: open-gap checkpoint, incomplete-round
 *  checkpoint, or the clean discharge (bib heal → structural gate → commit). */
export async function finalizeRound(args: {
  ctx: PipelineContext;
  state: StateJson;
  sctx: SolveRoundContext;
  mr: SolveMergeResult;
  dispatchCount: number;
  commitRound: () => Promise<void>;
}): Promise<Stage0SolveResult | StageResult> {
  const { ctx, state, sctx, mr, dispatchCount, commitRound } = args;
  const { core, corePath, carriedMembers, next } = sctx;
  const { openObligations, unmatchedProofIds, illegalDefTargets, solved, addedLemmas } = mr;
  // OPEN GAP handling. An open obligation on an OPEN-ENDED QUESTION (`oeq:`) node is, by
  // design, a LEGITIMATE RESIDUAL — a research question the note deliberately leaves open
  // (e.g. tightness). It is recorded and surfaced to D0.5, which judges whether it is an
  // acceptable residual (the rubric tiers open OEQs explicitly), NOT a pre-D0.5 halt. An
  // open obligation on a THEOREM / LEMMA / PROPOSITION is a real pipeline gap the
  // orchestrator must address (guidance / a paper / a reframing) → HALT.
  const oeqIds = new Set(
    // why: OEQ discharge exemption is valid only for nodes with both OEQ kind and `oeq:` id.
    core.statements.filter((s) => s.kind === "openendedquestion" && s.id.startsWith("oeq:")).map((s) => s.id),
  );
  if (openObligations.length > 0) {
    const obPath = openObligationsPath(ctx);
    await writeJsonAtomic(obPath, openObligations);
    const blocking = openObligations.filter((o) => !oeqIds.has(o.node_id));
    if (blocking.length > 0) {
      await commitRound();
      return {
        stage: "0",
        status: "checkpoint",
        advance: false,
        message:
          `Stage 0-SOLVE hit ${blocking.length} GENUINE OPEN GAP(S) on proved-required node(s) — orchestrator guidance requested ` +
          `(provide a direction / paper / reframing via the D0 directive, then re-run; a blind re-solve will not close these):\n` +
          blocking
            .map((o) => `  - ${o.node_id}: OPEN = ${o.what_is_open}\n      obstruction: ${o.obstruction}\n      tried: ${o.attempted}`)
            .join("\n") +
          `\nWritten to ${obPath}.`,
        artifacts: [corePath, obPath],
      };
    }
    // All open obligations are on OEQ nodes → acknowledged-open residual(s); proceed to D0.5.
    state.design_decisions["d0_open_oeq_residuals"] =
      `Open-ended question(s) left as the note's acknowledged open problem for D0.5 review: ` +
      openObligations.map((o) => o.node_id).join(", ");
    console.warn(
      `[D0-SOLVE] ${openObligations.length} open obligation(s), all on OEQ nodes — recorded as residual open question(s); proceeding to D0.5.`,
    );
  } else {
    // A round with NO obligations must clear the previous round's file (only the
    // apply path swept it), or a checkpoint message that pointed an inspector at
    // open_obligations.json keeps presenting the stale diagnostics as current —
    // the same class as the withheld_content.json sweep.
    await rm(openObligationsPath(ctx), { force: true });
  }

  // Incomplete-round checkpoint: some targets left to-prove (proved part of the group, ran
  // out of steam). EXCLUDE ALL open-ended questions — an OEQ may be a legitimately-open
  // residual whether or not it carries an explicit open obligation; whether that is
  // acceptable is a D0.5 tiering decision, mirroring the discharge gate. Theorems / lemmas
  // / props left to-prove still trigger the incomplete-round checkpoint.
  void oeqIds;
  const undischarged = core.statements.filter(
    // why: a mismatched `kind:"openendedquestion"` on a theorem/proposition id is still dischargeable.
    (s) => s.status === "to-prove" && !(s.kind === "openendedquestion" && s.id.startsWith("oeq:")),
  );
  if (undischarged.length > 0) {
    await commitRound();
    return {
      stage: "0",
      status: "checkpoint",
      advance: false,
      message:
        `Stage 0-SOLVE incomplete round: proved ${solved} this round, ${undischarged.length} still open ` +
        `(${undischarged.slice(0, 8).map((s) => s.id).join(", ")}${undischarged.length > 8 ? ", …" : ""}). ` +
        `Progress saved to the working state — re-run --stop-after D0 to continue (proved nodes are reused)` +
        (solved === 0
          ? ". WARNING: zero new proofs this round — the agent may be stuck or under-scoping; inspect before re-running."
          : ".") +
        // An id-mapping fault must never masquerade as solver weakness. If proofs were
        // emitted against ids that exist in no core store, say so explicitly and first.
        (unmatchedProofIds.length > 0
          ? ` PLUMBING FAULT (not a solver failure): ${unmatchedProofIds.length} emitted proof(s) named ` +
            `no core statement and were DROPPED: ${[...new Set(unmatchedProofIds)].join(", ")}. ` +
            `Reconcile the ids before re-dispatching — re-solving will not fix this.`
          : ""),
      artifacts: [corePath],
    };
  }

  healMissingBibCites(core);

  // Everything discharged → sanity-gate the structure, then it's a clean discharge.
  runPostSolveGate(core);

  await commitRound();

  // The refuted node was re-derived (or restated) this clean round — consume the F3 witness so it
  // does not re-surface in unrelated future solves. A still-incomplete round returned above keeps it.
  delete state.flags.redo_math_witness;

  return {
    message:
      `Stage 0-SOLVE discharged ${solved} target(s) across ${dispatchCount} dispatched unit(s) ` +
      `(reused ${carriedMembers} carried member proof(s) + ${Object.keys(next.solved).length - solved - carriedMembers} lemma(s)), added ${addedLemmas} lemma(s)` +
      (illegalDefTargets.length > 0
        ? ` (ignored ${illegalDefTargets.length} illegal class/unknown def change: ${illegalDefTargets.join(", ")})`
        : "") +
      // Emitted-vs-persisted reconciliation: these re-emissions were skipped as no-ops
      // (identical claim, settled node — canonical proof kept, alternative archived).
      (mr.duplicateReproofIds.length > 0
        ? ` (skipped ${mr.duplicateReproofIds.length} duplicate re-proof(s) of settled node(s), canonical kept: ${[...new Set(mr.duplicateReproofIds)].join(", ")})`
        : ""),
    coreJsonPath: corePath,
    solved,
    addedLemmas,
    proposedChanges: [],
  };
}
