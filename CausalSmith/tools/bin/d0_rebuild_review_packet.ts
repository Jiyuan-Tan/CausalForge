#!/usr/bin/env -S npx tsx
/**
 * Rebuild a rejected/interrupted D0 proposal-review packet without re-running the
 * mathematical solver. This is a recovery tool, not an apply path: it reads the
 * assembled core, durable working cursor, and proposal payload; recovers proof
 * payloads banked as current partial progress; and writes the review packet PLUS
 * a normalized `d0_working.json:proposals` (the sole proposal carrier). It does
 * NOT touch proto_core, core.json, solved proofs, or the escalation journal.
 *
 * Usage: npx tsx tools/bin/d0_rebuild_review_packet.ts <qid> <spec>
 *   [--solve-json <path> --augment-live-proposals]
 */
import { readFile, realpath } from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import type { PipelineContext } from "../src/types.js";
import { CoreSchema } from "../src/discovery/core/schema.js";
import { protoCoreJsonPath } from "../src/discovery/stages/neg1_2_author.js";
import { writeJsonAtomic } from "../src/shared/json_atomic.js";
import { buildReviewPacket } from "../src/discovery/review_packet.js";
import { pinWhitespaceEquivalentCurrent, readRoundProposals } from "../src/discovery/solve/proposals.js";
import { assembleCore } from "../src/discovery/core/assemble.js";
import {
  proposalReviewPacketPath,
} from "../src/discovery/discovery_paths.js";
import {
  loadWorkingState,
  proposalRevision,
  readEscalationLog,
  saveWorkingState,
} from "../src/discovery/stages/d0_working.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import {
  assertClaimChangingStatementReplacementsArePaired,
  readSolveUnitOutput,
} from "../src/discovery/solve/dispatch.js";
import { reusableOeqAnswerMatches } from "../src/discovery/solve/merge.js";
import { openSolveTarget } from "../src/discovery/solve/context.js";
import { coreRevision, definitionRevision, statementRevision } from "../src/discovery/core/revision.js";
import { coreEditTarget } from "../src/discovery/stages/d0_apply.js";
import { resolveRequiredCoreEditMandates } from "../src/discovery/solve/mandates.js";
import { loadState } from "../src/state.js";

const canonicalBag = (items: readonly unknown[]): string[] =>
  items.map((item) => JSON.stringify(item)).sort();

function exactBagMatches(a: readonly unknown[], b: readonly unknown[]): boolean {
  return JSON.stringify(canonicalBag(a)) === JSON.stringify(canonicalBag(b));
}

async function main(): Promise<void> {
  const [qid, spec] = process.argv.slice(2);
  const solveArg = process.argv.indexOf("--solve-json");
  const solveJsonPath = solveArg === -1 ? undefined : process.argv[solveArg + 1];
  const repairUnpairedClaimEdits = process.argv.includes("--repair-unpaired-claim-edits");
  const augmentLiveProposals = process.argv.includes("--augment-live-proposals");
  const includeDurableProofIds = process.argv.flatMap((arg, index, args) =>
    arg === "--include-durable-proof" && typeof args[index + 1] === "string" ? [args[index + 1]] : []);
  if (!qid || !spec || (solveArg !== -1 && !solveJsonPath)) {
    throw new Error(
      "Usage: d0_rebuild_review_packet.ts <qid> <spec> [--solve-json <path>] " +
      "[--augment-live-proposals]",
    );
  }
  if (includeDurableProofIds.length > 0) {
    throw new Error(
      "--include-durable-proof is retired: a preimage proof cannot certify a carrier's semantic postimage; " +
      "rerun the normal D0 solve/merge path",
    );
  }
  const ctx: PipelineContext = {
    repoRoot: findCausalSmithRoot(process.cwd()), qid, specialization: spec, dryRun: false, resume: true,
  };
  const proto = CoreSchema.parse(JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8")));
  const working = await loadWorkingState(ctx);
  if (!working) throw new Error("Cannot rebuild a D0 review packet without d0_working.json");
  const escalationLog = await readEscalationLog(ctx);
  if (escalationLog.some((entry) => (entry.required_core_edits?.length ?? 0) > 0)) {
    throw new Error(
      "D0 recovery found legacy required_core_edits with no recorded revision/snapshot basis; " +
      "re-adjudicate them with d0_directive --require-core-edit",
    );
  }
  const consumed = Math.min(working.escalation_entries_consumed ?? 0, escalationLog.length);
  const pendingMandates = escalationLog.slice(consumed)
    .flatMap((entry) => entry.required_core_edit_mandates ?? []);
  const pendingCancellations = escalationLog.slice(consumed)
    .flatMap((entry) => entry.cancelled_core_edit_mandates ?? []);
  const state = await loadState(ctx.repoRoot, qid, spec);
  const mandates = resolveRequiredCoreEditMandates({
    mandates: [...(working.required_core_edit_mandates ?? []), ...pendingMandates],
    cancellations: pendingCancellations,
    core: proto,
    working,
    proposalRevision: proposalRevision(state),
  });
  // Recovery becomes the durable carrier if the live solve was interrupted before
  // commitRound copied an unconsumed journal mandate onto the working cursor.
  working.required_core_edit_mandates = mandates;
  const mandatedTargets = new Set(mandates.map((mandate) => coreEditTarget(mandate.edit)));
  // A structural-gate failure can prevent core.json publication after a valid
  // proposal apply. Reconstruct the adjudication view through the SAME pure
  // render the solve commit uses (Phase 1 of the store consolidation — the old
  // hand-rolled derivation here was the seed for `assembleCore` and would only
  // drift from it); never fall back to an older rendered paper.
  // Recovery must validate revisions and choose replacement bytes from the
  // same authoritative generation. A published core may lag an interrupted
  // cursor; rebuilding it from proto+working prevents an old revision from
  // authorizing a repin onto newer durable claim bytes.
  const core = CoreSchema.parse(assembleCore(proto, working));

  const currentStatementById = new Map(core.statements.map((statement) => [statement.id, statement] as const));
  // Match apply's authority exactly: a frozen proto node wins; only an agent-added
  // statement absent from proto is sourced from the durable working record.  The
  // published core is an adjudication VIEW and can lag an interrupted cursor update.
  const durableStatementCurrentById = new Map(
    proto.statements.map((statement) => [statement.id, statement.statement] as const),
  );
  for (const record of Object.values(working.solved)) {
    if (record.node && !durableStatementCurrentById.has(record.node.id)) {
      durableStatementCurrentById.set(record.node.id, record.node.statement);
    }
  }
  const durableDefinitionCurrentById = new Map(
    proto.definitions
      .filter((definition) => definition.by_member_properties === undefined)
      .map((definition) => [definition.id, definition.construction] as const),
  );
  const durableDefinitionById = new Map(
    proto.definitions
      .filter((definition) => definition.by_member_properties === undefined)
      .map((definition) => [definition.id, definition] as const),
  );
  // Sole carrier: the proposals payload on the working cursor (the per-kind
  // mirror files are retired 2026-07-20).
  let roundProposals = await readRoundProposals(ctx, working);
  const currentBasisRevision = coreRevision(core);
  // Capture the original live carrier before any recovery-side evidence addition.
  // Final evidence checks below compare against this exact structural authority.
  const carriedMandateEdits = roundProposals.coreEdits
    .filter((edit) => mandatedTargets.has(coreEditTarget(edit)));
  const resolvedMandateEdits = mandates.map((mandate) => mandate.edit);
  let recoveredSolveSource: string | undefined;
  if (solveJsonPath) {
    const absoluteSolvePath = path.resolve(solveJsonPath);
    const canonicalSolvePath = await realpath(absoluteSolvePath);
    const discoveryDir = path.dirname(proposalReviewPacketPath(ctx));
    const liveProposalCount =
      roundProposals.statements.length + roundProposals.definitions.length +
      roundProposals.assumptions.length + roundProposals.coreEdits.length;
    if (!augmentLiveProposals || liveProposalCount === 0) {
      throw new Error(
        "--solve-json may only augment an existing capability-projected live bundle; " +
        "pass --augment-live-proposals. Lost-bundle reconstruction from an unauthenticated solve file is retired",
      );
    }
    if (process.argv.includes("--replace-live-proposals")) {
      throw new Error("--replace-live-proposals is retired; recovery must preserve the authenticated live bundle");
    }
    if (repairUnpairedClaimEdits) {
      throw new Error(
        "--repair-unpaired-claim-edits is retired for raw solve files; live ingest now rejects incomplete claim transactions",
      );
    }
    if (
      canonicalSolvePath !== absoluteSolvePath ||
      path.dirname(canonicalSolvePath) !== discoveryDir ||
      !/^solve_[A-Za-z0-9_]+\.json$/.test(path.basename(canonicalSolvePath))
    ) {
      throw new Error("--solve-json must name a non-symlink canonical solve_*.json artifact in this run's discovery directory");
    }
    // The agent's solve output is dense TeX (statements + proof_tex). Read it through
    // the same defense as the live solve boundary in `solve/dispatch.ts`; a raw parse
    // here would fail the recovery on the very escape class it exists to recover from.
    // Use the production reader so TeX companion references are resolved exactly
    // as they were in the live solve. Recovery previously parsed the JSON carrier
    // directly, making every valid companion-backed artifact unrecoverable.
    const recoveredOutput = await readSolveUnitOutput(absoluteSolvePath, path.basename(absoluteSolvePath));
    assertClaimChangingStatementReplacementsArePaired(recoveredOutput, core.statements);
    const proofIdCounts = new Map<string, number>();
    for (const proof of recoveredOutput.proofs) {
      proofIdCounts.set(proof.id, (proofIdCounts.get(proof.id) ?? 0) + 1);
    }
    const duplicateProofIds = [...proofIdCounts].filter(([, count]) => count > 1).map(([id]) => id);
    if (duplicateProofIds.length > 0) {
      throw new Error(
        `--solve-json contains duplicate proof id(s): ${duplicateProofIds.join(", ")}; ` +
        "recovery never merges proof payloads or intent bits",
      );
    }
    if (recoveredOutput.open_obligations.length > 0) {
      throw new Error(
        "--solve-json recovery supports proposal checkpoints only; open obligations require a normal merge",
      );
    }
    for (const statement of recoveredOutput.added_lemmas) {
      const durable = working.solved[statement.id];
      const canonical = proto.statements.find((candidate) => candidate.id === statement.id) ?? durable?.node;
      const durableStatement = canonical
        ? { ...canonical, proof_tex: durable?.proof_tex ?? canonical.proof_tex }
        : null;
      if (!durableStatement || !reusableOeqAnswerMatches(durableStatement, statement)) {
        throw new Error(
          `--solve-json added statement ${statement.id} is not an exact durable re-emission; ` +
          "a normal merge is required",
        );
      }
    }
    // A failed merge may have received an exact re-emission of an already mapped
    // OEQ answer alongside the proposal. Verify that reuse conservatively, then keep
    // the existing durable mapping; recovery must not install a theorem transition.
    for (const resolution of recoveredOutput.resolved_oeqs) {
      const mapping = working.resolved_oeqs?.[resolution.source_id];
      const theoremId = typeof mapping === "string" ? mapping : mapping?.theorem_id;
      const durable = working.solved[resolution.theorem.id];
      const overlay = recoveredOutput.proposed_statement_changes
        .find((change) => change.id === resolution.theorem.id);
      const durableTheorem = durable?.node
        ? {
            ...durable.node,
            proof_tex: durable.proof_tex,
            ...(overlay ? { statement: overlay.proposed } : {}),
          }
        : null;
      if (
        theoremId !== resolution.theorem.id ||
        durable?.partial === true ||
        !durableTheorem ||
        !reusableOeqAnswerMatches(durableTheorem, resolution.theorem)
      ) {
        throw new Error(
          `--solve-json OEQ resolution ${resolution.source_id}->${resolution.theorem.id} is not an exact ` +
          "reuse of the settled durable answer after its declared statement overlay",
        );
      }
    }
    // Prose is not a proposal carrier. Permit only byte-identical no-op echoes in a
    // mechanical recovery; any real prose delta must pass through the normal merge.
    const updates = recoveredOutput.prose_updates;
    if (updates) {
      const same = (a: unknown, b: unknown): boolean => JSON.stringify(a) === JSON.stringify(b);
      for (const field of ["tldr", "related_work", "interpretation", "technical_internal_limitation", "honest_scope"] as const) {
        if (updates[field] !== undefined && !same(core[field], updates[field])) {
          throw new Error(`--solve-json contains a non-no-op prose update for ${field}`);
        }
      }
      for (const [field, value] of Object.entries(updates.project_justification ?? {})) {
        if (!same(core.project_justification?.[field as keyof typeof core.project_justification], value)) {
          throw new Error(`--solve-json contains a non-no-op prose update for project_justification.${field}`);
        }
      }
      for (const [field, value] of Object.entries(updates.sampling_model ?? {})) {
        if (!same(core.sampling_model?.[field], value)) {
          throw new Error(`--solve-json contains a non-no-op prose update for sampling_model.${field}`);
        }
      }
      for (const note of updates.statement_notes ?? []) {
        const statement = core.statements.find((candidate) => candidate.id === note.id);
        if (!statement || ["justification", "gap", "consumer"].some((field) =>
          note[field as keyof typeof note] !== undefined &&
          !same(statement[field as keyof typeof statement], note[field as keyof typeof note]))) {
          throw new Error(`--solve-json contains a non-no-op statement note for ${note.id}`);
        }
      }
    }
    // The live carrier is the ownership- and capability-projected authority. A raw
    // artifact may supply a lost cited receipt only if its COMPLETE proposal/proof
    // bundle is byte-identical to that authority (apart from exact orchestrator
    // mandates, which never came from the worker). One overlapping proof is not an
    // authentication token: a stale/foreign unit must not smuggle a receipt into an
    // unrelated current postimage.
    const requireExactBag = (label: string, raw: readonly unknown[], live: readonly unknown[]): void => {
      if (!exactBagMatches(raw, live)) {
        throw new Error(
          `--solve-json ${label} does not exactly match the complete capability-projected live bundle`,
        );
      }
    };
    requireExactBag("proof set", recoveredOutput.proofs, roundProposals.proofs);
    requireExactBag(
      "statement-change set",
      recoveredOutput.proposed_statement_changes,
      roundProposals.statements,
    );
    requireExactBag(
      "definition-change set",
      recoveredOutput.proposed_definition_changes,
      roundProposals.definitions,
    );
    requireExactBag("assumption set", recoveredOutput.proposed_assumptions, roundProposals.assumptions);
    requireExactBag(
      "core-edit set",
      recoveredOutput.proposed_core_edits,
      roundProposals.coreEdits.filter((edit) => !mandatedTargets.has(coreEditTarget(edit))),
    );
    if (recoveredOutput.proofs.length === 0) {
      throw new Error("--solve-json augmentation requires a nonempty exact live-bundle proof set");
    }
    const recoveredCitations = recoveredOutput.added_lemmas.filter((statement) => statement.status === "cited");
    if (recoveredCitations.length > 0) {
      throw new Error(
        "--solve-json cannot recover cited-source receipts: raw worker artifacts carry no durable " +
        "capability-projected receipt manifest; rerun the normal D0 solve/merge path",
      );
    }
    recoveredSolveSource = absoluteSolvePath;
  }
  // Run these guards against the FINAL candidate evidence set. In particular,
  // --include-durable-proof must not turn a previously proofless, unsealed carrier
  // into evidence for a newly recovered symbol/definition mandate.
  const hasEvidence = roundProposals.proofs
    .some((proof) => !mandatedTargets.has(proof.id)) ||
    (roundProposals.citationRevalidations?.length ?? 0) > 0;
  // The basis guard covers EVERY nonempty live bundle, not just evidence-bearing
  // ones (audit 2026-08-30, blocker 2): the reseal below stamps a fresh
  // `basis_revision` and rebinds definition `based_on_revision` to the CURRENT
  // core, so recovering a proposal-only bundle across an intervening store change
  // would forge freshness for a postimage authored against a different basis —
  // apply would then overwrite the intervening change with stale metadata.
  const hasLiveProposalContent = hasEvidence ||
    roundProposals.statements.length > 0 ||
    roundProposals.definitions.length > 0 ||
    roundProposals.assumptions.length > 0 ||
    roundProposals.coreEdits.some((edit) => !mandatedTargets.has(coreEditTarget(edit)));
  // A MISSING basis is the legacy pre-seal cursor this CLI exists to recover —
  // but ONLY for a bundle of plain proposed-statement changes, the one channel
  // whose staleness is a complete PER-CHANGE guard (pinCurrent + apply's exact
  // current/revision checks; see the repin test). Every other channel lacks an
  // apply-side preimage guard covering all fields it may overwrite (assumption/
  // symbol/bibliography/comparator edits, definition-delete; statementRevision
  // hashes only id/kind/statement/status, so even statement-replace metadata
  // postimages are unguarded), and the reseal below stamps a fresh
  // basis_revision — recovering such an unsealed bundle would forge freshness
  // for content authored against an unknown basis (audit 2026-08-30, blocker 2
  // and its two delta iterations). Evidence-bearing bundles keep the strict
  // rule: missing counts as mismatch.
  const beyondStatementLane =
    roundProposals.definitions.length > 0 ||
    roundProposals.assumptions.length > 0 ||
    roundProposals.coreEdits.some((edit) => !mandatedTargets.has(coreEditTarget(edit)));
  const staleBasis = hasEvidence
    ? roundProposals.basis_revision !== currentBasisRevision
    : roundProposals.basis_revision !== undefined
      ? roundProposals.basis_revision !== currentBasisRevision
      : beyondStatementLane;
  if (hasLiveProposalContent && staleBasis) {
    throw new Error(
      `Refusing to reseal D0 proposals: live proposal basis ${roundProposals.basis_revision ?? "(missing)"} ` +
      `does not match current assembled basis ${currentBasisRevision}; rerun normal D0 solve/merge`,
    );
  }
  // Recovery reads the cursor STRUCTURALLY (readRoundProposals re-attaches types
  // without a schema pass), so a corrupt or hand-edited record could omit the
  // mandatory `current`/`proposed` echoes — exactly the fields the statement
  // lane's per-change staleness guards key on. Refuse rather than reseal.
  for (const change of roundProposals.statements) {
    if (typeof change.current !== "string" || change.current.trim().length === 0 ||
        typeof change.proposed !== "string" || change.proposed.trim().length === 0) {
      throw new Error(
        `Refusing to reseal D0 proposals: statement change ${change.id} lacks the mandatory ` +
        `current/proposed echo; rerun normal D0 solve/merge`,
      );
    }
  }
  if (hasEvidence && !exactBagMatches(carriedMandateEdits, resolvedMandateEdits)) {
    throw new Error(
      "Refusing to enlarge or change an evidence-bearing D0 bundle with recovered mandates; " +
      "rerun normal D0 solve/merge so proofs and citations are authored against the complete mandate set",
    );
  }
  const normalizedCurrentEchoIds: string[] = [];
  const pinCurrent = <T extends { id: string; current?: string; based_on_revision?: string }>(
    change: T,
    durableCurrent: string | undefined,
    validRevisions: readonly string[],
  ): T => {
    const pinned = pinWhitespaceEquivalentCurrent(change, durableCurrent, validRevisions);
    if (pinned !== change) normalizedCurrentEchoIds.push(change.id);
    return pinned;
  };
  roundProposals = {
    ...roundProposals,
    statements: roundProposals.statements.map((change) => {
      const target = currentStatementById.get(change.id);
      return pinCurrent(
        change,
        durableStatementCurrentById.get(change.id),
        target ? [statementRevision(target), statementRevision(openSolveTarget(target))] : [],
      );
    }),
    definitions: roundProposals.definitions.map((change) => {
      const target = durableDefinitionById.get(change.id);
      const pinned = pinCurrent(
        change,
        durableDefinitionCurrentById.get(change.id),
        target ? [change.based_on_revision ?? definitionRevision(target, core)] : [],
      );
      // Mirror live merge's pipeline-owned complete-definition revision binding.
      // A companion-backed recovery may carry the worker-visible local revision,
      // but apply authorizes the pair against the current assembled semantic basis.
      return target ? { ...pinned, based_on_revision: definitionRevision(target, core) } : pinned;
    }),
    coreEdits: roundProposals.coreEdits.map((edit) => {
      if (edit.kind !== "definition-replace") return edit;
      const target = durableDefinitionById.get(edit.id);
      return target ? { ...edit, based_on_revision: definitionRevision(target, core) } : edit;
    }),
  };
  const existingProofs = roundProposals.proofs as Array<{ id: string; proof_tex: string; argues_proposed?: boolean }>;
  const proofById = new Map<string, { proof_tex: string; argues_proposed?: boolean }>();
  const addProof = (id: string, proofTex: string, source: string, arguesProposed = false): void => {
    if (!id || !proofTex.trim()) return;
    if (proofById.has(id)) {
      throw new Error(`Duplicate ${source} proof for ${id}; recovery never merges payloads or intent bits`);
    }
    proofById.set(id, {
      proof_tex: proofTex,
      ...(arguesProposed ? { argues_proposed: true } : {}),
    });
  };
  for (const proof of existingProofs) {
    if (mandatedTargets.has(proof.id)) continue;
    if (currentStatementById.get(proof.id)?.kind === "openendedquestion") continue;
    addProof(proof.id, proof.proof_tex, "proposal-artifact", proof.argues_proposed === true);
  }

  const currentIds = new Set(currentStatementById.keys());
  const recovered: string[] = [];
  const durablePartialProofIdsIncluded: string[] = [];
  const openQuestionPartialResults: Array<{ id: string; partial_result: string }> = [];
  for (const [id, record] of Object.entries(working.solved)) {
    if (mandatedTargets.has(id)) continue;
    if (!record.partial || !currentIds.has(id) || !record.proof_tex.trim()) continue;
    if (currentStatementById.get(id)?.kind === "openendedquestion") {
      openQuestionPartialResults.push({ id, partial_result: record.proof_tex });
      continue;
    }
    // An arbitrary partial_result is solver context, not completed proof evidence.
    // Only the capability-projected live carrier or an explicitly selected,
    // preimage-valid durable proof may enter proposals.proofs for apply promotion.
    durablePartialProofIdsIncluded.push(id);
  }
  // Defence in depth: the collection loops above already skip mandated targets, but
  // quarantine again at the serialization boundary so a future recovery source cannot
  // reintroduce a proof/claim mutation beside an exact mandated operation.
  const provisionalProofs = [...proofById]
    .filter(([id]) => !mandatedTargets.has(id))
    .map(([id, proof]) => ({ id, ...proof }));
  // Preserve the original settled record and snapshot as provenance. Rebuilding a
  // packet is not an apply transaction: rejection/discard must leave reusable support
  // reusable. Atomic apply will reopen it if selected edits invalidate its basis and
  // then promote these reviewed bytes against the selected postimage.

  const proposedStatementChanges = roundProposals.statements
    .filter((change) => !mandatedTargets.has(change.id)) as unknown[];
  const proposedDefinitionChanges = roundProposals.definitions
    .filter((change) => !mandatedTargets.has(change.id)) as unknown[];
  const proposedAssumptions = roundProposals.assumptions
    .filter((assumption) => !mandatedTargets.has(assumption.id)) as unknown[];
  const proposedCoreEdits = [
    ...mandates.map((mandate) => structuredClone(mandate.edit) as Record<string, any>),
    ...roundProposals.coreEdits
      .filter((edit) => !mandatedTargets.has(coreEditTarget(edit))) as unknown as Array<Record<string, any>>,
  ];
  if (
    proposedStatementChanges.length === 0 && proposedDefinitionChanges.length === 0 &&
    proposedAssumptions.length === 0 && proposedCoreEdits.length === 0
  ) throw new Error("No D0 proposal checkpoint exists to rebuild");

  // `statement-replace` is a structural-node edit. stage0_apply intentionally
  // requires its statement/status/proof fields to equal the immutable original;
  // the actual revised proof travels through provisional_proofs. Some workers
  // redundantly copy the new proof into both channels. Normalize that duplication
  // only when the durable working proof is byte-identical, otherwise fail closed.
  const protoStatementById = new Map(proto.statements.map((statement) => [statement.id, statement] as const));
  const normalizedStatementReplaceProofIds: string[] = [];
  for (const edit of proposedCoreEdits) {
    if (edit.kind !== "statement-replace" || typeof edit.id !== "string" || !edit.proposed) continue;
    const original = protoStatementById.get(edit.id) ?? working.solved[edit.id]?.node;
    if (!original) continue;
    const proposedProof = typeof edit.proposed.proof_tex === "string" ? edit.proposed.proof_tex : undefined;
    const durableProof = working.solved[edit.id]?.proof_tex;
    const packetProof = proofById.get(edit.id)?.proof_tex;
    // Absence is the canonical statement-replace contract: apply carries the
    // authoritative proof independently. Only a redundantly authored proof needs
    // normalization/verification below.
    if (proposedProof === undefined) continue;
    if (proposedProof === original.proof_tex) {
      if (durableProof && durableProof !== (original.proof_tex ?? "")) {
        normalizedStatementReplaceProofIds.push(edit.id);
      }
      continue;
    }
    if (!proposedProof || (proposedProof !== durableProof && proposedProof !== packetProof)) {
      throw new Error(
        `statement-replace ${edit.id} changes immutable proof_tex without a byte-identical durable proof payload`,
      );
    }
    if (original.proof_tex === undefined) delete edit.proposed.proof_tex;
    else edit.proposed.proof_tex = original.proof_tex;
    normalizedStatementReplaceProofIds.push(edit.id);
  }

  const packetPath = proposalReviewPacketPath(ctx);
  // Persist the normalized payload back onto the sole carrier.
  const recoveredCore = CoreSchema.parse(assembleCore(proto, working));
  working.proposals = {
    // A rebuilt packet is a newly sealed adjudication view. Preserve the same
    // stale-write guard as a normal solve commit; dropping it makes every
    // definition-containing recovery bundle mechanically unapplyable.
    basis_revision: coreRevision(recoveredCore),
    statements: proposedStatementChanges,
    definitions: proposedDefinitionChanges,
    assumptions: proposedAssumptions,
    coreEdits: proposedCoreEdits,
    proofs: provisionalProofs,
    citationRevalidations: roundProposals.citationRevalidations ?? [],
  };
  await saveWorkingState(ctx, working);
  await writeJsonAtomic(
    packetPath,
    buildReviewPacket({
      core: recoveredCore,
      working,
      proposedStatementChanges,
      proposedDefinitionChanges,
      proposedAssumptions,
      proposedCoreEdits,
      requiredCoreEditMandates: working.required_core_edit_mandates,
      provisionalProofs,
      citationRevalidations: roundProposals.citationRevalidations ?? [],
      recovery: {
        mode: "mechanical-no-solver",
        ...(recoveredSolveSource ? { recovered_solve_source: recoveredSolveSource } : {}),
        current_core_source: "current-proto-plus-durable-working-state",
        recovered_partial_proof_ids: recovered,
        durable_partial_proof_ids_included: durablePartialProofIdsIncluded,
        explicitly_included_durable_proof_ids: [],
        normalized_current_echo_ids: normalizedCurrentEchoIds,
        normalized_statement_replace_proof_ids: normalizedStatementReplaceProofIds,
        proto_statement_ids: proto.statements.map((statement) => statement.id),
      },
    }),
  );
  console.log(JSON.stringify({
    packet: packetPath,
    proposals_carrier: "d0_working.json:proposals",
    recovered,
    normalized_current_echo_ids: normalizedCurrentEchoIds,
    normalized_statement_replace_proof_ids: normalizedStatementReplaceProofIds,
  }, null, 2));
}

main().catch((error: unknown) => {
  console.error(`d0_rebuild_review_packet: ${error instanceof Error ? error.message : String(error)}`);
  process.exitCode = 1;
});
