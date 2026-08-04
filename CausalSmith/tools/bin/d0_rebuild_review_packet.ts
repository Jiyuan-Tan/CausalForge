#!/usr/bin/env -S npx tsx
/**
 * Rebuild a rejected/interrupted D0 proposal-review packet without re-running the
 * mathematical solver. This is a recovery tool, not an apply path: it reads the
 * assembled core, durable working cursor, and proposal payload; recovers proof
 * payloads banked as current partial progress; and writes the review packet PLUS
 * a normalized `d0_working.json:proposals` (the sole proposal carrier). It does
 * NOT touch proto_core, core.json, solved proofs, or the escalation journal.
 *
 * Usage: npx tsx tools/bin/d0_rebuild_review_packet.ts <qid> <spec> [--solve-json <path>]
 */
import { readFile } from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import { artifactPath } from "../src/paths.js";
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
import { SolveUnitOutputSchema } from "../src/discovery/solve/schemas.js";
import { parseRepairedModelJson } from "../src/discovery/core/core_io.js";
import { reusableOeqAnswerMatches } from "../src/discovery/solve/merge.js";
import { openSolveTarget } from "../src/discovery/solve/context.js";
import { definitionRevision, statementRevision } from "../src/discovery/core/revision.js";
import { coreEditTarget } from "../src/discovery/stages/d0_apply.js";
import { resolveRequiredCoreEditMandates } from "../src/discovery/solve/mandates.js";
import { loadState } from "../src/state.js";



async function main(): Promise<void> {
  const [qid, spec] = process.argv.slice(2);
  const solveArg = process.argv.indexOf("--solve-json");
  const solveJsonPath = solveArg === -1 ? undefined : process.argv[solveArg + 1];
  if (!qid || !spec || (solveArg !== -1 && !solveJsonPath)) {
    throw new Error("Usage: d0_rebuild_review_packet.ts <qid> <spec> [--solve-json <path>]");
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
  let recoveredSolveSource: string | undefined;
  if (solveJsonPath) {
    const absoluteSolvePath = path.resolve(solveJsonPath);
    // The agent's solve output is dense TeX (statements + proof_tex). Read it through
    // the same defense as the live solve boundary in `solve/dispatch.ts`; a raw parse
    // here would fail the recovery on the very escape class it exists to recover from.
    const recoveredOutput = SolveUnitOutputSchema.parse(
      parseRepairedModelJson(await readFile(absoluteSolvePath, "utf8"), absoluteSolvePath),
    );
    if (recoveredOutput.open_obligations.length > 0) {
      throw new Error(
        "--solve-json recovery supports proposal checkpoints only; open obligations require a normal merge",
      );
    }
    for (const statement of recoveredOutput.added_lemmas) {
      const durable = working.solved[statement.id];
      const durableStatement = durable?.node
        ? { ...durable.node, proof_tex: durable.proof_tex }
        : null;
      if (
        durable?.partial === true ||
        !durableStatement ||
        !reusableOeqAnswerMatches(durableStatement, statement)
      ) {
        throw new Error(
          `--solve-json added statement ${statement.id} is not an exact settled durable re-emission; ` +
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
    // OWNERSHIP. Every guard above validates `added_lemmas` / `resolved_oeqs` /
    // `prose_updates` against this run's durable cursor — but the payload actually
    // INSTALLED below was validated against nothing, and `SolveUnitOutputSchema` carries
    // no qid. A solve file recovered from a DIFFERENT run whose proposals happen to touch
    // none of those three sections passes every check, replaces this run's live bundle
    // wholesale, and its proposal proofs are archived as `proposal-cleared`. Require each
    // proposed id to name an object this run actually has.
    const knownIds = new Set<string>([
      ...core.statements.map((s) => s.id),
      ...core.definitions.map((d) => d.id),
      ...core.assumptions.map((a) => a.id),
      ...Object.keys(working.solved ?? {}),
    ]);
    const foreign = [
      ...recoveredOutput.proposed_statement_changes.map((c) => c.id),
      ...recoveredOutput.proposed_definition_changes.map((c) => c.id),
      ...recoveredOutput.proposed_assumptions.map((c) => c.id),
    ].filter((id) => !knownIds.has(id));
    if (foreign.length > 0) {
      throw new Error(
        `--solve-json proposes changes to ids this run does not define (${[...new Set(foreign)].join(", ")}); ` +
        "the file almost certainly belongs to a different qid — refusing to replace this run's proposal bundle",
      );
    }
    // A live bundle is adjudicated state. Recovery is for a bundle that was LOST, so
    // silently overwriting a present one destroys decisions that were already made.
    const liveProposalCount =
      (working.proposals?.statements?.length ?? 0) +
      (working.proposals?.definitions?.length ?? 0) +
      (working.proposals?.assumptions?.length ?? 0) +
      (working.proposals?.coreEdits?.length ?? 0);
    if (liveProposalCount > 0 && !process.argv.includes("--replace-live-proposals")) {
      throw new Error(
        `--solve-json would replace ${liveProposalCount} live proposal(s) already on the working cursor. ` +
        "Recovery is for a LOST bundle; pass --replace-live-proposals to overwrite deliberately",
      );
    }
    const changedStatementIds = new Set(
      recoveredOutput.proposed_statement_changes.map((change) => change.id),
    );
    roundProposals = {
      statements: recoveredOutput.proposed_statement_changes,
      definitions: recoveredOutput.proposed_definition_changes,
      assumptions: recoveredOutput.proposed_assumptions,
      coreEdits: recoveredOutput.proposed_core_edits,
      proofs: recoveredOutput.proofs.filter((proof) =>
        proof.argues_proposed === true && changedStatementIds.has(proof.id)),
    };
    // The filter mirrors apply's `claimChangedIds`, which is correct — but every OTHER
    // proof in the recovered file is real new mathematics the failed merge produced, and
    // dropping it silently leaves the node open to be re-solved at full cost with no
    // record that a proof existed. Name them.
    const droppedProofIds = recoveredOutput.proofs
      .filter((proof) => !(proof.argues_proposed === true && changedStatementIds.has(proof.id)))
      .map((proof) => proof.id);
    if (droppedProofIds.length > 0) {
      console.warn(
        `[causalsmith] --solve-json recovery kept only proposal-arguing proofs; ` +
        `${droppedProofIds.length} other proof(s) in the file were NOT installed: ${droppedProofIds.join(", ")}. ` +
        "Re-run a normal merge if those proofs are needed.",
      );
    }
    recoveredSolveSource = absoluteSolvePath;
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
      return pinCurrent(
        change,
        durableDefinitionCurrentById.get(change.id),
        target ? [definitionRevision(target)] : [],
      );
    }),
  };
  const mandatedTargets = new Set(mandates.map((mandate) => coreEditTarget(mandate.edit)));
  const existingProofs = roundProposals.proofs as Array<{ id: string; proof_tex: string; argues_proposed?: boolean }>;
  const proofById = new Map<string, { proof_tex: string; argues_proposed?: boolean }>();
  const addProof = (id: string, proofTex: string, source: string, arguesProposed = false): void => {
    if (!id || !proofTex.trim()) return;
    const prior = proofById.get(id);
    if (prior !== undefined && prior.proof_tex !== proofTex) {
      throw new Error(`Conflicting ${source} proof for ${id}; refusing to choose one payload`);
    }
    proofById.set(id, {
      proof_tex: proofTex,
      ...((prior?.argues_proposed || arguesProposed) ? { argues_proposed: true } : {}),
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
    durablePartialProofIdsIncluded.push(id);
    if (!proofById.has(id)) recovered.push(id);
    addProof(id, record.proof_tex, "durable-working-state");
  }
  // Defence in depth: the collection loops above already skip mandated targets, but
  // quarantine again at the serialization boundary so a future recovery source cannot
  // reintroduce a proof/claim mutation beside an exact mandated operation.
  const provisionalProofs = [...proofById]
    .filter(([id]) => !mandatedTargets.has(id))
    .map(([id, proof]) => ({ id, ...proof }));

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
  working.proposals = {
    statements: proposedStatementChanges,
    definitions: proposedDefinitionChanges,
    assumptions: proposedAssumptions,
    coreEdits: proposedCoreEdits,
    proofs: provisionalProofs,
  };
  await saveWorkingState(ctx, working);
  await writeJsonAtomic(
    packetPath,
    buildReviewPacket({
      core,
      working,
      proposedStatementChanges,
      proposedDefinitionChanges,
      proposedAssumptions,
      proposedCoreEdits,
      requiredCoreEditMandates: working.required_core_edit_mandates,
      provisionalProofs,
      recovery: {
        mode: "mechanical-no-solver",
        ...(recoveredSolveSource ? { recovered_solve_source: recoveredSolveSource } : {}),
        current_core_source: "current-proto-plus-durable-working-state",
        recovered_partial_proof_ids: recovered,
        durable_partial_proof_ids_included: durablePartialProofIdsIncluded,
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
