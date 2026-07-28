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
import { existsSync } from "node:fs";
import { readFile } from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import { artifactPath } from "../src/paths.js";
import type { PipelineContext } from "../src/types.js";
import { CoreSchema } from "../src/discovery/core/schema.js";
import { coreJsonPath } from "../src/discovery/stages/d0_core.js";
import { protoCoreJsonPath } from "../src/discovery/stages/neg1_2_author.js";
import { writeJsonAtomic } from "../src/shared/json_atomic.js";
import { buildReviewPacket } from "../src/discovery/review_packet.js";
import { readRoundProposals } from "../src/discovery/solve/proposals.js";
import { solvedStatus } from "../src/discovery/core/status.js";
import {
  proposalReviewPacketPath,
} from "../src/discovery/discovery_paths.js";
import { loadWorkingState, saveWorkingState } from "../src/discovery/stages/d0_working.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { SolveUnitOutputSchema } from "../src/discovery/solve/schemas.js";
import { parseRepairedModelJson } from "../src/discovery/core/core_io.js";
import { reusableOeqAnswerMatches } from "../src/discovery/solve/merge.js";



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
  const publishedCorePath = coreJsonPath(ctx);
  const core = existsSync(publishedCorePath)
    ? CoreSchema.parse(JSON.parse(await readFile(publishedCorePath, "utf8")))
    : CoreSchema.parse((() => {
        // A structural-gate failure can prevent core.json publication after a
        // valid proposal apply. Reconstruct the adjudication view from the
        // authoritative current proto plus the durable provisional proof bank;
        // never fall back to an older rendered paper.
        const recovered = structuredClone(proto);
        const frozenById = new Map(recovered.statements.map((statement) => [statement.id, statement] as const));
        for (const [id, record] of Object.entries(working.solved)) {
          if (!record.node) continue;
          const frozen = frozenById.get(id);
          const proof = record.proof_tex.trim();
          if (frozen) {
            // A stale carried claim must not overwrite the current accepted
            // proto. Attach its proof only when the exact claim still matches.
            if (record.node.statement !== frozen.statement || proof.length === 0) continue;
            frozen.proof_tex = record.proof_tex;
            frozen.status = solvedStatus(frozen);
            continue;
          }
          recovered.statements.push({
            ...record.node,
            proof_tex: proof.length > 0 ? record.proof_tex : record.node.proof_tex,
            // Deliberately STRICTER than `solvedStatus`: with no recovered proof this
            // keeps the prior status rather than publishing `proved` over nothing. A
            // recovery tool must not manufacture a discharge it cannot substantiate.
            status: proof.length > 0 ? solvedStatus(record.node) : record.node.status,
          });
        }
        return recovered;
      })());

  const currentStatementById = new Map(core.statements.map((statement) => [statement.id, statement] as const));
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
    if (currentStatementById.get(proof.id)?.kind === "openendedquestion") continue;
    addProof(proof.id, proof.proof_tex, "proposal-artifact", proof.argues_proposed === true);
  }

  const currentIds = new Set(currentStatementById.keys());
  const recovered: string[] = [];
  const durablePartialProofIdsIncluded: string[] = [];
  const openQuestionPartialResults: Array<{ id: string; partial_result: string }> = [];
  for (const [id, record] of Object.entries(working.solved)) {
    if (!record.partial || !currentIds.has(id) || !record.proof_tex.trim()) continue;
    if (currentStatementById.get(id)?.kind === "openendedquestion") {
      openQuestionPartialResults.push({ id, partial_result: record.proof_tex });
      continue;
    }
    durablePartialProofIdsIncluded.push(id);
    if (!proofById.has(id)) recovered.push(id);
    addProof(id, record.proof_tex, "durable-working-state");
  }
  const provisionalProofs = [...proofById].map(([id, proof]) => ({ id, ...proof }));

  const proposedStatementChanges = roundProposals.statements as unknown[];
  const proposedDefinitionChanges = roundProposals.definitions as unknown[];
  const proposedAssumptions = roundProposals.assumptions as unknown[];
  const proposedCoreEdits = roundProposals.coreEdits as unknown as Array<Record<string, any>>;
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
      provisionalProofs,
      recovery: {
        mode: "mechanical-no-solver",
        ...(recoveredSolveSource ? { recovered_solve_source: recoveredSolveSource } : {}),
        current_core_source: existsSync(publishedCorePath)
          ? "published-core"
          : "current-proto-plus-durable-provisional-proofs",
        recovered_partial_proof_ids: recovered,
        durable_partial_proof_ids_included: durablePartialProofIdsIncluded,
        normalized_statement_replace_proof_ids: normalizedStatementReplaceProofIds,
        proto_statement_ids: proto.statements.map((statement) => statement.id),
      },
    }),
  );
  console.log(JSON.stringify({
    packet: packetPath,
    proposals_carrier: "d0_working.json:proposals",
    recovered,
    normalized_statement_replace_proof_ids: normalizedStatementReplaceProofIds,
  }, null, 2));
}

main().catch((error: unknown) => {
  console.error(`d0_rebuild_review_packet: ${error instanceof Error ? error.message : String(error)}`);
  process.exitCode = 1;
});
