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



async function main(): Promise<void> {
  const [qid, spec] = process.argv.slice(2);
  if (!qid || !spec) throw new Error("Usage: d0_rebuild_review_packet.ts <qid> <spec>");
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
  const roundProposals = await readRoundProposals(ctx, working);
  const existingProofs = roundProposals.proofs as Array<{ id: string; proof_tex: string }>;
  const proofById = new Map<string, string>();
  const addProof = (id: string, proofTex: string, source: string): void => {
    if (!id || !proofTex.trim()) return;
    const prior = proofById.get(id);
    if (prior !== undefined && prior !== proofTex) {
      throw new Error(`Conflicting ${source} proof for ${id}; refusing to choose one payload`);
    }
    proofById.set(id, proofTex);
  };
  for (const proof of existingProofs) {
    if (currentStatementById.get(proof.id)?.kind === "openendedquestion") continue;
    addProof(proof.id, proof.proof_tex, "proposal-artifact");
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
  const provisionalProofs = [...proofById].map(([id, proof_tex]) => ({ id, proof_tex }));

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
    const packetProof = proofById.get(edit.id);
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
