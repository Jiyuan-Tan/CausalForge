// The round's proposal payload — one object, one lifecycle.
//
// WHY THIS EXISTS. A D0 round's proposals were spread over five sibling files
// (`proposed_statement_changes`, `_definition_changes`, `_assumptions`,
// `_core_edits`, `_proofs`), each written and read independently. Nothing tied them
// together, so every consumer chose its own subset and the subsets disagreed:
//
//   - `d0_apply_change` read four of the five and never `_proofs`, so approving a
//     statement change discarded the proof written FOR that change
//   - the D0.5 reviewers read none of them, which is why "the reviewer never got the
//     full proof" — the payload existed and no reviewer consumed it
//   - the closure check (now `core/coherence.ts`) had to RECONSTRUCT the union to check that the atomic apply
//     could see every node, and got it wrong (it omitted `d0_working.json`, reporting
//     33 phantom uncarried nodes on a healthy run)
//
// The proposals share `d0_working.json`'s lifecycle exactly — per round, cleared by
// `clearRoundOutputs`, invalidated when D-1.2 advances the proposal revision — so
// they belong inside it. With one carrier the closure invariant
// `ids(core) ⊆ ids(proto) ∪ ids(working)` holds by construction rather than being
// re-derived by a checker that can be wrong.
//
// This module is the ONLY way to read or write the payload. `proto_core.json` stays
// separate (different lifecycle, different author, and it is the freeze baseline
// that makes silent claim-weakening detectable); `core.json` stays derived.

import { existsSync } from "node:fs";
import { artifactPath } from "../../paths.js";
import type { PipelineContext } from "../../types.js";
import type { WorkingState } from "../stages/d0_working.js";
import type { RawChange, RawAssumption, RawCoreEdit } from "../stages/d0_apply.js";

/** A same-round proof payload, banked while a structural proposal is pending.
 *  It supersedes the node's stale `proof_tex` for review and adjudication.
 *  `argues_proposed` declares the proof argues the PROPOSED statement text in the same
 *  bundle; apply promotes it in the same adjudication when that basis materializes. */
export interface ProvisionalProof {
  id: string;
  proof_tex: string;
  argues_proposed?: boolean;
}

/** Everything one D0 round proposes, adjudicated as a unit. */
export interface RoundProposals {
  statements: RawChange[];
  definitions: RawChange[];
  assumptions: RawAssumption[];
  coreEdits: RawCoreEdit[];
  proofs: ProvisionalProof[];
}

export function emptyProposals(): RoundProposals {
  return { statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [] };
}

export function hasProposals(p: RoundProposals): boolean {
  return p.statements.length > 0 || p.definitions.length > 0 || p.assumptions.length > 0 ||
    p.coreEdits.length > 0 || p.proofs.length > 0;
}

export interface PendingStatementSupersession {
  obsoleteId: string;
  replacementId: string;
}

/** Supersessions are the one proposal whose inert-looking halves are not independent:
 * the replacement node may already be in the derived core while deletion remains gated.
 * Keep the relation in the canonical proposal bundle and let solve/render fail closed on
 * it until the orchestrator consumes the bundle. */
export function pendingStatementSupersessions(p: Pick<RoundProposals, "coreEdits">): PendingStatementSupersession[] {
  return p.coreEdits.flatMap((edit) =>
    edit.kind === "statement-delete" && edit.replacement_id
      ? [{ obsoleteId: edit.id, replacementId: edit.replacement_id }]
      : [],
  );
}

/** Every id the payload would carry into the atomic base — the set the closure
 *  check in `core/coherence.ts` needs, computed HERE so no consumer has to
 *  reconstruct it. */
export function proposalIds(p: RoundProposals, coreEditTarget: (e: RawCoreEdit) => string): Set<string> {
  return new Set<string>([
    ...p.statements.map((c) => c.id),
    ...p.definitions.map((c) => c.id),
    ...p.assumptions.map((a) => a.id),
    ...p.coreEdits.map(coreEditTarget),
    ...p.proofs.map((x) => x.id),
  ]);
}

// ---------------------------------------------------------------------------
// Legacy per-kind files are RETIRED (2026-07-20). The payload's only carrier is
// `working.proposals`; `bin/migrate_dstage_stores.ts` folds a pre-fold run.
// Detecting a leftover legacy file here fails LOUD instead of silently reading
// an empty payload — adjudicating a phantom empty bundle clears real proposals.
// ---------------------------------------------------------------------------

const LEGACY_PROPOSAL_FILENAMES = [
  "proposed_statement_changes.json",
  "proposed_definition_changes.json",
  "proposed_assumptions.json",
  "proposed_core_edits.json",
  "proposed_proofs.json",
] as const;

function legacyProposalFilesOnDisk(ctx: PipelineContext): string[] {
  return LEGACY_PROPOSAL_FILENAMES
    .map((name) => artifactPath(ctx.repoRoot, ctx.qid, "discovery", name, [`${ctx.qid}_${name}`]))
    .filter((p) => existsSync(p));
}

/**
 * The round's proposals — `working.proposals`, the sole carrier. A pre-fold run
 * with legacy per-kind files on disk fails loud with a migration pointer.
 *
 * @param working the loaded working state, or null when there is none
 */
export async function readRoundProposals(
  ctx: PipelineContext,
  working: WorkingState | null,
): Promise<RoundProposals> {
  // WorkingState stores the payload structurally (its element types live in
  // stage0_apply, which would be a cycle), so re-attach the concrete types here —
  // this module is the single place that knows both sides.
  const stored = working?.proposals as Partial<RoundProposals> | undefined;
  if (stored) return { ...emptyProposals(), ...stored };
  const legacy = legacyProposalFilesOnDisk(ctx);
  if (legacy.length > 0) {
    throw new Error(
      `D0 proposals: working state carries no proposals payload but legacy per-kind file(s) exist on disk ` +
        `[${legacy.join(", ")}]. This run predates the store fold — run ` +
        `\`npx tsx bin/migrate_dstage_stores.ts <qid> <spec>\` before adjudicating; reading the legacy files ` +
        `directly is no longer supported.`,
    );
  }
  return emptyProposals();
}
