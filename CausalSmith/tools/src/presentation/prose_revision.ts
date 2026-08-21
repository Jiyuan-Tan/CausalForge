import { normalizeCitedScopeFootnotes, paperEnvMismatches, texEnvFor, type FormalBlock } from "./formal_layer.js";
import { normalizeFrozenEnvs, parseAnchoredEnvs } from "./tex_anchors.js";

/**
 * ONE applicator for "let a model rewrite prose, then guarantee the frozen layer
 * is byte-identical afterwards" — shared by the P3 revise loop and the P5
 * holistic reviser (which each used to hand-roll an overlapping guard stack).
 * The model owns prose, never the P1-frozen formal layer or P2-audited proofs:
 * paraphrased frozen bodies are mechanically re-imposed, deleted envs are
 * reinserted next to their surviving neighbours, structural changes (moved /
 * added / duplicated / reordered envs, an env renamed to any other id — known
 * ids trip the added/duplicate checks, unknown ids the rogue check — and a
 * changed proof-block count) throw, and a `paperEnvMismatches` assertion over
 * the before-present envs is the final frozen-integrity check.
 */

const PROOF_BLOCK_RE = /\\begin\{proof\}(?:\[[^\]]*\])?[\s\S]*?\\end\{proof\}/g;

/** The P2-audited proof blocks of a paper, in order (P3 snapshots these before revising). */
export function proofBlocks(tex: string): string[] {
  return [...tex.matchAll(PROOF_BLOCK_RE)].map((m) => m[0]);
}

/** Restore audited proof blocks while preserving the model's prose edits. A changed
 * proof-block count is structural and cannot be paired safely, so return null and
 * let the caller hard-stop. */
export function restoreAuditedProofBlocks(tex: string, audited: string[]): string | null {
  const current = proofBlocks(tex);
  if (current.length !== audited.length) return null;
  let i = 0;
  return tex.replace(PROOF_BLOCK_RE, () => audited[i++]);
}

/**
 * Reinsert any frozen environments that a prose revision deleted. Existing bodies
 * are first reset to their canonical text. Missing blocks are placed relative to
 * their nearest surviving neighbour in the pre-revision source, so the reviser's
 * surrounding prose is preserved. Adding, moving, duplicating, or reordering an
 * anchored environment is rejected: a revision stage is a manuscript editor, not
 * a formal-layer editor.
 */
export function restoreFrozenEnvsAfterRevision(
  before: string,
  revised: string,
  canonical: Map<string, string>,
  who = "P5 holistic reviser",
): string {
  const beforeIds = parseAnchoredEnvs(before).map((e) => e.obj_id).filter((id) => canonical.has(id));
  const beforeSet = new Set(beforeIds);
  const revisedIds = parseAnchoredEnvs(revised).map((e) => e.obj_id).filter((id) => canonical.has(id));
  const added = revisedIds.filter((id) => !beforeSet.has(id));
  if (added.length > 0) {
    throw new Error(`${who} moved/added frozen environment(s): ${[...new Set(added)].join(", ")}`);
  }
  const duplicate = revisedIds.find((id, i) => revisedIds.indexOf(id) !== i);
  if (duplicate) throw new Error(`${who} duplicated frozen environment: ${duplicate}`);
  const survivingOrder = beforeIds.filter((id) => revisedIds.includes(id));
  if (revisedIds.some((id, i) => id !== survivingOrder[i])) {
    throw new Error(`${who} reordered frozen environments`);
  }
  if (beforeIds.length === 0) return revised;

  let out = normalizeFrozenEnvs(revised, canonical);
  for (let i = 0; i < beforeIds.length; i++) {
    const id = beforeIds[i];
    if (parseAnchoredEnvs(out).some((e) => e.obj_id === id)) continue;
    const env = canonical.get(id)!;
    const present = new Set(parseAnchoredEnvs(out).map((e) => e.obj_id));
    const next = beforeIds.slice(i + 1).find((candidate) => present.has(candidate));
    const prev = [...beforeIds.slice(0, i)].reverse().find((candidate) => present.has(candidate));
    if (next) {
      const marker = canonical.get(next)!;
      const at = out.indexOf(marker);
      if (at >= 0) {
        out = `${out.slice(0, at)}${env}\n\n${out.slice(at)}`;
        continue;
      }
    }
    if (prev) {
      const marker = canonical.get(prev)!;
      const at = out.indexOf(marker);
      if (at >= 0) {
        const end = at + marker.length;
        out = `${out.slice(0, end)}\n\n${env}${out.slice(end)}`;
        continue;
      }
    }
    out = `${out.replace(/\s*$/, "")}\n\n${env}\n`;
  }
  return normalizeFrozenEnvs(out, canonical);
}

/** Apply a model's prose revision of `before` and return the guarded result.
 * `auditedProofs` (P3): re-impose the P2-audited proof blocks; a changed count throws.
 * The final assertion covers every env that was present in `before` — envs a prior
 * stage never placed are not this applicator's business. */
export function applyProseRevision(args: {
  before: string;
  revised: string;
  blocks: FormalBlock[];
  auditedProofs?: string[];
  who: string;
}): string {
  const envBlocks = args.blocks.filter((b): b is FormalBlock & { env: NonNullable<FormalBlock["env"]> } => b.env != null);
  const canonical = new Map(envBlocks.map((b) => [b.obj_id, texEnvFor(b)]));
  // Seal the rename vector: an env whose obj_id is outside the formal layer is
  // invisible to every canonical-keyed guard below (restore filters by
  // `canonical.has`, the final assertion is restricted to before-present ids) —
  // so a reviser could smuggle a forged body through by renaming its anchor.
  // Any anchored id that is neither canonical nor present pre-revision throws.
  const beforeAnchored = new Set(parseAnchoredEnvs(args.before).map((e) => e.obj_id));
  const rogue = parseAnchoredEnvs(args.revised)
    .map((e) => e.obj_id)
    .filter((id) => !canonical.has(id) && !beforeAnchored.has(id));
  if (rogue.length > 0) {
    throw new Error(`${args.who} introduced unknown anchored environment(s): ${[...new Set(rogue)].join(", ")}`);
  }
  let out = restoreFrozenEnvsAfterRevision(args.before, args.revised, canonical, args.who);
  if (args.auditedProofs) {
    const restored = restoreAuditedProofBlocks(out, args.auditedProofs);
    if (restored === null) {
      throw new Error(`${args.who} changed the proof-block count (restored); rerun the proof-audited stage before publishing`);
    }
    out = restored;
  }
  out = normalizeCitedScopeFootnotes(out, envBlocks);
  const beforeIds = new Set(parseAnchoredEnvs(args.before).map((e) => e.obj_id));
  const mismatches = paperEnvMismatches(out, envBlocks.filter((b) => beforeIds.has(b.obj_id)));
  if (mismatches.length > 0) {
    throw new Error(`${args.who} broke the frozen layer (restored): ${mismatches.join("; ")}`);
  }
  return out;
}
