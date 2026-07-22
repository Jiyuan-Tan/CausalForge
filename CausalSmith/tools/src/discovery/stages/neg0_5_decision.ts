// Pure decision logic for the D-0.5 angle/revise/pivot loop. No I/O — every
// function here maps loop state to a decision, so the loop control that used to
// live inline in a 1000-line runner is unit-testable as a decision table.
import { meetsNoveltyFloor } from "../../novelty.js";
import type { NoveltyTarget } from "../../novelty.js";

/**
 * Reviewer-flag codes that signal the KERNEL CLAIM is structurally broken
 * (definitional unfold, unbounded free parameter, no named focal object,
 * tautological iff). Triggers a kernel-replace dispatch: the producer is
 * asked to swap the headline kernel while keeping the angle's literature
 * anchor + seeds. Any one of these codes is enough to trigger.
 */
export const KERNEL_LEVEL_FLAG_CODES = new Set<string>([
  "C-definitional-unfold",
  "C-tautological-iff",
  "C-free-epsilon",
  "N-no-named-focal-object",
]);

/**
 * Reviewer-flag codes that signal the DRAFT EXECUTION is broken while the
 * kernel itself is plausibly fine (exhibit doesn't compute the promised
 * focal object, witness self-refutes, arithmetic wrong, terminology slips).
 * Triggers a draft-rebuild dispatch when >= DRAFT_REBUILD_FLAG_THRESHOLD
 * codes from this set are present.
 */
export const DRAFT_BROKEN_FLAG_CODES = new Set<string>([
  "N-promissory-object",
  "N-witness-trivial",
  "N-strawman",
  "N-mischar",
  "C-sanity",
  "C-coherence",
  "C-wellposed",
]);
export const DRAFT_REBUILD_FLAG_THRESHOLD = 2;

/** Normalize a reviewer's `verdict` field to the three-value enum, or null when it
 *  is missing/junk. A reviewer whose parseable JSON carries no usable verdict (a
 *  template TODO, a mis-keyed field) has NOT reviewed anything — the caller must
 *  halt mechanically rather than default to REVISE, which consumed one of the five
 *  revise rounds plus a producer re-author and poisoned the tier-promote history. */
export function normalizeReviewVerdict(verdict: string | null): "ACCEPT" | "REJECT" | "REVISE" | null {
  const v = (verdict ?? "").trim().toUpperCase();
  return v === "ACCEPT" || v === "REJECT" || v === "REVISE" ? v : null;
}

/** Extract every S/N/C flag code from a reviewer JSON. */
export function collectFlagCodes(reviewJson: Record<string, unknown>): string[] {
  const out: string[] = [];
  for (const key of ["structure_flags", "novelty_flags", "soundness_flags"] as const) {
    const arr = reviewJson[key];
    if (!Array.isArray(arr)) continue;
    for (const entry of arr) {
      if (entry && typeof entry === "object") {
        const code = (entry as { code?: unknown }).code;
        if (typeof code === "string") out.push(code);
      }
    }
  }
  return out;
}

/**
 * REJECT-escape classification: which single-shot rescue (if any) the current
 * angle gets before pivoting. Kernel-replace takes priority over draft-rebuild
 * when both patterns are present; each escape fires at most once per angle.
 */
export function decideRejectEscape(args: {
  codes: string[];
  angle: number;
  kernelReplaceUsedAngles: number[];
  draftRebuildUsedAngles: number[];
}): "kernel-replace" | "draft-rebuild" | null {
  const hasKernelFlag = args.codes.some((c) => KERNEL_LEVEL_FLAG_CODES.has(c));
  const draftBrokenCount = args.codes.filter((c) => DRAFT_BROKEN_FLAG_CODES.has(c)).length;
  if (hasKernelFlag && !args.kernelReplaceUsedAngles.includes(args.angle)) return "kernel-replace";
  if (
    draftBrokenCount >= DRAFT_REBUILD_FLAG_THRESHOLD &&
    !args.draftRebuildUsedAngles.includes(args.angle)
  ) {
    return "draft-rebuild";
  }
  return null;
}

export interface IterationRow {
  angle: number;
  version: number;
  mode: string;
  verdict: string;
  tier?: string;
  clean_substance?: boolean;
}

/**
 * Tier-saturation auto-promote (safe at -0.5 because this stage never verifies
 * proofs — math correctness is checked downstream at D0.5). True iff the CURRENT
 * verdict is REVISE at-or-above the run's novelty floor with clean substance,
 * AND the last 3 consecutive iterations on this angle (including the current
 * one, already appended) all held that bar. Prevents the cap-bound trap where
 * well-posedness nits dominate at the cap. NOT replicated at D0.5 — there
 * C-wellposed flags can be load-bearing and must escalate instead.
 */
export function decideTierSaturationPromote(args: {
  verdict: string;
  tier: string | undefined;
  cleanSubstance: boolean;
  iterations: IterationRow[];
  angle: number;
  noveltyTarget: NoveltyTarget;
}): boolean {
  if (args.verdict !== "REVISE") return false;
  if (!meetsNoveltyFloor(args.tier, args.noveltyTarget) || !args.cleanSubstance) return false;
  const recentSameAngle = args.iterations.filter((it) => it.angle === args.angle).slice(-3);
  return (
    recentSameAngle.length >= 3 &&
    recentSameAngle.every(
      (it) =>
        it.verdict === "REVISE" &&
        meetsNoveltyFloor(it.tier, args.noveltyTarget) &&
        it.clean_substance === true,
    )
  );
}

/**
 * REVISE-path outcome for the current angle:
 *  - "below-floor-kill": by `killVersion` the angle never reached the run's
 *    novelty floor in its history — polish won't break the ceiling, kill it;
 *  - "revise-cap-exhausted": the angle's revise cap is spent;
 *  - "revise": another revise round is available.
 */
export function decideReviseOutcome(args: {
  version: number;
  iterations: IterationRow[];
  angle: number;
  noveltyTarget: NoveltyTarget;
  reviseCap: number;
  killVersion: number;
}): "below-floor-kill" | "revise-cap-exhausted" | "revise" {
  if (args.version >= args.killVersion) {
    const reachedFloor = args.iterations.some(
      (it) => it.angle === args.angle && meetsNoveltyFloor(it.tier, args.noveltyTarget),
    );
    if (!reachedFloor) return "below-floor-kill";
  }
  if (args.version >= args.reviseCap) return "revise-cap-exhausted";
  return "revise";
}
