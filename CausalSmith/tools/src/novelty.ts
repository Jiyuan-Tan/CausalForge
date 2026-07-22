/**
 * Novelty-target vocabulary — UNIFIED with the reviewer publishability-tier ladder.
 *
 * A run's `--novelty` target IS a floor tier: the pipeline accepts a note iff the
 * reviewer-assessed tier meets (>=) the target. The vocabulary is therefore the
 * tier ladder itself: `flagship > field > subfield > incremental`.
 *
 * Historically the CLI used a separate spelling (`relative-to-repo` /
 * `relative-to-literature` / `field` / `flagship`) that mapped onto the tiers via
 * a lookup table. Those two legacy names are still ACCEPTED (old scripts + banked
 * `state.json`) and normalized to the tier vocabulary at every input boundary, but
 * the surfaced/canonical vocabulary is the tier names only.
 *
 * This is a leaf module (no project imports) so `parseArgs` and the state schema
 * can depend on it without pulling in the pipeline dispatcher.
 */

/** Canonical novelty-target vocabulary === the reviewer publishability-tier ladder. */
export type NoveltyTarget = "incremental" | "subfield" | "field" | "flagship";

/** Canonical targets, low → high. */
export const NOVELTY_TARGETS: readonly NoveltyTarget[] = [
  "incremental",
  "subfield",
  "field",
  "flagship",
] as const;

/** Reviewer publishability-tier ladder: flagship > field > subfield > incremental. */
export const REVIEWER_TIER_RANK: Record<string, number> = {
  flagship: 3,
  field: 2,
  subfield: 1,
  incremental: 0,
  // D-0.5 reviewer-prompt vocabulary: stage_neg1_review.txt's tier enum is
  // flagship|field|letter|not-publishable. Without these aliases both ranked
  // -1, which silently disabled the tier-saturation auto-promote and
  // force-killed clean letter-tier angles at the subfield floor.
  letter: 1,
  "not-publishable": 0,
};

/**
 * Legacy `--novelty` spellings, retained for back-compat (pre-unification scripts
 * and banked `state.json`). Mapped onto the canonical tier vocabulary on read.
 */
const LEGACY_NOVELTY_ALIASES: Record<string, NoveltyTarget> = {
  "relative-to-repo": "incremental",
  "relative-to-literature": "subfield",
};

/**
 * Normalize any accepted `--novelty` spelling — a canonical tier name or a legacy
 * alias — to the canonical tier vocabulary. Returns `undefined` for an
 * unrecognized value (callers turn that into a usage error or a fail-safe floor).
 */
export function normalizeNoveltyTarget(
  raw: string | undefined | null,
): NoveltyTarget | undefined {
  if (raw == null) return undefined;
  const t = raw.trim();
  if ((NOVELTY_TARGETS as readonly string[]).includes(t)) return t as NoveltyTarget;
  return LEGACY_NOVELTY_ALIASES[t];
}

/**
 * Does a reviewer-assessed `tier` meet the novelty-floor implied by the run's
 * `novelty_target`? Used by the Stage -0.5 angle/revise loop to gate BOTH the
 * tier-saturation auto-promote and the early angle-kill on the run's actual
 * ambition rather than the literal string `"flagship"`.
 *
 * An `incremental` target has no enforcement (any tier, including a missing one,
 * satisfies it). An unknown/missing tier never satisfies a non-incremental floor.
 * `target` is normalized defensively so a legacy spelling read straight from an
 * old `state.json` still resolves.
 */
export function meetsNoveltyFloor(
  tier: string | undefined,
  target: NoveltyTarget | string,
): boolean {
  const floor = normalizeNoveltyTarget(target) ?? (target as NoveltyTarget);
  if (floor === "incremental") return true;
  const floorRank = REVIEWER_TIER_RANK[floor];
  if (floorRank === undefined) return false; // fail-safe: unknown floor is unmet
  const tierRank = tier !== undefined ? (REVIEWER_TIER_RANK[tier] ?? -1) : -1;
  return tierRank >= floorRank;
}

/**
 * Build a reviewer-side directive that forbids ACCEPT when `tier_at_derivation`
 * is strictly below the orchestrator's `novelty_target`. Without this, the
 * reviewer can ACCEPT a `field`-tier kernel even when the user asked for
 * `flagship`, which is what happened on the flagship_explore/f1 run.
 *
 * Ordering: flagship > field > subfield > incremental. Because the target IS the
 * floor tier, `incremental` means no enforcement.
 */
export function tierFloorBlock(target: NoveltyTarget | string): string {
  const floor = normalizeNoveltyTarget(target) ?? (target as NoveltyTarget);
  if (floor === "incremental" || REVIEWER_TIER_RANK[floor] === undefined) return "";
  const acceptable: string =
    floor === "flagship"
      ? "flagship"
      : floor === "field"
        ? "flagship | field"
        : "flagship | field | subfield";
  return [
    "=== NOVELTY TIER FLOOR DIRECTIVE (orchestrator-enforced) ===",
    `The orchestrator has set novelty_target = ${floor}.`,
    `Tier ordering: flagship > field > subfield > incremental.`,
    `Acceptable tiers for ACCEPT: ${acceptable}.`,
    "",
    "Enforcement rule (overrides the default ACCEPT/REVISE/REJECT thresholds in the base prompt):",
    `  - If your own assessed tier_at_derivation is in {${acceptable}} AND every other dimension passes, return ACCEPT as usual.`,
    `  - If your assessed tier_at_derivation is strictly below the floor (${floor}), you MUST NOT return ACCEPT.`,
    `      * If the kernel still has a plausible repair path that could lift the tier, return REVISE with a novelty-flag specifically pointing at the tier gap (e.g. \"tier=${floor === "flagship" ? "field" : "subfield"} below novelty_target=${floor}; kernel needs <specific repair>\").`,
    `      * If no realistic local repair would lift the tier (the kernel is structurally non-${floor}), return REJECT and name the reason.`,
    "",
    "Do not silently downgrade a flagship target to field tier by accepting a field-tier kernel. The orchestrator is explicitly asking you to enforce the floor.",
    "=== END NOVELTY TIER FLOOR DIRECTIVE ===",
    "",
  ].join("\n");
}
