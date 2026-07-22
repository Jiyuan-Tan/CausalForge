// Per-theorem review propagation + failure-class hinting, shared across review
// boundaries (D0.5 and F1.5).
//
// Extracted from the (retired) monolithic Stage 0.5 (`stage0_5.ts`) so the
// active F1.5 stage (`stage1_5.ts`) can depend on `propagateTheoremReview`
// without pulling in the deleted legacy orchestrator. The class-hint table
// structures the human-readable `failure_reason` text (see below).

import type { ReviewResult } from "../judgment.js";
import type { Stage, StateJson } from "../types.js";

/**
 * Failure-class hint embedded in `failure_reason` when a causalsmith review
 * rejects a theorem. It tags the rejection with a coarse cause
 * (statement vs. setup vs. proof vs. substrate vs. translation) so the
 * downstream reroute / halt decision and the human reading the Note can
 * see at a glance why the theorem failed. (The former automated consumer,
 * study-pipeline S5's `failure_classifier`, was retired with the study pipeline.)
 */
type ClassHint =
  | "statement_wrong"
  | "setup_incomplete"
  | "proof_sketch_bug"
  | "substrate_missing"
  | "lean_translation_issue";

const CLASS_HINT_KEYWORDS: Record<ClassHint, string> = {
  statement_wrong: "theorem statement is wrong",
  setup_incomplete: "setup is incomplete (undeclared variable)",
  proof_sketch_bug: "proof sketch tactic failed",
  substrate_missing: "missing definition",
  lean_translation_issue: "lean translation issue",
};

/**
 * Stage 1.5's FQPHNLX reviewer emits per-finding `verdict: "FLAG-X"` plus a
 * top-level `classification`. Map those to a failure class the study-pipeline
 * classifier understands.
 *
 *   F (faithfulness drift)         → statement_wrong
 *   Q (quantifier scope absorbed)  → setup_incomplete  (type bindings missing)
 *   P (Iff.rfl-vacuous predicate)  → statement_wrong
 *   H (trivially-True hypothesis)  → statement_wrong
 *   U (hypothesis unused in proof) → statement_wrong   (claim is weaker than stated)
 *   N (notation/glossary)          → lean_translation_issue  (mechanical)
 *   L (fabricated lemma)           → proof_sketch_bug
 *   X (missing cross-reference)    → lean_translation_issue  (mechanical)
 *   mixed                          → statement_wrong  (heavier route wins)
 */
export function classHintFromFQPHNLX(code: string | undefined): ClassHint | null {
  switch (code) {
    case "F":
    case "P":
    case "H":
    case "U":
    case "mixed":
      return "statement_wrong";
    case "Q":
      return "setup_incomplete";
    case "L":
      return "proof_sketch_bug";
    case "N":
    case "X":
      return "lean_translation_issue";
    default:
      return null;
  }
}

export function inferClassHint(
  stage: Stage,
  finding: { verdict?: string } | null,
  review: ReviewResult,
): ClassHint {
  if (stage === "1.5") {
    const verdict = finding?.verdict ?? "";
    const code = verdict.match(/FLAG-([FQPHUNLX])/)?.[1];
    const fromFinding = classHintFromFQPHNLX(code);
    if (fromFinding) return fromFinding;
    const cls = (review as Record<string, unknown>).classification;
    const fromTop = classHintFromFQPHNLX(typeof cls === "string" ? cls : undefined);
    if (fromTop) return fromTop;
    // Stage 1.5 default: NL formalization rejections most commonly mean the
    // claim itself doesn't survive precise restatement.
    return "statement_wrong";
  }
  if (stage === "0.5") {
    // Stage 0.5 reviews the math claim itself — any rejection is about the
    // statement, not the translation.
    return "statement_wrong";
  }
  if (stage === "4") {
    // Stage 4 compares Lean output to the math; most rejections trace to
    // translation drift (the proof shape doesn't match the sketch).
    return "lean_translation_issue";
  }
  return "lean_translation_issue";
}

/**
 * Format a structured `failure_reason` string. Embeds:
 *   - `[stage:X.Y]` so the originating boundary is visible in the bank
 *   - `[class_hint:<class>]` so a structured reader can key off the class directly
 *   - The keyword phrase from `CLASS_HINT_KEYWORDS` as a human-readable cause tag
 *   - The reviewer's free-text one_line for human readers
 */
export function formatStuckReason(
  stage: Stage,
  hint: ClassHint,
  oneLine: string,
  theoremId: string,
): string {
  const text = oneLine.trim() || `Stage ${stage} reviewer rejected theorem ${theoremId}`;
  return `[stage:${stage}] [class_hint:${hint}] ${CLASS_HINT_KEYWORDS[hint]}: ${text}`;
}

/**
 * Propagate per-theorem verdicts from a Stage 0.5 ReviewResult to
 * `state.theorems`. Called after every reviewer invocation, before the
 * rewind decision. Backward compatible: no-op when `state.theorems` is
 * absent or empty.
 *
 * Mutation rules:
 * - Cross-boundary `failed` entries (e.g. set by a Stage 5 reject) are always
 *   preserved — a later boundary's pass cannot erase a confirmed failure.
 * - Same-boundary `stuck` entries (a soft flag set by an earlier attempt at
 *   THIS boundary) are cleared back to "pending" when the current review is
 *   an aggregate ACCEPT and the per-theorem verdict is pass/accept (the
 *   producer retry's local fix is treated as resolving the gap). On any
 *   other reviewer outcome the stuck flag is preserved.
 * - "fail" or "reject" verdicts on a "pending"/"in_progress" entry set
 *   status="stuck" and record failure_reason.
 * - "pass" or "accept" verdicts on a non-stuck entry leave it unchanged.
 */
export function propagateTheoremReview(
  state: StateJson,
  review: ReviewResult,
  stage: Stage = "0.5",
): void {
  if (!state.theorems || state.theorems.length === 0) return;
  const entries = (review as Record<string, unknown>).theorems_review;
  if (!Array.isArray(entries)) return;
  // Whether the top-level review verdict counts as a clean accept. Used to
  // distinguish "clear the stuck flag because attempt N at the SAME boundary
  // finally passed" from "keep the stuck flag because a later boundary just
  // happened to be a non-stuck stage". Only same-boundary ACCEPT clears.
  const reviewStatus = ((review as Record<string, unknown>).status ?? "").toString().toLowerCase();
  const reviewIsAccept = reviewStatus === "pass" || reviewStatus === "accept";

  const byId = new Map(state.theorems.map((e) => [e.theorem_local_id, e]));
  for (const item of entries as Array<{ theorem_local_id: string; verdict: string; findings?: Array<{ one_line?: string; verdict?: string } | unknown> }>) {
    if (typeof item.theorem_local_id !== "string") continue;
    const entry = byId.get(item.theorem_local_id);
    if (!entry) continue;
    const v = typeof item.verdict === "string" ? item.verdict.toLowerCase() : "";
    // Preserve cross-boundary `failed` state — Stage 5 failure markers must
    // not be erased by a later review's pass. For `stuck` (a soft flag set by
    // an earlier attempt at the SAME boundary): clear it on a per-theorem
    // pass within an aggregate ACCEPT review, since the producer retry's
    // local-fix evidently addressed the issue. Otherwise preserve.
    if (entry.status === "failed") continue;
    if (entry.status === "stuck") {
      if (reviewIsAccept && (v === "pass" || v === "accept")) {
        entry.status = "pending";
        delete entry.failure_reason;
      }
      continue;
    }
    if (v === "fail" || v === "reject") {
      entry.status = "stuck";
      const firstFinding = Array.isArray(item.findings) && item.findings.length > 0
        ? item.findings[0]
        : null;
      const one_line =
        firstFinding && typeof firstFinding === "object" && firstFinding !== null && "one_line" in firstFinding
          ? String((firstFinding as { one_line?: unknown }).one_line ?? "")
          : "";
      const hint = inferClassHint(
        stage,
        firstFinding && typeof firstFinding === "object" ? (firstFinding as { verdict?: string }) : null,
        review,
      );
      entry.failure_reason = formatStuckReason(stage, hint, one_line, item.theorem_local_id);
    }
    // "pass" / "accept" on a non-stuck entry → no mutation
  }
}
