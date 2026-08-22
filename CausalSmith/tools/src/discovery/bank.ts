/**
 * Bank vocabulary shared by `bin/bank_entry.ts`.
 *
 * The former seed-burn filter and reusable-artifact loader that lived here
 * were never wired into a stage (cold-start D-1 reads the bank through the
 * D-1.1 literature scout instead) and were removed on 2026-08-21.
 */
/**
 * Study-mode failure reason taxonomy for `--tier failed` entries in the
 * literature bank (`_literature_bank/_failed/<reason>/<bt_id>/`). Validated by
 * `bin/bank_entry.ts` when a study-mode qid is banked at the failed tier.
 *
 * Distinct from `bin/study_bank.ts`'s `REASONS` (study-pipeline *run*-level
 * quarantine, granularity = `run_id`); this taxonomy is theorem-level
 * (granularity = `bt_id = <qid>_<spec>`) and tracks where in the causalsmith
 * pipeline the formalization gave up.
 */
export const LITERATURE_FAILURE_REASONS = [
  // Stage 1.5 reviewer rejected the NL formalization plan beyond retry budget.
  "nl_review_rejected",
  // Stage 2 / 2.5 could not produce a sorry-only Lean scaffold (drift loops, missing imports).
  "scaffold_failed",
  // Stage 3 exhausted retries; sorries remain.
  "proof_fill_failed",
  // Stage 4 (equivalence review) judged the Lean theorem inequivalent to the NL claim.
  "equivalence_failed",
  // Stage 3.5 prune broke the build and snapshot restore also failed (rare).
  "unrecoverable_build",
  // `state.flags.missing_architecture` set; run cannot proceed without substrate work.
  "architecture_missing",
  // Orchestrator-driven catch-all when none of the above fits.
  "manual",
] as const;
export type LiteratureFailureReason = (typeof LITERATURE_FAILURE_REASONS)[number];
