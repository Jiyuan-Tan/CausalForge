---
qid: pid_fuzzy_rd_cutoff_shift
spec: ot_linear_fractional
topic: "Sharp OT/linear-fractional partial identification of a finite cutoff-shift, omega-weighted latent-rank PRTE in fuzzy RD"
novelty_target: field
tier_at_proposal: NA
tier_at_derivation: NA
proposal_promise_gap: "No counterfactual-arm information outside the cutoff, so the finite cutoff-shift identified bound is trivial without additional extrapolation content."
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - "The bound for this estimand is trivial in this setting because there is no information outside the cutoff for the counterfactual arm."
reusable_artifacts:
  - discovery/gaps.json
  - logs/stages/_d-1-1__you-are-stage-1-1-of-causalsmith-the-literature-.log
seeds_burned: []
proof_attempt_summary: |
  The run completed the D-1.1 literature and open-problem harvest, producing five
  source-grounded gaps, but was stopped before proposal review or mathematical
  derivation. The requested finite-shift counterfactual arm is unsupported outside
  the cutoff, so the resulting identified bound is trivial unless a genuinely
  informative extrapolation restriction or additional counterfactual data are added.
banked_on: "2026-07-16"
---

# pid_fuzzy_rd_cutoff_shift / ot_linear_fractional — Failed

**Topic.** Sharp OT/linear-fractional partial identification of a finite cutoff-shift, omega-weighted latent-rank PRTE in fuzzy RD.

**Novelty target.** field

**Stage -0.5 verdict.** NA

**Stage 0.5 verdict.** NA

**Banking reason.** The bound for this estimand is trivial in this setting because there is no information outside the cutoff for the counterfactual arm.

## Key files

- `pid_fuzzy_rd_cutoff_shift_ot_linear_fractional_state.json` — pipeline state at banking (`banked: true`).
- `pid_fuzzy_rd_cutoff_shift_ot_linear_fractional_proposal.tex` — final proposal version.
- `pid_fuzzy_rd_cutoff_shift_ot_linear_fractional.tex` — derivation note (if Stage 0 ran).
- `pid_fuzzy_rd_cutoff_shift_ot_linear_fractional_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_fuzzy_rd_cutoff_shift_ot_linear_fractional_reviews/` — per-version reviewer JSON files (if present).

## Notes

The literature map and five harvested open problems remain reusable for a
reformulated design that adds credible information about the counterfactual arm.
No proposal-review, derivation, formalization, or Lean proof artifacts were produced.
