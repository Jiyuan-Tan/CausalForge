---
qid: pid_multivariate_interval_regression
spec: v1
topic: "New topic: sharp identified regions for interval regression with several interval-measured regressors under coordinatewise or selected-coordinate monotonicity. Pre-anchor check: closest published anchor is Manski-Tamer interval regression for one interval-measured scalar regressor, with later set-inference work for the resulting identified set. Our theorem is not that because multi-coordinate interval regressors create a partial order: worst-case completions are governed by antichain/frontier geometry rather than the one-dimensional lower/upper endpoint ordering. Require a concrete nonroutine object: an antichain certificate or minimal frontier basis for sharp lower and upper regression-function envelopes, plus a finite two-regressor witness where coordinatewise monotonicity yields a nonrectangular identified region that cannot be recovered by intersecting one-dimensional Manski-Tamer bounds. If the proposal reduces to generic LP duality, ordinary interval arithmetic, or a definition-unfold frontier, pivot or stop early."
novelty_target: relative-to-literature
tier_at_proposal: REJECT
tier_at_derivation: NA
proposal_promise_gap: "kernel_substituted"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "Theorem 1 was already known: the scalar collapse is Manski-Tamer's scalar IMMI endpoint bound."
  - "The scalar antichain collapse failed: under IMMI, dominated endpoint cells can bind because g(c) is not implied monotone in the observed endpoint cell."
  - "Conjecture 1 was not well posed: the proposed frontier pruning dropped non-frontier lower/upper cells without an endpoint-cell stochastic-dominance or pruning condition."
  - "Conjecture 3 was promissory: the finite nonrectangular witness was only a skeleton and lacked numeric cell means and support-direction inequalities."
reusable_artifacts:
  - "pid_multivariate_interval_regression_v1_gaps.json: literature map for Manski-Tamer and random-set interval-regression anchors."
  - "pid_multivariate_interval_regression_v1_reviews/angle0_v1.json: counterexample-style reviewer diagnosis of why antichain/frontier pruning is invalid as stated."
  - "pid_multivariate_interval_regression_v1_proposal_angle0_rejected.tex: rejected proposal showing the tempting but invalid frontier-certificate formulation."
seeds_burned: []
proof_attempt_summary: |
  Attempted to turn multivariate interval regression with coordinatewise monotonicity into a sharp antichain/frontier certificate theorem plus a finite nonrectangular witness. The review found the core pruning step mathematically unjustified: interval validity and monotonicity do not imply that non-frontier endpoint cells can be discarded, and the one-dimensional reduction was already Manski-Tamer. Reuse the literature map and the negative diagnosis, but do not revive this kernel without an explicit endpoint-cell dominance condition or a fully specified witness.
banked_on: "2026-05-24"
---

# pid_multivariate_interval_regression / v1 â€” Failed

**Topic.** New topic: sharp identified regions for interval regression with several interval-measured regressors under coordinatewise or selected-coordinate monotonicity. Pre-anchor check: closest published anchor is Manski-Tamer interval regression for one interval-measured scalar regressor, with later set-inference work for the resulting identified set. Our theorem is not that because multi-coordinate interval regressors create a partial order: worst-case completions are governed by antichain/frontier geometry rather than the one-dimensional lower/upper endpoint ordering. Require a concrete nonroutine object: an antichain certificate or minimal frontier basis for sharp lower and upper regression-function envelopes, plus a finite two-regressor witness where coordinatewise monotonicity yields a nonrectangular identified region that cannot be recovered by intersecting one-dimensional Manski-Tamer bounds. If the proposal reduces to generic LP duality, ordinary interval arithmetic, or a definition-unfold frontier, pivot or stop early.

**Novelty target.** relative-to-literature

**Stage -0.5 verdict.** REJECT

**Stage 0.5 verdict.** NA

**Banking reason.** Stopped after first D-0.5 hard REJECT: antichain/frontier kernel was mathematically invalid as stated (frontier pruning not justified by interval validity/monotonicity), scalar collapse was already Manski-Tamer, and the nonrectangular witness was only promissory.

## Key files

- `pid_multivariate_interval_regression_v1_state.json` â€” pipeline state at banking (`banked: true`).
- `pid_multivariate_interval_regression_v1_proposal.tex` â€” final proposal version.
- `pid_multivariate_interval_regression_v1.tex` â€” derivation note (if Stage 0 ran).
- `pid_multivariate_interval_regression_v1_reviews.jsonl` â€” per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_multivariate_interval_regression_v1_reviews/` â€” per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
