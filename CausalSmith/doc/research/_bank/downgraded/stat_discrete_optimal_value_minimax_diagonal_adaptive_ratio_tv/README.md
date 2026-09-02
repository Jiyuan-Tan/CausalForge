---
qid: stat_discrete_optimal_value_minimax
spec: diagonal_adaptive_ratio_tv
topic: "Global finite-sample minimax bracket and impossibility result for the unrestricted optimal treatment-policy value with high-dimensional discrete confounders: for iid (X,A,Y), X in [d], binary A,Y, consistency, conditional exchangeability, and fixed overlap epsilon, target V*(P)=sum_x p_x max{mu_0x,mu_1x}; prove c_epsilon min{1,sqrt(d)/n+d/[n log(en)]} <= R_{n,d,epsilon} <= min{1,C_epsilon d/n} for all n>=1 and d>=2, with the upper bound attained by an explicit empirical cellwise ratio estimator; prove the lower bound by an exact equal-propensity L1 Markov reduction, a paired-sign fuzzy mixture, and null-cell padding; show that the originally proposed 1/n+d/[n log(en)] uniform upper certificate is impossible, that parametric MSE holds iff d=O(1), and that consistency requires d=o(n log n) and is guaranteed by d=o(n). Matching achievability and the intermediate consistency region remain open. This is scalar oracle optimal value, not learned-policy regret or fixed-dimensional honest-CI adaptation."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "Delivered tier subfield below novelty_target=field (floor=field); paper_score_ceiling=7.2 < ceiling_for_field=7.5."
  - "The delivered result is an unconditional but nonmatching bracket: the converse is of order sqrt(d)/n + d/[n log(en)], whereas certified achievability is only d/n, leaving a factor as large as log n and the entire intermediate consistency region unresolved."
  - "The root-changed attempt again stops at simultaneous uniform approximation and absolute-coefficient control for Gamma over vertex-touching and heavy near-tie boxes; consequently factorial variance, cross-cell covariance, and pilot-error bounds cannot close."
reusable_artifacts:
  - "discovery/core.json — final source-faithful theorem graph, including the global lower bracket, empirical-ratio upper bound, null-cell padding, and bounded-d parametric boundary."
  - "discovery/writeup.tex — complete mathematical derivation and literature positioning."
  - "discovery/proof_archive/index.jsonl — content-addressed record of attempted and retained D0 proof payloads."
  - "reviews/review_general.json — controlling subfield-tier assessment and exact field-tier gap."
  - "orchestrator/decision_log.jsonl — verbatim adjudications of the failed Gamma-certificate route, maximality audit, citation attestation, and terminal decision."
seeds_burned: []
proof_attempt_summary: |
  The run proved a global lower bound by combining an exact equal-propensity L1 reduction,
  a paired-sign mixture, a Jiao--Han--Weissman high-dimensional splice, and null-cell padding;
  it also proved a computable empirical cellwise-ratio upper bound and the exact bounded-d
  parametric boundary. A root-changed diagonal-adaptive polynomial/factorial-moment attempt
  failed at the simultaneous Gamma approximation and coefficient-growth inequality, so the
  d/n upper bound remains unmatched and the intermediate consistency region remains open.
banked_on: "2026-08-22"
---

# stat_discrete_optimal_value_minimax / diagonal_adaptive_ratio_tv — Downgraded

**Topic.** Global finite-sample minimax bracket and impossibility result for the unrestricted optimal treatment-policy value with high-dimensional discrete confounders: for iid (X,A,Y), X in [d], binary A,Y, consistency, conditional exchangeability, and fixed overlap epsilon, target V*(P)=sum_x p_x max{mu_0x,mu_1x}; prove c_epsilon min{1,sqrt(d)/n+d/[n log(en)]} <= R_{n,d,epsilon} <= min{1,C_epsilon d/n} for all n>=1 and d>=2, with the upper bound attained by an explicit empirical cellwise ratio estimator; prove the lower bound by an exact equal-propensity L1 Markov reduction, a paired-sign fuzzy mixture, and null-cell padding; show that the originally proposed 1/n+d/[n log(en)] uniform upper certificate is impossible, that parametric MSE holds iff d=O(1), and that consistency requires d=o(n log n) and is guaranteed by d=o(n). Matching achievability and the intermediate consistency region remain open. This is scalar oracle optimal value, not learned-policy regret or fixed-dimensional honest-CI adaptation.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REVISE

**Banking reason.** Sound global minimax bracket and exact bounded-alphabet boundary, but certified achievability remains d/n, leaving a factor as large as log n and the intermediate consistency region unresolved; final D0.5 tier is subfield below the field floor.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
