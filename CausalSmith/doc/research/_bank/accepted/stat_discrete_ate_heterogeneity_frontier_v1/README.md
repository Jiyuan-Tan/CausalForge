---
qid: stat_discrete_ate_heterogeneity_frontier
spec: v1
topic: "Two-sided minimax bracket and shrinking-radius localization for ATE estimation with high-dimensional discrete confounders. Observe n iid (X,A,Y) with X in [d], binary A, real Y, consistency, conditional exchangeability, fixed overlap epsilon, arbitrary unknown cell masses, and a fixed known scale M>=1 such that conditional means lie in [-M/2,M/2] and conditional second central moments are at most M^2. Let tau_k=E[Y|A=1,X=k]-E[Y|A=0,X=k], tau=sum_k p_k tau_k, and impose max_{k:p_k>0}|tau_k-tau|<=sigma M for known 0<=sigma<=2. Uniformly for 1<=d<=c_epsilon n^2/log(en), prove the same-class minimax bracket c_epsilon M^2{1/n+d/n^2+sigma^2 min[1,d^2/(n^2 log^2(en))]} <= R_{n,d,epsilon,M,sigma} <= C_epsilon M^2{1/n+min[1,d^2/(n^2 log^2(en)),sigma^2+d/n^2]}. Construct explicit clipped, total estimators under only the conditional-second-moment envelope: a signed one-mark heavy/light Chebyshev factorial estimator with no extra logarithmic loss and an occupancy-weighted treated-control estimator, combined by a known-radius selector. Prove the radius-dependent converse by scaled binary subclasses and a hypothesis-independent channel. Establish order matching at exact and unrestricted homogeneity, every radius bounded away from zero, saturation, the small-alphabet regime, and both parametric-dominance elbows; localize the only unresolved regime to b<<u<<1 and b<<sigma^2<<1, where b=1/n+d/n^2 and u=d^2/[n^2 log^2(en)], without claiming a uniformly matched frontier there. Use the Zeng--Balakrishnan--Han--Kennedy 401(k) comparison as the consumer, and do not claim inference or adaptation to unknown M or sigma."
novelty_target: field
banked_novelty_tier: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: "kernel_substituted"
reusable: solver_blocked
reraise_status: unknown
gap_reasons:
  - "The delivered result is an all-alphabet, same-class minimax bracket rather than a complete shrinking-radius frontier."
  - "In the residual regime b << u << 1 and b << sigma^2 << 1, the proved upper and lower benchmarks can differ by a logarithmic factor."
reusable_artifacts:
  - "Causalean/Stat/UStatistic/OrderM/PartialMatching.lean"
  - "Causalean/Stat/UStatistic/OrderM/MixedOrderCovariance.lean"
  - "Causalean/Stat/UStatistic/OrderM/MixedOrderBounds.lean"
  - "Causalean/Stat/Sample/OccupancyWeightedMean/"
  - "Causalean/Mathlib/Probability/BernoulliMeasure.lean (Bernoulli-weighted count enumeration)"
  - "Causalean/Stat/SampleSplit/FiniteSelector.lean"
  - "Causalean/Stat/SampleSplit/FiniteCategoryPilot.lean"
  - "Causalean/Stat/Sample/FiniteStratumMarkedRatioMse/"
  - "Causalean/Stat/Sample/PiTransport.lean"
  - "Causalean/Stat/Minimax/MinimaxRisk.lean (deterministic affine squared-risk transport)"
  - "Causalean/Stat/Minimax/MarkovKernelTransport.lean"
seeds_burned: []
proof_attempt_summary: |
  The run proved source-clean all-alphabet upper and lower minimax bounds, including exact and unrestricted endpoints, every fixed positive radius, saturation, and both parametric-dominance elbows. It formalized the continuous-outcome heavy/light and collision estimators together with scaled-binary lower transfers. The shrinking-radius wedge remains open because the available radius channel gives a product-type separation rather than the minimum-type separation needed to close the bracket.
banked_on: "2026-08-26"
paper_score: 6.6
paper_score_rationale: "Referee score of the kept bundle, as stamped by the pipeline from the last completed P5 review. Read it with the spread: the referee scored the SAME kept bytes twice, giving 7.0 (round_008) and 6.6 (round_009, the value stamped here), so single-read precision is about +/-0.4 at this level and the honest level is ~6.8. An 8.0 (the only minor_revision in ten reviews) was recorded at round_007 against a source state the pipeline's own P5 revision pass overwrote before it could be re-scored; those bytes are unrecoverable and the 8.0 is treated as an outlier, not as a kept version. Full trajectory: 6.5, 7.0, 6.5, 6.7, 6.8, 6.8, 6.5, 8.0, 7.0, 6.6. Standing substance of the review across rounds: the verified contribution is substantial and faithfully scoped, but the appendices read as machine output rather than an econometrics submission, which is inherent to shipping every proof inline."
---

# stat_discrete_ate_heterogeneity_frontier / v1 — Accepted

**Topic.** Two-sided minimax bracket and shrinking-radius localization for ATE estimation with high-dimensional discrete confounders. Observe n iid (X,A,Y) with X in [d], binary A, real Y, consistency, conditional exchangeability, fixed overlap epsilon, arbitrary unknown cell masses, and a fixed known scale M>=1 such that conditional means lie in [-M/2,M/2] and conditional second central moments are at most M^2. Let tau_k=E[Y|A=1,X=k]-E[Y|A=0,X=k], tau=sum_k p_k tau_k, and impose max_{k:p_k>0}|tau_k-tau|<=sigma M for known 0<=sigma<=2. Uniformly for 1<=d<=c_epsilon n^2/log(en), prove the same-class minimax bracket c_epsilon M^2{1/n+d/n^2+sigma^2 min[1,d^2/(n^2 log^2(en))]} <= R_{n,d,epsilon,M,sigma} <= C_epsilon M^2{1/n+min[1,d^2/(n^2 log^2(en)),sigma^2+d/n^2]}. Construct explicit clipped, total estimators under only the conditional-second-moment envelope: a signed one-mark heavy/light Chebyshev factorial estimator with no extra logarithmic loss and an occupancy-weighted treated-control estimator, combined by a known-radius selector. Prove the radius-dependent converse by scaled binary subclasses and a hypothesis-independent channel. Establish order matching at exact and unrestricted homogeneity, every radius bounded away from zero, saturation, the small-alphabet regime, and both parametric-dominance elbows; localize the only unresolved regime to b<<u<<1 and b<<sigma^2<<1, where b=1/n+d/n^2 and u=d^2/[n^2 log^2(en)], without claiming a uniformly matched frontier there. Use the Zeng--Balakrishnan--Han--Kennedy 401(k) comparison as the consumer, and do not claim inference or adaptation to unknown M or sigma.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** F5 clean; field-tier minimax bracket with the shrinking-radius wedge explicitly open.

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
