---
qid: panel_honest_did_phase
spec: v1
topic: "Sharp phase-transition theorem for Honest-DiD sensitivity analysis (Rambachan and Roth, 2023, Review of Economic Studies) and its descendants (Roth 2024 NBER). Honest-DiD relaxes the parallel trends assumption by bounding the deviation of the treatment-cohort post-trend from a linear pre-trend extrapolation by an M-budget, and reports a robust confidence interval CI(M) for the dynamic ATT that grows monotonically in M. The flagship question: characterize the sharp threshold M_star at which CI(M) first crosses zero (the smallest pre-trend deviation that the data CANNOT rule out a null treatment effect under), as a closed-form functional of the observable pre-trend covariance matrix and the post-period treatment-effect point estimate. The kernel claim is a sharp three-regime phase transition: when M < M_star_lo the null is robustly rejected for every admissible deviation; when M_star_lo <= M < M_star_hi the null is rejected only on a calibrated subset of admissible deviations parametrized by the projection direction; when M >= M_star_hi the null is robustly irrefutable. The theorem additionally provides closed-form expressions for M_star_lo and M_star_hi as singular values of an explicit observable kernel matrix combining the pre-period sample covariance, the post-period coefficient vector, and the second-difference smoothness operator, generalizing the Rambachan-Roth single-threshold characterization to the three-regime structure. Recovers Rambachan-Roth point identification at M=0 and provides the first sharp robust-inference phase transition with computable thresholds for staggered DiD."
novelty_target: flagship
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: "proposal_drift"
reusable: unknown
reraise_status: retry
gap_reasons:
  - 'Conjecture 1: C-sanity — The primitive gap is defined as ||J_agg u||_inf - ||J_A u||_inf, but on a one-dimensional active-face reduction support scales as the reciprocal of the seminorm, so Delta_F > 0 implies h_agg < h_coh and M_agg > M_coh, opposite to the stated conservative classification.'
  - 'Theorem 1: N-pub (angle 0) — The deterministic dictionary is standard support-function/trust-region convex geometry, not a novel theorem-level contribution.'
  - 'Conjecture 1: N-thin-survey (angle 0) — The proposal misses classical trust-region/point-to-ellipsoid prior art such as More-Sorensen 1983; tier=field below novelty_target=flagship unless a genuinely new econometric inference result is added.'
  - 'Conjecture 2: N-thin-survey (angle 0) — Even if true, the aggregation result reads as an operator refinement of Liu 2025 cohort-anchored robust inference, not a flagship-level standalone kernel.'
  - 'banked_reason — Math sound at field; flagship structurally unattainable for sensitivity-threshold framing. Re-review under widened flagship rubric (axes b/c added) flipped angle 2 v5 from REVISE@flagship to REJECT@not-publishable.'
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  The run attempted a three-regime phase-transition theorem characterizing when aggregate Honest-DiD sensitivity is sharp, conservative, or anti-conservative relative to cohort-level breakdown frontiers, with a primitive active-face matrix gap Delta_F as the certificate. Theorem 1 (LP-dual formula) survived as sound and incremental; Conjecture 1 collapsed because the Delta_F sign convention inverts the support-seminorm relationship — Delta_F > 0 implies h_agg < h_coh (conservative), opposite to the stated labeling. The aggregation quotient idea and the rank-loss discontinuity of Conjecture 2 remain plausibly open, but the final draft was banked with a confirmed sign inversion in the central classification.
banked_on: "2026-05-16"
---

# panel_honest_did_phase / v1 — Failed

**Topic.** Sharp phase-transition theorem for Honest-DiD sensitivity analysis (Rambachan and Roth, 2023, Review of Economic Studies) and its descendants (Roth 2024 NBER). Honest-DiD relaxes the parallel trends assumption by bounding the deviation of the treatment-cohort post-trend from a linear pre-trend extrapolation by an M-budget, and reports a robust confidence interval CI(M) for the dynamic ATT that grows monotonically in M. The flagship question: characterize the sharp threshold M_star at which CI(M) first crosses zero (the smallest pre-trend deviation that the data CANNOT rule out a null treatment effect under), as a closed-form functional of the observable pre-trend covariance matrix and the post-period treatment-effect point estimate. The kernel claim is a sharp three-regime phase transition: when M < M_star_lo the null is robustly rejected for every admissible deviation; when M_star_lo <= M < M_star_hi the null is rejected only on a calibrated subset of admissible deviations parametrized by the projection direction; when M >= M_star_hi the null is robustly irrefutable. The theorem additionally provides closed-form expressions for M_star_lo and M_star_hi as singular values of an explicit observable kernel matrix combining the pre-period sample covariance, the post-period coefficient vector, and the second-difference smoothness operator, generalizing the Rambachan-Roth single-threshold characterization to the three-regime structure. Recovers Rambachan-Roth point identification at M=0 and provides the first sharp robust-inference phase transition with computable thresholds for staggered DiD.

**Novelty target.** flagship

**D-0.5 verdict.** NO-PASS

**D0.5 verdict.** NA

**Banking reason.** Re-review under widened flagship rubric (axes b/c added) — D-0.5 angle 2 v5 verdict flipped from REVISE@flagship (original cap-exhausted run) to REJECT@not-publishable. New rubric is stricter for non-axis-(a/b/c) proposals: Honest-DiD M_star threshold is a calibration parameter (sensitivity intercept), not a non-equivalence between named estimators (b) or a strict extension of a previously-open class (c). Pipeline NO-PASS'd in 178s after 1 reviewer call. Math sound at field; flagship structurally unattainable for sensitivity-threshold framing.

## Key files

- `panel_honest_did_phase_v1_state.json` — pipeline state at banking (`banked: true`).
- `panel_honest_did_phase_v1_proposal.tex` — final proposal version.
- `panel_honest_did_phase_v1.tex` — derivation note (if D0 ran).
- `panel_honest_did_phase_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `panel_honest_did_phase_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
