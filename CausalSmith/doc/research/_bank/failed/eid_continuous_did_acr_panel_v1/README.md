---
qid: eid_continuous_did_acr_panel
spec: v1
topic: "Sharp non-equivalence and strict-extension theorem between three leading continuous-treatment difference-in-differences estimators for the Average Causal Response (ACR) curve: the nonparametric continuous-treatment DiD of D'Haultfœuille, Hoderlein, Sasaki (2023, Journal of Econometrics) that estimates the marginal ACR via quantile-quantile matching between treatment-intensity strata, the de Chaisemartin-D'Haultfœuille (2024) generalized parallel trends estimator that targets the ACR via local-linear weighting in (cohort, treatment-dose) cells, and the panel TWFE-with-continuous-treatment estimator (the empirical default) that regresses outcome on the interaction of cohort and dose. All three target the population ACR functional ACR(d) = d/dd E[Y(d) - Y(0)] under generalized parallel trends + monotone dose-response. The flagship question (axis b: non-equivalence frontier between three named published continuous-DiD estimators): characterize the sharp boundary in (dose-distribution heterogeneity, cohort-time variation, parallel-trend bandwidth) space at which the three estimators have asymptotically equivalent identifying functionals versus strictly different ACR-limit functionals. The kernel claim is a closed-form spectral non-equivalence theorem: the three estimators identify the same ACR(d) at every interior dose d and achieve identical asymptotic variance if and only if a heterogeneity condition kappa(d) := lambda_max(Sigma_dose(d) Pi_cohort) <= kappa_star holds for every d in the interior of the dose support, where kappa_star is a sharp threshold equal to the smallest singular value of an explicit observable kernel matrix combining the dose-distribution covariance, the cohort-period treatment-share matrix, and the parallel-trend smoothness bandwidth; when kappa(d) > kappa_star on a non-trivial dose set, the DHS quantile-matching estimator achieves the semiparametric efficiency bound, the dCDH local-linear estimator is consistent but inefficient by a factor proportional to the bandwidth-misspecification rate, and the TWFE estimator is biased proportional to the cohort-dose interaction excess. kappa_star is a NEW mathematical object computable from observable second moments + cohort-period treatment shares + parallel-trend bandwidth, NOT an existence/absence statement from prior work. Recovers TWFE consistency under homogeneous dose-cohort assignment (kappa(d)=0 for all d) and provides the first sharp triple-non-equivalence boundary for continuous-treatment DiD ACR identification in closed form."
novelty_target: flagship
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - 'Conjecture 1: N-thin-survey — tier=field below novelty_target=flagship; the comparison omits optimal-recovery/convex-function-class smoothness bounds such as ArmstrongKolesar2018, and the current kernel reads as a field-level DID specialization of C^{1,1} extension geometry unless tied to a named open no-QUG/minimax frontier.'
  - 'Conjecture 1: N-thin-survey (angle1_v1) — tier=field below novelty_target=flagship unless the redraft quotes an explicit open support-gap problem in the no-stayer continuous-DID literature and states a strictly new sharp-bound object beyond generic smoothness interpolation.'
  - 'Conjecture 2: C-wellposed (angle1_v1) — The converse says K_score nonzero, or a nonzero orthogonal score difference, implies a distinct first-order variance; nonzero score differences can have equal information norm unless a variance-gap or covariance condition is added.'
  - 'Conjecture 2: C-wellposed (angle1_v2) — The claimed two-endpoint Whitney modulus is built from the same incomplete Taylor rows; it is missing the sharp integral/Le Gruyer compatibility condition needed for a necessary-and-sufficient C^{1,1} derivative envelope.'
  - 'Theorem 2: N-pub — already-known; DCDHPSVB2025ContinuousEveryPeriod and DCDHK2026NoUntreated give the local observed-support slope/weighted-slope point-ID corner.'
  - 'Theorem 1: C-sanity (angle1_v2) — The stated W_T constraints are not sufficient for a C^{1,1} curve with Lipschitz constant B: with x0=0, x1=1, m=(0,1/2), v=(0,0), B=1 the rows pass, but no derivative with endpoints 0 and Lipschitz constant 1 can integrate to 1/2.'
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  The run attempted a flagship-tier sharp equivalence theorem among three named continuous-treatment DiD ACR estimators (DHS quantile-matching, dCDH local-linear, continuous-dose TWFE), then pivoted across three angles toward a partial-identification support-gap envelope for ACR(d) under no-stayer, no-near-zero designs. The pivoted partial-ID kernel (clipped-arc C^{1,1} extension program over observable dose-support gaps) was consistently assessed as field-tier and mathematically sound — all reviewers confirmed Conjecture 1 as new — but it never cleared the flagship bar because the novelty framing omitted Armstrong-Kolesar optimal-recovery comparators and failed to name an explicit open no-QUG/minimax frontier. Theorem 2 (point-ID sanity corner) was flagged already-known; Conjecture 2 (C-wellposed) had a residual soundness gap in its falsification certificate, and the common-intercept C^{1,1} compatibility constraints were incompletely specified in intermediate drafts.
banked_on: "2026-05-16"
---

# eid_continuous_did_acr_panel / v1 — Failed

**Topic.** Sharp non-equivalence and strict-extension theorem between three leading continuous-treatment difference-in-differences estimators for the Average Causal Response (ACR) curve: the nonparametric continuous-treatment DiD of D'Haultfœuille, Hoderlein, Sasaki (2023, Journal of Econometrics) that estimates the marginal ACR via quantile-quantile matching between treatment-intensity strata, the de Chaisemartin-D'Haultfœuille (2024) generalized parallel trends estimator that targets the ACR via local-linear weighting in (cohort, treatment-dose) cells, and the panel TWFE-with-continuous-treatment estimator (the empirical default) that regresses outcome on the interaction of cohort and dose. All three target the population ACR functional ACR(d) = d/dd E[Y(d) - Y(0)] under generalized parallel trends + monotone dose-response. The flagship question (axis b: non-equivalence frontier between three named published continuous-DiD estimators): characterize the sharp boundary in (dose-distribution heterogeneity, cohort-time variation, parallel-trend bandwidth) space at which the three estimators have asymptotically equivalent identifying functionals versus strictly different ACR-limit functionals. The kernel claim is a closed-form spectral non-equivalence theorem: the three estimators identify the same ACR(d) at every interior dose d and achieve identical asymptotic variance if and only if a heterogeneity condition kappa(d) := lambda_max(Sigma_dose(d) Pi_cohort) <= kappa_star holds for every d in the interior of the dose support, where kappa_star is a sharp threshold equal to the smallest singular value of an explicit observable kernel matrix combining the dose-distribution covariance, the cohort-period treatment-share matrix, and the parallel-trend smoothness bandwidth; when kappa(d) > kappa_star on a non-trivial dose set, the DHS quantile-matching estimator achieves the semiparametric efficiency bound, the dCDH local-linear estimator is consistent but inefficient by a factor proportional to the bandwidth-misspecification rate, and the TWFE estimator is biased proportional to the cohort-dose interaction excess. kappa_star is a NEW mathematical object computable from observable second moments + cohort-period treatment shares + parallel-trend bandwidth, NOT an existence/absence statement from prior work. Recovers TWFE consistency under homogeneous dose-cohort assignment (kappa(d)=0 for all d) and provides the first sharp triple-non-equivalence boundary for continuous-treatment DiD ACR identification in closed form.

**Novelty target.** flagship

**D-0.5 verdict.** NO-PASS

**D0.5 verdict.** NA

**Banking reason.** D-0.5 NO-PASS: angle 0 v1-v5 REVISE@flagship (5×, capped), angle 1 v1 REVISE@field → v2 REJECT@field (collapsed), angle 2 v1-v5 REVISE@field (cap). Continuous-DiD ACR non-equivalence kernel briefly recognized as flagship axis-b but proposer couldn't tighten angle 0 within cap, then degraded across pivots. Math sound at field tier.

## Key files

- `eid_continuous_did_acr_panel_v1_state.json` — pipeline state at banking (`banked: true`).
- `eid_continuous_did_acr_panel_v1_proposal.tex` — final proposal version.
- `eid_continuous_did_acr_panel_v1.tex` — derivation note (if D0 ran).
- `eid_continuous_did_acr_panel_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `eid_continuous_did_acr_panel_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
