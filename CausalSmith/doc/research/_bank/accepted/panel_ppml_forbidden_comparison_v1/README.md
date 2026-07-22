---
qid: panel_ppml_forbidden_comparison
spec: v1
topic: "Multiplicative Goodman-Bacon for staggered Poisson difference-in-differences: characterize the probability limit of the naive two-way (unit+time) fixed-effects PPML single-coefficient estimand under staggered adoption with heterogeneous multiplicative (proportional) treatment effects, and derive the sharp forbidden-comparison sign condition sign(d beta*/d delta_gt) = sign(Wtilde_gt), where Wtilde is the pseudo-true-weight (weighted-FWL) residual of the treatment indicator partialled against the unit and time fixed effects — showing a cohort with a larger true positive proportional effect can strictly lower the reported coefficient via already-treated cohorts acting as effective controls (the Poisson/multiplicative analog of Goodman-Bacon 2021 and de Chaisemartin-D'Haultfoeuille 2020, whose linear weighted-sum decomposition is Jensen-obstructed in the multiplicative case per Moreau-Kastler 2025). Deliver: (K1) an implicit PPML projection theorem — beta* is the unique pseudo-true root of the misspecified FE-Poisson score (White 1982), closed-form in a 2-cohort/3-period minimal instance, not a convex combination of the delta_gt; (K2) the effect-dependent sign condition with derivative E[Wtilde_it * d mu_it/d delta_gt] / E[w*_it Wtilde_it^2], the characterization of forbidden (negative-Wtilde) cells, and a proven-non-vacuous 2x3 instance; (K3) the corrected counterfactual-share-weighted proportional ATT PTT = sum omega_gt delta_gt (positive weights) with the influence function and consistent analytical asymptotic variance of the imputation ratio-of-ratios estimator, open in Moreau-Kastler 2025. Substrate: Wooldridge 2023 multiplicative parallel trends E[Y_it(0)|i,t]=exp(alpha_i+gamma_t)."
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: null
reusable: unknown
reraise_status: unknown
gap_reasons:
  - "No fixed-T consistency, limit distribution, or inference result is claimed for the extended-MLE sample convention."
  - "The requested influence-function and analytical-variance extension was not claimed; PTT is proved only as a positive counterfactual-share population estimand."
reusable_artifacts:
  - "Causalean/Stat/MEstimation/ArgmaxStability.lean"
  - "Causalean/Stat/MEstimation/FinitePoisson.lean"
  - "Causalean/Stat/MEstimation/FinitePoissonConsistency.lean"
  - "Causalean/Stat/MEstimation/FinitePoissonDerivative.lean"
  - "Causalean/Stat/MEstimation/FinitePoissonSign.lean"
seeds_burned: []
proof_attempt_summary: |
  The run proved the unit-FE PPML collapse, unique pseudo-true projection,
  effect-dependent weighted-FWL derivative sign theorem, primitive global
  frontier, and an explicit T=4 positive-effect sign-reversal witness. It also
  proved positive counterfactual-share PTT aggregation and its population ratio
  identity, while deliberately leaving fixed-T influence-function and analytical-
  variance theory outside the accepted scope.
banked_on: "2026-07-16"
paper_score: 5.5
paper_score_rationale: "The core deterministic sign-reversal result appears correct and potentially useful, but the manuscript is not yet strong enough for a leading econometrics journal because the empirical bridge, exposition of the central sign argument, and positioning remain underdeveloped."
---

# panel_ppml_forbidden_comparison / v1 — Accepted

**Topic.** Multiplicative Goodman-Bacon for staggered Poisson difference-in-differences: characterize the probability limit of the naive two-way (unit+time) fixed-effects PPML single-coefficient estimand under staggered adoption with heterogeneous multiplicative (proportional) treatment effects, and derive the sharp forbidden-comparison sign condition sign(d beta*/d delta_gt) = sign(Wtilde_gt), where Wtilde is the pseudo-true-weight (weighted-FWL) residual of the treatment indicator partialled against the unit and time fixed effects — showing a cohort with a larger true positive proportional effect can strictly lower the reported coefficient via already-treated cohorts acting as effective controls (the Poisson/multiplicative analog of Goodman-Bacon 2021 and de Chaisemartin-D'Haultfoeuille 2020, whose linear weighted-sum decomposition is Jensen-obstructed in the multiplicative case per Moreau-Kastler 2025). Deliver: (K1) an implicit PPML projection theorem — beta* is the unique pseudo-true root of the misspecified FE-Poisson score (White 1982), closed-form in a 2-cohort/3-period minimal instance, not a convex combination of the delta_gt; (K2) the effect-dependent sign condition with derivative E[Wtilde_it * d mu_it/d delta_gt] / E[w*_it Wtilde_it^2], the characterization of forbidden (negative-Wtilde) cells, and a proven-non-vacuous 2x3 instance; (K3) the corrected counterfactual-share-weighted proportional ATT PTT = sum omega_gt delta_gt (positive weights) with the influence function and consistent analytical asymptotic variance of the imputation ratio-of-ratios estimator, open in Moreau-Kastler 2025. Substrate: Wooldridge 2023 multiplicative parallel trends E[Y_it(0)|i,t]=exp(alpha_i+gamma_t).

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** Clean F5 with dual F4 statement convergence, zero proof holes or gates, and a field-tier novelty pass; user approved banking at CKPT 2; F7 shared-library promotion verified.

## Key files

- `panel_ppml_forbidden_comparison_v1_state.json` — pipeline state at banking (`banked: true`).
- `panel_ppml_forbidden_comparison_v1_proposal.tex` — final proposal version.
- `panel_ppml_forbidden_comparison_v1.tex` — derivation note (if Stage 0 ran).
- `panel_ppml_forbidden_comparison_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `panel_ppml_forbidden_comparison_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
