---
qid: panel_approx_nbhd_interference
spec: v1
topic: "Sharp non-equivalence and strict-extension theorem between three leading interference / network spillover identification estimators that handle SUTVA violation under approximate neighborhood interference: the Approximate Neighborhood Interference (ANI) estimator of Leung (2022, Econometrica) using exposure-mapping projection at fixed neighborhood radius r, the network-cluster-robust estimator of Leung (2023, Econometrica) with HAC-style cluster-bandwidth selection, and the randomization-test estimator of Basse, Ding, Feller, Toulis (2024, Econometrica) using exact randomization-based inference under partial interference. All three target the direct + spillover average treatment effect under bounded-degree network and exposure-mapping additivity. The flagship question (axis b: non-equivalence frontier between three named published network estimators): characterize the sharp boundary in (network density, exposure-radius, randomization-design) parameter space at which the three estimators have asymptotically equivalent identifying functionals versus strictly different limit functionals, as a function of (i) the network degree distribution rho, (ii) the exposure-misspecification rate epsilon_M, and (iii) the cluster-bandwidth scaling b_n. The kernel claim is a closed-form spectral non-equivalence theorem: ANI, network-CR, and randomization-test estimators identify the same direct + spillover effect and achieve identical asymptotic variance if and only if a degree-radius condition mu_max(rho, epsilon_M) <= mu_star, where mu_star is a sharp threshold equal to the smallest singular value of an explicit observable kernel built from rho, epsilon_M, and b_n; when mu_max > mu_star, the three diverge — ANI biased proportional to exposure-misspecification, network-CR consistent but inefficient by bandwidth, randomization-test achieves the design-based efficiency bound. mu_star is a NEW mathematical object, NOT existence/absence from prior. Recovers Leung 2022 ANI consistency under correctly-specified exposure (epsilon_M=0) and provides the first sharp triple-non-equivalence boundary for ANI / network-CR / randomization-test estimators in closed form."
novelty_target: flagship
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "kernel_substituted"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - 'Conjecture 2: C-wellposed — ''Lines 434-441 assume the open-set and positive-distance strict-separation behavior claimed in Conjecture 2 and Theorem 1.'''
  - 'Theorem thm:spectral-frontier — ''The derivation does not deliver the orchestrator-required flagship tier. The actual kernel is a generic row-stacking/operator-norm identity: define A as the stack of procedure differences, define Delta as sup ||Au||, then conclude equivalence iff Delta=0. It does not derive a new sharp spectral threshold in rho, epsilon_M, r, b, or design orbits.'''
  - 'Lemma lem:cov-decomposition — ''Lines 807-836 are explicitly definitional: the covariance discrepancy equals the covariance row block because that row block was defined to be the discrepancy.'''
  - 'Lemma exposure-score decomposition (angle 1) — ''The design-orbit decomposition claims theta_RT,n has the same target part tau_ds,n(r) without an exposure-fiber/orbit equality assumption'' — this equality is exactly what the theorem is supposed to diagnose.'
  - 'Main theorem novelty (angle 2) — ''After the procedure maps are defined, Delta_eta=0 iff C(eta) is in ker(A) is a generic null-space identity, not a flagship theorem-level contribution relative to the cited network-interference literature.'''
  - 'Assumptions 5, 7, 8, 9 (all angles) — ''Load-bearing theorem content is assumed: point-functional consistency/separation, convergence of all limiting operators, nondegenerate strict separation, and covariance efficiency.'''
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  Proposed a flagship sharp spectral non-equivalence frontier between ANI, network-cluster-robust, and randomization-test estimators, parameterized in (rho, epsilon_M, r, b_n, design orbits). All three Stage 0 derivation attempts collapsed the headline theorem to a generic finite-dimensional null-space identity: define A_n as the stacked procedure differences and Delta_eta as sup ||A_n u||, then equivalence iff Delta_eta = 0 — which is definitional, not a derived spectral threshold. The substantive econometric content (LLN separation, operator convergence, strict open-set separation) was uniformly shifted into Assumptions 5/7/8/9 rather than proved, and the headline Lemma 1 assumed the exposure-fiber/orbit equality that the theorem was supposed to diagnose.
banked_on: "2026-05-16"
---

# panel_approx_nbhd_interference / v1 — Failed

**Topic.** Sharp non-equivalence and strict-extension theorem between three leading interference / network spillover identification estimators that handle SUTVA violation under approximate neighborhood interference: the Approximate Neighborhood Interference (ANI) estimator of Leung (2022, Econometrica) using exposure-mapping projection at fixed neighborhood radius r, the network-cluster-robust estimator of Leung (2023, Econometrica) with HAC-style cluster-bandwidth selection, and the randomization-test estimator of Basse, Ding, Feller, Toulis (2024, Econometrica) using exact randomization-based inference under partial interference. All three target the direct + spillover average treatment effect under bounded-degree network and exposure-mapping additivity. The flagship question (axis b: non-equivalence frontier between three named published network estimators): characterize the sharp boundary in (network density, exposure-radius, randomization-design) parameter space at which the three estimators have asymptotically equivalent identifying functionals versus strictly different limit functionals, as a function of (i) the network degree distribution rho, (ii) the exposure-misspecification rate epsilon_M, and (iii) the cluster-bandwidth scaling b_n. The kernel claim is a closed-form spectral non-equivalence theorem: ANI, network-CR, and randomization-test estimators identify the same direct + spillover effect and achieve identical asymptotic variance if and only if a degree-radius condition mu_max(rho, epsilon_M) <= mu_star, where mu_star is a sharp threshold equal to the smallest singular value of an explicit observable kernel built from rho, epsilon_M, and b_n; when mu_max > mu_star, the three diverge — ANI biased proportional to exposure-misspecification, network-CR consistent but inefficient by bandwidth, randomization-test achieves the design-based efficiency bound. mu_star is a NEW mathematical object, NOT existence/absence from prior. Recovers Leung 2022 ANI consistency under correctly-specified exposure (epsilon_M=0) and provides the first sharp triple-non-equivalence boundary for ANI / network-CR / randomization-test estimators in closed form.

**Novelty target.** flagship

**D-0.5 verdict.** ACCEPT

**D0.5 verdict.** REJECT

**Banking reason.** D-0.5 ACCEPT@flagship on three consecutive angles (deepest pipeline reach of any run in this batch); all 3 D0 derivations completed; all 3 D0.5 reviews REJECTed on structural novelty — kernel reduces to tautological row-stacking / orbit-decomposition identity (Delta = sup||A_n u||, equivalence iff Delta=0) with substantive econometric content (LLN separation, operator convergence) shifted into assumptions. Each D0.5 reject triggered angle pivot rather than revise. Intervention-judge synthesis fallback PATCH FIRED LIVE on angle 2 (Bug B fix verified). Math sound at field tier for spectral compatibility frontier; flagship kernel structurally untenable — non-equivalence between ANI/network-CR/randomization-test reduces to trivial identity at the population truth.

## Key files

- `panel_approx_nbhd_interference_v1_state.json` — pipeline state at banking (`banked: true`).
- `panel_approx_nbhd_interference_v1_proposal.tex` — final proposal version.
- `panel_approx_nbhd_interference_v1.tex` — derivation note (if D0 ran).
- `panel_approx_nbhd_interference_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `panel_approx_nbhd_interference_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
