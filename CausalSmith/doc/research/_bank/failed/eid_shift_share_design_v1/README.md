---
qid: eid_shift_share_design
spec: v1
topic: "Sharp non-equivalence/strict-extension theorem between three leading shift-share / formula IV estimators: the canonical Bartik-style shift-share IV (Borusyak, Hull, Jaravel 2022, Review of Economic Studies) used with shock-level identifying variation, the recentered-instrument variant (Borusyak and Hull 2023, Econometrica) that subtracts the expected exposure-weighted shock under randomized counterfactual shock realizations, and the formula-IV / design-based variant (Borusyak 2025, Econometrics Journal) that relaxes the shock-exogeneity moment to a covariate-conditional design-based moment. All three target the structural exposure coefficient beta_exp on the same DGP under shock independence + exposure additivity. The flagship question (axis b: non-equivalence frontier between named published shift-share estimators): characterize the sharp boundary in shock-correlation/dependency space at which the three estimators have asymptotically equivalent identifying moments vs. strictly different limit functionals, as a function of (i) the shock cross-correlation matrix Omega, (ii) the exposure-share covariance Pi, and (iii) the covariate-conditional shock-mean leakage rate epsilon. The kernel claim is a closed-form spectral non-equivalence theorem: the Bartik IF, the recentered-IV IF, and the Borusyak design-IF identify the same structural beta_exp if and only if a spectral condition lambda_max(Omega Pi) <= lambda_star holds, where lambda_star is a sharp threshold equal to the smallest singular value of an explicit observable kernel built from Pi and the design-leakage rate epsilon; when lambda_max(Omega Pi) > lambda_star, the Bartik estimator is biased proportional to the shock-correlation excess while the recentered-IV remains consistent and the design-IV achieves the semiparametric efficiency bound. lambda_star is a NEW mathematical object computable from observable shock cross-moments + exposure-share covariance + design-leakage rate, NOT an existence/absence statement from prior work. Recovers the classical Bartik consistency under uncorrelated shocks (lambda_max(Omega Pi)=0) and provides the first sharp triple-non-equivalence boundary for shift-share / formula IV in closed form."
novelty_target: flagship
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: "kernel_substituted"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - 'Theorem 1: already-known — ''The moment decomposition is the standard recentered-formula-IV bias algebra from BorusyakHull2023Econometrica/BorusyakHullJaravel2025ECTJ written with q_B=0, q_R=m_R, q_D=m_D.'' (angle2_v1, N-pub)'
  - 'Conjecture 1: already-known — ''The claimed sharp uniform Pi-null frontier is subsumed by the published necessary-and-sufficient recentered-instrument validity condition; Pi-null is just the linear-share way to say the expected formula instrument is zero on all exposure rows.'' (angle2_v1, N-pub)'
  - 'Conjecture 1: N-mischar — ''The §8 comparison says BorusyakHull2023Econometrica/BorusyakHullJaravel2025ECTJ do not state an iff frontier, but their recentered formula-instrument characterization is already an iff validity boundary; the proposal only rewrites it in Pi notation.'' (angle2_v1)'
  - 'Conjecture 2: N-strawman — ''The witness targets a generic recentered-versus-design separation rather than a specific published estimator/workflow claim that asserts equality under positive leakage; it is a pedagogical example of known recentering bias.'' (angle2_v1)'
  - 'Theorem 1: C-wellposed (angle0_v1) — ''Omega is defined as E[(G-m_D)(G-m_D)''|S,C] with unit marginal shock scale, so Omega=0 means zero shock variance, not uncorrelated shocks, and conflicts with nonzero first stage.'''
  - 'Conjecture 1: C-wellposed (angle0_v1) — ''Equality of beta_B, beta_R, beta_D, and beta_exp cannot be determined from Omega, Pi, and epsilon alone without a defined residual shock-loading or covariance term for U.'''
  - 'Conjecture 2: C-wellposed (angle0_v1) — ''The scalar beta_R-beta_D is said to equal the projection of the vector epsilon onto A_epsilon; the statement needs a scalar functional of that projection.'''
  - 'Conjecture 1: C-sanity (angle1_v1) — ''The claimed exact consistency regions ker(Pi^{1/2}A) do not reduce from the stated moment expansion; the expansion gives q_A-orthogonality regions, so the flagship null-space frontier is not coherent as stated.'''
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  The proposal attempted a flagship-tier sharp Pi-loaded leakage-null frontier theorem separating canonical Bartik SSIV, Borusyak-Hull recentered IV, and design-based formula IV moments, framed as a new necessary-and-sufficient characterization. Across three angles and three reviewer rounds, every incarnation of the headline kernel (Theorem 1 + Conjecture 1) was ruled already-known: the 'Pi-null frontier' is merely a linear-share restatement of the recentered formula-instrument validity condition already stated as an iff boundary in BorusyakHull2023Econometrica and BorusyakHullJaravel2025ECTJ. Recurring soundness defects — Omega=0 conflated with uncorrelated shocks, scalar/vector projection mismatch in beta_R-beta_D, missing residual shock-loading term — were not corrected across angle pivots, and the pivot budget was exhausted with all three angles at REJECT/not-publishable.
banked_on: "2026-05-16"
---

# eid_shift_share_design / v1 — Failed

**Topic.** Sharp non-equivalence/strict-extension theorem between three leading shift-share / formula IV estimators: the canonical Bartik-style shift-share IV (Borusyak, Hull, Jaravel 2022, Review of Economic Studies) used with shock-level identifying variation, the recentered-instrument variant (Borusyak and Hull 2023, Econometrica) that subtracts the expected exposure-weighted shock under randomized counterfactual shock realizations, and the formula-IV / design-based variant (Borusyak 2025, Econometrics Journal) that relaxes the shock-exogeneity moment to a covariate-conditional design-based moment. All three target the structural exposure coefficient beta_exp on the same DGP under shock independence + exposure additivity. The flagship question (axis b: non-equivalence frontier between named published shift-share estimators): characterize the sharp boundary in shock-correlation/dependency space at which the three estimators have asymptotically equivalent identifying moments vs. strictly different limit functionals, as a function of (i) the shock cross-correlation matrix Omega, (ii) the exposure-share covariance Pi, and (iii) the covariate-conditional shock-mean leakage rate epsilon. The kernel claim is a closed-form spectral non-equivalence theorem: the Bartik IF, the recentered-IV IF, and the Borusyak design-IF identify the same structural beta_exp if and only if a spectral condition lambda_max(Omega Pi) <= lambda_star holds, where lambda_star is a sharp threshold equal to the smallest singular value of an explicit observable kernel built from Pi and the design-leakage rate epsilon; when lambda_max(Omega Pi) > lambda_star, the Bartik estimator is biased proportional to the shock-correlation excess while the recentered-IV remains consistent and the design-IV achieves the semiparametric efficiency bound. lambda_star is a NEW mathematical object computable from observable shock cross-moments + exposure-share covariance + design-leakage rate, NOT an existence/absence statement from prior work. Recovers the classical Bartik consistency under uncorrelated shocks (lambda_max(Omega Pi)=0) and provides the first sharp triple-non-equivalence boundary for shift-share / formula IV in closed form.

**Novelty target.** flagship

**D-0.5 verdict.** NO-PASS

**D0.5 verdict.** NA

**Banking reason.** D-0.5 NO-PASS — all 3 angles REJECT@not-publishable on v1 (immediate, no revise cycle). Recurring C-wellposed defects across pivots: Omega definition normalization wrong (Omega=0 ≠ uncorrelated shocks; uncorrelated normalized shocks yield diagonal not zero), scalar/vector projection mismatch (beta_R-beta_D claimed scalar but defined via vector projection), missing residual shock-loading term needed for beta-equality determination. Proposer didn't adjust across angle pivots. Reviewer also flagged missing Borusyak-Hull 2025 NBER w33594 as a closer comparator. Failure is proposer-side proposal-quality, not rubric incompatibility. Math kernel could be revised, but pivot budget exhausted.

## Key files

- `eid_shift_share_design_v1_state.json` — pipeline state at banking (`banked: true`).
- `eid_shift_share_design_v1_proposal.tex` — final proposal version.
- `eid_shift_share_design_v1.tex` — derivation note (if D0 ran).
- `eid_shift_share_design_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `eid_shift_share_design_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
