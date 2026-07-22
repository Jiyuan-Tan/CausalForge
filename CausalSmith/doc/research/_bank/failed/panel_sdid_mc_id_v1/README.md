---
qid: panel_sdid_mc_id
spec: v1
topic: "Sharp non-equivalence and strict-extension theorem between three leading panel identification estimators that combine pre-treatment unit weighting with time-period reweighting: the original Synthetic DiD (Arkhangelsky, Athey, Hirshberg, Imbens, Wager 2021, AER) with double-difference weights chosen by quadratic regularization, the Augmented Synthetic Control / matrix completion estimator (Athey, Bayati, Doudchenko, Imbens, Khosravi 2021, JASA) with nuclear-norm penalization on the donor-pool outcome matrix, and the staggered Synthetic DiD with cohort-time weights (Arkhangelsky-Imbens-Lei-Luo 2024, Quantitative Economics) extending SDiD to multiple treated cohorts. All three target the average treatment effect on the treated (ATT) under interactive fixed effects with bounded factor-loading rank R. The flagship question (axis b: non-equivalence frontier between three named published synthetic-control / matrix completion estimators OR axis c: strict extension to bounded-rank interactive-FE regime): characterize the sharp boundary in (R, T_pre, N_donor) parameter space at which the three estimators have asymptotically equivalent identifying functionals versus strictly different limit functionals. The kernel claim is a closed-form spectral non-equivalence theorem: SDiD, ASCM, and staggered-SDiD identify the same ATT and achieve identical asymptotic variance if and only if R <= R_star where R_star is a sharp threshold function of the smallest singular value of an explicit observable kernel matrix combining the donor pre-period outcome covariance, the cohort-time treated outcome regression, and the regularization strength sequence; when R > R_star, the three estimators have strictly different limit functionals — SDiD has bias proportional to the spectral gap, ASCM is consistent but inefficient by a factor depending on the nuclear-norm strength, and staggered-SDiD achieves the semiparametric efficiency bound. R_star is a NEW mathematical object computable from observable second moments + regularization sequence, NOT an existence/absence statement from prior work. Recovers the well-known equivalence under low-rank interactive FE (R=0 or R<<T_pre) and provides the first sharp triple-non-equivalence boundary for SDiD / matrix completion / staggered-SDiD in closed form."
novelty_target: flagship
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: "assumption_omitted"
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - 'Theorem 1 / C-sanity: The claimed inclusion {K_sdid=0} subset {K_rank,R=0} fails as stated: because lambda is unconstrained in K_sdid, any w with nonzero residual x0-X^T w can choose lambda to hit S_R, making K_sdid=0 without rank-completion visibility or uniqueness.'
  - 'Formal setup / Theorem 1 / C-wellposed: K_rank,R=0 is defined as an infimum distance to S_R but then interpreted as local uniqueness of the rank-R completion; the displayed functional encodes existence of a rank completion at S_R, not uniqueness.'
  - 'Conjecture 1 / C-sanity: The strict-lattice conjecture depends on the Theorem 1 lattice order, but the SDiD node is currently too permissive and can collapse the lattice for algebraic reasons unrelated to SDiD''s published first-order conditions.'
  - 'Conjecture 2 / C-wellposed: Phi_ridge, Phi_sdid, Phi_nuc and ''differ by first order in the penalty limit'' are named but not mathematically defined, so the exceptional set and stability claim are not yet precise statements.'
  - 'Conjecture 1 / C-wellposed: R_star is advertised as observable/computable, but its definition quantifies over all completions Q and tangent bases Pi_r(Q); the proposal needs a finite observable algorithm or optimization problem.'
  - 'Conjecture 1 / C-wellposed: The condition K=0 only annihilates tangent directions; it lacks an affine/basepoint residual term ensuring level equality of the ATT functionals on the completion class.'
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  Attempted a strict span-lattice theorem characterizing when convex SCM, ridge ASCM, SDiD, and nuclear-norm matrix completion induce the same ATT functional under bounded-rank IFE, with Conjectures 1-2 on open-set strict separation witnesses. The novelty was confirmed new or incremental-novel across all 11 reviewer rounds; the area collapsed on well-posedness: the SDiD certificate K_sdid was too permissive (unconstrained lambda could trivially satisfy K_sdid=0), K_rank,R conflated existence with uniqueness of the rank-R completion, and Phi_ridge/Phi_sdid/Phi_nuc were named without finite-dimensional definitions. The underlying lattice question remains genuinely open and flagship-grade; the proposal was stopped by definitional defects, not by a refutation of the math.
banked_on: "2026-05-16"
---

# panel_sdid_mc_id / v1 — Failed

**Topic.** Sharp non-equivalence and strict-extension theorem between three leading panel identification estimators that combine pre-treatment unit weighting with time-period reweighting: the original Synthetic DiD (Arkhangelsky, Athey, Hirshberg, Imbens, Wager 2021, AER) with double-difference weights chosen by quadratic regularization, the Augmented Synthetic Control / matrix completion estimator (Athey, Bayati, Doudchenko, Imbens, Khosravi 2021, JASA) with nuclear-norm penalization on the donor-pool outcome matrix, and the staggered Synthetic DiD with cohort-time weights (Arkhangelsky-Imbens-Lei-Luo 2024, Quantitative Economics) extending SDiD to multiple treated cohorts. All three target the average treatment effect on the treated (ATT) under interactive fixed effects with bounded factor-loading rank R. The flagship question (axis b: non-equivalence frontier between three named published synthetic-control / matrix completion estimators OR axis c: strict extension to bounded-rank interactive-FE regime): characterize the sharp boundary in (R, T_pre, N_donor) parameter space at which the three estimators have asymptotically equivalent identifying functionals versus strictly different limit functionals. The kernel claim is a closed-form spectral non-equivalence theorem: SDiD, ASCM, and staggered-SDiD identify the same ATT and achieve identical asymptotic variance if and only if R <= R_star where R_star is a sharp threshold function of the smallest singular value of an explicit observable kernel matrix combining the donor pre-period outcome covariance, the cohort-time treated outcome regression, and the regularization strength sequence; when R > R_star, the three estimators have strictly different limit functionals — SDiD has bias proportional to the spectral gap, ASCM is consistent but inefficient by a factor depending on the nuclear-norm strength, and staggered-SDiD achieves the semiparametric efficiency bound. R_star is a NEW mathematical object computable from observable second moments + regularization sequence, NOT an existence/absence statement from prior work. Recovers the well-known equivalence under low-rank interactive FE (R=0 or R<<T_pre) and provides the first sharp triple-non-equivalence boundary for SDiD / matrix completion / staggered-SDiD in closed form.

**Novelty target.** flagship

**D-0.5 verdict.** NO-PASS

**D0.5 verdict.** NA

**Banking reason.** D-0.5 NO-PASS@flagship: 10/11 versions REVISE@flagship across angles 0+1 (only angle0 v4 dropped to field; angle2 v1 REJECT@not-publishable). Same cap-bound flagship pattern as Run 4 (BJS) and Run 5 (DML). SDiD/ASCM/staggered-SDiD non-equivalence kernel consistently recognized as axis-b flagship-grade but proposer can't tighten well-posedness flags within 5-revise cap before angle 2 hits a definitional defect. Math+novelty sound at flagship; ACCEPT was reachable with looser cap or proposer-side well-posedness guard.

## Key files

- `panel_sdid_mc_id_v1_state.json` — pipeline state at banking (`banked: true`).
- `panel_sdid_mc_id_v1_proposal.tex` — final proposal version.
- `panel_sdid_mc_id_v1.tex` — derivation note (if D0 ran).
- `panel_sdid_mc_id_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `panel_sdid_mc_id_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
