---
qid: eid_dml_orth_uniform
spec: v2
topic: "Sharp uniform-in-DGP non-equivalence theorem between three leading double machine learning (DML) estimators for the average treatment effect under unconfoundedness: the original DML cross-fit estimator (Chernozhukov, Chetverikov, Demirer, Duflo, Hansen, Newey, Robins 2018, Econometrics Journal), the locally-robust orthogonal-score (LRO) estimator (Chernozhukov-Escanciano-Ichimura-Newey-Robins 2022, Econometrica), and the automatic debiased ML estimator (Chernozhukov-Newey-Singh 2022, Econometrica). All three target the same population functional E[Y(1)-Y(0)] and have first-order-equivalent influence functions when nuisance functions are estimated at the standard L^2 rate o(n^{-1/4}). The flagship question (axis b: non-equivalence frontier between three named published estimators): characterize the sharp boundary in nuisance-misspecification rate space r_g = r_g(n) for the outcome regression and r_p = r_p(n) for the propensity at which DML, LRO, and ADML have asymptotically equivalent variance vs. strictly different uniform-in-DGP variance lower bounds. The kernel claim is a closed-form spectral non-equivalence theorem: the three estimators achieve identical asymptotic variance bounds (and thus identical Wald confidence intervals at first order) if and only if r_g + r_p > rho_star, where rho_star is a sharp threshold function of the smallest eigenvalue of an explicit observable covariance kernel formed from the outcome residual and the propensity Riesz representer. When r_g + r_p <= rho_star, LRO and ADML strictly dominate DML by orthogonality, but LRO and ADML themselves diverge in variance lower bound proportional to the spectral gap, with ADML achieving the global semiparametric efficiency bound and LRO achieving only a local one. rho_star is a NEW mathematical object computable from observable second moments, not an existence/absence statement from prior work. Recovers the textbook L^2-rate equivalence (Chernozhukov et al 2018) at the boundary r_g+r_p=O(n^{-1/4}) and provides the first sharp triple non-equivalence boundary for DML estimators in closed form, separating the regime where DML, LRO, ADML give identical inference from the regime where the ordering DML < LRO < ADML is strict and quantifiable."
novelty_target: flagship
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: "constructive_object_missing"
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - 'Conjecture 1: C-wellposed — ''The load-bearing objects called exact published DML/LRO/ADML reports are still not pinned to explicit formulas from the cited papers: q_pub, c_{L,A,n}, and c_AD,n are introduced abstractly, so Gamma_{mell,n} and rho_star are not yet canonical.'''
  - 'Conjecture 1: C-sanity — ''With the locked finite-support q_pub, the propensity-score block is orthogonal to psi_n and to the outcome residual score blocks, so the full ADML projection has zero propensity coefficient and c_AD lies in the outcome-block LRO space; the assumed LRO-ADML separation is vacuous.'''
  - 'Assumption lro-separated: C-coherence — ''The noncontainment premise c_AD notin C_L,Apub contradicts the proposal''s own q_pub and L_Apub definitions in the finite-support audit design.'''
  - 'Conjecture 1: C-coherence — ''Assumption ass:lro-separated contradicts the normal-equation definition of c_{L,A,n}: c_{L,A,n} is already the Omega_n-projection of c_AD,n onto C_{L,A,n}, so the fixed non-equivalent LRO premise is impossible as written.'''
  - 'Conjecture 2: C-coherence — ''The proposed iff condition c_{L,A,n}=Pi_C^Omega c_AD,n is tautological under Assumption ass:reports, making the claimed outside-equivalence branch empty.'''
  - 'Conjecture 1: N-mischar — ''The proposal calls the outcome-block selector L_Apub an exact published LRO report, but the verified LRO paper gives a general locally robust GMM/sandwich construction, not this specific ATE outcome-only selector.'''
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  This run attempted a sharp spectral non-equivalence frontier (rho_star) characterizing when DML, LRO, and ADML ATE variance reports diverge, pivoting from the v1 failure at the common-EIF population variance collapse. The key objects — exact published variance-report coefficients c_{L,A,n} and c_AD,n, the observable covariance kernel's spectral threshold, and the LRO coefficient subspace C_{L,n} — were never pinned to concrete formulas from the cited papers across three revision angles and five iterations each. The flagship strict LRO-ADML separation was ultimately shown self-contradictory: in the proposal's own finite-support audit design, the ADML coefficient c_AD lies in the outcome-block LRO space, making the assumed LRO-ADML separation vacuous by construction.
banked_on: "2026-05-21"
---

# eid_dml_orth_uniform / v2 — Failed

**Topic.** Sharp uniform-in-DGP non-equivalence theorem between three leading double machine learning (DML) estimators for the average treatment effect under unconfoundedness: the original DML cross-fit estimator (Chernozhukov, Chetverikov, Demirer, Duflo, Hansen, Newey, Robins 2018, Econometrics Journal), the locally-robust orthogonal-score (LRO) estimator (Chernozhukov-Escanciano-Ichimura-Newey-Robins 2022, Econometrica), and the automatic debiased ML estimator (Chernozhukov-Newey-Singh 2022, Econometrica). All three target the same population functional E[Y(1)-Y(0)] and have first-order-equivalent influence functions when nuisance functions are estimated at the standard L^2 rate o(n^{-1/4}). The flagship question (axis b: non-equivalence frontier between three named published estimators): characterize the sharp boundary in nuisance-misspecification rate space r_g = r_g(n) for the outcome regression and r_p = r_p(n) for the propensity at which DML, LRO, and ADML have asymptotically equivalent variance vs. strictly different uniform-in-DGP variance lower bounds. The kernel claim is a closed-form spectral non-equivalence theorem: the three estimators achieve identical asymptotic variance bounds (and thus identical Wald confidence intervals at first order) if and only if r_g + r_p > rho_star, where rho_star is a sharp threshold function of the smallest eigenvalue of an explicit observable covariance kernel formed from the outcome residual and the propensity Riesz representer. When r_g + r_p <= rho_star, LRO and ADML strictly dominate DML by orthogonality, but LRO and ADML themselves diverge in variance lower bound proportional to the spectral gap, with ADML achieving the global semiparametric efficiency bound and LRO achieving only a local one. rho_star is a NEW mathematical object computable from observable second moments, not an existence/absence statement from prior work. Recovers the textbook L^2-rate equivalence (Chernozhukov et al 2018) at the boundary r_g+r_p=O(n^{-1/4}) and provides the first sharp triple non-equivalence boundary for DML estimators in closed form, separating the regime where DML, LRO, ADML give identical inference from the regime where the ordering DML < LRO < ADML is strict and quantifiable.

**Novelty target.** flagship

**Stage -0.5 verdict.** NO-PASS

**Stage 0.5 verdict.** NA

**Banking reason.** Stage -0.5 NO-PASS — pivot budget exhausted (3 angles x 5 revise rounds). Math-solve upgrade never tested: D-0.5 novelty reviewer rejected every variant because the banked v1 parent occupies the same kernel slot in the catalogue and cannot be dodged for a sibling re-test.

## Key files

- `eid_dml_orth_uniform_v2_state.json` — pipeline state at banking (`banked: true`).
- `eid_dml_orth_uniform_v2_proposal.tex` — final proposal version.
- `eid_dml_orth_uniform_v2.tex` — derivation note (if Stage 0 ran).
- `eid_dml_orth_uniform_v2_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `eid_dml_orth_uniform_v2_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
