---
qid: eid_dml_orth_uniform
spec: v1
topic: "Sharp uniform-in-DGP non-equivalence theorem between three leading double machine learning (DML) estimators for the average treatment effect under unconfoundedness: the original DML cross-fit estimator (Chernozhukov, Chetverikov, Demirer, Duflo, Hansen, Newey, Robins 2018, Econometrics Journal), the locally-robust orthogonal-score (LRO) estimator (Chernozhukov-Escanciano-Ichimura-Newey-Robins 2022, Econometrica), and the automatic debiased ML estimator (Chernozhukov-Newey-Singh 2022, Econometrica). All three target the same population functional E[Y(1)-Y(0)] and have first-order-equivalent influence functions when nuisance functions are estimated at the standard L^2 rate o(n^{-1/4}). The flagship question (axis b: non-equivalence frontier between three named published estimators): characterize the sharp boundary in nuisance-misspecification rate space r_g = r_g(n) for the outcome regression and r_p = r_p(n) for the propensity at which DML, LRO, and ADML have asymptotically equivalent variance vs. strictly different uniform-in-DGP variance lower bounds. The kernel claim is a closed-form spectral non-equivalence theorem: the three estimators achieve identical asymptotic variance bounds (and thus identical Wald confidence intervals at first order) if and only if r_g + r_p > rho_star, where rho_star is a sharp threshold function of the smallest eigenvalue of an explicit observable covariance kernel formed from the outcome residual and the propensity Riesz representer. When r_g + r_p <= rho_star, LRO and ADML strictly dominate DML by orthogonality, but LRO and ADML themselves diverge in variance lower bound proportional to the spectral gap, with ADML achieving the global semiparametric efficiency bound and LRO achieving only a local one. rho_star is a NEW mathematical object computable from observable second moments, not an existence/absence statement from prior work. Recovers the textbook L^2-rate equivalence (Chernozhukov et al 2018) at the boundary r_g+r_p=O(n^{-1/4}) and provides the first sharp triple non-equivalence boundary for DML estimators in closed form, separating the regime where DML, LRO, ADML give identical inference from the regime where the ordering DML < LRO < ADML is strict and quantifiable."
novelty_target: flagship
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "kernel_substituted"  # was tier_genuinely_below; reviews show the flagship kernel was substituted by a stipulated variance geometry, not merely framed one tier too high
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  # Conj-1 (student-frontier) and Conj-2 (two-cell-witness) were both marked
  # "confirmed" by the split D0 orchestrator, but all three D0.5 reviews graded
  # the derivation "revise" / below-flagship because the headline is imported by
  # assumption. Verbatim reviewer phrases (eid_dml_orth_uniform_v1_reviews.jsonl,
  # stage_0.5_to_0 attempts):
  - "the variance-rule linearization assumes the main frontier object, so Theorem student-frontier is an algebraic consequence of a free Bucket A-style premise rather than a derived named-estimator result"  # Conj-1
  - "the DML, LRO, and ADML adjoint matrices are stipulated, not derived from the published variance rules, so the witness proves a matrix projection example rather than an actual DML--LRO--ADML separation"  # Conj-2
  - "Assessed tier is below flagship: the current derivation is at most field/subfield because the comparator frontier is not derived from the named published estimators and the generic-class witness is stipulated through structural matrices"  # tier floor
  - "The proof asserts nonempty openness by perturbing stipulated coefficients and matrices, but does not construct a nondegenerate observable law whose actual estimator adjoints equal those matrices"  # open-set witness
  # Earlier (first-D0) stage_0.5_to_0 reject went further: at the population
  # truth the named DML/LRO/ADML variance maps coincide with identical
  # Riesz-direction derivatives — i.e. the proposal's strict-frontier kernel was
  # refuted, and the later "confirmation" only survives by stipulating the gap:
  - "the written named population variance maps all equal V_n at the truth and have the same Riesz-direction derivative ... That is a correction to the proposal, not a flagship equivalence/non-equivalence frontier between named published estimators"  # first-D0 reject
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  Attempted a flagship closed-form spectral threshold rho* separating a regime
  where DML/LRO/ADML give identical Wald CIs from one where the ordering
  DML<LRO<ADML is strict and quantifiable. The first D0/D0.5 round refuted the
  kernel: at the population truth the three named variance maps coincide with
  identical Riesz-direction derivatives, so the strict frontier is false as
  stated. A second (post-solver-upgrade) D0 split confirmed both conjectures
  (studentization frontier + two-cell witness), but only by stipulating the
  variance-ratio expansion and the DML/LRO/ADML adjoint matrices as
  assumptions; all three D0.5 reviews graded it below flagship (at most
  field/subfield) and the intervention judge JSON-failed 3x, routing to user.
  What remains open: deriving the projection-index geometry and an open set of
  observable laws from the actual named variance rules (AIPW / sandwich / Riesz)
  rather than assuming them.
banked_on: "2026-05-21"
---

# eid_dml_orth_uniform / v1 — Downgraded

**Topic.** Sharp uniform-in-DGP non-equivalence theorem between three leading double machine learning (DML) estimators for the average treatment effect under unconfoundedness: the original DML cross-fit estimator (Chernozhukov, Chetverikov, Demirer, Duflo, Hansen, Newey, Robins 2018, Econometrics Journal), the locally-robust orthogonal-score (LRO) estimator (Chernozhukov-Escanciano-Ichimura-Newey-Robins 2022, Econometrica), and the automatic debiased ML estimator (Chernozhukov-Newey-Singh 2022, Econometrica). All three target the same population functional E[Y(1)-Y(0)] and have first-order-equivalent influence functions when nuisance functions are estimated at the standard L^2 rate o(n^{-1/4}). The flagship question (axis b: non-equivalence frontier between three named published estimators): characterize the sharp boundary in nuisance-misspecification rate space r_g = r_g(n) for the outcome regression and r_p = r_p(n) for the propensity at which DML, LRO, and ADML have asymptotically equivalent variance vs. strictly different uniform-in-DGP variance lower bounds. The kernel claim is a closed-form spectral non-equivalence theorem: the three estimators achieve identical asymptotic variance bounds (and thus identical Wald confidence intervals at first order) if and only if r_g + r_p > rho_star, where rho_star is a sharp threshold function of the smallest eigenvalue of an explicit observable covariance kernel formed from the outcome residual and the propensity Riesz representer. When r_g + r_p <= rho_star, LRO and ADML strictly dominate DML by orthogonality, but LRO and ADML themselves diverge in variance lower bound proportional to the spectral gap, with ADML achieving the global semiparametric efficiency bound and LRO achieving only a local one. rho_star is a NEW mathematical object computable from observable second moments, not an existence/absence statement from prior work. Recovers the textbook L^2-rate equivalence (Chernozhukov et al 2018) at the boundary r_g+r_p=O(n^{-1/4}) and provides the first sharp triple non-equivalence boundary for DML estimators in closed form, separating the regime where DML, LRO, ADML give identical inference from the regime where the ordering DML < LRO < ADML is strict and quantifiable.

**Novelty target.** flagship

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REVISE

**Banking reason.** D0 re-test (post D0-solver upgrade) on prior kernel_substituted parent: D0 produced an honest artifact (split orchestrator settled all verdicts) but D0.5 reviewer judged the derivation below flagship — 'comparator frontier is not derived from the named published estimators and the generic-class witness is stipulated through structural matrices.' Intervention LLM hit JSON-parse failure 3x and fell back to route=user. Honest negative result: defect is upstream of D0 (proposal-level kernel/tier ceiling), not D0 solver.

## Key files

- `eid_dml_orth_uniform_v1_state.json` — pipeline state at banking (`banked: true`).
- `eid_dml_orth_uniform_v1_proposal.tex` — final proposal version.
- `eid_dml_orth_uniform_v1.tex` — derivation note (if Stage 0 ran).
- `eid_dml_orth_uniform_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `eid_dml_orth_uniform_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
