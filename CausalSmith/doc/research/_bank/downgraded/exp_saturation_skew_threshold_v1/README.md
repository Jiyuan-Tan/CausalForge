---
qid: exp_saturation_skew_threshold
spec: v1
topic: "Study optimal saturation design for two-stage randomized-saturation experiments under isolated partial interference by making the full bounded-support moment program the theorem object: under a specialized within-cluster homogeneous linear-in-share working model (a specialization of Cai, Pouget-Abadie and Airoldi 2022, not the full parent model), minimize V(nu)=V0+V1*m2+V3*m3+V4*(m4-m2^2) over laws nu on [0,1] with mean pbar. Prove the main result as a necessary-and-sufficient quartic dual/KKT global-optimality certificate for any candidate law, with a support-at-most-3 optimizer reduction. Only as a scoped corollary, in the positive-penalty symmetric-candidate regime V1>0,V4>0, characterize when the stratified symmetric law delta_pbar is globally optimal by the closed threshold min_{d in [-pbar,1-pbar]}(V1+V3*d+V4*d^2)>=0; when this fails construct the skewed two/three-point optimizer. Include the witness pbar=1/3,V1=1,V4=1,V3=-10: (2/3)delta_0+(1/3)delta_1 has m2=2/9,m3=2/27,m4-m2^2=2/81 and improves by -40/81 over delta_pbar. Recover the SUTVA corner V3=V4=0: V is linear in m2, so V1>0 gives within-cluster stratified delta_pbar, V1<0 gives cluster Bernoulli (1-pbar)delta_0+pbar delta_1, and V1=0 ties. Add finite-M attainability for denominator-compatible support masses/saturations and an O(1/M+1/m) rounding-loss clause, distinguishing M*pbar integrality for cluster Bernoulli vertices from m*pbar integrality for within-cluster stratified saturation."
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "Abstract quartic-program theory (global dual/KKT certificate, support-at-most-3, stratified threshold, finite-M attainability) is SOUND for general V — not the gap."
  - "DESIGN-SKEW HEADLINE DEGENERATE under the run's own model: HomogeneousLinearShareWorkingModel fixes a single global (beta0,beta1,gamma0,gamma1) for all units, so the Cai skew/kurtosis coefficients V3,V4 (sample variances of unit-level interference params gamma_i) are identically 0. The design variance reduces to V0+V1*Var[pi] with no skew dependence — the saturation-skew DESIGN claim is vacuous in the modeled setting."
  - "D0.5 PASSED this; the defect was caught only at formalization, paper-grounded against Cai-Pouget-Abadie-Airoldi arXiv:2203.09682 (Thm variance-dim / appendix Eve's-law derivation) and Lean-confirmed in Basic.lean. (D0.5 math review since hardened with a non-degeneracy/liveness check to catch this class pre-formalization.)"
  - "Formalization HALTED at F2/F3: F2 scaffold complete (gates threaded as Prop hypotheses), F3 proofs incomplete (sorries remained) when the run was stopped."
reusable_artifacts:
  - "discovery/core.json + formalization/ : the abstract quartic-program scaffold (sound, general V; reusable as-is)."
  - "Built substrate (committed bbc9fee7, CausalSmith/CausalSmith/Mathlib/): CompactContinuousMin (EVT — discharges the semialgebraic-optimization attainment gate directly); MomentSliceSupport (FULL Richter-Rogosinski heart, committed 88beec20, verified sorry-free + axiom-clean: not_four_distinct_in_support measure-level perturbation core, isAtomic_le_three_of_isExtremePoint = the extreme=>atomic step Mathlib lacks, + Prokhorov attainment). Remaining for full Winkler gate discharge: the Caratheodory-barycenter route bypassing Krein-Milman (only IsCompact(convexHull(Phi''K)), ~40 lines, not yet in Mathlib)."
  - "Cai algebra fragment + cached paper in session scratchpad: CaiExpansionAlgebra.partial.lean (empiricalLaw_centeredMoment moment change-of-variables; detDiffInMeans_eq affine collapse / V2=0 origin); scratchpad/cai_paper/ (randomized.tex, appendix.tex)."
seeds_burned: []
proof_attempt_summary: |
  Formalized the abstract quartic-program optimization theory (sound, general V) and built the
  supporting substrate concurrently, but halted at F2/F3 after a paper-grounded build revealed the
  run's homogeneous working model forces V3=V4=0 — the design variance carries no skew, so the
  saturation-skew DESIGN headline is degenerate/vacuous under the model (the abstract theory remains
  sound). CAD gate discharged (EVT); Winkler partial (atomic case built, extreme=>atomic remains); Cai
  gate blocked on the model degeneracy. RE-RAISE: heterogenize to Cai's unit-level gamma_i model
  (eq:dirg:ch3) so V3,V4 are non-degenerate, then build the L7/L8 finite-population permutation-moment
  substrate to discharge the Cai gate and realize the genuine skew-threshold design result.
banked_on: "2026-06-28"
---

# exp_saturation_skew_threshold / v1 — Downgraded

**Topic.** Study optimal saturation design for two-stage randomized-saturation experiments under isolated partial interference by making the full bounded-support moment program the theorem object: under a specialized within-cluster homogeneous linear-in-share working model (a specialization of Cai, Pouget-Abadie and Airoldi 2022, not the full parent model), minimize V(nu)=V0+V1*m2+V3*m3+V4*(m4-m2^2) over laws nu on [0,1] with mean pbar. Prove the main result as a necessary-and-sufficient quartic dual/KKT global-optimality certificate for any candidate law, with a support-at-most-3 optimizer reduction. Only as a scoped corollary, in the positive-penalty symmetric-candidate regime V1>0,V4>0, characterize when the stratified symmetric law delta_pbar is globally optimal by the closed threshold min_{d in [-pbar,1-pbar]}(V1+V3*d+V4*d^2)>=0; when this fails construct the skewed two/three-point optimizer. Include the witness pbar=1/3,V1=1,V4=1,V3=-10: (2/3)delta_0+(1/3)delta_1 has m2=2/9,m3=2/27,m4-m2^2=2/81 and improves by -40/81 over delta_pbar. Recover the SUTVA corner V3=V4=0: V is linear in m2, so V1>0 gives within-cluster stratified delta_pbar, V1<0 gives cluster Bernoulli (1-pbar)delta_0+pbar delta_1, and V1=0 ties. Add finite-M attainability for denominator-compatible support masses/saturations and an O(1/M+1/m) rounding-loss clause, distinguishing M*pbar integrality for cluster Bernoulli vertices from m*pbar integrality for within-cluster stratified saturation.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** Sound abstract quartic-program optimization theory (general V), but the saturation-skew DESIGN claim is degenerate under the run's homogeneous working model: it forces V3=V4=0, so the design variance has no skew dependence (paper-confirmed vs Cai arXiv:2203.09682; Lean-confirmed). Formalization halted at F2/F3 when stopped. Re-raise via heterogeneous (unit-level gamma_i) model + L7/L8 finite-population permutation-moment substrate.

## Key files

- `exp_saturation_skew_threshold_v1_state.json` — pipeline state at banking (`banked: true`).
- `exp_saturation_skew_threshold_v1_proposal.tex` — final proposal version.
- `exp_saturation_skew_threshold_v1.tex` — derivation note (if Stage 0 ran).
- `exp_saturation_skew_threshold_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `exp_saturation_skew_threshold_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
