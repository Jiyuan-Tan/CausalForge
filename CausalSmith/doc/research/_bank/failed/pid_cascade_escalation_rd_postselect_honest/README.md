---
qid: pid_cascade_escalation_rd
spec: postselect_honest
topic: "Transplant of honest/bias-aware regression-discontinuity partial identification (Kolesar-Rothe AER'18 discrete running variable; Armstrong-Kolesar optimal bias-aware honest CIs) into LLM-cascade routing: identify the NET escalation policy value V = E[Y(large)-Y(small)-kappa | boundary] of a cascade that escalates query x to the large model iff a learned calibrated confidence score c-hat(x) >= tau-hat. Non-verbatim witness: (1) tau-hat is chosen cost-optimally on the SAME data (UCCI 2605.18796), a SELECTED cutoff, so pointwise-in-cutoff honest RD CIs lose validity -> need post-selection honest bounds uniform over a specified population cutoff-selection functional tau*(P); (2) c-hat is a generated/estimated calibrated score (isotonic steps, mass points) endogenous to Y(small) (the small model's own confidence), breaking the classical continuity-of-CEF-in-running-variable proof; (3) deterministic threshold routing fails backdoor-ATE positivity globally (2605.25998 leaves this open), so only the LOCAL net-value at the boundary is identified - a different functional. Target the honest identified set [L*(M),U*(M)] for the POPULATION net value of the selected routing rule under bounded calibration-CEF curvature M, with critical curvature/cost-slack M* at which 0 enters [L*,U*] (sign of net escalation value loses identification), plus the post-selection-honest estimation rung (bias-aware local-linear endpoint estimator with uniform coverage over the M-class and the cutoff-selection; generated-regressor correction). Target tier: field."
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "constructive_object_missing"
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - "Final D0.5 review made no net progress: width_term_omitted@lem:postselect-honest-ci-under-gates, CRUX_ASSUMED@conj:postselect-honest-ci, and frontier_contact_not_discharged@conj:active-set-geometry remained open."
  - "The selected-cutoff active-set geometry depended on unsupported perfect-spline/finite affine-branch reductions: bad_parametric_reduction and NONAFFINE_REDUCTION_GAP at lem:perfect-spline-active-set."
  - "The generated-score correction was self-discharging: def:generated-score-drift-handle treated hat G_n as a whole-gap envelope rather than primitive additive components with separate control, and lem:ghat-envelope-valid dropped a gap term."
  - "The post-selection honest-CI rung lacked the empirical-process, selected-threshold localization, oracle-neighborhood coverage, and generated-score expansion ingredients needed to transfer fixed-cutoff honest RD to the selected feasible cutoff."
reusable_artifacts:
  - "discovery/core.json - final D0 core for selected-cutoff net escalation value, curvature-budget endpoint interval, critical curvature, and post-selection honest-CI handles."
  - "discovery/solve_conj_active_set_geometry.json and solve_conj_postselect_honest_ci.json - solver traces for the two unresolved conjectural nodes."
  - "discovery/d0_escalation_log.jsonl and pipeline.jsonl - escalation trail documenting the generated-score drift and perfect-spline active-set blockers."
  - "discovery/gaps.json and discovery/proposal.tex - literature/open-problem map for selected cutoff honest RD, generated calibrated scores, and LLM cascade routing."
seeds_burned: []
proof_attempt_summary: |
  The run tried to build a field-tier selected-cutoff honest RD partial-ID result for LLM cascade escalation: a curvature-budget sharp interval for the boundary net value, a critical-curvature sign frontier, finite active-set geometry, and post-selection honest feasible inference with generated-score correction. Stage -0.5 accepted the topic, but D0.5 repeatedly found that the core assumed the hard parts: finite perfect-spline active-set structure, primitive generated-score drift control, and selected-threshold honest-CI process bounds. A retry should keep the selected-cutoff problem framing and literature map, but must either prove those gates directly or narrow the claim before rerunning discovery.
banked_on: "2026-06-30"
---

# pid_cascade_escalation_rd / postselect_honest — Failed

**Topic.** Transplant of honest/bias-aware regression-discontinuity partial identification (Kolesar-Rothe AER'18 discrete running variable; Armstrong-Kolesar optimal bias-aware honest CIs) into LLM-cascade routing: identify the NET escalation policy value V = E[Y(large)-Y(small)-kappa | boundary] of a cascade that escalates query x to the large model iff a learned calibrated confidence score c-hat(x) >= tau-hat. Non-verbatim witness: (1) tau-hat is chosen cost-optimally on the SAME data (UCCI 2605.18796), a SELECTED cutoff, so pointwise-in-cutoff honest RD CIs lose validity -> need post-selection honest bounds uniform over a specified population cutoff-selection functional tau*(P); (2) c-hat is a generated/estimated calibrated score (isotonic steps, mass points) endogenous to Y(small) (the small model's own confidence), breaking the classical continuity-of-CEF-in-running-variable proof; (3) deterministic threshold routing fails backdoor-ATE positivity globally (2605.25998 leaves this open), so only the LOCAL net-value at the boundary is identified - a different functional. Target the honest identified set [L*(M),U*(M)] for the POPULATION net value of the selected routing rule under bounded calibration-CEF curvature M, with critical curvature/cost-slack M* at which 0 enters [L*,U*] (sign of net escalation value loses identification), plus the post-selection-honest estimation rung (bias-aware local-linear endpoint estimator with uniform coverage over the M-class and the cutoff-selection; generated-regressor correction). Target tier: field.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** D0.5 repeatedly failed on selected-cutoff geometry, generated-score drift, and post-selection honest-CI gaps; the last review still required new math or definition repair beyond an in-place D0.R edit.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note from Stage 0.
- `reviews.jsonl` — Stage -0.5 reviewer log.
- `pipeline.jsonl` — D0/D0.5 checkpoint and escalation log.
- `reviews/` — per-version proposal reviewer JSON files.

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
