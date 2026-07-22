---
qid: eid_bjs_if_contrast_frontier
spec: v1
topic: "Flagship topic with hand-derived nonroutine object: sharp influence-function non-equivalence frontier for four named staggered-DiD estimators: Borusyak-Jaravel-Spiess imputation (ReStud 2024), Sun-Abraham interaction-weighted (JoE 2021), Callaway-Sant'Anna group-time doubly robust (JoE 2021), and Wooldridge cohort-time saturated TWFE (2021). Pre-anchor check: closest banked proposal is eid_bjs_efficient_event_study_v1, which almost cleared flagship but failed because K_star was vague/undefined and the projection-loss object was not uniquely specified. Our theorem is not that because this run must replace the vague threshold with a concrete finite cohort-event IF contrast matrix C(pi,Sigma,G,T), computed from named observable cohort shares and pre-period covariance primitives, and an explicit 3-cohort x 4-period witness where the four estimators identify the same ATT but have provably different influence-function projections and variances. If the proposal becomes a generic FWL/projection identity, a low-rank slogan, or an efficiency claim without the contrast matrix and worked witness, pivot or stop early. Required kernel: an iff frontier C tau = 0 for first-order IF equivalence, a strict-gap formula ||C tau||^2_{Omega}, and a corrected efficient projection map recovering the BJS IF."
novelty_target: flagship
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "Angle 0 and 1 were rejected or field-tier because the estimator frontier was either already covered by published EIF/comparator results or not mathematically well posed."
  - "Angle 2 briefly reached REVISE@flagship at v3, but later reviews fell back to field when the promised contrast matrix and projection-loss object were not derived from estimator equations."
  - "Final angle 4 review: C was computed only after asserting published selectors E_m and nuisance designs Z_m; Exhibit 9.1 did not derive those matrices from explicit estimator equations."
  - "Final review: once C_m is defined as L_m - L_EIF, the iff frontier C tau = 0 is the kernel condition of the defined contrast matrix, so the nontrivial content was assumed rather than constructed."
  - "Final review: quotient norm Omega_m and corrected projection Pi_m^star were validated only under asserted identity covariance/selector simplifications and did not preserve the target aggregation a' tau."
reusable_artifacts:
  - "eid_bjs_if_contrast_frontier_v1_gaps.json: literature map for BJS, Sun-Abraham, Callaway-Sant'Anna, Wooldridge, and Chen-Sant'Anna-Xie EIF comparators."
  - "eid_bjs_if_contrast_frontier_v1_reviews/angle2_v3.json: best review, with a transient flagship-tier signal before the construction defects resurfaced."
  - "eid_bjs_if_contrast_frontier_v1_reviews/angle4_v3.json: final concise diagnosis of promissory C/Omega/Pi objects and definitional contrast algebra."
  - "eid_bjs_if_contrast_frontier_v1_proposal_angle2_rejected.tex: most useful rejected proposal version for understanding the matrix-frontier attempt."
seeds_burned: []
proof_attempt_summary: |
  Attempted to rescue the earlier BJS event-study efficiency frontier by replacing the vague K_star object with a finite IF contrast matrix, quotient variance gap, and corrected projection. The proposal never derived those objects from the named estimators' equations; it treated estimator selector matrices and nuisance projections as primitives, making the flagship iff C tau = 0 a definition unfold. A future revival would need to compute BJS, SA, CS, and Wooldridge loadings entrywise from the published estimators before naming the contrast frontier.
banked_on: "2026-05-25"
---

# eid_bjs_if_contrast_frontier / v1 - Failed

**Topic.** Flagship topic with hand-derived nonroutine object: sharp influence-function non-equivalence frontier for four named staggered-DiD estimators: Borusyak-Jaravel-Spiess imputation (ReStud 2024), Sun-Abraham interaction-weighted (JoE 2021), Callaway-Sant'Anna group-time doubly robust (JoE 2021), and Wooldridge cohort-time saturated TWFE (2021). Pre-anchor check: closest banked proposal is eid_bjs_efficient_event_study_v1, which almost cleared flagship but failed because K_star was vague/undefined and the projection-loss object was not uniquely specified. Our theorem is not that because this run must replace the vague threshold with a concrete finite cohort-event IF contrast matrix C(pi,Sigma,G,T), computed from named observable cohort shares and pre-period covariance primitives, and an explicit 3-cohort x 4-period witness where the four estimators identify the same ATT but have provably different influence-function projections and variances. If the proposal becomes a generic FWL/projection identity, a low-rank slogan, or an efficiency claim without the contrast matrix and worked witness, pivot or stop early. Required kernel: an iff frontier C tau = 0 for first-order IF equivalence, a strict-gap formula ||C tau||^2_{Omega}, and a corrected efficient projection map recovering the BJS IF.

**Novelty target.** flagship

**Stage -0.5 verdict.** NO-PASS

**Stage 0.5 verdict.** NA

**Banking reason.** D-0.5 NO-PASS after 5 angles under flagship target: the best angle briefly reached REVISE@flagship but all surviving versions left the IF contrast matrix, quotient norm, or corrected projection as asserted/promissory objects; final review classified the kernel as field-tier definitional contrast algebra.

## Key files

- `eid_bjs_if_contrast_frontier_v1_state.json` - pipeline state at banking (`banked: true`).
- `eid_bjs_if_contrast_frontier_v1_proposal.tex` - final proposal version.
- `eid_bjs_if_contrast_frontier_v1_reviews.jsonl` - per-round reviewer log.
- `eid_bjs_if_contrast_frontier_v1_reviews/` - per-version reviewer JSON files.

## Notes

Reflection: this was proposal-angle quality failure with a useful diagnostic, not reviewer strictness and not D0 weakness. The topic may still have a real flagship route, but the proposer repeatedly failed the required pre-anchor delta: it did not hand-derive the estimator loadings from BJS/SA/CS/Wooldridge equations. The transient angle2 v3 flagship signal should not be chased without doing that derivation first.
