---
qid: pid_overlap_tail_phase
spec: v1
topic: "New flagship topic: critical-overlap tail exponent for sharp partial identification of treatment effects under positivity failure. Pre-anchor check: closest published anchors are Khan-Tamer 2010 on irregular identification/support and inverse weighting, Rothe-style robust inference under limited overlap, Hong-Leung-Li finite-population limited-overlap inference, and recent non-overlap ATE bounds. Our theorem is not that because it is not an estimator or trimming rule and not the generic statement that non-overlap widens Manski bounds: the focal object is an overlap-tail profile alpha(P) and an extremal-law certificate showing an exact phase threshold for the sharp identified-set width of CATT/ATE under bounded outcomes and observed covariate-propensity tail mass. Require a concrete nonroutine object: a finite/two-tail witness family with the same nominal overlap support but different polynomial tail exponents, an explicit endpoint-attaining sequence, and an iff threshold separating finite-width, polynomial blow-up, and vacuous regimes. If the proposal reduces to ordinary support coverage, overlap weights, Manski missing-cell bounds, trimming, or generic LP duality without the exponent witness and endpoint certificate, pivot or stop early."
novelty_target: flagship
tier_at_proposal: REVISE
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "Angle 0: with s1=1-e and 0<s1<=t<1/2, mu1(t)=E[e 1_tail] is at least nu1(t)=E[s1 1_tail], so the alpha1>1 branch and A1(t)->0 branch are impossible."
  - "Angle 0: after Theorem 1 gives W1=mu1/pi, the phase statement reduces to the ratio mu1/nu1 plus routine regular-variation comparison."
  - "Angle 1: the reviewer classified the kernel as field-tier because it was a regular-variation re-expression of bounded missing-mass width, not a strict comparator-anchored frontier."
  - "Angle 1: Conjectures 1 and 2 both triggered C-definitional-unfold: the phase laws followed from Manski missing-arm width plus tail-mass asymptotics or a change of measure."
  - "Angle 1: the ATE width formula still had correctness errors: missing intersection residual for overlapping tails and a false 2B Manski corner where the treatment-effect range width is 4B."
reusable_artifacts:
  - "pid_overlap_tail_phase_v1_gaps.json: useful literature map for limited overlap, tail-rate inference, non-overlap bounds, and prior CausalSmith overlap/heavy-tail failures."
  - "pid_overlap_tail_phase_v1_reviews/angle0_v1.json: explicit algebraic refutation of the first alpha-profile definition."
  - "pid_overlap_tail_phase_v1_reviews/angle1_v1.json: clean diagnosis that the revised two-tail profile remains bounded missing-mass plus regular variation."
  - "pid_overlap_tail_phase_v1_proposal_angle0_rejected.tex: rejected proposal illustrating the tempting but impossible mu/nu exponent phase law."
seeds_burned: []
proof_attempt_summary: |
  Attempted a flagship partial-ID theorem where limited-overlap tail exponents determine sharp CATT/ATE interval width. The first angle was internally false under its own tail definitions; the pivot repaired that specific inequality but still reduced to Manski bounded-outcome missing-cell width and regular-variation bookkeeping. Reuse the literature map and negative algebraic checks, but do not revive this as a flagship topic unless the theorem is a true comparator frontier against a named published bound with two laws sharing that comparator's inputs but differing in an independently meaningful sharp-width object.
banked_on: "2026-05-24"
---

# pid_overlap_tail_phase / v1 - Failed

**Topic.** New flagship topic: critical-overlap tail exponent for sharp partial identification of treatment effects under positivity failure. Pre-anchor check: closest published anchors are Khan-Tamer 2010 on irregular identification/support and inverse weighting, Rothe-style robust inference under limited overlap, Hong-Leung-Li finite-population limited-overlap inference, and recent non-overlap ATE bounds. Our theorem is not that because it is not an estimator or trimming rule and not the generic statement that non-overlap widens Manski bounds: the focal object is an overlap-tail profile alpha(P) and an extremal-law certificate showing an exact phase threshold for the sharp identified-set width of CATT/ATE under bounded outcomes and observed covariate-propensity tail mass. Require a concrete nonroutine object: a finite/two-tail witness family with the same nominal overlap support but different polynomial tail exponents, an explicit endpoint-attaining sequence, and an iff threshold separating finite-width, polynomial blow-up, and vacuous regimes. If the proposal reduces to ordinary support coverage, overlap weights, Manski missing-cell bounds, trimming, or generic LP duality without the exponent witness and endpoint certificate, pivot or stop early.

**Novelty target.** flagship

**Stage -0.5 verdict.** REVISE

**Stage 0.5 verdict.** NA

**Banking reason.** Stopped after angle 0 REJECT and angle 1 REVISE@field under flagship target: angle 0 tail exponent was internally impossible, and angle 1 collapsed to bounded missing-mass/Manski width plus regular-variation bookkeeping (C-definitional-unfold).

## Key files

- `pid_overlap_tail_phase_v1_state.json` - pipeline state at banking (`banked: true`).
- `pid_overlap_tail_phase_v1_proposal.tex` - final proposal version.
- `pid_overlap_tail_phase_v1_reviews.jsonl` - per-round reviewer log.
- `pid_overlap_tail_phase_v1_reviews/` - per-version reviewer JSON files.

## Notes

Reflection: this was a topic/proposal-strength failure. The D-1.1 literature scout found a real-looking gap, but the hand proposal could not make the overlap exponent do more than reindex missing-cell mass. The reviewer behavior was useful rather than over-strict: it caught both a concrete algebraic contradiction and the later definitional-unfold collapse.
