---
qid: eid_lp_svar_channel_frontier
spec: v1
topic: "Repaired LP/SVAR sign, pasting, and non-Gaussian cumulant channel frontier after the eid_lp_svar_nonequiv_upgrade near-miss."
novelty_target: flagship
tier_at_proposal: REJECT
tier_at_derivation: NA
proposal_promise_gap: "kernel_substituted"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "angle0_v1: Theorem 1 was already-known; support equality under identical common restrictions is PMW common-estimand equality plus equality of optimization domains, and was already present in eid_lp_svar_nonequiv_upgrade2."
  - "angle0_v1: c_w(P) was not computed in the exhibit; only one comparison quotient was shown, not the infimum over K_w(P) or Gamma_w(P)."
  - "angle0_v1: c_w(P)>0 and Gamma_w(P)>0 were effectively built into assumptions, while the equality case required zero channels excluded by those assumptions."
  - "angle0_v1: the theta=pi/4 comparison was infeasible for the cumulant-compatible set, so the displayed loss was not h_H-h_C."
  - "angle1_v1: c_w(P) was internally contradicted. At nonrepresentable LP support maximizers the numerator h_L-w'r is zero, forcing the infimum c_w(P)=0 exactly where the conjecture needs positive separation."
  - "angle1_v1: the two-shock exhibit was a PMW no-gap corner with h_L=h_C=1, not a positive separation witness."
  - "angle1_v1: the claimed residual and exposure formulas were not determined by Section 6 primitives; K_u, kappa values, delta_4, and sign-row matrix A were not specified."
reusable_artifacts:
  - "eid_lp_svar_channel_frontier_v1_gaps.json: useful literature map and exact failure anchors for common-restriction LP/SVAR, sign exposure, cumulant labels, weak non-Gaussianity, and c_w(P)."
  - "eid_lp_svar_channel_frontier_v1_reviews/angle0_v1.json: decisive warning that common-restriction equality and parent-margin collapse are already known/repo-covered."
  - "eid_lp_svar_channel_frontier_v1_reviews/angle1_v1.json: decisive algebraic refutation of the support-loss-to-distance-product c_w(P) definition."
  - "eid_lp_svar_channel_frontier_v1_proposal_angle0_rejected.tex and proposal_angle1_rejected.tex: negative examples of circular c_w(P) and no-gap two-shock witnesses."
seeds_burned:
  - "Common-restriction LP/SVAR support equality as a flagship theorem."
  - "c_w(P) support-loss-to-distance-product infimum over LP support maximizers."
  - "Two-shock trigonometric witness as written for positive LP/SVAR channel separation."
proof_attempt_summary: |
  Attempted to repair the LP/SVAR flagship near-miss by making the channel frontier explicit and fixing the prior PMW/common-restriction sanity issue. Both reviewed angles failed hard: the first repeated known common-restriction equality and made c_w circular at the zero-channel boundary, while the pivot's c_w definition forced itself to zero at the support-maximizer points it needed to separate. Future work should not revive this channel-frontier path without a genuinely new non-corner witness whose h_L, h_C, cumulant residuals, sign rows, and support gap are all computed from primitive rotation geometry.
banked_on: "2026-05-25"
---

# eid_lp_svar_channel_frontier / v1 - Failed

**Topic.** Repaired LP/SVAR sign, pasting, and non-Gaussian cumulant channel frontier after the `eid_lp_svar_nonequiv_upgrade` near-miss.

**Novelty target.** flagship

**Stage -0.5 verdict.** REJECT / not-publishable on angle0 v1 and angle1 v1.

**Stage 0.5 verdict.** NA

**Banking reason.** Stopped at D-0.5 after two hard rejects. Angle 0 repeated already-known common-restriction equality and had a circular/undefined `c_w(P)` boundary. Angle 1's `c_w(P)` infimum was forced to zero at LP support maximizers, and the two-shock exhibit was a no-gap corner rather than a positive separation witness.

## Key Files

- `eid_lp_svar_channel_frontier_v1_gaps.json` - harvested literature and open problems.
- `eid_lp_svar_channel_frontier_v1_proposal_angle0_rejected.tex` - first rejected proposal.
- `eid_lp_svar_channel_frontier_v1_proposal_angle1_rejected.tex` - pivot rejected proposal.
- `eid_lp_svar_channel_frontier_v1_reviews.jsonl` - per-round reviewer log.
- `eid_lp_svar_channel_frontier_v1_reviews/angle0_v1.json` - first hard reject.
- `eid_lp_svar_channel_frontier_v1_reviews/angle1_v1.json` - second hard reject.
- `eid_lp_svar_channel_frontier_v1_state.json` - pipeline state at banking.

## Reflection

Failure cause: topic/proposal strength with a math-kernel weakness, not reviewer strictness or D0 solver weakness. The near-miss looked promising from prior flagship reviews, but the required repair was not local: the candidate `c_w(P)` object itself was contradictory under the intended support-maximizer regime.
