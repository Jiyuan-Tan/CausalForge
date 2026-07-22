---
qid: eid_anchor_icp_dantzig_frontier
spec: v1
topic: "Exact non-equivalence frontier among ICP, anchor regression, and Causal Dantzig in linear Gaussian SEMs with anchors/environments."
novelty_target: flagship
tier_at_proposal: REVISE
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "angle0_v1: tier=field below novelty_target=flagship; the proposed K object was a stacked residual vector, but the theorem used rank, kernel, r_*, and N_* as if K were an independently defined linear operator."
  - "angle0_v1: Conjecture 1 was C-definitional-unfold: after notation repair, the iff mostly unfolded the definition because K stacked exactly the ICP, anchor, Dantzig, and omitted-coordinate equations."
  - "angle0_v1: Conjecture 2 lacked a valid non-corner 2-anchor by 2-covariate witness; the displayed eta_2 case failed both anchor and Dantzig residual rows."
  - "angle0_v2: Theorem 1 was already-known, a routine population translation of published ICP, anchor-regression, and Causal-Dantzig definitions."
  - "angle0_v2: the proposal silently replaced the published Causal-Dantzig environment moment equation with Cov(A,Y-X'b)=0 without a Z-encoding, centering, or weighting bridge."
  - "angle0_v2: Conjecture 1 remained field-tier; the affine-image iff was still definitional stacking, and flagship would require independent determinant/minor conditions plus a minimality theorem."
reusable_artifacts:
  - "eid_anchor_icp_dantzig_frontier_v1_gaps.json: useful literature map for ICP, anchor regression, Causal Dantzig, distributional anchor regression, and environment/IV links."
  - "eid_anchor_icp_dantzig_frontier_v1_reviews/angle0_v1.json: stop anchor for invalid K-as-vector/operator notation and invalid q=p=2 witness rows."
  - "eid_anchor_icp_dantzig_frontier_v1_reviews/angle0_v2.json: decisive diagnosis that published-equation stacking is field-tier and that the Causal-Dantzig bridge is missing."
  - "eid_anchor_icp_dantzig_frontier_v1_proposal.tex: reusable only as a field-tier catalogue of population equations; do not lift its K frontier as a flagship kernel."
seeds_burned:
  - "Three-way ICP/anchor/Causal-Dantzig affine-image equality frontier."
  - "K(Sigma,S)b=h(Sigma,S) stacked-pencil theorem without independent minors."
  - "q=p=2 covariance-witness claim without row-by-row valid covariance certificate."
proof_attempt_summary: |
  Attempted a flagship exact-ID invariance frontier comparing ICP, anchor regression, and Causal Dantzig through a finite covariance pencil. The first revision opportunity did not produce a nonroutine object: the reviewer still saw routine translations of published estimating equations plus definitional affine-image algebra, and also caught a missing bridge from Causal-Dantzig environment moments to anchor covariance moments. Future work in this area needs a hand-derived determinant/minor classification and a valid minimal covariance witness before invoking thmsmith again.
banked_on: "2026-05-25"
---

# eid_anchor_icp_dantzig_frontier / v1 - Failed

**Topic.** Exact non-equivalence frontier among Invariant Causal Prediction, anchor regression, and Causal Dantzig in linear Gaussian SEMs with anchors/environments.

**Novelty target.** flagship

**Stage -0.5 verdict.** REVISE / field at angle0 v1 and angle0 v2.

**Stage 0.5 verdict.** NA

**Banking reason.** Stopped at D-0.5 after angle0 v2 remained field-tier under the flagship target. The main theorem was already-known population-equation translation, the frontier was still stacked affine-image algebra, and the proposed Causal-Dantzig anchor-moment bridge was not justified.

## Key Files

- `eid_anchor_icp_dantzig_frontier_v1_gaps.json` - literature map and harvested open problems.
- `eid_anchor_icp_dantzig_frontier_v1_proposal.tex` - final proposal version.
- `eid_anchor_icp_dantzig_frontier_v1_reviews.jsonl` - per-round reviewer log.
- `eid_anchor_icp_dantzig_frontier_v1_reviews/angle0_v1.json` - first D-0.5 review.
- `eid_anchor_icp_dantzig_frontier_v1_reviews/angle0_v2.json` - decisive second D-0.5 review.
- `eid_anchor_icp_dantzig_frontier_v1_state.json` - pipeline state at banking.

## Reflection

Failure cause: topic/proposal strength. The harvested literature gap was real, but the proposer did not cross the flagship pre-anchor delta: the concrete object was not independent of the three published equations, and the witness was not fully computed. Reviewer strictness and D0 solver weakness were not the bottleneck.
