---
qid: pid_proximal_null_realizability
spec: v1
topic: "Latent-realizability of proximal bridge-null directions. Pre-anchor check: closest anchors are proximal causal inference without unique bridges, the published null-annihilator quotient criterion, and finite negative-control latent-class formulations. Why non-trivial? The target is not the already-solved algebraic row-space criterion and not an LP/Manski bound: require a finite observed negative-control law where the bridge equation has algebraic null directions, but only some null directions are induced by valid latent negative-control causal models with nonnegative latent strata and exclusion restrictions. The theorem should characterize the realizable null cone and prove a non-equivalence witness: two observed laws with the same bridge operator nullspace and same algebraic quotient certificate, but different sharp ATE sets because one null direction is latent-model-realizable and the other is a spurious bridge-fiber artifact. Why promising? The nonroutine object is a realizability certificate separating algebraic bridge fibers from causal latent-model fibers, with a hand-derived 2x3 or 3x3 witness and endpoint-attaining latent laws. If the delta reduces to LP duality, Manski missing-cell bounds, standard null-annihilator algebra, or definition-unfold latent-class feasibility, pivot or accept field-tier."
novelty_target: flagship
tier_at_proposal: REJECT
tier_at_derivation: NA
proposal_promise_gap: "constructive_object_missing"
reusable: not_reusable
reraise_status: retry
gap_reasons:
  - "Angle 0 v1: D-0.5 REVISE at field tier; Conjecture 2 lacked a valid concrete non-corner witness because Exhibit 9.2's displayed latent law did not realize the claimed bridge segment."
  - "Angle 0 v1: the promised Farkas multiplier and distinct sharp ATE sets were not computed and verified from the Section 6 primitives."
  - "Angle 0 v1: the null-cone certificate mostly unfolded generic finite-dimensional polyhedral projection/Farkas theorem."
  - "Angle 0 v2: D-0.5 again stayed field tier; reviewers still found invalid finite witness algebra and generic Farkas projection."
  - "Angle 0 v3: pipeline marked the angle needs-pivot."
  - "Angle 1 v1: D-0.5 REJECT at field tier."
reusable_artifacts:
  - "pid_proximal_null_realizability_v1_gaps.json: literature/open-problem map around proximal nonunique bridges and latent-class realizability."
  - "pid_proximal_null_realizability_v1_proposal_angle0_rejected.tex: invalid witness/Farkas-certificate attempt; useful as a negative artifact."
  - "pid_proximal_null_realizability_v1_proposal_angle1_rejected.tex: field-tier pivot; do not reuse as flagship kernel."
  - "pid_proximal_null_realizability_v1_reviews.jsonl: reviewer trail documenting the failed witness and generic-Farkas collapse."
seeds_burned:
  - index: 0
    one_liner: "Characterize the latent-realizable proximal bridge-null cone by a finite Farkas certificate and prove it can be strictly smaller than the algebraic bridge kernel."
    reason: "Angle 0 failed to repair the same-quotient/different-sharp-set witness and Farkas certificate; angle 1 rejected field-tier. Reviewers found invalid finite witness algebra, generic Farkas projection, and no flagship characterization beyond latent-class feasibility."
  - index: 1
    one_liner: "Give sharp ATE bounds in rank-deficient finite proximal models by optimizing only over latent-realizable bridge-null directions."
    reason: "Angle 0 failed to repair the same-quotient/different-sharp-set witness and Farkas certificate; angle 1 rejected field-tier. Reviewers found invalid finite witness algebra, generic Farkas projection, and no flagship characterization beyond latent-class feasibility."
proof_attempt_summary: |
  The run tried to separate algebraic proximal bridge null directions from latent-model-realizable null directions, aiming for two observed laws with the same bridge quotient but different sharp ATE sets. The idea did not produce a verified finite witness: the displayed latent law failed its own bridge-segment arithmetic, the Farkas certificate was unfinished, and the characterization collapsed toward generic latent-class feasibility. Future work would need a hand-solved finite table before rerunning this topic.
banked_on: "2026-05-25"
---

# pid_proximal_null_realizability / v1 — Failed

**Topic.** Latent-realizability of proximal bridge-null directions. Pre-anchor check: closest anchors are proximal causal inference without unique bridges, the published null-annihilator quotient criterion, and finite negative-control latent-class formulations. Why non-trivial? The target is not the already-solved algebraic row-space criterion and not an LP/Manski bound: require a finite observed negative-control law where the bridge equation has algebraic null directions, but only some null directions are induced by valid latent negative-control causal models with nonnegative latent strata and exclusion restrictions. The theorem should characterize the realizable null cone and prove a non-equivalence witness: two observed laws with the same bridge operator nullspace and same algebraic quotient certificate, but different sharp ATE sets because one null direction is latent-model-realizable and the other is a spurious bridge-fiber artifact. Why promising? The nonroutine object is a realizability certificate separating algebraic bridge fibers from causal latent-model fibers, with a hand-derived 2x3 or 3x3 witness and endpoint-attaining latent laws. If the delta reduces to LP duality, Manski missing-cell bounds, standard null-annihilator algebra, or definition-unfold latent-class feasibility, pivot or accept field-tier.

**Novelty target.** flagship

**Stage -0.5 verdict.** REJECT

**Stage 0.5 verdict.** NA

**Banking reason.** Stopped after the final budgeted attempt failed to reach flagship: angle 0 stayed field-tier and needed a pivot because its finite witness/Farkas certificate was invalid, then angle 1 rejected at field tier; the latent-realizability topic remained a generic finite LP/projection feasibility problem without a verified nonroutine witness.

## Key files

- `pid_proximal_null_realizability_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_proximal_null_realizability_v1_proposal.tex` — final proposal version.
- `pid_proximal_null_realizability_v1.tex` — derivation note (if Stage 0 ran).
- `pid_proximal_null_realizability_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_proximal_null_realizability_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
