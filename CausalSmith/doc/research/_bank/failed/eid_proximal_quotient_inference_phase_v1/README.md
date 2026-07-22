---
qid: eid_proximal_quotient_inference_phase
spec: v1
topic: "Weak-quotient inference phase for proximal bridge target uniqueness. Pre-anchor check: closest anchors are the Zhang-Li-Miao-Tchetgen Tchetgen null-annihilator criterion for nonunique bridges, proximal AIPW bridge estimation papers, and weak-identification/singular-matrix inference. Why non-trivial? The target is not the already-solved algebraic quotient criterion and not another completeness threshold: require a fixed-rank finite negative-control model where the bridge operator and target loading are estimated, and derive a local-to-nullspace phase theorem for the plug-in quotient diagnostic. The nonroutine object is a cone-angle certificate: when the target-loading distance to the estimated bridge nullspace is separated from zero, ordinary Gaussian inference is valid; when it is n^{-1/2}-local, the diagnostic has a nonstandard projected-Gaussian/chi-bar-square law and naive quotient-identification decisions have nonvanishing size distortion. Why promising? This is estimator geometry around a published identification criterion, with a two-matrix hand witness and explicit phase boundary, not LP duality or support coverage. If the delta reduces to standard singular-value perturbation, generic weak-IV analogies, path derivatives, or rephrasing the Zhang nullspace iff, pivot or accept field-tier."
novelty_target: flagship
tier_at_proposal: REVISE
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "Angle 0 v1: D-0.5 REVISE at field tier; Theorem 1's population cone-angle criterion was a relabelling of the row-space/null-annihilator criterion."
  - "Angle 0 v1: the static bridge-nonuniqueness/target-uniqueness condition was already covered by Zhang et al."
  - "Angle 0 v1: Kleibergen-Paap, Andrews-Cheng, and Han-McCloskey comparator anchors were too thin for a flagship frontier."
  - "Angle 0 v1: Pi_N and Dkappa were not defined as explicit finite-dimensional linear maps."
  - "Angle 0 v2: D-0.5 again stayed field tier; the local cone-angle diagnostic remained incremental rank/weak-ID machinery rather than a strict comparator-facing proximal inference theorem."
reusable_artifacts:
  - "eid_proximal_quotient_inference_phase_v1_gaps.json: literature map for proximal quotient identification and weak rank/singular inference."
  - "eid_proximal_quotient_inference_phase_v1_proposal.tex: final field-tier proposal; useful as a negative example of cone-angle diagnostic novelty limits."
  - "eid_proximal_quotient_inference_phase_v1_reviews.jsonl: D-0.5 reviewer trail explaining why the topic did not clear flagship."
seeds_burned:
  - index: 0
    one_liner: "Introduce a cone-angle quotient certificate for finite proximal bridges and conjecture separated Gaussian versus n^{-1/2}-local projected-Gaussian laws for the plug-in diagnostic."
    reason: "Angle 0 stayed field-tier through two versions; reviewers found the population criterion already known, comparator anchors thin, Pi_N/Dkappa underdefined, and the local cone-angle law insufficient for flagship novelty."
proof_attempt_summary: |
  The run tried to build an inference theory around the already-known proximal bridge quotient criterion by estimating the bridge operator, target loading, and angle to the bridge nullspace. The idea remained coherent but incremental: reviewers treated the population result as already known and the local diagnostic as standard rank/weak-identification perturbation without a named proximal comparator theorem being strictly extended. A future retry would need a complete uniform inference/pretest theorem with explicit Pi_N and Dkappa maps and concrete comparator non-representability.
banked_on: "2026-05-25"
---

# eid_proximal_quotient_inference_phase / v1 — Failed

**Topic.** Weak-quotient inference phase for proximal bridge target uniqueness. Pre-anchor check: closest anchors are the Zhang-Li-Miao-Tchetgen Tchetgen null-annihilator criterion for nonunique bridges, proximal AIPW bridge estimation papers, and weak-identification/singular-matrix inference. Why non-trivial? The target is not the already-solved algebraic quotient criterion and not another completeness threshold: require a fixed-rank finite negative-control model where the bridge operator and target loading are estimated, and derive a local-to-nullspace phase theorem for the plug-in quotient diagnostic. The nonroutine object is a cone-angle certificate: when the target-loading distance to the estimated bridge nullspace is separated from zero, ordinary Gaussian inference is valid; when it is n^{-1/2}-local, the diagnostic has a nonstandard projected-Gaussian/chi-bar-square law and naive quotient-identification decisions have nonvanishing size distortion. Why promising? This is estimator geometry around a published identification criterion, with a two-matrix hand witness and explicit phase boundary, not LP duality or support coverage. If the delta reduces to standard singular-value perturbation, generic weak-IV analogies, path derivatives, or rephrasing the Zhang nullspace iff, pivot or accept field-tier.

**Novelty target.** flagship

**Stage -0.5 verdict.** REVISE

**Stage 0.5 verdict.** NA

**Banking reason.** Stopped early after repeated D-0.5 field-tier reviews: the proximal quotient inference topic was coherent but remained an incremental rank/weak-identification diagnostic around the already-known Zhang null-annihilator criterion, without a flagship comparator-facing uniform inference theorem.

## Key files

- `eid_proximal_quotient_inference_phase_v1_state.json` — pipeline state at banking (`banked: true`).
- `eid_proximal_quotient_inference_phase_v1_proposal.tex` — final proposal version.
- `eid_proximal_quotient_inference_phase_v1.tex` — derivation note (if Stage 0 ran).
- `eid_proximal_quotient_inference_phase_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `eid_proximal_quotient_inference_phase_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
