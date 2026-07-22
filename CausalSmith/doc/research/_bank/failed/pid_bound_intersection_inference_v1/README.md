---
qid: pid_bound_intersection_inference
spec: v1
topic: "New topic: inference for nonparametric partial-identification bound intersections over rich or continuous covariate level sets. Pre-anchor check: closest published anchors are Manski nonparametric bounds, Imbens-Manski confidence intervals, Chernozhukov-Hong-Tamer set inference, and Andrews-Shi moment-inequality inference. Our theorem is not that because the object is the nonregular endpoint functional formed by intersecting estimated level-set bounds as the active level-set geometry changes. Require a concrete nonroutine object: a tangent-cone or EIF-style phase threshold separating unique-active, finite-multi-active, and continuum-active flat-face regimes, plus a hand-derived bootstrap-failure or limit-law witness. If the proposal reduces to ordinary interval intersection, generic moment inequalities, or finite-cell Manski bounds, pivot or stop early."
novelty_target: relative-to-literature
tier_at_proposal: REJECT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "Angle 0 Conjecture 1: N-pub -- contact-cone derivative is the standard supremum-functional active-set derivative, already covered by Chernozhukov-Lee-Rosen 2013 and Fang-Santos 2019."
  - "Angle 0 Conjecture 2: N-pub -- singleton/finite/continuum regimes are cardinality cases of the active-set supremum law already implicit in Chernozhukov-Lee-Rosen 2013."
  - "Angle 1 Theorem 1: N-pub -- finite two-coordinate contact derivative and local max law are a direct max-map directional-delta specialization already covered by Fang-Santos 2019 and standard intersection-bound endpoint theory."
  - "Angle 1 Conjecture 1: N-strawman -- negative result attacks a generic centered naive bootstrap, but does not name a published intersection-bound estimator or workflow that recommends that naive calibration."
reusable_artifacts:
  - path: "pid_bound_intersection_inference_v1_gaps.json"
    kind: literature_map
    one_line: "Useful map for intersection-bound inference: CLR 2013, Fang-Santos 2019, Imbens-Manski 2004, CHT 2007, Andrews-Shi 2013, Lee-Song-Whang 2018, KMS 2019."
  - path: "pid_bound_intersection_inference_v1_reviews/angle0_v1.json"
    kind: counterexample
    one_line: "Reviewer shows contact-cone/phase-threshold framing collapses to known active-set supremum inference."
  - path: "pid_bound_intersection_inference_v1_reviews/angle1_v1.json"
    kind: counterexample
    one_line: "Reviewer shows the bootstrap-failure witness is just Fang-Santos max-map theory unless paired with a new correction rule or named workflow failure."
seeds_burned: []
proof_attempt_summary: |
  Attempted a nonregular inference topic for endpoints formed by intersections over rich covariate level sets. Two independently reviewed angles failed hard at D-0.5: the contact-cone/phase-threshold angle was already CLR active-set supremum inference, and the two-point bootstrap-failure angle was a routine Fang-Santos max-map example without a named published workflow target. This is a topic choice/proposer-angle failure; future work here needs a genuinely new correction/calibration rule, not another negative bootstrap witness.
banked_on: "2026-05-24"
---

# pid_bound_intersection_inference / v1 â€” Failed

**Topic.** New topic: inference for nonparametric partial-identification bound intersections over rich or continuous covariate level sets. Pre-anchor check: closest published anchors are Manski nonparametric bounds, Imbens-Manski confidence intervals, Chernozhukov-Hong-Tamer set inference, and Andrews-Shi moment-inequality inference. Our theorem is not that because the object is the nonregular endpoint functional formed by intersecting estimated level-set bounds as the active level-set geometry changes. Require a concrete nonroutine object: a tangent-cone or EIF-style phase threshold separating unique-active, finite-multi-active, and continuum-active flat-face regimes, plus a hand-derived bootstrap-failure or limit-law witness. If the proposal reduces to ordinary interval intersection, generic moment inequalities, or finite-cell Manski bounds, pivot or stop early.

**Novelty target.** relative-to-literature

**Stage -0.5 verdict.** REJECT

**Stage 0.5 verdict.** NA

**Banking reason.** Stopped after two D-0.5 hard REJECT angles: both kernels were subsumed by Chernozhukov-Lee-Rosen intersection-bound active-set inference plus Fang-Santos max/bootstrap theory; failure is topic/proposal choice, not solver weakness.

## Key files

- `pid_bound_intersection_inference_v1_state.json` â€” pipeline state at banking (`banked: true`).
- `pid_bound_intersection_inference_v1_proposal.tex` â€” final proposal version.
- `pid_bound_intersection_inference_v1.tex` â€” derivation note (if Stage 0 ran).
- `pid_bound_intersection_inference_v1_reviews.jsonl` â€” per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_bound_intersection_inference_v1_reviews/` â€” per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
