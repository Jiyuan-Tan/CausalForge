---
qid: eid_ida_selective_pivot
spec: v1
topic: "Selective-inference pivot for IDA/MPDAG possible causal effects. Pre-anchor check: closest published anchors are IDA and joint-IDA possible-effect multisets (Maathuis-Kalisch-Buhlmann), Perkovic/Guo-Perkovic minimal enumeration for MPDAG possible effects, and Lee-Sun-Sun-Taylor polyhedral selective inference after model selection. Why non-trivial? The target is not another MPDAG orientation criterion or adjustment-set enumeration: require a hand-derived polyhedral selection certificate for the event that a particular DAG completion/effect is the reported extremal possible effect, and an exact truncated-Gaussian pivot for inference on that selected extremal causal effect under linear-Gaussian SEMs. Why promising? The nonroutine object is estimator/inference geometry: the IDA max-effect selection event becomes a finite intersection of affine inequalities in regression coefficient estimates, with a two-completion witness showing naive Wald coverage fails while the selective pivot is exact. If the delta reduces to IDA enumeration, standard adjustment, constrained-gradient geometry, or ordinary post-selection inference without a causal-effect selection map, pivot or accept field-tier."
novelty_target: flagship
tier_at_proposal: REJECT
tier_at_derivation: NA
proposal_promise_gap: "constructive_object_missing"
reusable: not_reusable
reraise_status: retry
gap_reasons:
  - "Angle 0 v1: D-0.5 REVISE at field tier; the flagship object was an affine discovery certificate but Exhibit 9.1 computed only an assumed exact graph-screen row."
  - "Angle 0 v2: D-0.5 REVISE at field tier; the proposal still did not name a determinate CPDAG/MPDAG discovery rule for A_{0,n}, b_{0,n}, rho_n, c_n, and kappa_n."
  - "Angle 0 v3: D-0.5 REVISE at field tier; the pipeline killed the angle as nonflagship after repeated field-tier reviews."
  - "Reviewer diagnosis: without a concrete PC/GES/MPDAG witness with explicit partial-correlation thresholds and certificate rows, the object stayed promissory."
  - "Angle 1 v1: D-0.5 REJECT at not-publishable tier."
  - "The overall delta remained Lee selective inference plus IDA enumeration, not a flagship causal post-selection theorem."
reusable_artifacts:
  - "eid_ida_selective_pivot_v1_gaps.json: literature map for IDA, joint-IDA, MPDAG minimal enumeration, and post-selection causal discovery inference."
  - "eid_ida_selective_pivot_v1_proposal_angle0_rejected.tex: best field-tier version; useful as a negative template for why naming a discovery rule is mandatory."
  - "eid_ida_selective_pivot_v1_proposal_angle1_rejected.tex: not-publishable pivot; do not reuse as a proposal kernel."
  - "eid_ida_selective_pivot_v1_reviews.jsonl: reviewer trail explaining the missing concrete affine discovery certificate."
seeds_burned:
  - index: 0
    one_liner: "Derive a polyhedral certificate for the event that a named minimally enumerated IDA/MPDAG branch is the reported extremal possible effect, then conjecture a truncated-Gaussian selective pivot for that selected effect."
    reason: "Angle 0 could not rise above field tier after repeated revisions; angle 1 was not-publishable. Reviewers found promissory affine discovery certificates, missing concrete PC/GES witness rows, and insufficient novelty beyond Lee selective inference plus IDA enumeration."
  - index: 1
    one_liner: "Construct selective confidence regions for the deduplicated IDA/MPDAG possible-effect set and the min-absolute lower-bound score after graph learning and minimal enumeration."
    reason: "Angle 0 could not rise above field tier after repeated revisions; angle 1 was not-publishable. Reviewers found promissory affine discovery certificates, missing concrete PC/GES witness rows, and insufficient novelty beyond Lee selective inference plus IDA enumeration."
proof_attempt_summary: |
  The run tried to convert IDA/MPDAG possible-effect enumeration into a flagship selective-inference theorem for the selected extremal causal effect. The core object never became concrete: the proposal invoked an affine discovery certificate but did not derive it from a named discovery rule with explicit statistic thresholds, so reviewers treated the result as a field-tier instantiation of Lee selective inference plus IDA enumeration. A retry would need a fully worked PC-stable or GES certificate example before making any flagship claim.
banked_on: "2026-05-25"
---

# eid_ida_selective_pivot / v1 — Failed

**Topic.** Selective-inference pivot for IDA/MPDAG possible causal effects. Pre-anchor check: closest published anchors are IDA and joint-IDA possible-effect multisets (Maathuis-Kalisch-Buhlmann), Perkovic/Guo-Perkovic minimal enumeration for MPDAG possible effects, and Lee-Sun-Sun-Taylor polyhedral selective inference after model selection. Why non-trivial? The target is not another MPDAG orientation criterion or adjustment-set enumeration: require a hand-derived polyhedral selection certificate for the event that a particular DAG completion/effect is the reported extremal possible effect, and an exact truncated-Gaussian pivot for inference on that selected extremal causal effect under linear-Gaussian SEMs. Why promising? The nonroutine object is estimator/inference geometry: the IDA max-effect selection event becomes a finite intersection of affine inequalities in regression coefficient estimates, with a two-completion witness showing naive Wald coverage fails while the selective pivot is exact. If the delta reduces to IDA enumeration, standard adjustment, constrained-gradient geometry, or ordinary post-selection inference without a causal-effect selection map, pivot or accept field-tier.

**Novelty target.** flagship

**Stage -0.5 verdict.** REJECT

**Stage 0.5 verdict.** NA

**Banking reason.** Stopped early after the selective-IDA topic failed to reach flagship: angle 0 stayed field-tier through three revisions and was killed as nonflagship, then angle 1 rejected as not-publishable; the proposal did not deliver a concrete discovery-rule certificate or a flagship post-selection causal inference object.

## Key files

- `eid_ida_selective_pivot_v1_state.json` — pipeline state at banking (`banked: true`).
- `eid_ida_selective_pivot_v1_proposal.tex` — final proposal version.
- `eid_ida_selective_pivot_v1.tex` — derivation note (if Stage 0 ran).
- `eid_ida_selective_pivot_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `eid_ida_selective_pivot_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
