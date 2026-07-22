---
qid: eid_policy_commutator_phase
spec: v1
topic: "Policy-intervention commutator phase for longitudinal causal effects. Pre-anchor check: closest published anchors are Kennedy's incremental propensity-score interventions, longitudinal/resource-constrained IPSI work, Richardson-Robins natural-value interventions, and Diaz-style longitudinal modified treatment policies. Why non-trivial? The target is not another positivity-free identification formula or EIF/path-derivative calculation: require a finite two-time binary transition-kernel witness in which applying an odds-multiplier IPSI and a natural-value modified treatment policy in opposite orders gives two identified but unequal stochastic-policy estimands, plus a closed-form commutator coefficient whose zero set is exactly the no treatment-confounder-feedback/no effect-modification phase. Why promising? The nonroutine object is a hand-derived operator non-equivalence certificate, not a sensitivity bound: a minimal law showing that two standard policy classes that each preserve support do not compose commutatively under longitudinal feedback. If the delta reduces to standard g-formula identification, EIF calculus, or resource-constraint Lagrange multipliers, pivot or accept field-tier."
novelty_target: flagship
tier_at_proposal: REJECT
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "Angle 0 v1: D-0.5 REJECT, not-publishable; the cold-start version did not deliver a coherent flagship commutator object."
  - "Angle 1 v1: D-0.5 REVISE at field tier; Theorem 1 was already-known extended-g-formula identification once the two policy kernels were specified."
  - "Angle 1 v1: the proposed observable commutator was promissory because Exhibit 9.1 computed only a product C_delta(P), not the two ordered policy means whose difference it claimed to equal."
  - "Angle 1 v1: Conjecture 2's zero phase was a definitional zero-product rule after defining C_delta(P), with fewer than three nontrivial proof steps."
  - "Angle 1 v2: D-0.5 REJECT at field tier; revision still did not make the ordered-policy commutator an independent object."
  - "Angle 2 v1: D-0.5 REJECT at letter tier; pivot did not produce a comparator-facing flagship theorem."
reusable_artifacts:
  - "eid_policy_commutator_phase_v1_gaps.json: literature map and open-problem harvest for IPSI, LMTP, natural-value interventions, and resource-limited longitudinal policies."
  - "eid_policy_commutator_phase_v1_proposal_angle0_rejected.tex: not-publishable cold-start commutator framing to avoid."
  - "eid_policy_commutator_phase_v1_proposal_angle1_rejected.tex: field-tier revision showing why explicit ordered g-formulas are necessary but insufficient."
  - "eid_policy_commutator_phase_v1_proposal_angle2_rejected.tex: letter-tier pivot; useful only as a negative topic-selection artifact."
  - "eid_policy_commutator_phase_v1_reviews.jsonl: compact reviewer trail showing the progression from not-publishable to field to letter-tier failure."
seeds_burned:
  - index: 0
    one_liner: "Construct a two-time binary witness where IPSI-after-LMTP and LMTP-after-IPSI are both identified but unequal, with a closed-form commutator coefficient."
    reason: "Angles 0-2 failed D-0.5 review; reviewers found routine extended-g-formula identification, promissory/underdefined ordered-policy means, definitional zero-product phase, and no comparator-facing flagship theorem."
  - index: 1
    one_liner: "Prove a sharp zero-set theorem for the IPSI-LMTP commutator as exactly the no-feedback or no-effect-modification phase."
    reason: "Angles 0-2 failed D-0.5 review; reviewers found routine extended-g-formula identification, promissory/underdefined ordered-policy means, definitional zero-product phase, and no comparator-facing flagship theorem."
  - index: 2
    one_liner: "Give paired SWIG/g-formula criteria for the two ordered IPSI-LMTP compositions and compare their counterfactual independences."
    reason: "Angles 0-2 failed D-0.5 review; reviewers found routine extended-g-formula identification, promissory/underdefined ordered-policy means, definitional zero-product phase, and no comparator-facing flagship theorem."
proof_attempt_summary: |
  The run tried to build a flagship non-equivalence theorem for two longitudinal support-preserving policy operators: odds-multiplier IPSI and natural-value/LMTP intervention. The promising-looking commutator collapsed because the pipeline either restated standard extended-g-formula identification or defined a zero-product coefficient instead of deriving it from two explicit ordered policy means. Future work in this neighborhood needs a genuinely independent operator algebra or a published comparator-facing theorem, not another finite policy-kernel product identity.
banked_on: "2026-05-25"
---

# eid_policy_commutator_phase / v1 — Failed

**Topic.** Policy-intervention commutator phase for longitudinal causal effects. Pre-anchor check: closest published anchors are Kennedy's incremental propensity-score interventions, longitudinal/resource-constrained IPSI work, Richardson-Robins natural-value interventions, and Diaz-style longitudinal modified treatment policies. Why non-trivial? The target is not another positivity-free identification formula or EIF/path-derivative calculation: require a finite two-time binary transition-kernel witness in which applying an odds-multiplier IPSI and a natural-value modified treatment policy in opposite orders gives two identified but unequal stochastic-policy estimands, plus a closed-form commutator coefficient whose zero set is exactly the no treatment-confounder-feedback/no effect-modification phase. Why promising? The nonroutine object is a hand-derived operator non-equivalence certificate, not a sensitivity bound: a minimal law showing that two standard policy classes that each preserve support do not compose commutatively under longitudinal feedback. If the delta reduces to standard g-formula identification, EIF calculus, or resource-constraint Lagrange multipliers, pivot or accept field-tier.

**Novelty target.** flagship

**Stage -0.5 verdict.** REJECT

**Stage 0.5 verdict.** NA

**Banking reason.** Stopped early after repeated D-0.5 failures: angle 0 was not-publishable, angle 1 remained field-tier and then rejected after revision, and angle 2 rejected at letter tier; the policy-commutator topic collapsed into standard g-formula/policy-kernel algebra or an under-defined zero-product phase rather than a flagship operator non-equivalence theorem.

## Key files

- `eid_policy_commutator_phase_v1_state.json` — pipeline state at banking (`banked: true`).
- `eid_policy_commutator_phase_v1_proposal.tex` — final proposal version.
- `eid_policy_commutator_phase_v1.tex` — derivation note (if Stage 0 ran).
- `eid_policy_commutator_phase_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `eid_policy_commutator_phase_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
