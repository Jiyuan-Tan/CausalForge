---
qid: eid_proximal_bridge_quotient
spec: v1
topic: "Proximal bridge quotient identification without completeness: target uniqueness under nonunique outcome bridges."
novelty_target: flagship
tier_at_proposal: NA
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "Stage -1.1 rejected the topic with code=already-solved."
  - "Zhang, Li, Miao, and Tchetgen Tchetgen already state that when the outcome bridge equation holds, a linear functional of a possibly nonunique bridge is identified iff the functional's loading lies in the orthocomplement of the bridge operator nullspace."
  - "In finite negative-control matrices this is exactly the requested row-space/null-annihilator certificate."
  - "The requested 3x3 witness would only illustrate the published criterion, not produce a new identification theorem."
reusable_artifacts:
  - "eid_proximal_bridge_quotient_v1_gaps.json: Stage -1.1 evidence identifying the published null-annihilator result."
  - "eid_proximal_bridge_quotient_v1_pipeline.jsonl: rejection message and suggested alternatives, including finite witness classification, latent-model-induced null directions, and inference for estimated quotient certificates."
  - "No proposal/review artifacts were generated because the topic stopped during gap harvesting."
seeds_burned:
  - index: 0
    one_liner: "(seed index 0 — one-liner not found in state.json)"
    reason: "Already solved by Zhang/Li/Miao/Tchetgen Tchetgen null-annihilator result; do not retry the quotient bridge criterion itself as a flagship topic."
proof_attempt_summary: |
  This attempt targeted a quotient bridge certificate showing that bridge nonuniqueness can coexist with point identification of the ATE when null bridge directions have zero target contrast. It failed before proposal review because the exact nullspace orthocomplement criterion is already published. Future proximal topics should build on that result, for example by studying inference for estimated quotient certificates or model-realizable null directions, not by reproving the algebraic criterion.
banked_on: "2026-05-25"
---

# eid_proximal_bridge_quotient / v1 — Failed

**Topic.** Proximal bridge quotient identification without completeness: target uniqueness under nonunique outcome bridges.

**Novelty target.** flagship

**Stage -0.5 verdict.** NA

**Stage 0.5 verdict.** NA

**Banking reason.** Stage -1.1 rejected the topic as already solved: Zhang, Li, Miao, and Tchetgen Tchetgen already give the bridge-nullspace orthocomplement criterion for identifying a linear functional of a nonunique outcome bridge.

## Key files

- `eid_proximal_bridge_quotient_v1_state.json` — pipeline state at banking (`banked: true`).
- `eid_proximal_bridge_quotient_v1_proposal.tex` — final proposal version.
- `eid_proximal_bridge_quotient_v1.tex` — derivation note (if Stage 0 ran).
- `eid_proximal_bridge_quotient_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `eid_proximal_bridge_quotient_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
