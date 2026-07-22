---
qid: eid_mpdag_effect_invariance_witness
spec: v1
topic: "MPDAG total-effect invariance witness for P(Y | do(A)): an orientation-cut certificate over DAG completions."
novelty_target: flagship
tier_at_proposal: NA
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "Stage -1.1 rejected the topic with code=already-solved."
  - "Perkovic 2020 develops a necessary-and-sufficient causal identification criterion for MPDAGs."
  - "Definition 3.1 uses the same invariance/non-invariance target over DAGs represented by the MPDAG."
  - "Proposition 3.2 gives the failure condition when a proper possibly causal path starts with an undirected edge."
  - "Theorem 3.6 proves sufficiency when no such path exists."
  - "The topic was also classified as graphical MPDAG/CPDAG/PAG identification theory, outside CausalSmith's econometric-methodology scope except as field-tier formalization of known results."
reusable_artifacts:
  - "eid_mpdag_effect_invariance_witness_v1_gaps.json: Stage -1.1 evidence locating the exact Perkovic 2020 coverage."
  - "eid_mpdag_effect_invariance_witness_v1_pipeline.jsonl: rejection message and suggested pivot toward econometric inference for enumerated effects rather than graph certificates."
  - "No proposal/review artifacts were generated because the topic stopped during gap harvesting."
seeds_burned:
  - index: 0
    one_liner: "(seed index 0 — one-liner not found in state.json)"
    reason: "Already solved by Perkovic 2020; do not retry pure MPDAG/CPDAG orientation certificates as flagship thmsmith topics."
proof_attempt_summary: |
  This attempt salvaged the previous fairness graph idea into an ordinary MPDAG/CPDAG total-effect invariance theorem for P(Y | do(A)). It failed before proposal review because the exact orientation-cut criterion is already in Perkovic 2020, including the undirected-first-edge obstruction and sufficiency result. Future nearby work should not target graph-identification certificates directly; use MPDAG/PAG enumeration only as input to an econometric inference or efficiency question.
banked_on: "2026-05-25"
---

# eid_mpdag_effect_invariance_witness / v1 — Failed

**Topic.** MPDAG total-effect invariance witness for P(Y | do(A)): an orientation-cut certificate over DAG completions.

**Novelty target.** flagship

**Stage -0.5 verdict.** NA

**Stage 0.5 verdict.** NA

**Banking reason.** Stage -1.1 rejected the topic as already solved: Perkovic 2020 already gives the necessary-and-sufficient MPDAG total-effect identification/invariance criterion, including the undirected first-edge failure condition and sufficiency theorem.

## Key files

- `eid_mpdag_effect_invariance_witness_v1_state.json` — pipeline state at banking (`banked: true`).
- `eid_mpdag_effect_invariance_witness_v1_proposal.tex` — final proposal version.
- `eid_mpdag_effect_invariance_witness_v1.tex` — derivation note (if Stage 0 ran).
- `eid_mpdag_effect_invariance_witness_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `eid_mpdag_effect_invariance_witness_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
