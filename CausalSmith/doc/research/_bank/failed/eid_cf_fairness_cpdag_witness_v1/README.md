---
qid: eid_cf_fairness_cpdag_witness
spec: v1
topic: "Counterfactual-fairness CPDAG orientation witness: a Markov-equivalence orientation certificate for path-specific unfair effects under imperfect causal graphs."
novelty_target: flagship
tier_at_proposal: NA
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "Stage -1.1 rejected the topic with code=out-of-scope."
  - "R2 fired because the kernel was a CPDAG/Markov-equivalence orientation certificate for counterfactual and path-specific fairness."
  - "The evidence placed the topic in structural causal model counterfactual fairness, path-specific/cross-world mediation identification, and graphical-model equivalence-class reasoning rather than the allowed econometric identification, partial-identification, panel, or causal-ML orthogonality clusters."
  - "The suggested salvage was to drop fairness/path-specific semantics and re-run as an ordinary MPDAG/CPDAG total-effect invariance problem for P(Y | do(A)) over DAG completions."
reusable_artifacts:
  - "eid_cf_fairness_cpdag_witness_v1_gaps.json: Stage -1.1 evidence and out-of-scope routing rationale."
  - "eid_cf_fairness_cpdag_witness_v1_pipeline.jsonl: exact rejection message and suggested in-scope reruns."
  - "No proposal/review artifacts were generated because the topic stopped during gap harvesting."
seeds_burned:
  - index: 0
    one_liner: "(seed index 0 — one-liner not found in state.json)"
    reason: "Out-of-scope at Stage -1.1; do not retry fairness/path-specific CPDAG orientation witnesses in thmsmith unless the cluster policy changes."
proof_attempt_summary: |
  This attempt proposed a graph-theoretic orientation witness for counterfactual fairness under imperfect causal graphs. It failed before proposal review because thmsmith classified fairness/path-specific CPDAG orientation semantics as outside the allowed discovery clusters. The reusable lesson is to keep future graph topics inside ordinary econometric total-effect invariance or exact-identification questions, not fairness-specific counterfactual notions.
banked_on: "2026-05-25"
---

# eid_cf_fairness_cpdag_witness / v1 — Failed

**Topic.** Counterfactual-fairness CPDAG orientation witness: a Markov-equivalence orientation certificate for path-specific unfair effects under imperfect causal graphs.

**Novelty target.** flagship

**Stage -0.5 verdict.** NA

**Stage 0.5 verdict.** NA

**Banking reason.** Stage -1.1 rejected the topic as out-of-scope: the CPDAG counterfactual-fairness/path-specific orientation certificate lives in fairness and graphical-model equivalence-class reasoning rather than the allowed econometric identification, partial-identification, panel, or causal-ML orthogonality clusters.

## Key files

- `eid_cf_fairness_cpdag_witness_v1_state.json` — pipeline state at banking (`banked: true`).
- `eid_cf_fairness_cpdag_witness_v1_proposal.tex` — final proposal version.
- `eid_cf_fairness_cpdag_witness_v1.tex` — derivation note (if Stage 0 ran).
- `eid_cf_fairness_cpdag_witness_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `eid_cf_fairness_cpdag_witness_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
