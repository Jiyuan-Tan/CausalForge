---
qid: exp_bipartite_minimax_design
spec: v1
topic: "Minimax-optimal heterogeneous Bernoulli design for bipartite-interference experiments: minimize a graph-only worst-case design-based variance envelope (the supremum of the Hajek estimator's asymptotic variance over bounded potential outcomes, a closed-form functional of the bipartite graph G and the per-intervention-unit probability vector p) over p subject to a budget and positivity floor, delivering the optimal design p*(G) with an OBSERVABLE optimality certificate --- a convex-relaxation-plus-rounding approximation-ratio bound alpha provably nonvacuous under an explicit intervention-unit output-degree-dispersion regime --- together with the supporting non-identical-Bernoulli Hajek martingale CLT and conservative variance estimator establishing the design's Wald-coverage validity; extends 'Design-based causal inference in bipartite experiments' (arXiv:2501.09844), which proves the CLT and closed-form variance only for a homogeneous Bernoulli(p) design and explicitly leaves heterogeneous per-unit probabilities to future research."
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: null
reusable: unknown
reraise_status: unknown
gap_reasons: []
reusable_artifacts:
  - discovery/core.json
  - discovery/resolved_oeqs_manual.json
  - discovery/solve_oeq_dispersion_certificate.json
  - formalization/plan.json
  - graph.json
seeds_burned: []
proof_attempt_summary: |
  D0 answered the former dispersion-certificate OEQ negatively by constructing
  finite bipartite graphs whose first-order dispersion summaries remain controlled
  while alpha_cert diverges. The reopened F pipeline preserved inherited proofs,
  formalized that construction as dispersionCertificateUnbounded, and completed
  proof filling, lint, dual-model review, a full paper build, and the axiom audit.
banked_on: "2026-07-13"
paper_score: 6.2
paper_score_rationale: "The formal results appear internally sound and carefully caveated, but the paper does not yet demonstrate enough econometric value or practical relevance for a leading journal."
---

# exp_bipartite_minimax_design / v1 — Accepted

**Topic.** Minimax-optimal heterogeneous Bernoulli design for bipartite-interference experiments: minimize a graph-only worst-case design-based variance envelope (the supremum of the Hajek estimator's asymptotic variance over bounded potential outcomes, a closed-form functional of the bipartite graph G and the per-intervention-unit probability vector p) over p subject to a budget and positivity floor, delivering the optimal design p*(G) with an OBSERVABLE optimality certificate --- a convex-relaxation-plus-rounding approximation-ratio bound alpha provably nonvacuous under an explicit intervention-unit output-degree-dispersion regime --- together with the supporting non-identical-Bernoulli Hajek martingale CLT and conservative variance estimator establishing the design's Wald-coverage validity; extends 'Design-based causal inference in bipartite experiments' (arXiv:2501.09844), which proves the CLT and closed-form variance only for a homogeneous Bernoulli(p) design and explicitly leaves heterogeneous per-unit probabilities to future research.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** Verified CKPT2: the migrated dispersion counterexample theorem is fully proved, dual-model matched, unconditional over its stated parameter domains, and axiom-clean under the project convention.

## Key files

- `exp_bipartite_minimax_design_v1_state.json` — pipeline state at banking (`banked: true`).
- `exp_bipartite_minimax_design_v1_proposal.tex` — final proposal version.
- `exp_bipartite_minimax_design_v1.tex` — derivation note (if Stage 0 ran).
- `exp_bipartite_minimax_design_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `exp_bipartite_minimax_design_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

The migrated theorem replaces the obsolete `oeq:dispersion-certificate`; future
work should reuse the preserved counterexample construction and must not recreate
the old unanswered-question `Prop`.
