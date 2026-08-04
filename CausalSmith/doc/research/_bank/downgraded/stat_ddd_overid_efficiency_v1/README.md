---
qid: stat_ddd_overid_efficiency
spec: v1
topic: "Incremental joint constant-score-span GMM weighting and pointwise inference for a prespecified aggregate of covariate-adjusted staggered DDD effects when multiple admissible comparison cohorts share units. The note takes the published Ortiz-Villavicencio--Sant'Anna pairwise scores as a fixed retained score vector, identifies the causal aggregate, constructs an everywhere-defined clipped, projected, and ridged cross-fitted estimator conditional on supplied L4 nuisance rates and a product-rate condition, and compares joint covariance weighting with separate within-block optimization. Its contribution is the DDD-specific shared-cell covariance mapping, the exact if-and-only-if equality frontier and quadratic variance gap, a feasible descriptive loss diagnostic, and a bounded open nonzero-effect strict-gap family. Hsieh's shared-unit covariance accounting and generic finite-dimensional GMM/SUR quadratic algebra are prior art and are not claimed as new. The scope is pointwise and finite dimensional: no full conditional-moment efficient influence function or semiparametric efficiency bound, uniform learner attainability or coverage, or covariate-varying relative-precision result is claimed."
novelty_target: incremental
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: "tier_genuinely_below"
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The optimization and quadratic frontier are finite-dimensional GMM/SUR projection algebra, so the DDD-specific contribution is chiefly the shared-cell covariance mapping and its implementation rather than a new general efficiency theory."
  - "This is too narrow for field or flagship status because it neither characterizes the full conditional-moment efficiency bound nor establishes uniform attainability, coverage, or inference for the estimated variance gap."
reusable_artifacts:
  - path: discovery/core.json
    kind: operator
    one_line: Typed 11-node core containing the retained pairwise-score covariance map, joint loading, exact equality frontier, variance-gap diagnostic, and strict-gap family.
  - path: discovery/writeup.tex
    kind: witness
    one_line: Fully rendered mathematical derivation with the DDD shared-cell covariance expansion and bounded nonzero-effect strict-gap construction.
  - path: discovery/proof_archive/index.jsonl
    kind: proof_archive
    one_line: Auditable proof snapshots and revisions for reusing settled D0 derivations without repeating the solve history.
seeds_burned: []
proof_attempt_summary: |
  Stage D proved and reviewed the complete 11-node constant-score-span result:
  identification, conditional pointwise inference for the feasible joint estimator,
  an exact joint-versus-separate equality frontier and quadratic variance gap, and a
  bounded strict-gap family. Math and decision review passed, and the final general
  referee graded the result subfield, but the original broader semiparametric-efficiency
  ambition remained outside scope: no full conditional-moment EIF/bound, uniform learner
  attainability or coverage, or inference for the estimated gap was established. The user
  therefore banked the sound result as downgraded at the D-F boundary without formalization.
banked_on: "2026-08-01"
---

# stat_ddd_overid_efficiency / v1 — Downgraded

**Topic.** Incremental joint constant-score-span GMM weighting and pointwise inference for a prespecified aggregate of covariate-adjusted staggered DDD effects when multiple admissible comparison cohorts share units. The note takes the published Ortiz-Villavicencio--Sant'Anna pairwise scores as a fixed retained score vector, identifies the causal aggregate, constructs an everywhere-defined clipped, projected, and ridged cross-fitted estimator conditional on supplied L4 nuisance rates and a product-rate condition, and compares joint covariance weighting with separate within-block optimization. Its contribution is the DDD-specific shared-cell covariance mapping, the exact if-and-only-if equality frontier and quadratic variance gap, a feasible descriptive loss diagnostic, and a bounded open nonzero-effect strict-gap family. Hsieh's shared-unit covariance accounting and generic finite-dimensional GMM/SUR quadratic algebra are prior art and are not claimed as new. The scope is pointwise and finite dimensional: no full conditional-moment efficient influence function or semiparametric efficiency bound, uniform learner attainability or coverage, or covariate-varying relative-precision result is claimed.

**Novelty target.** incremental

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** D0.5 math and decision reviews passed; the note achieved subfield novelty within its explicit constant-score-span scope, and the user elected to bank it as downgraded at the D-F boundary without entering formalization.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
