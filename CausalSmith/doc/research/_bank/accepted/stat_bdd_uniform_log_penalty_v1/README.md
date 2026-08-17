---
qid: stat_bdd_uniform_log_penalty
spec: v1
topic: "Dual co-main contribution for Cattaneo–Titiunik–Yu distance-based boundary estimation. First, on the exact P_NP(L,q) law class for integer q >= 1 and L >= 4, prove the (log n/n)^(1/4) lower bound for arbitrary law-independent point-indexed Borel sections and hence for the literal displayed CTY common-map class; this full-P_NP result is converse-only and claims no full-class achievability. Second, on the distinct exact displayed L-uniformized Euclidean-distance, uniform-kernel CTY Assumptions 1–2 plus Theorem-2-envelope class P12(p,nu,L), retain the explicit winsorized Gram-stabilized expected-risk upper for L >= 4 and the matched outer-expected minimax frontier for L >= L0(p). Position the P12 theorem as a separate co-main result: CTY provide identification, sequence-scoped bias, and probability-order stochastic control but do not state this common-law-class outer-expected minimax equality. Do not claim broader metric/kernel coverage, exact constants, or transfer of the P12 upper to full P_NP."
novelty_target: field
banked_novelty_tier: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: "kernel_substituted"
reusable: solver_blocked
reraise_status: unknown
gap_reasons:
  - "The full P_NP result is converse-only: no full-class achievability is claimed."
  - "The matched frontier is proved on the separate structured P12 class, not on full P_NP."
reusable_artifacts:
  - Causalean/Stat/Minimax/MaximalCoupling.lean
  - Causalean/Stat/Minimax/CoordinatewiseOverlap.lean
  - Causalean/Mathlib/Probability/FiniteMarkedPoissonPartition/Depoissonization.lean
  - Causalean/Mathlib/MeasureTheory/AnalyticSetUniversalMeasurability/UpperSemianalytic.lean
  - Causalean/Stat/Concentration/VarianceAdaptiveVCExpectedMaximal/Separability.lean
  - Causalean/Stat/Concentration/VarianceAdaptiveVCExpectedMaximal/EntropyChaining.lean
  - Causalean/Mathlib/InformationTheory/CommonStatisticBernoulli.lean
  - Causalean/Stat/Nonparametric/LocalPolynomial/GramCoercivity.lean
  - Causalean/Mathlib/Analysis/HalfDiscPolar.lean
  - Causalean/Stat/Nonparametric/LocalPolynomial/CoordinateDerivative.lean
seeds_burned: []
proof_attempt_summary: |
  The accepted derivation proved the same-class logarithmic converse by a
  coordinatewise-overlap marked-Poisson reduction and separately assembled the
  winsorized outer-risk upper bound on the exact P12 class.  Promotion moved the
  reusable coupling, depoissonization, empirical-process, Bernoulli-kernel,
  coercivity, polar-integration, and derivative-control substrate into Causalean;
  the angular hard family and CTY-specific theorem assembly remain local.
banked_on: "2026-08-13"
paper_score: 6.8
paper_score_rationale: "The verified lower-bound and conditional signed-frontier results are real and potentially useful, but the manuscript needs sharper claim calibration, cleaner assumption bookkeeping, and better exposition before publication."
---

# stat_bdd_uniform_log_penalty / v1 — Accepted

**Topic.** Dual co-main contribution for Cattaneo–Titiunik–Yu distance-based boundary estimation. First, on the exact P_NP(L,q) law class for integer q >= 1 and L >= 4, prove the (log n/n)^(1/4) lower bound for arbitrary law-independent point-indexed Borel sections and hence for the literal displayed CTY common-map class; this full-P_NP result is converse-only and claims no full-class achievability. Second, on the distinct exact displayed L-uniformized Euclidean-distance, uniform-kernel CTY Assumptions 1–2 plus Theorem-2-envelope class P12(p,nu,L), retain the explicit winsorized Gram-stabilized expected-risk upper for L >= 4 and the matched outer-expected minimax frontier for L >= L0(p). Position the P12 theorem as a separate co-main result: CTY provide identification, sequence-scoped bias, and probability-order stochastic control but do not state this common-law-class outer-expected minimax equality. Do not claim broader metric/kernel coverage, exact constants, or transfer of the P12 upper to full P_NP.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** F5 clean after dual-model F4 convergence: exact same-class CTY logarithmic converse and a distinct matched P12 outer-risk frontier, with zero added assumptions or proof holes.

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
