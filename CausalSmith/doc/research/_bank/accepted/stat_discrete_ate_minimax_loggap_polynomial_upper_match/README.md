---
qid: stat_discrete_ate_minimax_loggap
spec: polynomial_upper_match
topic: "Sharp minimax ATE estimation with unrestricted high-dimensional discrete confounders: for iid (X,A,Y) with X in [d], binary A and Y, overlap epsilon <= P(A=1|X=k) <= 1-epsilon, and unrestricted cell probabilities and conditional response means, prove that the exact minimax MSE is asymptotically equivalent up to epsilon-dependent constants to 1/n + [d/(n log n)]^2 uniformly for d <= c n log n; construct a computable hybrid estimator using plug-in estimation on well-populated cells and polynomial/factorial-moment estimation on sparsely populated cells, pair it with the published moment-matching lower bound, and establish parametric MSE through d of order sqrt(n) log n and consistency through d=o(n log n), thereby closing the log-squared gap left by Zeng-Balakrishnan-Han-Kennedy (arXiv:2405.00118). Delegate the exact heavy/light split, polynomial basis and degree constants, Poissonization details, and variance normalization to derivation, but require a proved light-cell approximation-and-variance lemma and a verified two-category confounding witness."
novelty_target: field
banked_novelty_tier: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: null
reusable: unknown
reraise_status: unknown
gap_reasons: []
reusable_artifacts:
  - discovery/writeup.tex
  - formalization/plan.json
  - formalization/crosswalk_full.md
seeds_burned: []
proof_attempt_summary: |
  The run completed the computable hybrid-estimator upper bound, light-cell
  approximation-and-variance lemma, asymptotic regime corollaries, and the
  two-category confounding witness with no proof holes. The minimax lower half
  transfers the published moment-matching input `ZengOneArmMinimaxLower` to
  ATE; that published construction is cited and attested, not rederived here.
banked_on: "2026-07-18"
paper_score: 8.2
paper_score_rationale: "The paper delivers a technically meaningful and well-scoped minimax contribution with unusually good claim fidelity, but it still needs presentational and reproducibility tightening before publication."
---

# stat_discrete_ate_minimax_loggap / polynomial_upper_match — Accepted

**Topic.** Sharp minimax ATE estimation with unrestricted high-dimensional discrete confounders: for iid (X,A,Y) with X in [d], binary A and Y, overlap epsilon <= P(A=1|X=k) <= 1-epsilon, and unrestricted cell probabilities and conditional response means, prove that the exact minimax MSE is asymptotically equivalent up to epsilon-dependent constants to 1/n + [d/(n log n)]^2 uniformly for d <= c n log n; construct a computable hybrid estimator using plug-in estimation on well-populated cells and polynomial/factorial-moment estimation on sparsely populated cells, pair it with the published moment-matching lower bound, and establish parametric MSE through d of order sqrt(n) log n and consistency through d=o(n log n), thereby closing the log-squared gap left by Zeng-Balakrishnan-Han-Kennedy (arXiv:2405.00118). Delegate the exact heavy/light split, polynomial basis and degree constants, Poissonization details, and variance normalization to derivation, but require a proved light-cell approximation-and-variance lemma and a verified two-category confounding witness.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** Clean F5 with dual F4 convergence, zero proof holes or gates, and a field-tier novelty pass; user approved CKPT 2. The ZengOneArmMinimaxLower lower bound is cited and transferred to ATE, not rederived.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The paper proof is 14,197 Lean source lines across a topic-split module tree.
Post-F5 promotion moved the generic infinite-product IID constructor to
`Causalean.Stat.Sample.PiTransport` and the generic Bernoulli-count tails to
`Causalean.Stat.Concentration.TailBounds.BinomialCount`; the ATE-specific
estimator and rate arguments remain paper-local.
