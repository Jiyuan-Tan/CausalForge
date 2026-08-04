---
qid: stat_plm_two_nuisance_minimax
spec: v1
topic: "Close the full two-nuisance structure-agnostic minimax gap for the partially linear causal coefficient: match Gu–Yin–Cai–Fan Appendix A.1 with a budget-aware two-sided empirical-balancing estimator, or prove the missing cross-stochastic lower bound"
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "The standard one-regressor root-n reduction at degenerate X is not field-level as positioned: the note concedes gu2026optimally only displays nonmatching bounds, so it identifies no specific published product-converse, estimator, or workflow that this negative result refutes."
  - "The clipped covariance estimator supplies the upper-rate deliverable but appears only in proof_tex; state it in the Stat target/theorem so the estimator and its rate are node-addressable."
  - "TERMINAL_BELOW_FLOOR: the strongest proved result is an incremental degenerate-covariate counterexample, and neither a budget-aware two-sided balancing theorem nor a nondegenerate cross-stochastic hard family is currently supported by the proof core."
reusable_artifacts:
  - "discovery/core.json — structured degenerate-covariate root-n counterexample, clipped covariance estimator proof, and corrected comparator table"
  - "discovery/writeup.tex — rendered matching upper/lower root-n argument and covariate-richness obstruction"
  - "discovery/proto_core.json — verified literature map and exact fixed-class experiment definitions"
seeds_burned:
  - index: 0
    one_liner: "all-estimator cross-stochastic converse"
    reason: "The universal fixed-class cross-stochastic product converse collapses on the allowed degenerate-covariate subclass; the surviving root-n counterexample is incremental rather than field-level."
proof_attempt_summary: |
  The run attempted the missing fixed-class cross-stochastic product converse in the asymmetric pure-stochastic regime. D0 instead proved that the universal converse collapses on an allowed degenerate-covariate subclass: a clipped covariance estimator and bounded non-atomic Le Cam submodel give matching root-n risk independently of the nuisance budgets. What remains is genuinely new mathematics under a quantitative covariate-richness condition—either a nondegenerate cross-stochastic hard family or a budget-aware two-sided empirical-balancing upper theorem.
banked_on: "2026-07-24"
---

# stat_plm_two_nuisance_minimax / v1 — Downgraded

**Topic.** Close the full two-nuisance structure-agnostic minimax gap for the partially linear causal coefficient: match Gu–Yin–Cai–Fan Appendix A.1 with a budget-aware two-sided empirical-balancing estimator, or prove the missing cross-stochastic lower bound

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The standard one-regressor root-n reduction at degenerate X is mathematically sound but does not close or refute Gu et al.'s two-nuisance gap at field tier.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The counterexample is useful as a scope guard for future attempts: any claimed
product frontier must exclude or separately handle degenerate covariate laws. The
entry is marked `not_reusable` as a direct retry seed because its proof core does not
contain the nondegenerate balancing or testing machinery needed to reach field tier.
