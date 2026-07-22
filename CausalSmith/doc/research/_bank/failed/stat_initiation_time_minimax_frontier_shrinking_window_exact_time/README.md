---
qid: stat_initiation_time_minimax_frontier
spec: shrinking_window_exact_time
topic: "minimax shrinking-window frontier for exact initiation-time causal survival effects: in the single-initiation illness-death model of Martinussen-Knudsen-Rytgaard arXiv:2605.31130, let the intervention window b_n around an interior initiation time u* shrink to zero; under a known s-Holder initiation-time response class, local initiation-density positivity, CAR censoring, bounded hazards, and explicit b_n-weighted cross-fitted nuisance-product conditions, prove the sharp minimax absolute-error rate n^(-s/(2s+1)) for the exact-time terminal-event risk with a local-polynomial one-step estimator based on the published EIF and a matching local-bump lower bound, then derive a uniform triangular-array Gaussian approximation and a computable worst-case-Holder-bias-aware confidence interval with honest coverage and optimal expected length; retain the 1,896-couple immediate-versus-six-month IUI treatment-delay analysis as the applied consumer"
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: "Define an explicit measurable cross-fitted learner family with foldwise clipping/positivity, or quantify learner-bandwidth pairs with uniform remainder assumptions; then re-review the otherwise field-grade kernel."
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - "The fitted hazards in \\widehat R_{b_n} are not a specified measurable learning procedure or a quantified learner class, so C^{BA}_{n,alpha}[b_n], B^G_alpha, and its claimed honesty are not yet determinate objects."
  - "Angle 0 incorrectly treated Martinussen--Knudsen--Rytgaard Theorem 4.1 as licensing substitution of an externally fixed q_b; the paper's EIF is for its own natural-hazard-derived normalized-window intervention."
  - "The critical-regime law initially lacked a triangular law, centered/scaled statistic, and an explicit map from the limiting marked point process to a real-valued law."
reusable_artifacts:
  - "discovery/gaps.json — literature scan and comparator map."
  - "discovery/proto_core.json — final field-tier angle with the independently derived exogenous-hazard EIF setup and typed Gaussian/critical experiment skeleton."
  - "reviews/angle1_v5.json — final one-defect review and concrete learner-class repair path."
  - "orchestrator/decision_log.jsonl — full sol consultations, rejected constructions, and anti-repetition constraints across both angles."
seeds_burned: []
proof_attempt_summary: |
  Discovery explored two field-tier angles over 18 proposal/review iterations. The first angle collapsed because it repeatedly substituted an exogenous initiation density into a published EIF that did not support that substitution; the second rebuilt the EIF and effective-count experiment from first principles and reached a field-grade proposal with no novelty flags. It was stopped at D-0.5 because the cross-fitted hazard learner remained unspecified, leaving the proposed bias-aware interval and honesty class mathematically indeterminate; a future retry should start from angle 1 and define an explicit measurable learner family with foldwise clipping, positivity, and uniform remainder conditions.
banked_on: "2026-07-22"
---

# stat_initiation_time_minimax_frontier / shrinking_window_exact_time — Failed

**Topic.** minimax shrinking-window frontier for exact initiation-time causal survival effects: in the single-initiation illness-death model of Martinussen-Knudsen-Rytgaard arXiv:2605.31130, let the intervention window b_n around an interior initiation time u* shrink to zero; under a known s-Holder initiation-time response class, local initiation-density positivity, CAR censoring, bounded hazards, and explicit b_n-weighted cross-fitted nuisance-product conditions, prove the sharp minimax absolute-error rate n^(-s/(2s+1)) for the exact-time terminal-event risk with a local-polynomial one-step estimator based on the published EIF and a matching local-bump lower bound, then derive a uniform triangular-array Gaussian approximation and a computable worst-case-Holder-bias-aware confidence interval with honest coverage and optimal expected length; retain the 1,896-couple immediate-versus-six-month IUI treatment-delay analysis as the applied consumer

**Novelty target.** field

**Stage -0.5 verdict.** NO-PASS

**Stage 0.5 verdict.** NA

**Banking reason.** Stopped after D-0.5 revision caps: field-grade rare-initiation phase-transition kernel remained mathematically incomplete because the fitted learner/procedure class was not determinate, so the bias-aware interval and honesty class were not well-posed.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The final reviewer still assessed the kernel at field tier. Reuse the angle-1
causal/statistical definitions and literature work, but independently verify
the displayed exogenous-hazard EIF and do not restore the angle-0 Theorem 4.1
substitution. The bank is tagged `reraise_status: retry` because the remaining
defect is a concrete procedure-typing gap rather than a refuted topic.
