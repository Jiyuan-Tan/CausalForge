---
qid: scm_cs_hedge_completeness
spec: v1
topic: "completeness of the SS-ID algorithm at its open cs_fail_2 failure line for data fusion under systematic selection (Lee-Ghassami-Shpitser, arXiv:2404.06602, UAI 2024): define the context-specific hedge (CS-hedge) as a graph-only correlation-hiding structure over label-set ADMG multigraphs, and prove the context-marginal sufficiency lemma — every admissible context U-severs one side, so each context law depends only on the uncoupled per-side marginals while the target Q = p(Y(a), S=empty), living in the un-severed S=empty world, depends on the coupled sum kappa — hence SS-ID is sound and complete, settling the authors' published conjecture"
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: not_reusable
reraise_status: retry
gap_reasons:
  - "forced_label_deletion: each eligible A_0-serious context deletes the required labelled S→A_0 edge, so the asserted line-9 trace instead has a valid Algorithm 2 candidate."
  - "target-functional-mismatch: the prompt and stale core metadata use a natural S=empty event with a pi(empty) factor, whereas SS-ID targets do(A=a,S=empty)."
  - "novelty-floor-unmet: no generic final-return family or universal cs_fail_2 certificate was proved."
reusable_artifacts:
  - path: discovery/solve_thm_context_marginal_sufficiency.json
    scope: "Restricted two-arm parity/context-marginal calculation only; it is not implied by arbitrary cs_fail_2 traces and must use the context-setting intervention target."
  - path: discovery/gaps.json
    scope: "Literature and open-problem map; verify cited source claims independently before reuse."
seeds_burned:
  - index: 0
    one_liner: "Every terminal SS-ID confounded-selector failure contains a CS-hedge that witnesses nonidentification of \\(p(Y(a),S=\\emptyset)\\)."
    reason: "The universal terminal CS-hedge and exact two-block context-severing claims were not established; the attempted witness was refuted by forced selector-edge label deletion."
  - index: 1
    one_liner: "A label-aware two-block hedge hides its coupling from every supplied context law exactly when each nonempty context severs one block."
    reason: "The universal terminal CS-hedge and exact two-block context-severing claims were not established; the attempted witness was refuted by forced selector-edge label deletion."
proof_attempt_summary: |
  The run proved a restricted parity cancellation lemma, then attempted to turn a
  four-vertex support-pooling construction into an identified Algorithm 2 line-9
  failure. D0.5 refuted that trace because mandatory selector-edge labels are
  deleted in every eligible serious context, yielding a valid candidate instead.
  The published SS-ID completeness conjecture therefore remains open.
banked_on: "2026-07-16"
---

# scm_cs_hedge_completeness / v1 — Failed

**Topic.** completeness of the SS-ID algorithm at its open cs_fail_2 failure line for data fusion under systematic selection (Lee-Ghassami-Shpitser, arXiv:2404.06602, UAI 2024): define the context-specific hedge (CS-hedge) as a graph-only correlation-hiding structure over label-set ADMG multigraphs, and prove the context-marginal sufficiency lemma — every admissible context U-severs one side, so each context law depends only on the uncoupled per-side marginals while the target Q = p(Y(a), S=empty), living in the un-severed S=empty world, depends on the coupled sum kappa — hence SS-ID is sound and complete, settling the authors' published conjecture

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** FAIL

**Banking reason.** D0.5 rejected the headline: the proposed terminal trace violates mandatory LS-ADMMG label deletion, the prompt uses the wrong SS-ID target semantics, and no universal cs_fail_2 certificate was proved.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — unaccepted Stage 0 derivation note.
- `reviews/reviews.jsonl` — per-round reviewer log.
- `reviews/review_math.json` and `reviews/review_rubric.json` — terminal D0.5 findings.

## Notes

The exact two-block/universal-extraction seeds are burned. A future attempt may
retry the broader completeness problem only with the correct context-setting
target and a new terminal certificate checked against mandatory LS-ADMMG labels.
