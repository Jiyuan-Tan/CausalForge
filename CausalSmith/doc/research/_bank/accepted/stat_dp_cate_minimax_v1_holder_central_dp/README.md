---
qid: stat_dp_cate_minimax_v1
spec: holder_central_dp
topic: "Differentially private minimax rate for pointwise CATE estimation under Holder smoothness and central (eps,delta)-DP: the sharp two-sided rate for tau(x0)=E[Y(1)-Y(0)|X=x0] pairing a private higher-order-influence-function doubly-robust R-learner (upper bound, with privatized estimation of the alpha-smooth propensity and beta-smooth outcome nuisances) against a localized fingerprinting/tracing lower bound, extending the non-private CATE minimax rate of Kennedy-Balakrishnan-Robins-Wasserman (2024, arXiv 2203.00837) with a derived DP-cost term and a new privacy-dominated regime/phase boundary in (smoothness, dimension, privacy) space; differs from upper-bound-only private-CATE methods (DP-CATE 2503.03486, Niu 2202.11043) and from private pointwise nonparametric regression (Cai-Chakraborty-Vuursteen 2406.06755) by delivering the matching causal-functional lower bound"
novelty_target: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: "kernel_substituted"
reusable: solver_blocked
reraise_status: unknown
gap_reasons:
  # TODO: paste verbatim reviewer phrases identifying which Conjecture
  # collapsed and why. Source: stat_dp_cate_minimax_v1_holder_central_dp_reviews.jsonl and any
  # *_oneshot_stage0_5_*.txt files in this directory.
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  TODO: 2-3 sentence epitaph — what was attempted, what collapsed, what remains.
banked_on: "2026-07-12"
---

# stat_dp_cate_minimax_v1 / holder_central_dp — Accepted

**Topic.** Differentially private minimax rate for pointwise CATE estimation under Holder smoothness and central (eps,delta)-DP: the sharp two-sided rate for tau(x0)=E[Y(1)-Y(0)|X=x0] pairing a private higher-order-influence-function doubly-robust R-learner (upper bound, with privatized estimation of the alpha-smooth propensity and beta-smooth outcome nuisances) against a localized fingerprinting/tracing lower bound, extending the non-private CATE minimax rate of Kennedy-Balakrishnan-Robins-Wasserman (2024, arXiv 2203.00837) with a derived DP-cost term and a new privacy-dominated regime/phase boundary in (smoothness, dimension, privacy) space; differs from upper-bound-only private-CATE methods (DP-CATE 2503.03486, Niu 2202.11043) and from private pointwise nonparametric regression (Cai-Chakraborty-Vuursteen 2406.06755) by delivering the matching causal-functional lower bound

**Novelty target.** subfield

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** F5-clean: all 7 headline results proven and axiom-clean (barrier, converse, achievability, certified two-sided bracket, sharp beta=gamma rate, regression inheritance); zero substrate gates; F4 converged with both reviewers matched. Banked at novelty tier subfield per user decision.

## Key files

- `stat_dp_cate_minimax_v1_holder_central_dp_state.json` — pipeline state at banking (`banked: true`).
- `stat_dp_cate_minimax_v1_holder_central_dp_proposal.tex` — final proposal version.
- `stat_dp_cate_minimax_v1_holder_central_dp.tex` — derivation note (if Stage 0 ran).
- `stat_dp_cate_minimax_v1_holder_central_dp_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `stat_dp_cate_minimax_v1_holder_central_dp_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
