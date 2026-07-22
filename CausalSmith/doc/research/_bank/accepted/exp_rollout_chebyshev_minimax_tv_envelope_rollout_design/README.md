---
qid: exp_rollout_chebyshev_minimax
spec: tv_envelope_rollout_design
topic: "Optimal Chebyshev-spaced rollout measurement schedule and minimax linear-unbiased total-treatment-effect estimation under β-order network interference (Cortez et al. 2024, arXiv:2405.05119): over a Sobolev-ellipsoid β-order coefficient class, WHICH treated-fractions to roll out to is the design variable; the optimum is Chebyshev-spaced, and the minimax linear-unbiased estimator attains a worst-case design-variance β-exponent (C_s(c)/q)^{2β} with a matching lower bound from the classical Chebyshev extremal property — resolving whether Cortez et al.'s (β/q)^{2β} interpolation-variance penalty is intrinsic (exponential ORDER 2β fixed, BASE reducible via additional measurement points k=⌈cβ⌉)"
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: null
reusable: unknown
reraise_status: unknown
gap_reasons:
  # TODO: paste verbatim reviewer phrases identifying which Conjecture
  # collapsed and why. Source: exp_rollout_chebyshev_minimax_tv_envelope_rollout_design_reviews.jsonl and any
  # *_oneshot_stage0_5_*.txt files in this directory.
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  TODO: 2-3 sentence epitaph — what was attempted, what collapsed, what remains.
banked_on: "2026-07-02"
paper_score: 5.8
paper_score_rationale: "The verified mathematical core is coherent and potentially useful, but the paper is too narrowly delivered relative to its econometric framing and several prose claims and objects around interference, exact rollout risk, and covariance structure need substantial tightening before publication."
---

# exp_rollout_chebyshev_minimax / tv_envelope_rollout_design — Accepted

**Topic.** Optimal Chebyshev-spaced rollout measurement schedule and minimax linear-unbiased total-treatment-effect estimation under β-order network interference (Cortez et al. 2024, arXiv:2405.05119): over a Sobolev-ellipsoid β-order coefficient class, WHICH treated-fractions to roll out to is the design variable; the optimum is Chebyshev-spaced, and the minimax linear-unbiased estimator attains a worst-case design-variance β-exponent (C_s(c)/q)^{2β} with a matching lower bound from the classical Chebyshev extremal property — resolving whether Cortez et al.'s (β/q)^{2β} interpolation-variance penalty is intrinsic (exponential ORDER 2β fixed, BASE reducible via additional measurement points k=⌈cβ⌉)

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** Matched two-sided Chebyshev-Lobatto minimax over the TV-envelope rollout-node-placement design problem (base rho(q)/q, field tier); both substrate gates (Ehlich-Zeller/Bernstein-Szego + finite-dim l1/linf duality) proven 0-sorry axiom-clean via study sub-pipelines.

## Key files

- `exp_rollout_chebyshev_minimax_tv_envelope_rollout_design_state.json` — pipeline state at banking (`banked: true`).
- `exp_rollout_chebyshev_minimax_tv_envelope_rollout_design_proposal.tex` — final proposal version.
- `exp_rollout_chebyshev_minimax_tv_envelope_rollout_design.tex` — derivation note (if Stage 0 ran).
- `exp_rollout_chebyshev_minimax_tv_envelope_rollout_design_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `exp_rollout_chebyshev_minimax_tv_envelope_rollout_design_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
