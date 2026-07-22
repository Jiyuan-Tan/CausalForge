---
qid: pid_heavy_tail_cate_bounds
spec: v1
topic: "Sharp partial identification of the conditional average treatment effect when the propensity score is bounded away from {0,1} but the outcome regression admits heavy tails (no uniform sub-Gaussian / sub-exponential moment bound). Find a regime-opening or strict-extension result on the bound width and its dependence on a heavy-tail index alpha."
novelty_target: flagship
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: "kernel_substituted"
reusable: unknown
reraise_status: retry
gap_reasons:
  - 'Conjecture 2: C-sanity — The exhibited truncated-Pareto witness has finite support for every finite n, so it cannot itself satisfy W_Gamma(P'')=+infty; the sketch proves only divergence along a sequence, not the stated neighborhood witness.'
  - 'Theorem 2: C-sanity — The claimed alpha->infty equality to the bounded-support Manski-MSM width contradicts the proposal''s own Exhibit 9.3, where the Hölder limit is only a loose upper bound and not the stated width.'
  - 'Conjecture 1: C-wellposed — W_Gamma is defined as the no-tail-restriction case ''beyond integrability'', but the necessity branch ranges over alpha*(P;x,a) <= 1 laws where the conditional mean and hence CATE width may be undefined without an extended-expectation convention.'
  - 'Theorem 1: C-coherence — The §4 formula includes an extra c(alpha) while §8 defines only c_Gamma=(Gamma-1)Gamma^{-1/alpha}; the proof sketch''s Hölder factor also uses Gamma^{1-1/alpha}, so the constants do not cohere.'
  - 'Conjecture 1: N-mischar — The proposal says YadlowskyNamkoongBasuDuchiTian2022Bounds assumes bounded outcomes for its closest CATE bound, but the paper is formulated for real-valued outcomes and explicitly develops CATE/ATE bounds under Gamma-selection bias.'
  - 'Theorem 2: N-pub — The bounded-support Manski/MSM specialization is not novel relative to KallusMaoZhou2019CATEIntervals and Manski1990AERBounds.'
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  Attempted a moment-existence dichotomy for sharp MSM(Gamma) CATE width under heavy-tailed (unbounded) outcomes, claiming finite width iff E[|Y|^alpha | X,A] < inf for some alpha > 1. The core converse witness (Conjecture 2 / Conjecture 3) collapsed: the truncated-Pareto construction has finite support for every finite n and proves only divergence along a sequence, not an actual neighborhood witness satisfying W_Gamma(P') = +inf. The headline comparators were also mischaracterized: Yadlowsky et al. 2022 is formulated for real-valued outcomes, not bounded-outcome-only, which narrows the claimed gap. One genuinely novel object survives — the Pareto-extremal converse witness concept (Conjecture 2 rated 'new' on both repo and published axes) — but the surrounding kernel collapsed before any Lean formalization was attempted.
banked_on: "2026-05-24"
---

# pid_heavy_tail_cate_bounds / v1 — Failed

**Topic.** Sharp partial identification of the conditional average treatment effect when the propensity score is bounded away from {0,1} but the outcome regression admits heavy tails (no uniform sub-Gaussian / sub-exponential moment bound). Find a regime-opening or strict-extension result on the bound width and its dependence on a heavy-tail index alpha.

**Novelty target.** flagship

**Stage -0.5 verdict.** NO-PASS

**Stage 0.5 verdict.** NA

**Banking reason.** Discovery NO-PASS after 5 angles (0-4); best tier=field; blocking: N-mischar on KMZ/Yadlowsky comparators, C-sanity on converse witness and Manski-limit theorem.

## Key files

- `pid_heavy_tail_cate_bounds_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_heavy_tail_cate_bounds_v1_proposal.tex` — final proposal version.
- `pid_heavy_tail_cate_bounds_v1.tex` — derivation note (if Stage 0 ran).
- `pid_heavy_tail_cate_bounds_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_heavy_tail_cate_bounds_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
