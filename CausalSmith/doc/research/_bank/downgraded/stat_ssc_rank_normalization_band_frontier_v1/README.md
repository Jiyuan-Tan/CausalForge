---
qid: stat_ssc_rank_normalization_band_frontier
spec: v1
topic: "Rank normalization and target-loading weak-identification boundaries for honest Synthetic Survival Control bands. In the right-censored survival-factor panel, make the canonical coordinate construction conditional on the model's target-pre factor compatibility and use the positive pre-period Gram for uniqueness; define W_r^* as the minimax expected supremum width among uniformly honest continuous-time bands for the missing post-control survival curve. Prove the sharp exact-rank-one frontier W_1^* asymptotic to (N0 KD)^(-1/2). For every fixed r>=2 on the quantitatively strong exact-rank class, prove the unrestricted bracket c rho_r <= W_r^* <= C{rho_r+eta_D(K_D)}, with W_r^* asymptotic to rho_r only on subregimes where eta_D(K_D)=O(rho_r), and do not assert unrestricted tightness. Prove the flagship same-topic boundary that, without a uniform positive pre-period contrast-Gram lower bound, minimax honest width is Theta(1) even on a donor-visible known-rank-two subclass of the Han--Shah Theorem 1 factor-and-span model; hence donor-rank detection alone cannot license shrinking or rank-adaptive bands. Construct and rigorously validate the censoring-aware patient-level functional-PCR martingale-multiplier band for the stated upper envelope, with controlled interpolation and normalization-preserving Le Cam lower pairs. The remaining repair must derive the target coordinate from factor compatibility and positive-Gram uniqueness, prove the pooled non-identically-censored rank-one Kaplan--Meier expansion and multiplier coupling, establish a genuinely grid-uniform conditional multiplier and random-quantile theorem for the data-dependent functional-PCR derivative including covariance estimation, entropy and fallback events, correct the Pinsker locator to Lemma 2.5(i), and substantively position or remove every retained comparator. Do not claim unrestricted higher-rank W_r^* asymptotic to rho_r unless an explicit measurable estimator is proved to remove eta_D uniformly for every relative-growth sequence; a matching eta_D converse would instead sharpen the upper envelope, not imply the rho_r frontier. Do not strengthen the model, retreat to pointwise or balanced-only asymptotics, or offer bootstrap validity without the minimax converses."
novelty_target: flagship
banked_novelty_tier: field
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "tier=field below flagship floor"
  - "requested strength-indexed decaying-Gram frontier/adaptive result is a new research program and not a bounded in-scope repair"
reusable_artifacts:
  - "discovery/writeup.tex"
  - "discovery/proto_core.json"
  - "discovery/proof_archive/"
  - "discovery/durable_proof_graph.json"
  - "reviews/review_math.json"
  - "reviews/review_general.json"
seeds_burned: []
proof_attempt_summary: |
  The run completed a mathematically accepted 43-page discovery proof of the
  rank-normalized SSC band construction and minimax bounds; all 24 proof records
  were discharged, all six citations were verified, and the final math and
  decision reviews passed. The cold general review assessed the result at field
  tier rather than the required flagship tier; reaching flagship would require a
  new decay-indexed Gram frontier and adaptive-band or impossibility theory.
token_usage:
  complete: false
  orchestrator_tokens: 1528558
  pipeline_codex_tokens: 85108778
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-08-28"
---

# stat_ssc_rank_normalization_band_frontier / v1 — Downgraded

**Topic.** Rank normalization and target-loading weak-identification boundaries for honest Synthetic Survival Control bands. In the right-censored survival-factor panel, make the canonical coordinate construction conditional on the model's target-pre factor compatibility and use the positive pre-period Gram for uniqueness; define W_r^* as the minimax expected supremum width among uniformly honest continuous-time bands for the missing post-control survival curve. Prove the sharp exact-rank-one frontier W_1^* asymptotic to (N0 KD)^(-1/2). For every fixed r>=2 on the quantitatively strong exact-rank class, prove the unrestricted bracket c rho_r <= W_r^* <= C{rho_r+eta_D(K_D)}, with W_r^* asymptotic to rho_r only on subregimes where eta_D(K_D)=O(rho_r), and do not assert unrestricted tightness. Prove the flagship same-topic boundary that, without a uniform positive pre-period contrast-Gram lower bound, minimax honest width is Theta(1) even on a donor-visible known-rank-two subclass of the Han--Shah Theorem 1 factor-and-span model; hence donor-rank detection alone cannot license shrinking or rank-adaptive bands. Construct and rigorously validate the censoring-aware patient-level functional-PCR martingale-multiplier band for the stated upper envelope, with controlled interpolation and normalization-preserving Le Cam lower pairs. The remaining repair must derive the target coordinate from factor compatibility and positive-Gram uniqueness, prove the pooled non-identically-censored rank-one Kaplan--Meier expansion and multiplier coupling, establish a genuinely grid-uniform conditional multiplier and random-quantile theorem for the data-dependent functional-PCR derivative including covariance estimation, entropy and fallback events, correct the Pinsker locator to Lemma 2.5(i), and substantively position or remove every retained comparator. Do not claim unrestricted higher-rank W_r^* asymptotic to rho_r unless an explicit measurable estimator is proved to remove eta_D uniformly for every relative-growth sequence; a matching eta_D converse would instead sharpen the upper envelope, not imply the rho_r frontier. Do not strengthen the model, retreat to pointwise or balanced-only asymptotics, or offer bootstrap validity without the minimax converses.

**Novelty target.** flagship

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REVISE

**Banking reason.** D0.5.G tier=field, floor=flagship, meets_floor=false.

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
