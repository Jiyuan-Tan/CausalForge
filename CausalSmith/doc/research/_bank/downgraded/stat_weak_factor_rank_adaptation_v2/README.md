---
qid: stat_weak_factor_rank_adaptation
spec: v2
topic: "Union-honest rank-and-strength adaptation for a scalar missing-block functional under a public fixed four-block causal-panel mask. Define rank zero separately and exact-rank positive-strength strata. Characterize finite-sample minimax expected length on every stratum under honesty over their union. Decide whether pairwise observed-Gaussian moduli suffice or least-favorable mixtures enlarge the correct functional. Deliver an evaluable characterization and either one data-only q/h-free attaining interval or the sharp unavoidable simultaneous excess. PRESOLVE EVIDENCE REQUIRING VERIFICATION: a legal 4x4 rank-two signed-permutation mixture has no linear term in chi-square divergence despite positive component KL, and a balanced rank-one analogue suggests an n^(1/4) gap over pairwise modulus. UNRESOLVED BOTTLENECK: simultaneous mixture-test inversion. EARLY KILL TEST: certified solution of the zero-plus-64-orbit interval problem."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "kernel_substituted"
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - "The stated profile rule is an evaluable, union-honest constant-factor oracle construction, but it neither characterizes the stratumwise minimax expected lengths nor attains their simultaneous optimum (the exact excess remains only bracketed), so it is weaker than the promised attaining/sharp simultaneous deliverable."
  - "The retry contains no solver-authored exact continuum theorem statement."
  - "The superseding proofs establish only finite-grid duality and a [1,K_alpha] comparator, explicitly disclaiming sharpness."
reusable_artifacts:
  - "discovery/writeup.tex — sound finite-grid primal/likelihood dual, exact 65-law orbit specialization, continuum-honest profile interval, and constant-factor stratumwise bounds."
  - "discovery/proto_core.json — final result graph, including the finite-action purification dependency and mixture-versus-pairwise witness."
  - "discovery/proof_archive/ — immutable solver proof payloads for the accepted finite-grid and profile-interval results."
  - "reviews/review_rubric.json — concise kernel-substitution boundary and tier assessment."
  - "orchestrator/decision_log.jsonl — attempted exact-continuum repair obligations, atomic rejection receipts, and terminal classification."
seeds_burned: []
proof_attempt_summary: |
  The run proved the exact finite-grid simultaneous-regret primal/dual with finite-action purification, a strict mixture-versus-pairwise orbit witness, and an evaluable continuum union-honest profile interval with constant-factor stratumwise guarantees. Two directed attempts to pass from canonical finite nets to the exact continuum minimax frontiers and sharp simultaneous excess did not produce the required liminf/limsup coverage transfer, limiting Borel-measure duality, or deterministic continuum attainment. The surviving result is sound and reusable, but the exact continuum kernel remains open and the achieved novelty tier is subfield.
token_usage:
  complete: true
  orchestrator_tokens: 154901
  pipeline_codex_tokens: 29490672
  pipeline_claude_tokens: 0
  total_tokens_consumed: 29645573
banked_on: "2026-08-29"
---

# stat_weak_factor_rank_adaptation / v2 — Downgraded

**Topic.** Union-honest rank-and-strength adaptation for a scalar missing-block functional under a public fixed four-block causal-panel mask. Define rank zero separately and exact-rank positive-strength strata. Characterize finite-sample minimax expected length on every stratum under honesty over their union. Decide whether pairwise observed-Gaussian moduli suffice or least-favorable mixtures enlarge the correct functional. Deliver an evaluable characterization and either one data-only q/h-free attaining interval or the sharp unavoidable simultaneous excess. PRESOLVE EVIDENCE REQUIRING VERIFICATION: a legal 4x4 rank-two signed-permutation mixture has no linear term in chi-square divergence despite positive component KL, and a balanced rank-one analogue suggests an n^(1/4) gap over pairwise modulus. UNRESOLVED BOTTLENECK: simultaneous mixture-test inversion. EARLY KILL TEST: certified solution of the zero-plus-64-orbit interval problem.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The exact continuum minimax frontier and sharp simultaneous excess remain unproved; the sound finite-grid duality and constant-factor continuum interval achieve subfield rather than the field floor.

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
