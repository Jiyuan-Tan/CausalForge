---
qid: eid_proximal_completeness
spec: v1
topic: "Sharp critical-completeness threshold for proximal identification of long-term ATE via outcome-bridge functions when the completeness condition on negative-control proxies approaches violation"
novelty_target: flagship
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: "assumption_omitted"
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - 'Theorem 1: already-known — ''eid_proximal_phase_v1: finite null-annihilator / row-space criterion for proximal ATE invariance over nonunique bridge fibers'' and ''ZhangLiMiaoTchetgen2023: proximal counterfactual means / ATE can be identified without unique bridge functions under additional regularity'''
  - 'Conjecture 1: C-wellposed — ''The target is the causal ATE E[Y(1)-Y(0)], but §2/§7 state proxy exclusions and bridge existence without explicitly stating latent exchangeability / no unmeasured confounding beyond U, so λ''β is not yet well-posed as the causal ATE.'''
  - 'Conjecture 2: C-wellposed — ''Make Conjecture 2 explicitly say whether the residual-projection set targets the causal ATE or only the finite bridge functional when the row-space condition approaches failure.'''
  - 'Banked reason: ''the named focal scalar (critical completeness) is an operator-theoretic limit (minimum singular value of an unobserved integral operator), not evaluable in observed-data primitives — recurring C-flag on usability/evaluability of the threshold. Anti-pattern: Computable map absent satisfied in name but not in evaluability.'''
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  The proposal conjectured a three-region weak-proxy phase diagram for proximal ATE inference indexed by the target-relevant Riesz-certificate scalar rho_n(P). Conjectures 1 and 2 survived all 25 novelty rounds as genuinely new on both repo and published axes; Theorem 1 was correctly demoted to incremental scaffolding. The run exhausted the revision cap on a single recurring C-wellposed flag: latent proximal exchangeability (the assumption linking the finite-sieve functional lambda'*beta to the causal ATE E[Y(1)-Y(0)]) was never added to Assumptions 1-5, and the banked reason further notes that rho_n depends on the minimum singular value of an unobserved operator, leaving the focal scalar not evaluable in observed-data primitives.
banked_on: "2026-05-22"
---

# eid_proximal_completeness / v1 — Failed

**Topic.** Sharp critical-completeness threshold for proximal identification of long-term ATE via outcome-bridge functions when the completeness condition on negative-control proxies approaches violation

**Novelty target.** flagship

**Stage -0.5 verdict.** NO-PASS

**Stage 0.5 verdict.** NA

**Banking reason.** Stage -1.2 NO-PASS @ flagship (D-1.2 effort=high). 25 reviewer rounds across 4 angles; final angle=4 v5 REVISE@flagship S=0 N=0 C=1. Never advanced past D-0.5. Topic reached flagship shape but the named focal scalar (critical completeness) is an operator-theoretic limit (minimum singular value of an unobserved integral operator), not evaluable in observed-data primitives — recurring C-flag on usability/evaluability of the threshold. Anti-pattern: 'Computable map absent' satisfied in name but not in evaluability. High-effort drafter could not rescue an operator-spectrum focal object.

## Key files

- `eid_proximal_completeness_v1_state.json` — pipeline state at banking (`banked: true`).
- `eid_proximal_completeness_v1_proposal.tex` — final proposal version.
- `eid_proximal_completeness_v1.tex` — derivation note (if Stage 0 ran).
- `eid_proximal_completeness_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `eid_proximal_completeness_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
