---
qid: pid_dose_response_iv
spec: v1
topic: "Sharp partial identification of marginal dose-response derivatives under bounded unmeasured confounding via a continuous instrumental variable with quantile-copula restrictions on potential-outcome dependence"
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: ACCEPT
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
banked_novelty_tier: subfield
proposal_promise_gap: "tier_genuinely_below"
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The actually derived kernel is below novelty_target=field: the LP sharpness result is mostly the standard finite-polytope projection argument, and the sign result is an existential two-bin witness whose key margins and perturbation persistence are assumed rather than derived. Assessed tier would be subfield/incremental unless strengthened into a genuinely new sharp/tighter bound or regime-opening theorem."
  - "To satisfy the field-tier floor, the main theorem should also be framed as a genuinely new sharp/tighter bound or regime-opening copula-tube result, not just the standard LP representation plus a saturated two-bin illustration."
  - "D-0.5 angle reviews repeatedly graded Theorem 1 and Theorem 2 incremental on the published axis."
  - "RETIER 2026-07-18: round 1 graded subfield/incremental with a named structural repair; round 2 flipped to field on CORRECTNESS repairs only (circularity removed, exact rho*=1/8 computed) without touching the novelty objection. Decisively, the witness carrying the whole novelty claim sets Gamma=1, eta=0 and degenerate X — the continuous IV, the marginal sensitivity model, and the moment tolerance (the three advertised contributions) are all inert in the theorem that carries the novelty."
proof_attempt_summary: |
  Attempted a sharp finite LP envelope for an adjacent-rank dose-response slope under continuous
  IV with a sup-norm quantile-copula tube around comonotonicity. Proposition 1 (finite LP
  sharpness) is self-labelled routine; Proposition 2 — the substantive half — is a single
  hand-computed existential witness at t=3/4, Q0(u)=u/2, Q1(v)=v with the sensitivity apparatus
  switched off. Sharp lower bound 7/8 - 4rho + 4rho^2 and sign threshold rho* = 1/8 are correct
  but instance-specific. No endpoint estimator and no inference over the identified set anywhere,
  including in the formalization checklist.
banked_on: "2026-05-14"
retiered_on: 2026-07-18
retiered_from: candidates
---

# pid_dose_response_iv / v1 — Downgraded

**Topic.** Sharp partial identification of marginal dose-response derivatives under bounded unmeasured confounding via a continuous instrumental variable with quantile-copula restrictions on potential-outcome dependence

**Novelty target.** field

**D-0.5 verdict.** ACCEPT

**D0.5 verdict.** ACCEPT

**Banking reason.** D-0.5 ACCEPT angle 1 v5 tier=field; D0.5 ACCEPT tier=field — sharp finite LP envelope for adjacent-rank dose-response slope under continuous IV with quantile-copula tube; sign certificate via two-bin witness.

Re-tiered from `candidates` to `downgraded` on 2026-07-18. The `candidates` tier has been retired from the bank and the pipeline.

This entry was banked `field` on a D0.5 ACCEPT. An independent per-entry re-grade on 2026-07-18 assessed it **subfield**, in agreement with the objections already recorded in this entry's own review log before the accepting round reversed them (see `gap_reasons`). The math is sound; the novelty framing was too high — which is what `downgraded` means. `reraise_status: re-raise`: do not treat this direction as refuted. Re-anchor at the corrected tier, or pivot to the adjacent hard kernel recorded under **Re-anchor path** below.


## Re-anchor path (recorded before the seed burn)

Prove rho*(P,tau,Gamma) as a general functional of arbitrary margins with Gamma and eta actually
binding (not the saturated degenerate instance), plus the missing estimation rung. Unperformed
math, not a regrade.

## Key files

- `pid_dose_response_iv_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_dose_response_iv_v1_proposal.tex` — final proposal version.
- `pid_dose_response_iv_v1.tex` — derivation note (if D0 ran).
- `pid_dose_response_iv_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `pid_dose_response_iv_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
