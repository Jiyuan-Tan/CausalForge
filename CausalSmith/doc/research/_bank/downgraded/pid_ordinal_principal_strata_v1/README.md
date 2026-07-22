---
qid: pid_ordinal_principal_strata
spec: v1
topic: "Sharp partial identification of principal-stratum-specific average causal effects when the post-treatment intermediate variable is ordinal with K>=3 levels and the principal ignorability assumption is relaxed to a bounded covariate-conditional principal-score divergence between adjacent stratum pairs, recovering Frangakis-Rubin point identification under principal ignorability and the binary case at the trivial bound"
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
  - "the theorem-level novelty is still under-argued relative to the field target: sharpness of a finite posterior-weight LP is largely a generic disintegration/LP result once the adjacent posterior-divergence model is assumed, and the literature review is thinner than the Stage -1 proposal because it omits several ordinal/nonbinary principal-stratification comparators. Assessed tier would be subfield unless the note better establishes that the adjacent-chain posterior-divergence model and compatibility theorem open a genuinely new field-level regime."
  - "the proof does not fully construct a complete finite-support law showing strict containment of the whole effect interval as stated."
  - "RETIER 2026-07-18: attempt 2 flipped to accept@field nine minutes later; the revision added three missing comparators and fixed a LaTeX environment — i.e. it discharged the COLLISION complaint while never rebutting the 'generic disintegration/LP result' diagnosis and naming no new regime. The reviewer conflated 'no prior-art collision' with 'field tier'. Principal scores are ASSUMED KNOWN (the 'nuisances assumed known' failure mode), and there is no estimation rung at all."
proof_attempt_summary: |
  Attempted a sharp finite-support adjacent-chain posterior LP for ordinal principal strata under a
  Rosenbaum-style Gamma bound on adjacent latent posterior weights, with a nonrectangular
  compatibility gap witnessed at K=3, Gamma=2 (7/15 vs 5/9). The gap theorem is genuine and
  checkable — just not field-tier: Theorem 1 is Bayes disintegration plus a compact convex LP once
  the sensitivity model is written down, and Theorem 2 is the expected monotone direction proved at
  one numeric instance rather than a facet characterization. Improves no published bound, rate, or
  order. Substantially the same template as pid_ordinal_late_partial_defiers_v1.
banked_on: "2026-05-15"
retiered_on: 2026-07-18
retiered_from: candidates
---

# pid_ordinal_principal_strata / v1 — Downgraded

**Topic.** Sharp partial identification of principal-stratum-specific average causal effects when the post-treatment intermediate variable is ordinal with K>=3 levels and the principal ignorability assumption is relaxed to a bounded covariate-conditional principal-score divergence between adjacent stratum pairs, recovering Frangakis-Rubin point identification under principal ignorability and the binary case at the trivial bound

**Novelty target.** field

**D-0.5 verdict.** ACCEPT

**D0.5 verdict.** ACCEPT

**Banking reason.** D0.5 ACCEPT at novelty_target=field; sharp finite-support adjacent-chain posterior LP with nonrectangular ordinal compatibility gap for ordinal principal strata under bounded covariate-conditional principal-score divergence; tier_at_derivation=field.

Re-tiered from `candidates` to `downgraded` on 2026-07-18. The `candidates` tier has been retired from the bank and the pipeline.

This entry was banked `field` on a D0.5 ACCEPT. An independent per-entry re-grade on 2026-07-18 assessed it **subfield**, in agreement with the objections already recorded in this entry's own review log before the accepting round reversed them (see `gap_reasons`). The math is sound; the novelty framing was too high — which is what `downgraded` means. `reraise_status: re-raise`: do not treat this direction as refuted. Re-anchor at the corrected tier, or pivot to the adjacent hard kernel recorded under **Re-anchor path** below.


## Re-anchor path (recorded before the seed burn)

Endpoint estimation and inference over the identified set with ESTIMATED principal scores (the
omitted #9 rung), or a facet characterization of when and by how much the ordinal polytope
strictly beats edgewise pasting rather than a single witness. New candidate, own gate.

## Key files

- `pid_ordinal_principal_strata_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_ordinal_principal_strata_v1_proposal.tex` — final proposal version.
- `pid_ordinal_principal_strata_v1.tex` — derivation note (if D0 ran).
- `pid_ordinal_principal_strata_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `pid_ordinal_principal_strata_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
