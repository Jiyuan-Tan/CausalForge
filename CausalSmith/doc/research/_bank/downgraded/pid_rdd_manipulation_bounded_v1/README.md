---
qid: pid_rdd_manipulation_bounded
spec: v1
topic: "Sharp partial identification of the local average treatment effect at a regression-discontinuity cutoff when the running variable is subject to bounded manipulation, with the manipulation magnitude bounded by a McCrary-style density-discontinuity envelope and a covariate-conditional manipulation-share bound, recovering Lee 2008 sharp RD point identification at the trivial bound and characterizing the tightest sharp interval as a function of the discontinuity-magnitude and covariate-share parameters"
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
  - "the current derivation is at most subfield: contaminated-distribution trimming plus finite-dimensional linear-fractional/KKT geometry under externally imposed caps. Since the required accept floor is field, the note must be revised rather than accepted."
  - "is essentially a mixture/Radon-Nikodym reparameterization of the maintained model, so by itself it appears subfield rather than field tier"
  - "The cap-envelope separation result cannot carry field-level novelty because the strict separation is assumed rather than derived (Assumption 10 contained the strict gap the proposition concluded — outright circularity)."
  - "the genuinely new economics/econometrics content would have to come from deriving a nontrivial new feasible set or proving that cell caps strictly sharpen the GRR-style envelope on a generic class."
  - "RETIER 2026-07-18: round 2 de-tautologized Assumption 10 and added one numerical witness — a CORRECTNESS repair on a single instance, not the requested generic-class result — yet novelty flipped revise -> pass and stamped tier_at_derivation: field. D-0.5 trajectory REVISE(field) -> REVISE(letter) -> REVISE(letter) -> ACCEPT(field) with no recorded content change. The 'envelope' half contributes nothing: since Gerard-Rokkanen-Rothe endpoints are monotone in the removed share, the envelope set is just the GRR bound at tau = rho-bar. Strictly weaker than its own anchor on the estimation axis, which GRR deliver."
proof_attempt_summary: |
  Attempted a sharp identified set for the RD local Wald effect under bounded one-sided
  manipulation as a fractional retention-weight program with a global mass budget, covariate-cell
  caps and a retained-W-law equality, plus a cap-envelope separation theorem. Theorem 1 is a
  contaminated-law reparameterization; Prop 2 is textbook linear-fractional geometry; Prop 3 is
  sanity faces recovering Hahn-Todd-van der Klaauw and Lee; Theorem 4 — the only tier-bearing item
  — proves that adding a constraint strictly tightens a bound on one K=2 three-atom witness
  (U=3/7 < 1/2). No endpoint estimator and no inference, the rung GRR do deliver.
banked_on: "2026-05-15"
retiered_on: 2026-07-18
retiered_from: candidates
---

# pid_rdd_manipulation_bounded / v1 — Downgraded

**Topic.** Sharp partial identification of the local average treatment effect at a regression-discontinuity cutoff when the running variable is subject to bounded manipulation, with the manipulation magnitude bounded by a McCrary-style density-discontinuity envelope and a covariate-conditional manipulation-share bound, recovering Lee 2008 sharp RD point identification at the trivial bound and characterizing the tightest sharp interval as a function of the discontinuity-magnitude and covariate-share parameters

**Novelty target.** field

**D-0.5 verdict.** ACCEPT

**D0.5 verdict.** ACCEPT

**Banking reason.** D0.5 ACCEPT at novelty_target=field; cap-envelope separation theorem for sharp budgeted conditional trimming under bounded RD manipulation; tier_at_derivation=field.

Re-tiered from `candidates` to `downgraded` on 2026-07-18. The `candidates` tier has been retired from the bank and the pipeline.

This entry was banked `field` on a D0.5 ACCEPT. An independent per-entry re-grade on 2026-07-18 assessed it **subfield**, in agreement with the objections already recorded in this entry's own review log before the accepting round reversed them (see `gap_reasons`). The math is sound; the novelty framing was too high — which is what `downgraded` means. `reraise_status: re-raise`: do not treat this direction as refuted. Re-anchor at the corrected tier, or pivot to the adjacent hard kernel recorded under **Re-anchor path** below.


## Re-anchor path (recorded before the seed burn)

Either (a) a general-class theorem that cell caps strictly sharpen the GRR envelope on an
open/generic set of designs, with the capped endpoint characterized in closed form or by a
certified algorithm as a function of (rho-bar, s-bar); or (b) the missing #9 rung — a consistent
endpoint estimator with valid inference over the budgeted-trimming identified set. Both are new
kernels needing their own gate round.

## Key files

- `pid_rdd_manipulation_bounded_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_rdd_manipulation_bounded_v1_proposal.tex` — final proposal version.
- `pid_rdd_manipulation_bounded_v1.tex` — derivation note (if D0 ran).
- `pid_rdd_manipulation_bounded_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `pid_rdd_manipulation_bounded_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
