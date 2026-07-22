---
qid: pid_did_anticipation_bounded
spec: v1
topic: "Sharp partial identification of the cohort-by-period average treatment effect on the treated under staggered adoption when the no-anticipation assumption is relaxed to bounded anticipation k periods before adoption with a covariate-conditional anticipation magnitude bound, recovering Callaway-Sant'Anna and de Chaisemartin-D'Haultfoeuille at the trivial bound"
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
  - "because sharpness relies on a labelled variation-independence assumption, the derivation is field-tier rather than flagship"
  - "though its central sharpness step is assumed through a variation-independent box condition"
  - "Promote the variation-independent anticipation-box condition from a scope assumption into an explicit compatibility lemma or example family, so sharpness is not perceived as assumed by definition (named repair, effort: medium — NEVER APPLIED; Assumption 5 entered the proof unchanged)."
  - "D-0.5 per-theorem grades on the published axis: Theorem 1 incremental, Theorem 2 already-known."
  - "RETIER 2026-07-18: the sharpness proof is circular — Assumption 5 states that every array in the box is compatible with a P-preserving PO law, which is exactly what the theorem concludes. Residue is the Rambachan-Roth support-function template with the latent vector relabelled from trend violations to anticipation distortions, keeping RR's easy half (support-function ID) and dropping RR's hard half (fixed-length CIs, conditional least-favorable inference)."
proof_attempt_summary: |
  Attempted a sharp identified interval for staggered-DID group-time ATT under bounded
  anticipation, decomposing ATT(g,t|x) into an observed contrast plus a signed linear functional
  of latent anticipation distortions from both the treated cohort's base period and not-yet-treated
  comparison cohorts. The decomposition algebra and the support-function endpoint are correct but
  routine; the sharpness step is assumed rather than proved (variation-independent box), so the
  load-bearing construction — PO laws realizing arbitrary anticipation arrays at fixed P and
  baseline parallel trends — was never built. No inference rung; HonestDiD already ships the
  bounded-violation sensitivity machinery.
banked_on: "2026-05-15"
retiered_on: 2026-07-18
retiered_from: candidates
---

# pid_did_anticipation_bounded / v1 — Downgraded

**Topic.** Sharp partial identification of the cohort-by-period average treatment effect on the treated under staggered adoption when the no-anticipation assumption is relaxed to bounded anticipation k periods before adoption with a covariate-conditional anticipation magnitude bound, recovering Callaway-Sant'Anna and de Chaisemartin-D'Haultfoeuille at the trivial bound

**Novelty target.** field

**D-0.5 verdict.** ACCEPT

**D0.5 verdict.** ACCEPT

**Banking reason.** D0.5 ACCEPT at novelty_target=field; sharp bounded-anticipation ATT support interval under labelled variation-independent box assumption; tier_at_derivation=field.

Re-tiered from `candidates` to `downgraded` on 2026-07-18. The `candidates` tier has been retired from the bank and the pipeline.

This entry was banked `field` on a D0.5 ACCEPT. An independent per-entry re-grade on 2026-07-18 assessed it **subfield**, in agreement with the objections already recorded in this entry's own review log before the accepting round reversed them (see `gap_reasons`). The math is sound; the novelty framing was too high — which is what `downgraded` means. `reraise_status: re-raise`: do not treat this direction as refuted. Re-anchor at the corrected tier, or pivot to the adjacent hard kernel recorded under **Re-anchor path** below.


## Re-anchor path (recorded before the seed burn)

Characterize WHEN variation-independence fails in staggered designs — which risk-set / horizon
configurations couple anticipation coordinates and make the box bound strictly conservative —
together with the sharp bound on the coupled set. A different kernel with its own gate budget,
not a repair of this one (the reviewer's named compatibility-lemma repair was scoped
'effort: medium', i.e. not field-tier).

## Key files

- `pid_did_anticipation_bounded_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_did_anticipation_bounded_v1_proposal.tex` — final proposal version.
- `pid_did_anticipation_bounded_v1.tex` — derivation note (if D0 ran).
- `pid_did_anticipation_bounded_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `pid_did_anticipation_bounded_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
