---
qid: pid_policy_regret_ch_sensitivity
spec: v1
topic: "Sharp closed-form minimax-regret optimal policy and matching regret bound for offline policy learning under unmeasured confounding bounded by a Cinelli-Hazlett (2020) R-squared-sensitivity parameter: explicit Tikhonov-regularized inverse-propensity policy formula whose regret-bound dependence on the sensitivity parameter recovers Kallus-Zhou (2021) marginal-sensitivity-model bounds as the parameter goes to infinity and Adjaho-Christensen (2023) covariate-shift policy-evaluation bounds as the parameter goes to zero, with a sharpness witness via two boundary R-squared environments saturating the regret bound; extends Cinelli-Hazlett (2020, Section 7) sensitivity analysis from point-estimated effects to sharp policy-regret theory, the directly cited open direction in their conclusion"
novelty_target: flagship
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  # Stage 0.5 REJECT classification = novelty (NOT correctness); correctness
  # and structure both PASS in both attempts. Verbatim/near-verbatim reviewer lines:
  - "The derived kernel is an elementary support-function calculation plus a finite positive-rank-one matrix criterion for scalar calibration; it does not meet the orchestrator-enforced flagship floor and does not establish a regime-opening sharp bound, published-estimator equivalence frontier, strict extension of prior literature, or generic-class obstruction."
  - "Theorem 1 / Theorem 2: The support-function bounds and all-pairs scalar-calibration frontier are finite-dimensional convex-duality and rank-one algebra once the local ambiguity sets are assumed."
  - "Related work and positioning: it does not identify a prior open problem or named published estimator frontier that this theorem newly resolves."
  - "Negative-result component: The refutation of Conjecture 2 corrects an open-set wording error and gives a finite witness, but it is not promoted to a generic-class obstruction and therefore cannot support flagship tier."
  - "Assessed tier_at_derivation is subfield, strictly below novelty_target=flagship, so the artifact cannot be accepted under the floor directive."
  - "the current derivation is a sound subfield-level support-function calibration lemma, not a flagship derivation." (correctness PASS, structure PASS in both stage_0.5 attempts)
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  Three proposal angles were drafted; angles 1 and 2 reached Stage -0.5 ACCEPT at
  flagship tier, but both were REJECTED at Stage 0.5 on the novelty floor (NOT
  correctness — structure and correctness PASS in every reviewed attempt). The
  derived kernel reduces to standard support-function evaluations (L2 / mean-zero
  L-infinity / covariate-only-tilt balls) plus a positive-rank-one finite-matrix
  scalar-calibration criterion: mathematically coherent and sound, but assessed
  tier_at_derivation = subfield, strictly below the flagship target. Nothing
  collapsed mathematically; the conjecture genuinely sits below flagship and
  cannot reach it by re-derivation, so the pipeline pivoted (re_derive route to
  Stage -1) rather than burning further Stage 0 attempts.
banked_on: "2026-05-20"
---

# pid_policy_regret_ch_sensitivity / v1 — Downgraded

**Topic.** Sharp closed-form minimax-regret optimal policy and matching regret bound for offline policy learning under unmeasured confounding bounded by a Cinelli-Hazlett (2020) R-squared-sensitivity parameter: explicit Tikhonov-regularized inverse-propensity policy formula whose regret-bound dependence on the sensitivity parameter recovers Kallus-Zhou (2021) marginal-sensitivity-model bounds as the parameter goes to infinity and Adjaho-Christensen (2023) covariate-shift policy-evaluation bounds as the parameter goes to zero, with a sharpness witness via two boundary R-squared environments saturating the regret bound; extends Cinelli-Hazlett (2020, Section 7) sensitivity analysis from point-estimated effects to sharp policy-regret theory, the directly cited open direction in their conclusion

**Novelty target.** flagship

**D-0.5 verdict.** ACCEPT

**D0.5 verdict.** REJECT

**Banking reason.** Both productive angles ACCEPT -0.5 flagship, both REJECT 0.5 with proposal_promise_gap=tier_genuinely_below: sensitivity-analysis algebra has subfield-tier substance even when derived faithfully.

## Key files

- `pid_policy_regret_ch_sensitivity_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_policy_regret_ch_sensitivity_v1_proposal.tex` — final proposal version.
- `pid_policy_regret_ch_sensitivity_v1.tex` — derivation note (if D0 ran).
- `pid_policy_regret_ch_sensitivity_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `pid_policy_regret_ch_sensitivity_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
