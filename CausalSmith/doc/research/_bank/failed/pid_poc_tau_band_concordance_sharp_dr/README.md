---
qid: pid_poc_tau_band
spec: concordance_sharp_dr
topic: "family-free sharp identified set for probabilities of causation with continuous outcomes under a Kendall-tau band on potential-outcome dependence: characterize the sharp general-probability-of-necessity (GPN) set by DIRECT pointwise optimization of the copula value C(u1,u0) over all copulas whose Kendall's tau lies in a given band, using the closed-form Nelsen tau-constrained pointwise copula bounds; pair it with a doubly-robust efficient-influence-function estimator of the set endpoints and interval inference over the tau-indexed identified set. Differs from the one-parameter Gaussian-copula rho-interval of Chaoge-Han-Liu-Wu (arXiv:2605.01883) by being family-free and carrying the estimation/inference rung the anchor lacks"
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "constructive_object_missing"
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - "Final D0.5 review stayed non-convergent after D0.R: band_envelope_smoothness_not_discharged@lem:tau-band-piecewise-smooth, band_envelope_branch_glue_unproved@lem:tau-band-piecewise-smooth, and the EIF/CLT results inherited that undischarged band smoothness."
  - "The proof switched estimator objects in thm:regular-one-step-clt and used an unstated upstream expansion in lem:score-consistency, so the cross-fitted one-step CLT was not discharged from the declared primitive nuisance and sampling assumptions."
  - "Earlier D0.5 rounds repeatedly flagged the sharpness bridge for the Kendall-tau band: citation_overreach_tau_band_interval@lem:tau-copula-attainment and missing interval-band/measurable-selector attainment for the exact sharp GPN interval."
  - "The estimator/inference layer required new off-piece score and remainder control plus operational clipping/positivity structure; those were new mathematical or definition-level ingredients, not in-place D0.R edits."
reusable_artifacts:
  - "discovery/core.json - final typed D0 core with the attempted Kendall-tau-band GPN sharpness, regular-piece endpoint EIF, and one-step CLT DAG."
  - "discovery/proto_core.json and proto_core.json.bak_* - frozen proposal skeleton plus the sequence of narrowing/repair attempts around band attainment, off-piece control, and foldwise rates."
  - "discovery/solve_thm_sharp_tau_band_gpn.json, solve_thm_population_endpoint_eif.json, solve_thm_regular_one_step_clt.json - solver traces for the three main result nodes."
  - "discovery/d0_escalation_log.jsonl and pipeline.jsonl - escalation trail showing which D0.5 findings survived in-place repair attempts."
seeds_burned: []
proof_attempt_summary: |
  The run tried to turn family-free Kendall-tau pointwise copula envelopes into a sharp continuous-GPN partial-ID theorem, then add regular-piece EIF and cross-fitted one-step endpoint inference. The proposal cleared Stage -0.5 at field tier, but D0.5 repeatedly found missing load-bearing mathematics: interval-band copula attainment/measurable selection, band-envelope smoothness, off-piece score and remainder control, and an estimator object mismatch in the one-step CLT. A retry should preserve the literature map and solver traces but first supply a real tau-band attainment theorem and a primitive estimator/inference construction, rather than reusing the current sharpness and CLT claims unchanged.
banked_on: "2026-06-30"
---

# pid_poc_tau_band / concordance_sharp_dr — Failed

**Topic.** family-free sharp identified set for probabilities of causation with continuous outcomes under a Kendall-tau band on potential-outcome dependence: characterize the sharp general-probability-of-necessity (GPN) set by DIRECT pointwise optimization of the copula value C(u1,u0) over all copulas whose Kendall's tau lies in a given band, using the closed-form Nelsen tau-constrained pointwise copula bounds; pair it with a doubly-robust efficient-influence-function estimator of the set endpoints and interval inference over the tau-indexed identified set. Differs from the one-parameter Gaussian-copula rho-interval of Chaoge-Han-Liu-Wu (arXiv:2605.01883) by being family-free and carrying the estimation/inference rung the anchor lacks

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** D0.5 repeatedly failed on load-bearing tau-band sharpness, endpoint regularity, and one-step CLT gaps; the last review still required new math beyond an in-place D0.R edit.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note from Stage 0.
- `reviews.jsonl` — Stage -0.5 reviewer log.
- `pipeline.jsonl` — D0/D0.5 checkpoint and escalation log.
- `reviews/` — per-version proposal reviewer JSON files.

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
