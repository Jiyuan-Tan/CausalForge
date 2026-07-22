---
qid: pid_alwaystaker_adrf_sharp_conditional
spec: frechet_fractional_program
topic: "Sharp covariate-conditional identified set for the always-takers average dose-response function under a sufficient-set sample-selection restriction with continuous treatment (Lee–Liu 2025, the deferred sharp case): characterize it as the value of a global support-function / linear-fractional program over feasible conditional always-takers proportions π_AT(X), coupled across X by the shared denominator E[π_AT(X)] and solved via a scalar Dinkelbach/KKT threshold; with a primitive-verifiable condition C under which the pointwise-Fréchet plug-in is exactly sharp; plus a doubly-robust kernel-localized estimator of the endpoints and inference over the identified set"
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  # The math is SOUND (novelty/decision referee = PASS, field). No conjecture collapsed.
  # NO-PASS cause = the strict reproduce-don't-check math referee never returned a clean
  # 0-finding round; it kept surfacing ever-deeper rigor sub-steps on the (intricate)
  # constructions plus dependency-declaration hygiene. Final open findings at banking:
  - "hidden_measurability@lem:measurable-completion-kernel — measurable-kernel step asserted, needs explicit joint-Borel weight-map + regular-conditional-distribution measurability"
  - "missing_domination@lem:uniform-transform-ulln — uniform LLN needs an explicit integrable dominating envelope (added ass:local-density-lower-bound in the last directive; solver had not yet emitted it)"
  - "hidden_assumption@thm:global-support-function, hidden_assumption@thm:pointwise-plugin-sharpness, hidden_dependency@prop:sufficient-value-reduction — used-but-undeclared depends_on edges (pure graph hygiene)"
  # RESOLVED earlier (do NOT re-open — the root-gap fix closed these): attainment_gap /
  # band_converse_not_discharged / missing_latent_attainment (sharpness), and
  # global_ulln_laundered / missing_local_density_control / process_assumption_laundered
  # (estimator). Also resolved: the estimator-side laundering (feasible DR limit law) by
  # scoping the rung to plug-in consistency + a from-primitives uniform LLN.
reusable_artifacts:
  - "discovery/writeup.tex + discovery/core.json — full sound field-tier note (sharp set + condition C + consistency estimator)"
  - "lem:measurable-completion-kernel — measurable Frechet always-taker completion via extremal coupling + Ionescu-Tulcea/disintegration (Kallenberg); reusable for any sample-selection sharp-attainment proof"
  - "lem:conditional-trimming-fiber-attainment + lem:latent-completion-pasting — the sharp ⊇ attainment construction"
  - "lem:uniform-transform-ulln + lem:bounded-bernstein-grid-bound — Bernstein+grid uniform LLN for a kernel-localized transform with density-lower-bound"
seeds_burned: []
proof_attempt_summary: |
  Field-tier sharp partial-ID of the always-takers ADRF (Lee-Liu 2025 deferred covariate case): sharp
  support-function/Dinkelbach identified set + iff pointwise-plugin sharpness condition C + plug-in
  consistency estimator, all proven; novelty PASS. The two genuine root gaps — measurable Frechet
  completion (attainment ⊇) and the ULLN's local-density domination — were the real recurring blockers
  and were CLOSED (Ionescu-Tulcea measurable completion; Bernstein+grid ULLN with f_d≥c_f). Banked NO-PASS
  only because the strict reproduce-don't-check D0.5 referee kept surfacing deeper measurability/domination
  sub-steps + declaration hygiene on the intricate constructions; not a kernel failure — re-raise by
  finishing those construction sub-steps (or route straight to F1-F5, where Lean settles the rigor).
banked_on: "2026-07-01"
---

# pid_alwaystaker_adrf_sharp_conditional / frechet_fractional_program — Failed

**Topic.** Sharp covariate-conditional identified set for the always-takers average dose-response function under a sufficient-set sample-selection restriction with continuous treatment (Lee–Liu 2025, the deferred sharp case): characterize it as the value of a global support-function / linear-fractional program over feasible conditional always-takers proportions π_AT(X), coupled across X by the shared denominator E[π_AT(X)] and solved via a scalar Dinkelbach/KKT threshold; with a primitive-verifiable condition C under which the pointwise-Fréchet plug-in is exactly sharp; plus a doubly-robust kernel-localized estimator of the endpoints and inference over the identified set

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** D0.5 revise-exhausted NO-PASS, but MATH IS SOUND field-tier (novelty referee passed): sharp covariate-conditional identified set for the always-takers ADRF as a support-function/Dinkelbach program + iff pointwise-plugin sharpness condition C + plug-in consistency estimator; the two real root gaps (measurable Frechet completion via Ionescu-Tulcea; ULLN density-lower-bound domination) were genuinely closed; parked at the D0.5 deep-construction-rigor boundary (residual measurability/domination sub-steps + dependency hygiene the strict referee keeps probing). Re-raisable: not a kernel failure.

## Key files

- `pid_alwaystaker_adrf_sharp_conditional_frechet_fractional_program_state.json` — pipeline state at banking (`banked: true`).
- `pid_alwaystaker_adrf_sharp_conditional_frechet_fractional_program_proposal.tex` — final proposal version.
- `pid_alwaystaker_adrf_sharp_conditional_frechet_fractional_program.tex` — derivation note (if Stage 0 ran).
- `pid_alwaystaker_adrf_sharp_conditional_frechet_fractional_program_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_alwaystaker_adrf_sharp_conditional_frechet_fractional_program_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
