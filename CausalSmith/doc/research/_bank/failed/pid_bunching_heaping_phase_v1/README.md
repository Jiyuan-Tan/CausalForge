---
qid: pid_bunching_heaping_phase
spec: v1
topic: "New topic: sharp partial identification for bunching designs when the running variable is observed only through deterministic rounding or heaping. Pre-anchor check: closest published anchors are Saez/Chetty/Kleven bunching estimators and recent general bunching identification/inference papers, plus heaped-running-variable measurement-error work. Our theorem is not that because the estimand here is the aliasing frontier created by the coarsening operator: construct a finite signed-nullspace witness showing two latent densities with different bunching mass but identical rounded histograms, and a phase threshold in the heap-grid width versus excluded-window geometry for when any estimator can or cannot recover the mass. If the proposal reduces to generic deconvolution, polynomial counterfactual extrapolation, ordinary Manski bounds, or LP duality without an explicit aliasing certificate, pivot or stop early."
novelty_target: relative-to-literature
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "Theorem 1 omitted the actual endpoint formula and point-identification condition, so Section 9 did not expose the computable bounding map."
  - "The sharp interval proof used convexity/polytope structure of the feasible contrast set, but the assumptions only gave compact nonemptiness."
  - "The novelty remained largely a standard finite-dimensional nullspace/linear-program reparameterization rather than a heap-specific phase threshold beyond generic nullspace annihilation."
  - "The run was launched at relative-to-literature novelty before the flagship clarification; under the intended flagship target, the D0.5 reviews clearly fell short."
reusable_artifacts:
  - "pid_bunching_heaping_phase_v1_gaps.json: literature map for bunching, rounded/heaped running variables, discrete RD, and interval/random-set partial identification anchors."
  - "pid_bunching_heaping_phase_setup.json: finite heap-incidence setup and notation for observable rounded histograms, latent fibers, continuation restrictions, and excess-mass loading."
  - "pid_bunching_heaping_phase_conj_2_fragment.tex: useful negative distinction between feasible-face rank and full-nullspace rank; salvage only as field-tier infrastructure."
  - "pid_bunching_heaping_phase_v1_reviews/stage_0.5_to_0_attempt2.json: concise diagnosis of why the D0 theorem contract and convexity assumptions failed."
seeds_burned: []
proof_attempt_summary: |
  Attempted to turn deterministic heaping in bunching designs into a sharp heap-aliasing frontier and equal-grid phase screen. The proposal found a plausible field-tier finite nullspace object, but D0 did not produce a clean theorem contract: the endpoint formula was not lifted into the theorem, convex/polyhedral feasibility was missing, and the reviewer still saw generic LP/nullspace machinery. Reuse the literature map and the feasible-face-vs-full-nullspace distinction, but do not revive this topic for flagship without a genuinely heap-geometric threshold theorem or a hand-derived certificate that is not just row-span annihilation.
banked_on: "2026-05-24"
---

# pid_bunching_heaping_phase / v1 - Failed

**Topic.** New topic: sharp partial identification for bunching designs when the running variable is observed only through deterministic rounding or heaping. Pre-anchor check: closest published anchors are Saez/Chetty/Kleven bunching estimators and recent general bunching identification/inference papers, plus heaped-running-variable measurement-error work. Our theorem is not that because the estimand here is the aliasing frontier created by the coarsening operator: construct a finite signed-nullspace witness showing two latent densities with different bunching mass but identical rounded histograms, and a phase threshold in the heap-grid width versus excluded-window geometry for when any estimator can or cannot recover the mass. If the proposal reduces to generic deconvolution, polynomial counterfactual extrapolation, ordinary Manski bounds, or LP duality without an explicit aliasing certificate, pivot or stop early.

**Novelty target.** relative-to-literature

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REVISE

**Banking reason.** Stopped after two D0.5 REVISE reviews: theorem contract still omitted endpoint formula, convex/polyhedral feasibility was missing for the sharp interval claim, and novelty remained field-tier generic LP/nullspace rather than flagship heap-grid phase structure.

## Key files

- `pid_bunching_heaping_phase_v1_state.json` - pipeline state at banking (`banked: true`).
- `pid_bunching_heaping_phase_v1_proposal.tex` - final proposal version.
- `pid_bunching_heaping_phase_v1.tex` - derivation note.
- `pid_bunching_heaping_phase_v1_reviews.jsonl` - per-round reviewer log.
- `pid_bunching_heaping_phase_v1_reviews/` - per-version reviewer JSON files.

## Notes

Reflection: this was mainly topic/proposal-strength failure, not reviewer strictness. The Stage -0.5 reviewer accepted at field tier only, and both D0.5 reviews repeated the same concern that the nonroutine object had collapsed into finite LP geometry. There was also a pipeline/tooling issue earlier in the run: the parser could not handle accepted Stage -1 theorem headers without explicit `Conjecture N` prefixes; that was fixed and regression-tested before the D0.5 reviews.
