---
qid: stat_prte_ot_boundary_adaptation
spec: v1
topic: "Sharp limit experiment and a tail-adaptive honest-CI adaptation lower bound for the continuous-instrument optimal-transport PRTE sharp partial-identification bound endpoint, indexed by the propensity-boundary tail exponent alpha; phase transition alpha*=1 separating root-n-regular (Gaussian) from boundary-irregular (non-Gaussian) limits; deliver both the boundary-localized limit law and a two-alpha Le Cam adaptation lower bound (no honest CI adapts across the tail class). Anchor: arXiv:2604.12263 (PRTE partial ID with IV via optimal transport), whose Thm 5.11 gives only a rate for the continuous-instrument bound endpoint, no limit law or CI."
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: retry
gap_reasons:
  - 'thm:endpoint-limit-law / ass:ccot-donsker: discharge_or_rescope — "The required empirical-path rate ||hat_P_n-P||_F = O_P(rho_n(alpha)^(-1)) is exactly the bound that makes the ass:ccot-gamma-hadamard remainder negligible" (conclusion-shaped rate; the boundary-scale plug-in remainder cannot be obtained from standard sqrt(n)-Donsker + Hadamard because Gamma has a B^(-1/2) boundary singularity — the functional delta method is a regular-case tool). This is the load-bearing OPEN gap.'
  - 'Earlier rounds, same crux under different framings: estimator_side_laundering@ass:ccot-empirical-remainder (r0); headline_expansion_assumed@ass:ccot-active-face-hadamard-smoothness + estimator_rate_not_discharged@ass:ccot-empirical-process-scale (r3/r8). The pure-Hadamard reframe (r9) removed the headline laundering but the reviewer correctly re-surfaced the boundary-remainder RATE underneath.'
  - 'Cross-alpha no-honest-adaptation CONVERSE: witness_not_in_alpha1_class + lower_bound_not_discharged — proven UNATTAINABLE as stated (codex-verified arithmetic): P_1n in P_n(alpha_1) requires perturbing the operative shell [n^-1,n^-beta], costing Hellinger >= n^(-beta*alpha_0) so n*H^2 -> inf and product TV -> 1; no class-separated yet n-indistinguishable two-point pair exists. Dropped from the kernel and recorded as an OEQ.'
  - 'Residual (non-blocking) hygiene at cap: redundant_class_clauses / redundant_assumptions (minimal-depends_on vs class-membership tug-of-war), unused_parameter@def:strict-overlap-class (dummy p_so, removed).'
reusable_artifacts:
  - 'discovery/core.json + writeup.tex — the POSITIVE kernel is sound and consistent (dangling-citation-clean): prop:phase-normalization, thm:local-experiment (boundary process limit), prop:boundary-nonuniformity (corrected to the u_0->0 claim), thm:endpoint-limit-law (alpha-indexed endpoint decomposition, alpha>=1 unconditional / alpha<1 conditional on projection nondegeneracy), prop:strict-overlap-reduction, oeq:boundary-honest-ci (conditional fixed-alpha CI). Lift these; only the boundary-remainder discharge is open.'
  - 'discovery/d0_escalation_log.jsonl (rounds 2-10) — the full construction + de-laundering directive trail, incl. the refuted two-point converse arithmetic and the pure-Hadamard von-Mises framing (via functional delta method, vanderVaart1998).'
  - 'OEQs to re-raise from: (1) OT-functional differentiability / boundary-remainder rate for the CCOT endpoint plug-in (the blocker; a research problem of its own); (2) cross-alpha honest-adaptation lower bound under MODIFIED classes that separate the membership shells from the testing-separation scale; (3) primitive construction of the fixed-alpha CI calibrator.'
seeds_burned: []
proof_attempt_summary: |
  Ten D0 solve/D0.5 rounds. The POSITIVE kernel is sound and field-novel (rubric PASSED throughout): a new alpha-indexed continuous-instrument OT-boundary PRTE endpoint limit law with an alpha*=1 phase transition (the anchor arXiv:2604.12263 gave only a rate). The cross-alpha adaptation CONVERSE was honestly REFUTED as provably unattainable under the class definitions (dropped -> OEQ). The single load-bearing blocker is the boundary-scale plug-in REMAINDER rate: because the OT endpoint functional is boundary-singular (B^(-1/2)), the remainder cannot be controlled by standard Hadamard+Donsker regularity, and every framing that supplied the needed rate was correctly flagged as conclusion-shaped laundering. Rigorously closing it needs OT-functional differentiability / boundary-remainder theory that does not exist off-the-shelf, OR an explicitly conditional (rescoped) theorem. Reraisable (retry) once that substrate exists. Two durable pipeline fixes were produced this run: a D0 post-render dangling-citation consistency gate (stage0_typed.ts) and a cross-target-shared-helper emit rule in the D0 solve prompt.
banked_on: "2026-07-01"
---

# stat_prte_ot_boundary_adaptation / v1 — Failed

**Topic.** Sharp limit experiment and a tail-adaptive honest-CI adaptation lower bound for the continuous-instrument optimal-transport PRTE sharp partial-identification bound endpoint, indexed by the propensity-boundary tail exponent alpha; phase transition alpha*=1 separating root-n-regular (Gaussian) from boundary-irregular (non-Gaussian) limits; deliver both the boundary-localized limit law and a two-alpha Le Cam adaptation lower bound (no honest CI adapts across the tail class). Anchor: arXiv:2604.12263 (PRTE partial ID with IV via optimal transport), whose Thm 5.11 gives only a rate for the continuous-instrument bound endpoint, no limit law or CI.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** D0.5 revise-cap exhausted (rubric PASS=field-novel; math NO-PASS). Sound, novel alpha-indexed OT-boundary continuous-instrument PRTE endpoint limit law + alpha*=1 phase transition; the ONE genuine open gap is the boundary-scale plug-in remainder rate (discharge_or_rescope@ass:ccot-donsker) — the OT endpoint's boundary-singular remainder needs OT-functional differentiability theory beyond standard Hadamard+Donsker (a research problem of its own). Cross-alpha adaptation converse honestly refuted (proven unattainable under the class defs) -> OEQ. Reraisable when the OT-differentiability substrate exists.

## Key files

- `stat_prte_ot_boundary_adaptation_v1_state.json` — pipeline state at banking (`banked: true`).
- `stat_prte_ot_boundary_adaptation_v1_proposal.tex` — final proposal version.
- `stat_prte_ot_boundary_adaptation_v1.tex` — derivation note (if Stage 0 ran).
- `stat_prte_ot_boundary_adaptation_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `stat_prte_ot_boundary_adaptation_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
