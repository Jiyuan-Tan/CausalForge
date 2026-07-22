---
qid: stat_dose_response_minimax
spec: holder_anisotropic_converse
topic: "Minimax lower bound for the interior continuous-treatment dose-response curve E[mu(t,X)] under anisotropic Holder smoothness (treatment-direction alpha, treatment-density beta, covariate-direction s), matching the published HOIF upper rate of Bonvini-Kennedy (arXiv:2207.11825); distinguished from incremental-effect/edge-dose continuous-exposure minimax bounds."
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: unknown
gap_reasons:
  - "None: the certified partial theorem passed F2.5 and dual-model F4. The unrestricted same-class beta-sensitive upper frontier is deliberately preserved as an open handle, not counted as delivered content."
reusable_artifacts:
  - "Causalean/Stat/Minimax/BretagnolleHuber.lean — bretagnolle_huber_affinity, already promoted."
  - "CausalSmith/Stat/STAT_DoseResponseMinimax_Research/Helpers/Witness/ — genuine two-point continuous-dose witness with the regression, X-density, and treatment-density semantic ties proved."
  - "CausalSmith/Stat/STAT_DoseResponseMinimax_Research/Helpers/RateAlgebra.lean — smooth/deficient rho_n exponent identities."
  - "CausalSmith/Stat/STAT_DoseResponseMinimax_Research/Helpers/UpperBoundCited.lean — source-attested, estimator-specific Bonvini–Kennedy conditional comparator; not a same-class minimax upper theorem."
seeds_burned: []
proof_attempt_summary: |
  Certified the all-beta minimax MSE lower floor n^(-2 alpha/(2 alpha+1)) under
  baseline-submodel slack and assembled its comparison with the published rho_n
  exponent in both covariate-smoothness regimes. The proof is sorry-free and
  axiom-clean; the deficient-regime same-class upper frontier remains open.
banked_on: "2026-07-13"
paper_score: 4
paper_score_rationale: "The verified result is a correct but narrow one-sided lower bound, while the paper’s terminology and positioning still invite a stronger minimax/frontier interpretation than the results deliver."
---

# stat_dose_response_minimax / holder_anisotropic_converse — Accepted

**Topic.** Minimax lower bound for the interior continuous-treatment dose-response curve E[mu(t,X)] under anisotropic Holder smoothness (treatment-direction alpha, treatment-density beta, covariate-direction s), matching the published HOIF upper rate of Bonvini-Kennedy (arXiv:2207.11825); distinguished from incremental-effect/edge-dose continuous-exposure minimax bounds.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** F5 clean: certified all-beta lower-floor theorem and regime comparison passed genuine F2.5/F4 review; unrestricted same-class upper frontier remains open.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/writeup.tex` and `discovery/core.json` — corrected derivation note and typed source of truth.
- `formalization/formalization.md` and `formalization/plan.json` — synchronized bridge note and formalization plan.
- `graph.json` — final matched proof/review graph, including the open beta-frontier handle.
- `pipeline.jsonl` and `orchestrator/decision_log.jsonl` — F2.5–F5 convergence and orchestration receipts.

## Notes

The banked theorem is conditional on `BaselineSubmodelSlack` and standing regime
conditions; “axiom-clean” does not mean assumption-free. The semantic ties
`mu-is-regression`, `px-is-x-density`, and `pi-is-cond-treatment-density` are
faithful to the original note's definitions. `beta-dominates-alpha` is explicitly
non-load-bearing for the certified partial theorem, which holds for every fixed
`beta > 0`.
