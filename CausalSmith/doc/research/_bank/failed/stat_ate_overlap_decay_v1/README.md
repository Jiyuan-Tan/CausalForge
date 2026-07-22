---
qid: stat_ate_overlap_decay
spec: v1
topic: "Minimax estimation rate for the ATE under structure-agnostic nuisance estimation when overlap decays one-sidedly near the propensity-score boundary. Focal object: the minimax rate threshold as a joint function of the overlap-decay exponent and nuisance smoothness, characterizing the regime where one-sided overlap decay strictly changes the achievable ATE rate relative to the bounded-overlap structure-agnostic result."
novelty_target: relative-to-literature
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  # Source: review_decision.json (Stage 0.5 decision, verdict=fail) + review_general.json.
  - 'conj:minimax-frontier / headline_underdelivered + upper_rate_overclaim (decision FAIL): the headline sharp shell-sensitive weak-overlap minimax frontier is not delivered — the discharged core gives only a parametric n^(-1/2) LOWER floor (conj:tail-lower-bound) plus an estimator-side O_P(U_n(lambda)) / R_n^* achievability UPPER bound; the two match only on the sub-regime where R_n^* is already root-n, and the exact weak-overlap minimax rate elsewhere is left OPEN.'
  - 'prop:tail-order-reduction / nonuniform_comparison_gap: the claimed c_1 R_n <= U_n <= c_2 R_n "constants depending only on the class constants" are in fact law-specific (ass:tail-shell supplies shell constants existentially per law), so the class-uniform U_n ≍ R_n comparison that prop:phase-diagram and the frontier upgrade rely on is NOT established.'
  - 'thm:clipped-upper / scope_overreach_on_rate_premise + hidden_fold_structure: the clipped-score upper envelope is extended from W_n to W_n^reg via an extra pointwise premise not carried by the node, and the cross-fit proof introduces foldwise nuisance fits (hat_g_{1,m}, hat_g_{0,m}, hat_e_m) not declared by the symbols or def:crossfit-estimator.'
  - 'conj:tail-lower-bound / missing-dependency + lem:frontier-power-rate / hidden-grid-assumption (general review, revise): the parametric floor closes via lem:two-point-le-cam-in-probability and the frontier rate via the polynomial clipping grid Lambda_n, neither listed in depends_on — undeclared DAG structure. prop:comparator-separation is a surrogate: strict weak-overlap deterioration is shown for the clipped-estimator upper frontier, not for the actual minimax risk (needs a shell-matching converse).'
reusable_artifacts:
  - path: discovery/core.json
    kind: literature_map
    one_line: 'Sound one-sided weak-overlap class W_n(kappa, r_0n, r_1n, r_en) + tail-shell / right-overlap / region-compatibility assumptions and the full symbol table (tail exponent kappa, clipping threshold lambda, envelope U_n, surrogate R_n, frontier functional R_n^*) — reusable scaffolding for any weak-overlap rate run.'
  - path: discovery/core.json
    kind: operator
    one_line: 'The POSITIVE kernel that survives: thm:clipped-upper (cross-fit clipped-score UPPER envelope / estimator-side achievability), conj:tail-lower-bound (parametric n^(-1/2) floor), lem:frontier-power-rate + lem:phase-boundary-from-critical-exponent (R_n^* ~ n^(-nu) with the B=min{1/2,a_1+a_e,a_0+a_e} phase boundary), prop:strict-overlap-sanity. Lift these; only the class-uniform comparison and the shell-matching converse are open.'
  - path: discovery/writeup.tex
    kind: other
    one_line: 'Full informal derivation of the envelope/surrogate/frontier construction and the phase diagram.'
  - path: discovery/d0_escalation_log.jsonl
    kind: other
    one_line: 'D0 solve/D0.5 escalation trail — the construction history and the successive framings the reviewer flagged as scope-overreach / conclusion-shaped.'
seeds_burned: []
proof_attempt_summary: |
  Studied full-population ATE minimax estimation over one-sided weak-overlap classes (left propensity tail P(e(X) <= lambda) of order lambda^kappa, right tail regular). The positive machinery is sound and reusable: a clipped-score upper envelope U_n(lambda), its tail-order surrogate R_n, the clipping-frontier functional R_n^* with an explicit power-rate / phase-boundary characterization, an estimator-side achievability bound, and a parametric root-n lower floor. The math FAILS at the headline: the advertised sharp shell-sensitive weak-overlap minimax FRONTIER is not delivered — the class-uniform comparison U_n ≍ R_n is only per-law (not uniform over the class), so the floor-and-achievability sandwich matches exactly only on the already-root-n sub-regime and the true minimax rate off it stays OPEN; the strict-deterioration comparator is a clipped-estimator surrogate, not the minimax risk. Reraisable (retry) once a class-uniform U_n ≍ R_n comparison and a shell-matching converse (lower bound at the R_n^* rate) exist.
banked_on: "2026-07-10"
---

# stat_ate_overlap_decay / v1 — Failed

**Topic.** Minimax estimation rate for the ATE under structure-agnostic nuisance estimation when overlap decays one-sidedly near the propensity-score boundary. Focal object: the minimax rate threshold as a joint function of the overlap-decay exponent and nuisance smoothness, characterizing the regime where one-sided overlap decay strictly changes the achievable ATE rate relative to the bounded-overlap structure-agnostic result.

**Novelty target.** relative-to-literature

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** Stage 0.5 decision FAIL — headline sharp weak-overlap minimax frontier (conj:minimax-frontier) underdelivered: the class-uniform U_n≍R_n comparison and R_n^* upper frontier are not discharged (scope_overreach_on_rate_premise + hidden_fold_structure + nonuniform_comparison_gap), leaving a parametric lower floor plus estimator-side O_P(U_n) achievability; crossfit-estimator / tail-order-reduction kernel is reusable (solver-blocked).

## Key files

- `stat_ate_overlap_decay_v1_state.json` — pipeline state at banking (`banked: true`).
- `stat_ate_overlap_decay_v1_proposal.tex` — final proposal version.
- `stat_ate_overlap_decay_v1.tex` — derivation note (if Stage 0 ran).
- `stat_ate_overlap_decay_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `stat_ate_overlap_decay_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

Banked FAILED per operator decision: the math fails at the headline but the
kernel is reusable (`reusable: solver_blocked`, `reraise_status: retry`).

**Re-use, don't re-derive:** the weak-overlap class definitions, the
envelope/surrogate/frontier construction, the power-rate + phase-boundary
lemmas, the estimator-side achievability bound, and the parametric floor
(`discovery/core.json`, `discovery/writeup.tex`).

**The single open blocker (what to build before re-raising):** a
*class-uniform* comparison `c_1 R_n <= U_n <= c_2 R_n` (the current constants
are law-specific) plus a *shell-matching converse* — a minimax lower bound at
the `R_n^*` rate off the root-n sub-regime. Until those exist, the headline
sharp weak-overlap minimax frontier cannot be closed and only the
floor-and-achievability sandwich holds.

The FAIL verdict is preserved verbatim in `review_decision.json`; the
supporting revise findings in `review_general.json`.
