---
qid: stat_longterm_measurement_design
spec: v1
topic: "Measurement design as the argument of the semiparametric efficiency bound for long-term treatment effects. Setting: the Imbens-Kallus-Mao-Wang long-term data-combination model (arXiv:2202.07234, JRSS-B 2025) verbatim -- an observational sample observing short-term outcomes and the long-term outcome but confounded by a latent variable, an experimental sample with randomized treatment and short-term outcomes but no long-term outcome, external validity, the sequential-outcome restriction, and the two completeness conditions -- with target the long-term average treatment effect in the observational population. New primitive the anchor lacks: a finite catalogue of candidate short-term outcomes with per-variable measurement costs, a per-unit cost for an experimental unit and a higher one for a long-term-follow-up unit, a per-unit measurement-cost cap, and an ex-ante-known admissible family of (measured subset, role-assignment) pairs, every member of which is assumed regular. Focal object: the design-value function, the budget-normalized local semiparametric efficiency bound for the long-term ATE indexed by the measurement design, defined as infinity off the regular set, and its profile over the budget allocation between the two samples. Open content: whether selecting short-term proxies by their predictive power for the long-term outcome carries any finite efficiency guarantee. The conjecture is that it does not -- that over a non-degenerate region of laws no predictive optimizer is design-value optimal and the worst-case ratio of the design value at a predictive optimizer to the design-value minimum over the admissible family is unbounded, with every admissible design regular so that the failure is efficiency and not identification -- together with the positive side, that the design-value gap on the admissible family is the correct selection criterion, is identified by a full-catalogue pilot, and yields a feasible plug-in measurement-design rule. Prior art leaves this open: the anchor and the surrogate-index literature take the measured proxy system and the sampling ratio as exogenously given, published surrogate efficiency results compare with versus without a given surrogate set rather than optimizing over sets, and existing optimal-measurement-design results cover only linear front-door and Gaussian instrumental-variable models or optimize two-phase sampling probabilities for a fixed measured variable set. The anchor itself reports, without explanation, that its estimator can perform worse as surrogates are added, and attributes this to bridge non-uniqueness."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The negative comparison is a published CLW predictive-design selector versus the note's own bridge-efficient oracle benchmark, rather than two published estimators."
  - "The note proves a genuine unbounded efficiency-ratio failure for the transported CLW affine criterion and for two population squared-risk selectors, but only through a specially structured binary finite-cell family whose openness is relative to its factorized model."
  - "The arm-normalized design value is generally a source-score or restricted-submodel gradient variance, not an unconditional causal semiparametric efficiency bound; absolute efficiency is established only under the separately cited fixed-system IKM premises."
  - "The feasible bridge-value selector and Wald procedure are derived from primitive conditions only on the bounded fixed-dimensional bridge-basis subclass, while the broader observable-class results retain learner-rate, multiplier, and variance-estimation hypotheses."
  - "D0.5 stopped at external verification of the CLW source statement; completing that bounded check would not change the comparator asymmetry behind the user's novelty judgment."
reusable_artifacts:
  - "discovery/core.json — settled 26-statement typed discovery core."
  - "discovery/writeup.tex — complete D-stage derivation note."
  - "discovery/solve_thm_empirical_clw_integer_selector.json — empirical finite-catalogue CLW selector derivation."
  - "discovery/solve_thm_sharp_predictive_operator_certificate.json — predictive/operator counterexample derivation."
  - "reviews/review_math.json and reviews/review_rubric.json — clean correctness and structure reviews."
  - "orchestrator/decision_log.jsonl — source-faithful CLW pivot, repairs, maximality audit, and terminal rationale."
seeds_burned: []
proof_attempt_summary: |
  Discovery settled 26 statements (23 proved and three cited), including exact feasible-budget and empirical OLS selection results, unbounded ratios on relatively open regular common-identification regions, and a positive bridge-value design rule. Math and structure review passed, and the cold tier review graded the package field, but D0.5 stopped before acceptance for external attestation of the CLW source statement; no formalization stage began. Under the user's stricter comparator standard, the surviving contribution is a sound specialized counterexample and companion design note at subfield tier, suitable for re-raising only if a stronger published comparator or broader benchmark is found.
banked_on: "2026-08-02"
---

# stat_longterm_measurement_design / v1 — Downgraded

**Topic.** Measurement design as the argument of the semiparametric efficiency bound for long-term treatment effects. Setting: the Imbens-Kallus-Mao-Wang long-term data-combination model (arXiv:2202.07234, JRSS-B 2025) verbatim -- an observational sample observing short-term outcomes and the long-term outcome but confounded by a latent variable, an experimental sample with randomized treatment and short-term outcomes but no long-term outcome, external validity, the sequential-outcome restriction, and the two completeness conditions -- with target the long-term average treatment effect in the observational population. New primitive the anchor lacks: a finite catalogue of candidate short-term outcomes with per-variable measurement costs, a per-unit cost for an experimental unit and a higher one for a long-term-follow-up unit, a per-unit measurement-cost cap, and an ex-ante-known admissible family of (measured subset, role-assignment) pairs, every member of which is assumed regular. Focal object: the design-value function, the budget-normalized local semiparametric efficiency bound for the long-term ATE indexed by the measurement design, defined as infinity off the regular set, and its profile over the budget allocation between the two samples. Open content: whether selecting short-term proxies by their predictive power for the long-term outcome carries any finite efficiency guarantee. The conjecture is that it does not -- that over a non-degenerate region of laws no predictive optimizer is design-value optimal and the worst-case ratio of the design value at a predictive optimizer to the design-value minimum over the admissible family is unbounded, with every admissible design regular so that the failure is efficiency and not identification -- together with the positive side, that the design-value gap on the admissible family is the correct selection criterion, is identified by a full-catalogue pilot, and yields a feasible plug-in measurement-design rule. Prior art leaves this open: the anchor and the surrogate-index literature take the measured proxy system and the sampling ratio as exogenously given, published surrogate efficiency results compare with versus without a given surrogate set rather than optimizing over sets, and existing optimal-measurement-design results cover only linear front-door and Gaussian instrumental-variable models or optimize two-phase sampling probabilities for a fixed measured variable set. The anchor itself reports, without explanation, that its estimator can perform worse as surrogates are added, and attributes this to bridge non-uniqueness.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** Sound subfield result, but below the intended field bar: it compares the published CLW predictive-design selector with this note's newly defined bridge-efficient oracle benchmark rather than establishing a published-vs-published dominance result.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

CLW is itself published. The limiting issue is that the denominator in the
headline ratio is the note's newly defined bridge-efficient oracle benchmark,
not another published estimator. A future upgrade should retain the full-Gram
binary construction and exact integer/empirical selector analysis, while seeking
a published bridge-design rule or a broader benchmark that makes the comparison
field-level on its face.
