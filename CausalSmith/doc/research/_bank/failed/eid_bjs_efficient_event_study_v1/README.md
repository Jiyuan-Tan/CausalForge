---
qid: eid_bjs_efficient_event_study
spec: v1
topic: "Sharp efficiency-equivalence/non-equivalence theorem across the four leading staggered DiD estimators: Borusyak-Jaravel-Spiess (2024 RES) imputation, Sun-Abraham (2021 JoE) interaction-weighted, Callaway-Sant'Anna (2021 JoE) doubly-robust group-time, and Wooldridge (2021) cohort-time-saturated TWFE. Under heterogeneous treatment effects in cohort and event-time, all four point-identify the same average treatment effect on the treated (ATT) under no-anticipation + parallel trends. The flagship question (axis b, equivalence/non-equivalence frontier between named published estimators): characterize the sharp boundary at which these four estimators have asymptotically equivalent influence functions vs. strictly different ones, as a function of (i) the cohort-time treatment-effect heterogeneity matrix Tau, (ii) the cohort-share vector pi, and (iii) the pre-period covariance matrix Sigma. The kernel claim is a closed-form spectral non-equivalence theorem: the BJS imputation IF and the SA-CS-Wooldridge IFs span identical orthogonal-score subspaces if and only if a low-rank condition rank(Tau) <= K_star holds, where K_star is a sharp threshold equal to the smallest singular value of an explicit observable kernel matrix combining pi and Sigma; when rank(Tau) > K_star, the four estimators have strictly distinct asymptotic variances and BJS achieves the semiparametric efficiency bound while the others sacrifice efficiency proportional to the rank gap. K_star is a new mathematical object computable from observable cohort shares and pre-period covariances, not an existence/absence statement from prior work. Recovers the well-known equivalence under homogeneous effects (rank(Tau)=0) and provides the first sharp efficiency-equivalence boundary for staggered DiD in closed form."
novelty_target: flagship
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - 'Conjecture 1: N-mischar — ChenSantAnnaXie2025 is underplayed: it derives closed-form EIFs and efficient variance bounds for modern DiD/ES parameters and explicitly benchmarks TWFE, CS, SA, BJS, Wooldridge-type estimators, so the proposal must separate its quotient-equality frontier from that stronger efficient-EIF benchmark.'
  - 'Conjecture 1: N-thin-survey — tier=field below novelty_target=flagship unless the redraft turns the Gamma condition into a frontier relative to the true ChenSantAnnaXie2025 EIF, or proves a genuinely new sharp equality threshold not implied by their efficient-bound geometry.'
  - 'Conjecture 1: C-coherence — Assumption 8 makes BJS the canonical gradient by assumption, while §4-§5 position the claim under the general parallel-trends staggered-DiD model where ChenSantAnnaXie2025 claims EIF-based estimators dominate existing BJS/SA/CS/W implementations; the model restriction needs to be pinned or the baseline changed.'
  - 'Conjecture 1: C-wellposed — The proposal still says non-BJS estimators share or differ in ''canonical gradients''; in semiparametric terminology the canonical gradient belongs to the parameter/model, so this should be stated as estimator influence functions versus the efficient EIF.'
  - 'Theorem 2: already-known — SunAbraham2021, CallawaySantAnna2021, Wooldridge2021: homogeneous-effect/equivalent-estimand sanity corner.'
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  Attempted a flagship-tier spectral non-equivalence theorem across four staggered-DiD estimators (BJS, SA, CS, Wooldridge): the headline kernel — a quotient row-space condition Gamma_m(pi,Sigma,a)*tau=0 characterizing necessary and sufficient IF-equivalence — was rated incremental across all 15 attempts (3 angles x 5 revisions each) because ChenSantAnnaXie2025 was found to already benchmark closed-form EIFs across these four estimator classes. The core Theorem 1 (aggregation equality is not IF equality) and Conjecture 1 (Gamma_m frontier) both held as plausible math objects, but Assumption 8 axiomatically declared BJS the canonical gradient in a model where ChenSantAnnaXie2025's EIF-based estimators may dominate BJS, leaving the proposal incoherent at the flagship tier. Theorem 2 (homogeneous-effects reduction) was judged already-known from SA/CS/Wooldridge directly.
banked_on: "2026-05-16"
---

# eid_bjs_efficient_event_study / v1 — Failed

**Topic.** Sharp efficiency-equivalence/non-equivalence theorem across the four leading staggered DiD estimators: Borusyak-Jaravel-Spiess (2024 RES) imputation, Sun-Abraham (2021 JoE) interaction-weighted, Callaway-Sant'Anna (2021 JoE) doubly-robust group-time, and Wooldridge (2021) cohort-time-saturated TWFE. Under heterogeneous treatment effects in cohort and event-time, all four point-identify the same average treatment effect on the treated (ATT) under no-anticipation + parallel trends. The flagship question (axis b, equivalence/non-equivalence frontier between named published estimators): characterize the sharp boundary at which these four estimators have asymptotically equivalent influence functions vs. strictly different ones, as a function of (i) the cohort-time treatment-effect heterogeneity matrix Tau, (ii) the cohort-share vector pi, and (iii) the pre-period covariance matrix Sigma. The kernel claim is a closed-form spectral non-equivalence theorem: the BJS imputation IF and the SA-CS-Wooldridge IFs span identical orthogonal-score subspaces if and only if a low-rank condition rank(Tau) <= K_star holds, where K_star is a sharp threshold equal to the smallest singular value of an explicit observable kernel matrix combining pi and Sigma; when rank(Tau) > K_star, the four estimators have strictly distinct asymptotic variances and BJS achieves the semiparametric efficiency bound while the others sacrifice efficiency proportional to the rank gap. K_star is a new mathematical object computable from observable cohort shares and pre-period covariances, not an existence/absence statement from prior work. Recovers the well-known equivalence under homogeneous effects (rank(Tau)=0) and provides the first sharp efficiency-equivalence boundary for staggered DiD in closed form.

**Novelty target.** flagship

**D-0.5 verdict.** NO-PASS

**D0.5 verdict.** NA

**Banking reason.** D-0.5 NO-PASS@flagship after 3 angles × 5 revises (15 attempts). NEW failure mode under widened rubric: 14 of 15 versions reached REVISE@flagship (vs. all-REVISE@field before rubric change) — kernel recognized at flagship axis (b) for non-equivalence between BJS imputation, SA, CS, Wooldridge with K_star spectral threshold. Cap=5 revises/angle insufficient to clear well-posedness flags (K_star=0 corner case undefined, Z_M projection loss not uniquely specified across the 4 estimators). Suggests proposer-side issue: nitpicks dominate at flagship tier; either cap should lift conditionally on persistent flagship REVISE, or proposer needs tighter well-posedness scaffolding. Math+novelty sound at flagship; ACCEPT was reachable with 1-2 more revises.

## Key files

- `eid_bjs_efficient_event_study_v1_state.json` — pipeline state at banking (`banked: true`).
- `eid_bjs_efficient_event_study_v1_proposal.tex` — final proposal version.
- `eid_bjs_efficient_event_study_v1.tex` — derivation note (if D0 ran).
- `eid_bjs_efficient_event_study_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `eid_bjs_efficient_event_study_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
