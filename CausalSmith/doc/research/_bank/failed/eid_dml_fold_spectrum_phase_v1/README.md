---
qid: eid_dml_fold_spectrum_phase
spec: v1
topic: "Unequal-fold cross-fitting phase threshold for DML causal estimators. Pre-anchor check: closest anchors are Chernozhukov-Chetverikov-Demirer-Duflo-Hansen-Newey-Robins double/debiased ML, standard K-fold cross-fitting implementations, and the AutoID fold-restricted CLT/rate-conversion substrate. Why non-trivial? The target is not ordinary cross-fitting consistency: require a fold-mass spectrum c_k and an explicit phase theorem separating full sqrt(n) asymptotic linearity with variance inflation, vanishing-fold slower-rate regimes, and degenerate leave-one-out limits for orthogonal AIPW/DML scores. Why promising? The nonroutine object is estimator geometry: a hand-derived fold-spectrum certificate and a two-fold triangular-array witness showing the usual DML variance formula fails when one evaluation fold has c_k -> 0. If the delta is only a restatement of sample splitting, path derivatives, or standard CLT bookkeeping, pivot or accept field-tier."
novelty_target: flagship
tier_at_proposal: REJECT
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "angle0_v1: Gamma_n was a promissory certificate; Section 9 only plugged in assumed R_{k,n} error envelopes rather than computing the certificate from observed primitives or a worked learner/law."
  - "angle0_v1: the vanishing-fold witness was mathematically wrong; with n a_n -> lambda, the root-n contribution of the vanishing evaluation fold has variance a_n -> 0."
  - "angle1_v1: Exhibit 9.2 specified a nondegenerate ATE law but not a concrete fold/nuisance mechanism producing the advertised perturbation and tau^2/lambda gap."
  - "angle1_v1: B_{2,n}=xi_n/sqrt(n a_n) implies sqrt(n) a_n B_{2,n}=sqrt(a_n) xi_n -> 0 and n a_n^2 Var(B_{2,n})=a_n tau^2 -> 0, contradicting the claimed variance gap."
  - "angle1_v1: Theorem 1 assumed equal-fold hypotheses but referenced the fold-linear term without including the fold-linear assumption."
reusable_artifacts:
  - path: eid_dml_fold_spectrum_phase_v1_gaps.json
    kind: literature_map
    one_line: "Literature map for DML cross-fitting, custom folds, growing-K DML, no-split DML, and geometry-specific variance comparators."
  - path: eid_dml_fold_spectrum_phase_v1_reviews/angle0_v1.json
    kind: counterexample
    one_line: "Reviewer diagnosis that the initial fold-spectrum phase certificate was symbolic and the vanishing-fold variance witness had the wrong scaling."
  - path: eid_dml_fold_spectrum_phase_v1_reviews/angle1_v1.json
    kind: counterexample
    one_line: "Decisive algebraic refutation of the proposed small-fold perturbation scaling."
  - path: eid_dml_fold_spectrum_phase_v1_proposal_angle1_rejected.tex
    kind: other
    one_line: "Negative example of a fold-mass sandwich proposal; useful only as a warning about missing concrete learner/split primitives."
seeds_burned:
  - index: 0
    one_liner: "Construct a fold-spectrum certificate Gamma_n that sharply separates root-n DML, small-fold slower limits, and leave-one-out endpoints for unequal cross-fitting folds."
    reason: "D-0.5 reviews found the fold-spectrum certificate promissory, the vanishing-fold variance witness mathematically wrong, and the fold-mass sandwich pivot not-publishable."
  - index: 1
    one_liner: "Give a two-fold triangular-array witness where c_2,n -> 0 invalidates the usual DML score-variance report while the ATE and pointwise nuisance rates stay fixed."
    reason: "D-0.5 reviews found the fold-spectrum certificate promissory, the vanishing-fold variance witness mathematically wrong, and the fold-mass sandwich pivot not-publishable."
  - index: 2
    one_liner: "Derive a fold-mass-indexed sandwich variance for deterministic custom DML folds and repeated-fold aggregation."
    reason: "D-0.5 reviews found the fold-spectrum certificate promissory, the vanishing-fold variance witness mathematically wrong, and the fold-mass sandwich pivot not-publishable."
proof_attempt_summary: |
  Attempted a flagship estimator-geometry theorem for unequal cross-fitting in DML, first as a fold-spectrum phase certificate and then as a fold-mass sandwich variance. The reviewer found both the object and the witness insufficient: the first was symbolic triangular-array bookkeeping, and the second had an algebraically wrong small-fold variance calculation. Future DML-fold work needs a concrete learner/split primitive and a hand-checked variance identity before it is worth another flagship run.
banked_on: "2026-05-25"
---

# eid_dml_fold_spectrum_phase / v1 — Failed

**Topic.** Unequal-fold cross-fitting phase threshold for DML causal estimators. Pre-anchor check: closest anchors are Chernozhukov-Chetverikov-Demirer-Duflo-Hansen-Newey-Robins double/debiased ML, standard K-fold cross-fitting implementations, and the AutoID fold-restricted CLT/rate-conversion substrate. Why non-trivial? The target is not ordinary cross-fitting consistency: require a fold-mass spectrum c_k and an explicit phase theorem separating full sqrt(n) asymptotic linearity with variance inflation, vanishing-fold slower-rate regimes, and degenerate leave-one-out limits for orthogonal AIPW/DML scores. Why promising? The nonroutine object is estimator geometry: a hand-derived fold-spectrum certificate and a two-fold triangular-array witness showing the usual DML variance formula fails when one evaluation fold has c_k -> 0. If the delta is only a restatement of sample splitting, path derivatives, or standard CLT bookkeeping, pivot or accept field-tier.

**Novelty target.** flagship

**Stage -0.5 verdict.** REJECT

**Stage 0.5 verdict.** NA

**Banking reason.** Stopped early after D-0.5 rejected the initial fold-spectrum phase angle as field-tier and rejected the fold-mass sandwich pivot as not-publishable; the DML unequal-fold topic collapsed into standard triangular-array/variance bookkeeping with broken witness claims.

## Key files

- `eid_dml_fold_spectrum_phase_v1_state.json` — pipeline state at banking (`banked: true`).
- `eid_dml_fold_spectrum_phase_v1_proposal.tex` — final proposal version.
- `eid_dml_fold_spectrum_phase_v1.tex` — derivation note (if Stage 0 ran).
- `eid_dml_fold_spectrum_phase_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `eid_dml_fold_spectrum_phase_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

Reflection: this was a topic/proposal-strength failure with a math-kernel weakness, not reviewer strictness or a D0 solver issue. The idea had a plausible estimator-geometry shape, but without a concrete nuisance-learner process the fold-mass object collapsed into standard triangular-array variance bookkeeping. No pipeline bug was observed after launch; the shell timeout did not kill the pipeline, so the active heartbeat was checked, the run was stopped manually, and `bank_entry.ts` retired it.
