---
qid: stat_reversekl_two_coverage
spec: linear_exact_shell
topic: "Fixed-design reverse-KL-regularized offline linear contextual-bandit learning on exact (C,D) shells: characterize shell feasibility, prove a universal measurable O~(dD min{eta/epsilon,epsilon^-2}) feature-coverage upper bound, and show that (d,C,D,eta) does not determine minimax difficulty by contrasting a zero-risk experiment with a pointwise-local Omega_{C,D,eta}(d/epsilon) experiment; no uniform D- or eta-dependent converse or persistent quadratic lower branch is claimed."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: "kernel_substituted"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  # Stage 0.5.G reviewer, verbatim (reviews/review_general.json):
  - "The delivered result is a one-sided universal achievability theorem ... it does not determine a matched minimax frontier."
  - "The informative converse is only the pointwise local Omega_{C,D,eta}(d/epsilon) result, with constants absorbing any claimed dependence on D and eta, and no quadratic converse is proved."
  - "The principal learner requires idealized exact global optimization, with no efficient implementation or approximation-regret guarantee."
  # Independent referee re-grade, 2026-08-05 (not from the pipeline chain):
  - "The entire D-dependence of the headline theorem is the definition of D applied once. lem:feature-coverage-domination (writeup.tex:861-888) states E_{rho,pi*} h^2 <= D_P * E_{rho,pi_ref} h^2 for linear h, and D_P := lambda_max(Lambda_ref^{-1/2} Lambda*_P Lambda_ref^{-1/2}) = sup_b (b'Lambda*_P b)/(b'Lambda_ref b) IS that inequality. The lemma is a largest generalized eigenvalue read backwards; there is no mathematical content between assuming D_P = D and concluding the rate is proportional to D."
  - "D_P is exactly the RELATIVE CONDITION NUMBER of Agarwal-Kakade-Lee-Mahajan (JMLR 22, 2021; arXiv:1908.00261), adopted as the offline partial-coverage index by Uehara-Sun (arXiv:2107.06226). Neither is cited. So ass:feature-exact-shell — self-labelled 'Novel' — is a standing assumption of the offline-RL coverage literature restated with equality instead of inequality."
  - "The promised matching lower bound was not merely missed: thm:fixed-design-index-insufficiency proves a uniform index-only lower bound cannot exceed 1, i.e. the converse is impossible in the form promised. The run's own maximality consultation records 'MAXIMALITY: NO-ROOM'."
  - "The surviving dD upper bound is NOT for the promised learner. The computable localized-pessimistic learner is refuted by the note's own prop:empirical-ball-dimension-witness (it loses a factor d); dD was recovered only by inventing a new learner that the note concedes 'is an idealized global-optimization procedure; computational efficiency is not established'. The word 'computable' was dropped from the deliverable."
  - "By the run's own bookkeeping it beat zero comparators: all six entries in core.json comparator_promise_table are downgraded_to_informed_by, and the pivotal one (Ji et al., the tabular matching frontier this run promised to lift to linear features) is matched_by 'unmatched'."
  - "No causal estimand. Under ass:reference-logging the behavior policy equals the known KL reference, so there is no confounding, no positivity question and no identification content — this is offline-bandit / RLHF learning theory, and the Stat-cluster causal-estimand guard is not met."
  - "The advertised slow-branch refutation is near-vacuous: with (d, D, eta) FIXED and epsilon -> 0, min{eta/epsilon, epsilon^{-2}} = eta/epsilon whenever eta*epsilon <= 1, so the quadratic branch is inactive by definition of the min. The genuine phase transition in this literature is about JOINT (eta, epsilon) scaling, which a one-variable frontier structurally cannot see."
  - "The 'finite exponential nonlinear-semidefinite feasibility certificate' (lem:fixed-experiment-shell-certificate) is a literal transcription of 'ess sup = C' into 'bounded everywhere, attained at one cell' and 'lambda_max = D' into 'D*B - G psd with a null vector', plus a 2^|X| case enumeration. It computes nothing and supplies no algorithm."
reusable_artifacts:
  - path: ../../../../../legacy/lean/STAT_ReverseklTwoCoverage_Research/
    kind: operator
    one_line: "The retired Lean tree (90 modules, 621 declarations), moved out of the compiled library on 2026-08-05. The substrate is reusable independently of the tier verdict — Gibbs/RegretIdentity* (Gibbs regret identity, pessimism/plug-in conversions), Localization/* (bounded-linear localization, uniform Gibbs radius comparison), Coverage/FeatureDomination. See that folder's README.md for the four remaining sorries and restore instructions. Promotion to the shared library has NOT been done."
  - path: discovery/writeup.tex
    kind: counterexample
    one_line: "The paired same-index experiments showing two setups with IDENTICAL coverage indices and very different sample requirements (frontier non-uniqueness). Genuine daylight over Nguyen-Tang & Arora ICML 2024 Example 3.3: theirs uses an infinite index, this uses EQUAL FINITE indices. Small but real."
  - path: discovery/recovery_feasible_index_region.json
    kind: lp_setup
    one_line: "Feasible-index-region recovery record for the fixed-design shell certificate."
  - path: formalization/plan.json
    kind: other
    one_line: "F1 formalization plan — the node-to-Lean-module mapping for the retired tree; needed to navigate the legacy Lean folder."
  - path: discovery/core.json
    kind: literature_map
    one_line: "Comparator promise table (all six downgraded_to_informed_by, Ji et al. unmatched) plus attestations for Zhao et al. arXiv:2502.06051 and the KL-regularized offline-RL line. The table is itself the clearest evidence of the shortfall."
seeds_burned: []
proof_attempt_summary: |
  Aimed to characterize the minimax sample complexity of KL-regularized offline
  policy learning as a function of two coverage indices, proving a matching
  same-shell lower bound against a COMPUTABLE localized-pessimistic upper bound
  and thereby determining when the pointwise index C is irrelevant beyond the
  feature index D. What was delivered is a one-sided achievability bound for a
  different, non-computable learner, whose entire D-dependence is the definition
  of D unfolded once and whose D is the published relative condition number of
  Agarwal et al. under another name; the promised converse was proved IMPOSSIBLE
  in the form promised, and the C-irrelevance question dissolved rather than
  resolved (C is always irrelevant). Formalization reached F2 with 621 Lean
  declarations before being stopped: the four remaining sorries are the
  load-bearing ones, including the headline theorem itself.
banked_on: "2026-08-05"
---

# stat_reversekl_two_coverage / linear_exact_shell — Downgraded

**Topic.** Fixed-design reverse-KL-regularized offline linear contextual-bandit learning on exact (C,D) shells: characterize shell feasibility, prove a universal measurable O~(dD min{eta/epsilon,epsilon^-2}) feature-coverage upper bound, and show that (d,C,D,eta) does not determine minimax difficulty by contrasting a zero-risk experiment with a pointwise-local Omega_{C,D,eta}(d/epsilon) experiment; no uniform D- or eta-dependent converse or persistent quadratic lower branch is claimed.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** Independent referee re-grade: subfield, not field. The entire D-dependence of the headline theorem is the definition of D unfolded once (lem:feature-coverage-domination is the Rayleigh-quotient definition of the largest generalized eigenvalue), and D is identically the published relative condition number of Agarwal-Kakade-Lee-Mahajan (JMLR 2021) adopted by Uehara-Sun, uncited here. The promised matching lower bound was not merely missed but proved impossible in the promised form, and the surviving upper bound is for a different, non-computable learner. By its own comparator table all six comparators are downgraded_to_informed_by and the pivotal one (Ji et al.) is unmatched. No causal estimand: under ass:reference-logging the logging policy equals the KL reference, so there is no confounding or identification content.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

**Why this was downgraded, in plain terms.** You have logged data from a
recommendation-style system and want to pick a better decision rule without a new
experiment, scored with a penalty for drifting from the policy that generated the
data — the objective used to fine-tune language models. The question is how many
logged observations you need, as a function of two numbers summarizing how well
the logged data covers the policy you want to deploy. What was proved is one
direction only: an upper bound for a computationally infeasible procedure, plus
the observation that the second coverage number never matters. The promised
matching lower bound is not merely absent — the note proves no such bound of the
promised form can exist. And the inequality driving the upper bound is a one-line
restatement of the definition of the coverage number, which is itself a quantity
already named and used in the literature.

**Marked `true-negative`, not `re-raise`.** Both candidate rescues are closed:

- *Deliver the matching converse* — foreclosed by the note's own
  `thm:fixed-design-index-insufficiency` (a uniform index-only lower bound cannot
  exceed 1). Getting a converse means abandoning the exact-shell-as-model-class
  formulation, which is the run's entire scaffolding. The run's own maximality
  consultation (`orchestrator/d0_round59_corrected_maximality_verdict.txt`)
  returns "MAXIMALITY: NO-ROOM" and says a stronger uniform lower frontier "would
  require new research".
- *Claim the upper bound as the advance* — blocked by the definitional unfold,
  and by the note's own concession (§Honest scope) that it "does not dominate
  their [Zhao et al.'s] general-function, sufficiently-small-accuracy,
  high-probability result".

Do not re-raise this kernel. The honest positioning for the delivered content is
"linear specialization of Zhao et al. with the relative condition number, plus a
coverage-insufficiency example" — section material, not a paper.

**The one idea here with independent life — as a DIFFERENT project.** The note
observes D_P <= D^2_{pi*} <= d*D_P under directional richness (writeup.tex:49),
i.e. a trace-versus-spectral separation between coverage indices. If one could
prove the SPECTRAL index is the correct one — a lower bound scaling with D_P, a
matching upper bound, and a family where the trace index overstates difficulty by
a genuine factor d — that would be a real contribution. This note explicitly does
not do it and flags it as requiring new research. It is a new topic, not a
re-raise of this one.

**Lean code.** Retired to `CausalSmith/legacy/lean/STAT_ReverseklTwoCoverage_Research/`
on 2026-08-05 — outside the `lean_lib` source path, so it is no longer compiled by
`lake -d CausalSmith build` and no longer swept by `tools/scripts/full_tree_build.sh`.
Nothing imported it; the full-tree sweep was green (415 modules) after the move.
The 621 proved declarations are scaffolding beneath four remaining sorries which
are precisely the load-bearing ones — the headline theorem
(`Upper/CleanTemperature.lean:93`) is entirely `sorry` and additionally takes
`ZhaoUniformSquareComparison` and `MeasurableMaximumTheorem` as Lean *hypotheses*
rather than proving them. Finishing it would formalize a definitional unfold.
The substrate listed under `reusable_artifacts` is worth promoting; that is a
deliberate human step and has not been done.

**Process note for the pipeline.** This run consumed roughly 60 D0 rounds and
~18 hand-driven orchestrator repairs. The prose was honestly resynchronized at
each retreat — the TL;DR and honest-scope sections disclose the weakening
accurately, so this is honest retreat rather than concealment — but the retreat
went all the way to the ground while the project-level framing (§Project
justification "Fill") still sells three contributions that are, respectively, a
definitional transcription, a definitional unfold of a known index, and a
published observation restated for this objective.
