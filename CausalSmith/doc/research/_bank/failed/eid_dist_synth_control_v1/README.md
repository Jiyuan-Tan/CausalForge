---
qid: eid_dist_synth_control
spec: v1
topic: "Distributional synthetic control: sharp identification of the counterfactual outcome distribution for a treated unit under a quantile-rank-invariant interactive factor structure with finitely many donor units"
novelty_target: flagship
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "kernel_substituted"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - 'Conjecture 1 (point-boundary): refuted by the note''s own three-block finite-support counterexample — row-span failure on I_M coexists with Q_DW(P)={0} because monotonicity and fixed neighboring blocks squeeze all compatible quantile values to zero, so positive-measure row-span failure plus rank/interior conditions do NOT imply non-singleton donor-weight identified set.'
  - 'Conjecture 2 (escape): partial only — ''the fragment proves an explicit algebraic witness and a determinant-stable rank-wise row-span failure neighborhood. It does not prove the conjecture''s stronger claim that every panel in a nonempty relatively d_infty-open neighborhood admits two monotone-admissible global common-loading systems.'''
  - 'Theorem 1 (Sharp factor-law identified set): ''The theorem restates the definition of Q_I(P) as the compatible-system image and does not expose a computable map from observed inputs for the full factor-law class.'' — definition-body restatement, not a causal ExactID result.'
  - 'Novelty floor: ''Assessed tier is below novelty_target=flagship; the kernel is a row-span diagnostic and monotone-envelope correction rather than a flagship theorem, and no local revision would lift it to the required flagship tier.'''
  - 'Theorem 1 / Theorem 2 (pivot angles): ''The marginal-counterfactual identification statement is already the core object of Gunsilius2023DiSCo and Chen2020DistributionalSC, not a new theorem.'' and ''The comonotone/copula-stability positive corner is the standard rank/dependence-restriction formula from AtheyImbens2006CIC and CallawayLi2019QTEDID.'' — both assessed as already-known.'
  - 'Anchor mismatch (angle 0): ''The declared run cluster is exactid, but the locked-parameter block and the whole derivation are panel/distributional-synthetic-control objects. The ExactID anchor tuple should include a graph/SWIG, treatment, target estimand, and identifying assumptions.'''
  - 'Proof correctness (angle 0/1): ''The converse construction assigns an arbitrary q in Q_C(P) as the treated post-period counterfactual but does not construct latent factors/loadings satisfying Assumption qif or the locked rank-invariant quantile-factor model.'''
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  The run attempted a flagship exact-identification result for the distributional synthetic-control (DiSCo) treatment-effect frontier, proposing that the sharp identified set for the treatment-effect distribution equals the Frechet-Makarov/optimal-transport copula envelope after marginal DiSCo identification, with an iff diagnostic W(d). The headline Conjecture 1 (sharp copula frontier) was refuted by the derivation's own three-block finite-support counterexample showing row-span failure coexisting with a singleton donor-weight identified set, and Conjecture 2's flagship claim of a relatively d-infinity-open global monotone-selection nonidentification regime was not proved — only a finite-dimensional witness with determinant-stable rank-wise failure was established. Theorem 1 collapsed to a definition-body restatement of Q_I(P), and Theorems 1 and 2 across multiple pivot angles were judged already-known by published comparators (Gunsilius2023DiSCo, AtheyImbens2006CIC, CallawayLi2019QTEDID); no local repair could lift any surviving residual to the required flagship tier.
banked_on: "2026-05-21"
---

# eid_dist_synth_control / v1 — Failed

**Topic.** Distributional synthetic control: sharp identification of the counterfactual outcome distribution for a treated unit under a quantile-rank-invariant interactive factor structure with finitely many donor units

**Novelty target.** flagship

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0 re-test (post D0-solver upgrade) on prior kernel_substituted parent: First post-restore D0.5 on the original angle 0 v5 proposal returned REVISE@flagship - Theorem 1 (Sharp factor-law identified set) correctness, Section 7 (Estimand-defining functional) correctness. New D0 still produced a derivation whose headline sharpness theorem has correctness gaps relative to the proposal kernel. Pipeline then silently pivoted (rewound_from_stage0_5_pivot) to angle 1 then angle 2; subsequent D0.5 reviews on the pivoted angles produced Case 6b reject (Conjecture 1 refuted by note own finite-support counterexample, Conjecture 2 flagship monotone-selection not proved, Theorem 1 collapses to definition restatement). Run stopped mid-angle-2 pivot per user direction. Apples-to-apples verdict on original kernel: new D0 did not resolve headline-sharpness correctness shortfall; classification remains kernel_substituted.

## Key files

- `eid_dist_synth_control_v1_state.json` — pipeline state at banking (`banked: true`).
- `eid_dist_synth_control_v1_proposal.tex` — final proposal version.
- `eid_dist_synth_control_v1.tex` — derivation note (if Stage 0 ran).
- `eid_dist_synth_control_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `eid_dist_synth_control_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
