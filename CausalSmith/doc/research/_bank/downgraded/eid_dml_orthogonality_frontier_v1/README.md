---
qid: eid_dml_orthogonality_frontier
spec: v1
topic: "Uniform-in-DGP Neyman orthogonality breakdown frontier for heterogeneous-treatment-effect DML estimators across nuisance classes parametrized by Holder smoothness and metric entropy"
novelty_target: flagship
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "constructive_object_missing"
reusable: unknown  # was solver_blocked; corrected — no Lean solver ran, failure was a D0.5 math-derivation gap (frontier assumed, not derived), so solver_blocked is inapt
reraise_status: retry
gap_reasons:
  # D0.5 verdicts: 3x REVISE (mixed), all flagging the same correctness/novelty gap.
  # No *_oneshot_stage0_5_*.txt present; phrases lifted from the three
  # stage_0.5_to_0_attempt*.json verbatim_critique blocks.
  - "the advertised frontier theorem is not actually derived at flagship strength"  # correctness (attempt1)
  - "Assumption 4 states the empirical-process upper bound ... Assumption 6 then assumes active tangent cones and lower-bound constants that realize matching minimax lower bounds at the same scale ... The conclusion is therefore too close to the assumption package"  # correctness (attempt1)
  - "the decisive content is already built into Assumption (crossfit) and Assumption (curvature) ... not a proof of the promised sharp Holder/entropy DML frontier from primitive conditions"  # correctness (attempt2)
  - "With those two assumptions in place, Theorem 1 becomes a repackaging of the assumed upper and lower channels rather than a primitive necessary-and-sufficient theorem"  # correctness (attempt3)
  - "the related-work comparison does not establish that this high-level assumed frontier resolves an open regime relative to at least two close comparators or a cited open problem"  # novelty (attempt1)
  - "does not derive the empirical-process leakage scale from entropy primitives, does not derive the active lower-bound construction from a concrete Holder/report-class geometry"  # novelty (attempt1)
  - "the high-level active-frontier assumption is not a published named structural restriction and effectively imports the claimed boundary"  # novelty (attempt2)
  - "the oracle-process centering convention should be made explicit in the theorem statement or replaced by the natural influence function l(X)Gamma - theta_0(l)"  # correctness, minor (attempt2)
reusable_artifacts:
  - eid_dml_orthogonality_frontier_setup.json        # locked ExactID anchor + AIPW identifying functional (reviewers: structure PASS)
  - eid_dml_orthogonality_frontier_v1_gaps.json      # 7-problem literature_map (5 web / 1 prior / 1 both), cited comparators
  - eid_dml_orthogonality_frontier_v1.tex            # Stage 0 derivation: AIPW exact-ID algebra + Holder exponent calc both reviewed correct
  - eid_dml_orthogonality_frontier_conj_2_fragment.tex  # Holder-rate frontier exponent reduction (Conj 2 confirmed, algebra correct)
seeds_burned: []
proof_attempt_summary: |
  Attempted a primitive necessary-and-sufficient uniform-in-DGP frontier C_n(P) / F_n(P)
  at which first-order Neyman-orthogonal HTE-DML stops being uniformly asymptotically
  linear and Gaussian, with a Holder/entropy specialization (r_g+r_p>1/2 and min(r_g,r_p)>zeta).
  The AIPW exact-ID algebra and the Holder exponent reduction held (both conjecture fragments
  verdict=confirmed, reviewers found the algebra correct), but the headline iff theorem
  collapsed: across 3 D0.5 attempts (all REVISE) reviewers found the upper Gaussian channel
  and matching minimax lower channel were imposed via Assumptions 4/6 (the user-approved
  A-frontier-active consolidation) rather than derived from primitive maximal-inequality and
  local-minimax arguments — a conditional field-tier theorem dressed as a flagship frontier.
  What remains open: deriving the empirical-process upper scale and an actual matching
  lower-bound construction from the locked Holder/report-class primitives.
banked_on: "2026-05-22"
---

# eid_dml_orthogonality_frontier / v1 — Downgraded

**Topic.** Uniform-in-DGP Neyman orthogonality breakdown frontier for heterogeneous-treatment-effect DML estimators across nuisance classes parametrized by Holder smoothness and metric entropy

**Novelty target.** flagship

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REVISE

**Banking reason.** D-0.5 ACCEPT@flagship (angle=4 v3, 25 reviews); D0 derivation completed; D0.5 REJECT (correctness: frontier encoded in Assumptions 4+6 rather than derived); Bucket-A theorem split applied (theorem_splits=1, added_assumptions=[A-frontier-active]); D0 re-derived; D0.5 again 3x REVISE all same flag; loop-guard escalated to USER (Case 2d). Pipeline-proposed actions: (i) demote Theorem 1 to field-tier conditional and accept non-flagship novelty; (ii) replace A-frontier-active with primitive empirical-process maximal-inequality + minimax lower-bound arguments. Run was on D-1.2 effort=high — high effort helped surface a real frontier gap rather than concealing it. Downstream-reusable: setup + theorem statement + Assumption A-frontier-active + Bucket-A split machinery.

## Key files

- `eid_dml_orthogonality_frontier_v1_state.json` — pipeline state at banking (`banked: true`).
- `eid_dml_orthogonality_frontier_v1_proposal.tex` — final proposal version.
- `eid_dml_orthogonality_frontier_v1.tex` — derivation note (if Stage 0 ran).
- `eid_dml_orthogonality_frontier_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `eid_dml_orthogonality_frontier_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
