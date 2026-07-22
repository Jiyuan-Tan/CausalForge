---
qid: pid_mte_multi_iv
spec: v1
topic: "Sharp partial identification of the marginal treatment effect curve and policy-relevant treatment effects with two or more binary instruments, overlapping but distinct propensity-score supports, and a flexible MTE shape class (Bernstein-polynomial basis): a closed-form linear program characterizing the identified set as a function of the joint instrument-propensity distribution, with an explicit dual representation that yields PRTE bounds strictly tighter than the single-instrument MST (2018, Section 6) benchmark by a computable amount equal to the moment-cone width of the joint propensity distribution projected onto the basis; recovers Mogstad-Santos-Torgovitsky (2018, ECMA) Theorem 1 in the single-instrument special case. MST (2018, Section 6, p. 1623) explicitly state the multi-instrument extension is left for future work."
novelty_target: flagship
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: "constructive_object_missing"
reusable: solver_blocked
reraise_status: re-raise
gap_reasons:
  # Verbatim/near-verbatim reviewer phrases from the per-version review JSONs.
  # Two distinct failure modes across the 3 angles: (A) tier-too-high (field<flagship)
  # because MTW2024 already does multi-IV MTE aggregation; (B) the headline algebra
  # collapses / is ill-posed in every angle's flagship-reaching kernel.
  - "tier=field below novelty_target=flagship; MTW2024 already publishes multiple-IV MTE aggregation that is more informative than separate instruments, so the proposal needs a sharper published-frontier claim than a support-function gap diagnostic." # angle0_v1, N-thin-survey
  - "The claimed distinction between observed-face zero width and convex policy-mixture support collapses: every chord row a_c is a row of A(P), hence a_c is in N_F(P), so conv{a_c}+N_F(P)=N_F(P)." # angle1_v3 REJECT, C-sanity
  - "Pivot the quotient definition; the current flagship mixture kernel is algebraically collapsed by the proposal's own definition of N_F(P)." # angle1_v3 REJECT, recommended_next_step
  - "The eta=0 reduction does not follow as written: omega=0 and nu=0 do not force pi to put zero mass on defier response maps because the displayed constraint is only 0 <= omega <= C_pi pi, so violating pi-mass can be hidden at zero budget." # angle2_v3 REJECT, C-sanity
  - "K_viol(P) is not well-defined as a function of P alone: the 'homogeneous envelope after removing baseline nonviolating response masses' does not specify which exact-PM primal pi or active face supplies the compensating mass, yet the derivative formula depends on that tangent set." # angle2_v3 REJECT, C-wellposed
  - "the novelty kernel survives, but the current zero-budget algebra is load-bearing and false as stated." # angle2_v3 REJECT, recommended_next_step
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  Proposed a closed-form LP + dual for sharp multi-binary-IV MTE/PRTE partial
  identification (Bernstein basis), claiming PRTE bounds strictly tighter than
  single-IV MST(2018) by a "moment-cone width" amount, with later angles pivoting
  to a bounded partial-monotonicity-violation sensitivity kernel. NO-PASS at the
  proposal gate (Stage -0.5): 3 angles / 11 versions never cleared review and the
  run was banked before any derivation. Two recurring objections — (i) novelty
  capped at field, not flagship, since MTW2024 already extends MST to multiple IVs
  and shows aggregation beats separate instruments, so the width-gap diagnostic is
  not a sharp enough published-frontier claim; and (ii) the flagship-reaching kernel
  in each angle is algebraically collapsed / ill-posed (angle1: conv{a_c}+N_F(P)=N_F(P)
  by the proposal's own N_F definition; angle2: the eta=0 exact-PM reduction is false
  as written and K_viol(P) is not well-defined as a function of P alone). Reviewers
  judged the underlying area real and the kernel "new," but the load-bearing algebra
  false as stated; never derived.
banked_on: "2026-05-20"
---

# pid_mte_multi_iv / v1 — Downgraded

**Topic.** Sharp partial identification of the marginal treatment effect curve and policy-relevant treatment effects with two or more binary instruments, overlapping but distinct propensity-score supports, and a flexible MTE shape class (Bernstein-polynomial basis): a closed-form linear program characterizing the identified set as a function of the joint instrument-propensity distribution, with an explicit dual representation that yields PRTE bounds strictly tighter than the single-instrument MST (2018, Section 6) benchmark by a computable amount equal to the moment-cone width of the joint propensity distribution projected onto the basis; recovers Mogstad-Santos-Torgovitsky (2018, ECMA) Theorem 1 in the single-instrument special case. MST (2018, Section 6, p. 1623) explicitly state the multi-instrument extension is left for future work.

**Novelty target.** flagship

**D-0.5 verdict.** NO-PASS

**D0.5 verdict.** NA

**Banking reason.** D-0.5 NO-PASS: 3 angles capped at field tier; literature scout likely found post-2018 follow-ups closing the named open.

## Key files

- `pid_mte_multi_iv_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_mte_multi_iv_v1_proposal.tex` — final proposal version.
- `pid_mte_multi_iv_v1.tex` — derivation note (if D0 ran).
- `pid_mte_multi_iv_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `pid_mte_multi_iv_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
