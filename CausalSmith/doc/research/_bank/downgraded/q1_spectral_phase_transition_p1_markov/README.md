---
qid: q1_spectral_phase_transition
spec: p1_markov
topic: "Spectral phase transitions for staggered two-way fixed effects on Markov-modulated treatment adoption: a mixing-time/spectral-gap threshold theorem that sharply separates the point-identified, partially-identified, and non-identified regimes for the dynamic ATT, together with the matching FWL/minimal-basis structural change on each side of the threshold. Goal: a flagship-tier identification phase-transition result that ties the spectral gap of the adoption Markov chain to identifiability of dynamic treatment effects, generalizing static minimal-basis theory and providing a Lean-formalizable identification frontier."
novelty_target: flagship
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  # Verbatim/near-verbatim reviewer phrases from
  # q1_spectral_phase_transition_p1_markov_reviews.jsonl (stage_0.5_to_0) and the
  # conj_*_verdict.json files. Both motivating conjectures were refuted; the
  # surviving theorem is routine linear algebra and the flagship spectral kernel
  # was left unproved/assumed.
  - "The artifact refutes both motivating conjectures instead of proving a flagship phase-transition or minimal-basis theorem, and the remaining proved theorem is a routine finite-dimensional row-space trichotomy. Under novelty_target=flagship, this derivation is below the required floor."
  - "both headline results refute internal in-repo conjectures rather than a named published estimator/workflow, so the artifact cannot clear novelty_target=flagship under the negative-result rules. This is not a derivation slip a Stage-0 redo can fix on the same .tex; the conjecture choice itself is the defect."
  - "Conjecture 1 (refuted-with-counterexample): for K={-1,0}, a_T=b_T=T^{-1/2}, the persistent direction q=E0+C11 has two-way residualized Gram scale at least T/64 while Lambda_T(K) asymp T^{1/2}, so sigma_max(G_T(K))/Lambda_T(K) diverges — refuting the proposed singular-value envelope."
  - "Conjecture 2 (refuted-with-counterexample): the finite-T witness T=2, K={-1,0}, a=b=1/2, B*={C10+C11} gives the row identity ell = 16 A_1 + 8 A_2, so {C10,C11} is not minimal in the proposal's basis class."
  - "the genuinely novel spectral phase-transition kernel is explicitly left unproved; the actual proved theorem-level content is mostly generic row-space/affine-fiber linear algebra plus a simple Markov window count."
  - "The negative-result rule requires a named published paper, estimator, or workflow using the refuted method ... the note does not identify a published method or estimator that makes the refuted claim."
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  D0 re-test (post-solver-upgrade) of a flagship spectral phase-transition kernel: an
  innovation-mass threshold Xi_T separating point/partial/non-identified regimes for the
  dynamic ATT under Markov adoption, motivated by two conjectures (Conj 1: a Lambda_T
  singular-value envelope for the FWL history Gram; Conj 2: minimality of the {C10,C11}
  nuisance basis). The split orchestrator settled honestly: the producer's own witnesses
  refuted BOTH conjectures (Conj 1 via the persistent direction E0+C11 whose residualized
  Gram scale grows like T while Lambda_T ~ T^{1/2}; Conj 2 via the T=2 row identity
  ell = 16 A_1 + 8 A_2). What remains is only a routine finite-dimensional row-space
  trichotomy (Theorem 1) plus a Markov clean-window support count; the flagship spectral
  kernel was never proved, and the negative results target internal in-repo conjectures
  rather than any named published estimator, so Stage 0.5 rejected at the flagship floor
  (Case 6b). Defect is upstream of the solver, at the proposal-level kernel/tier choice.
banked_on: "2026-05-21"
---

# q1_spectral_phase_transition / p1_markov — Downgraded

**Topic.** Spectral phase transitions for staggered two-way fixed effects on Markov-modulated treatment adoption: a mixing-time/spectral-gap threshold theorem that sharply separates the point-identified, partially-identified, and non-identified regimes for the dynamic ATT, together with the matching FWL/minimal-basis structural change on each side of the threshold. Goal: a flagship-tier identification phase-transition result that ties the spectral gap of the adoption Markov chain to identifiability of dynamic treatment effects, generalizing static minimal-basis theory and providing a Lean-formalizable identification frontier.

**Novelty target.** flagship

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0 re-test (post D0-solver upgrade) on prior kernel_substituted parent: D0 produced an honest artifact (split orchestrator settled all verdicts without silently substituting the kernel) but D0.5 Case 6b reject@flagship — both headline results refute internal in-repo conjectures rather than a named published estimator/workflow; flagship floor unreachable on this proposal. pivot_budget already exhausted (NEG1_PIVOT_BUDGET=3). Honest negative result: defect is upstream of D0 (proposal-level kernel/tier), not D0 solver.

## Key files

- `q1_spectral_phase_transition_p1_markov_state.json` — pipeline state at banking (`banked: true`).
- `q1_spectral_phase_transition_p1_markov_proposal.tex` — final proposal version.
- `q1_spectral_phase_transition_p1_markov.tex` — derivation note (if Stage 0 ran).
- `q1_spectral_phase_transition_p1_markov_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `q1_spectral_phase_transition_p1_markov_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
