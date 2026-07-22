---
qid: pid_ot_dte_marginal
spec: v1
topic: "Sharp partial identification of distributional treatment effects via optimal-transport extremal couplings under marginal-overlap restrictions on counterfactual outcome distributions"
novelty_target: flagship
tier_at_proposal: NO-PASS
tier_at_derivation: REVISE
proposal_promise_gap: "kernel_substituted"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - 'Conjecture 1: cycle-frontier — ''the one-cell Conjecture 1 counterexample is arithmetically credible'' but ''correctly refutes the proposed iff criterion as stated''; verdict: refuted-with-counterexample'
  - 'Conjecture 2: witness — ''The Conjecture 2 theorem is the main obstacle. The proof ... says that the witness basis contains endpoint tables pi_s^star in the relevant rank-tube faces ... but the note never displays those tables or the rank-tube inequalities that make them feasible and optimal'''
  - 'Conjecture 2: C-wellposed — ''the key implication that any full-data optimizer would induce residuals from a single global vertex potential is not proved from the definitions of Q(P), L(P), V(P), or C_{rho,s}'''
  - 'Novelty: ''The negative result does not name a specific published estimator/workflow claim that is refuted, and the claimed open-set witness is not yet positioned as a generic-class obstruction against a named target'''
  - 'Overall: proposal_promise_gap=kernel_substituted (reviewer 1), direction_only (reviewer 2), constructive_object_missing (reviewer 3); intervention route: ''recast the paper around the factual-compatibility theorem with a computable response-type feasibility correction'''
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  The proposal attempted to prove an iff covariate-aggregation frontier for overlap-restricted DTE path sets (A_D(P)=0 iff conditional and pooled OT path sets coincide), but the headline kernel was never established: Conjecture 1 (the cycle-frontier criterion) was refuted by a clean one-cell binary counterexample showing Gamma(P,0)=0 yet Theta_I != Theta_L, while Conjecture 2 (open-set strict-containment witness) was filed as confirmed but all three stage-0.5 reviewers found its core finite LP certificate, pastability-to-single-potential lemma, and rank-tube constraints asserted rather than derived. The validated output — the factual-compatibility counterexample and the outer-envelope inclusion — is mathematically sound and real, but falls below the flagship novelty floor on its own; the path forward is a reframed proposal built around the factual-compatibility correction as the focal theorem.
banked_on: "2026-05-22"
---

# pid_ot_dte_marginal / v1 — Failed

**Topic.** Sharp partial identification of distributional treatment effects via optimal-transport extremal couplings under marginal-overlap restrictions on counterfactual outcome distributions

**Novelty target.** flagship

**Stage -0.5 verdict.** NO-PASS

**Stage 0.5 verdict.** REVISE

**Banking reason.** Stage -1.2 NO-PASS @ flagship after 4 pivots (budget exhausted). Path: angles cycled through OT pooled-vs-conditional DTE envelope, finite diagnostics, dependence lattice, lifted-OT pasting; one angle reached D-0.5 ACCEPT but D-0.5→0 review fired proposal_promise_gap=kernel_substituted/direction_only/constructive_object_missing (Conj-2 witness lacked finite LP certificate; load-bearing pastability lemma asserted not derived). Surviving Conj-1 refutation + outer-envelope inclusion is sound but field-tier only, does not clear flagship novelty floor alone.

## Key files

- `pid_ot_dte_marginal_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_ot_dte_marginal_v1_proposal.tex` — final proposal version.
- `pid_ot_dte_marginal_v1.tex` — derivation note (if Stage 0 ran).
- `pid_ot_dte_marginal_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_ot_dte_marginal_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
