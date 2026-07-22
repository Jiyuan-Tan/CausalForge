---
qid: scm_mediator_monotonicity_pn_v1
spec: mediator_defier_gap
topic: "On the confounded complete-mediation graph X->M->Y (X randomized, M<->Y confounded by an unmeasured U, all binary), characterize when mediator monotonicity M_1>=M_0 strictly tightens the SHARP sign-free response-function bound on the probability of necessity PN=P(Y_{x=0}=0 | X=1,Y=1). Deliver: the sharp sign-free bound [L0,U0] using the full experimental law P(M,Y|do(x)); the sharp monotonicity-restricted bound [L1,U1] (delete mediator-defier response types), whose endpoints are closed-form max/min-of-affine functionals via finite canonical-SCM-type vertex enumeration; and THE KERNEL: a necessary-and-sufficient computable threshold T(P) plus closed-form gap for strict containment [L1,U1] strictly-inside [L0,U0], attributable specifically to the deleted mediator-defier coupling, proven strict on a nonempty open set of compatible distributions. Estimation rung: X-randomized plug-in endpoint estimators with Fang-Santos directional-delta / intersection-bounds inference valid at the nonsmooth ties."
novelty_target: field
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: null
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "With S^- and S^+ defined as minimum defier mass on the sign-free endpoint-optimal faces and Q_1 defined by zero defier mass, the stated iff is the routine compact-LP fact that an endpoint face intersects Q_1; this is a 1-2-step reduction and caps the flagship framing at field."
  - "The preserved kernel is false: exact dual enumeration gives L_0(p)=L_1(p)=max{0,p_000+p_010-p_100-p_110}/d(p) on P_1. Mediator monotonicity can tighten only the upper PN endpoint, so no compatible law can have both endpoint gains positive as required by the escalation directive."
  - "Independent gpt-5.6-sol medium gate verified L0=L1 universally but found original proper containment remains true via upper-only tightening. Reclassified terminal:tex-claim-wrong to terminal:below-floor: upper-only iff/gap is sound but subfield/routine."
reusable_artifacts:
  - path: discovery/gaps.json
    kind: literature_map
    one_line: Literature and prior-proposal map for PN bounds with a confounded complete mediator; reuse the citations and comparator audit, not the rejected two-endpoint claim.
  - path: discovery/proto_core_angle0_rejected.json
    kind: lp_setup
    one_line: Complete 16-type canonical-SCM response-function setup, observable-law constraints, PN loading, and sign-free versus mediator-monotone polytopes.
  - path: logs/stages/_d-0-5__mode-revise-vn-1-kernel-preserved.log
    kind: counterexample
    one_line: Raw v6 audit containing the exact lower-endpoint equality that rules out simultaneous strict gains and identifies upper-only tightening as the surviving result.
seeds_burned: []
proof_attempt_summary: |
  The discovery phase attempted a field-tier observable threshold for strict contraction of the
  sharp PN interval after deleting mediator-defier response types, together with closed-form
  endpoint gaps and tie-aware inference. Exact response-type enumeration showed that the lower
  endpoints always coincide, L0=L1, so the proposed open region with both endpoint gains cannot
  exist. Proper containment through upper-endpoint tightening remains sound, but its finite
  transportation-LP iff and gap were independently assessed as subfield/routine; the run stopped
  before D0 derivation or Lean formalization.
banked_on: "2026-07-15"
---

# scm_mediator_monotonicity_pn_v1 / mediator_defier_gap — Downgraded

**Topic.** On the confounded complete-mediation graph X->M->Y (X randomized, M<->Y confounded by an unmeasured U, all binary), characterize when mediator monotonicity M_1>=M_0 strictly tightens the SHARP sign-free response-function bound on the probability of necessity PN=P(Y_{x=0}=0 | X=1,Y=1). Deliver: the sharp sign-free bound [L0,U0] using the full experimental law P(M,Y|do(x)); the sharp monotonicity-restricted bound [L1,U1] (delete mediator-defier response types), whose endpoints are closed-form max/min-of-affine functionals via finite canonical-SCM-type vertex enumeration; and THE KERNEL: a necessary-and-sufficient computable threshold T(P) plus closed-form gap for strict containment [L1,U1] strictly-inside [L0,U0], attributable specifically to the deleted mediator-defier coupling, proven strict on a nonempty open set of compatible distributions. Estimation rung: X-randomized plug-in endpoint estimators with Fang-Santos directional-delta / intersection-bounds inference valid at the nonsmooth ties.

**Novelty target.** field

**Stage -0.5 verdict.** NO-PASS

**Stage 0.5 verdict.** NA

**Banking reason.** Independent validity gate: the original proper-containment result is sound only through upper-endpoint tightening; L0=L1 universally, and the surviving upper-only iff/gap is subfield rather than the requested field tier.

## Key files

- `state.json` — pipeline state at banking (`banked: true`, tier `downgraded`).
- `discovery/proto_core_angle0_rejected.json` — final substantive proposal core and finite response-type LP setup.
- `reviews/reviews.jsonl` and `reviews/angle0_v*.json` — per-round D-0.5 reviewer receipts.
- `orchestrator/decision_log.jsonl` — root-fix, terminal consultation, and below-floor reclassification receipts.
- `logs/stages/_d-0-5__mode-revise-vn-1-kernel-preserved.log` — raw v6 lower-endpoint collapse audit.

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
