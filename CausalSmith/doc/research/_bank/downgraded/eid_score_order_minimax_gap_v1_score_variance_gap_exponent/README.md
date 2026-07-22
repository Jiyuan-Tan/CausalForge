---
qid: eid_score_order_minimax_gap_v1
spec: score_variance_gap_exponent
topic: "First minimax lower bound for score-matching topological-order recovery in nonlinear additive-Gaussian ANM SCMs, indexed by SCORE's native leaf/non-leaf score-variance gap C_m = min over non-leaf j of Var[d s_j/d x_j]: construct an explicit mirror-symmetric two-hypothesis family P_+(delta), P_-(delta) of opposite-order ANMs meeting at the direction-unidentifiable linear-Gaussian center P_0, with equal gap C_m(delta)=c1*delta^2 by the x<->y exchange symmetry and nonzero tangent-score difference c2=E_{P_0}[(v_+ - v_-)^2]>0 iff mechanism curvature g''!=0; via Chernoff information C*(delta)=(c2/8c1)*C_m(delta)+o(C_m(delta)) prove the asymptotic minimax order-error inf_pi max Pr[wrong]=exp[-n(C*+o_n(1))] under an explicit iterated delta->0, n->infinity limit -- the first converse for SCORE (Zhu-Locatello-Cevher NeurIPS'23, whose exp(-Theta(n C_m^2)) guarantee is an upper bound only), settling whether the sharp score-gap exponent is linear C_m (SCORE suboptimal) or C_m^2 (matched), with a curvature-normalized leaf detector attaining the sharp exponent as the estimation rung"
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "The discharged result is a pointwise Chernoff calculation for one hand-specified mirror pair, not a SCORE-method lower/upper frontier."
  - "The score-contrast result supplies neither a concrete trainer satisfying the Jacobian-estimability assumption nor an attainable error exponent."
  - "The explicit learner plus coefficient-one Chernoff lift was not feasible under the pointwise C3/envelope primitives without materially changing the kernel."
reusable_artifacts:
  - kind: witness
    path: discovery/core.json
    one_line: "Sound five-result mirror-path core: C_m(delta) and Chernoff information are both linear in delta^2, with the local minimax elbow proved."
  - kind: other
    path: discovery/writeup.tex
    one_line: "Deterministically rendered derivation of the sound v18 core; this, not the later rejected pivot proposal, is the authoritative note."
  - kind: literature_map
    path: reviews/review_general.json
    one_line: "Cold-referee subfield assessment and exact field-lift obstruction/direction."
seeds_burned: []
proof_attempt_summary: |
  The v18 core proves a mirror-symmetric two-hypothesis local-information result:
  five statements are discharged and the primitive tilted-attainability problem
  remains explicitly open. Repeated field-lift attempts could not honestly derive
  a law-independent score-Jacobian learner attaining the Chernoff constant from the
  stated primitives; later adaptation and generic-noise pivots were rejected and
  are retained only as audit history. The user stopped further iteration and banked
  the sound kernel at subfield tier.
banked_on: "2026-07-15"
---

# eid_score_order_minimax_gap_v1 / score_variance_gap_exponent — Downgraded

**Topic.** First minimax lower bound for score-matching topological-order recovery in nonlinear additive-Gaussian ANM SCMs, indexed by SCORE's native leaf/non-leaf score-variance gap C_m = min over non-leaf j of Var[d s_j/d x_j]: construct an explicit mirror-symmetric two-hypothesis family P_+(delta), P_-(delta) of opposite-order ANMs meeting at the direction-unidentifiable linear-Gaussian center P_0, with equal gap C_m(delta)=c1*delta^2 by the x<->y exchange symmetry and nonzero tangent-score difference c2=E_{P_0}[(v_+ - v_-)^2]>0 iff mechanism curvature g''!=0; via Chernoff information C*(delta)=(c2/8c1)*C_m(delta)+o(C_m(delta)) prove the asymptotic minimax order-error inf_pi max Pr[wrong]=exp[-n(C*+o_n(1))] under an explicit iterated delta->0, n->infinity limit -- the first converse for SCORE (Zhu-Locatello-Cevher NeurIPS'23, whose exp(-Theta(n C_m^2)) guarantee is an upper bound only), settling whether the sharp score-gap exponent is linear C_m (SCORE suboptimal) or C_m^2 (matched), with a curvature-normalized leaf detector attaining the sharp exponent as the estimation rung

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REVISE

**Banking reason.** Math-sound mirror-path Chernoff and minimax result, but the explicit score-Jacobian learner and attainable sharp exponent remain open; cold referee tiered the delivered kernel subfield below the requested field floor.

## Key files

- `state.json` — complete pipeline and banking state (`banked: true`).
- `discovery/core.json` — authoritative sound v18 typed core: five proved results plus one open OEQ.
- `discovery/writeup.tex` — authoritative deterministic v18 derivation note.
- `reviews/review_general.json` — cold-referee `subfield < field` verdict and lift directive.
- `orchestrator/decision_log.jsonl` — full revision, adjudication, rollback-fix, stop, and banking receipts.

## Notes

The active proposal cursor had moved to later rejected adaptation/generic-noise
pivots when banking was requested. Those proposal artifacts are audit history,
not the banked mathematical contribution. Reuse `discovery/core.json` and
`discovery/writeup.tex`; any future return to this topic should use a genuinely
different kernel rather than resume the exhausted learner-attainment loop.
