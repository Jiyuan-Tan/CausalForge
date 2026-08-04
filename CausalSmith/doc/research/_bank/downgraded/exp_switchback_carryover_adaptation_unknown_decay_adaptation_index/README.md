---
qid: exp_switchback_carryover_adaptation
spec: unknown_decay_adaptation_index
topic: "is adaptation to an unknown carryover-decay scale free in switchback experimental design: in the design-based regime with one unit, horizon T, binary assignment path W in {0,1}^T and a FIXED potential-outcome array Y_t : {0,1}^t -> [-B,B] (all randomness in the assignment, no outcome noise), restrict carryover NOT by a distributed-lag functional form but by an impulse-response envelope on the potential-outcome map itself, Yc(w) := { Y : |Y_t(z_{1:t}) - Y_t(z'_{1:t})| <= sum_{l<t} w_l 1{z_{t-l} != z'_{t-l}}; |Y_t| <= B }, and take the nested scale Pc_beta := Yc(w^{(beta)}) with w^{(beta)}_l = C(1+l)^{-(1+beta)} for beta in [beta_lo,beta_hi], so beta' > beta implies Pc_{beta'} subset Pc_beta; for the design-identified GATE_T(Y) = (1/T) sum_t [Y_t(1_{1:t}) - Y_t(0_{1:t})], let D_T be ALL randomized assignment rules L(W_t | W_{1:t-1}, Y^obs_{1:t-1}) (fully sequential rules included, non-adaptive designs a subclass), define the oracle minimax risk R_T(beta) := inf over pi in D_T, inf over theta_hat, sup over Y in Pc_beta of E_pi|theta_hat - GATE_T(Y)| and the ADAPTATION INDEX A_T := inf over pi in D_T, inf over theta_hat, sup over beta in [beta_lo,beta_hi] of (sup over Y in Pc_beta of E_pi|theta_hat - GATE_T(Y)|)/R_T(beta), and settle the dichotomy (K1) A_T -> infinity, so no design — including sequential ones that re-target using realized past outcomes — matches the beta-aware oracle simultaneously up to a T-free constant, adaptation is never free; and (K2) A_T = T^{o(1)}, so knowledge of beta is worth no power of T. The exact orders of A_T and R_T(beta), the optimal block geometry in beta, the multiscale design and selection rule attaining (K2), the two-class construction attaining (K1), and all constants are DELEGATED. This is the min-over-designs-max-over-the-PAIR (array, decay index) problem that Bojinov-Simchi-Levi-Zhao Thm 2 and Yu-Ma-Liu Thm 2 never pose, both holding the carryover order KNOWN"
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "The problem remains mathematically sound and promising, but the current solver could not prove the policy-uniform shifted/multiscale cadence dichotomy needed for a matching carryover-sensitive oracle lower bound."
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - 'The central unknown-decay adaptation object is not characterized: the note proves only 1 <= A_T(C) <= O(T^(1/(4 beta_- + 2))), while divergence, subpolynomial adaptation, and sharp order all remain open.'
  - 'The claimed beta-aware exponent is only an achievability ceiling because the converse is the generic no-carryover T^(-1/2) obstruction, which does not match T^(-beta/(2 beta + 1)).'
  - 'The exact constant 8e-4 applies to an auxiliary homogeneous-history variance, not estimator risk, maximal bias, or minimax risk, so it cannot supply the missing sharpness.'
reusable_artifacts:
  - path: discovery/core.json
    kind: other
    one_line: 'Typed theorem graph containing the exact finite Markov variance certificate, conditional replacement bound, B-risk homogeneous selector, supported-prior lower bounds, and the open adaptation kernel.'
  - path: discovery/writeup.tex
    kind: other
    one_line: 'Rendered derivation of the sound subfield-tier result, including V-dagger, E-cond, exact endpoints, and all no-overclaim qualifications.'
  - path: discovery/open_obligations.json
    kind: other
    one_line: 'Canonical unresolved K1/K2 obligation and the policy-uniform cross-law gap that a stronger solver must close.'
  - path: reviews/review_general.json
    kind: other
    one_line: 'Cold general-referee field-floor assessment identifying the unmatched oracle exponent and exact lift required for field tier.'
  - path: orchestrator/decision_log.jsonl
    kind: counterexample
    one_line: 'Auditable maximality and feasibility receipts, including the sparse-switch cadence obstruction to complementing the current lower-bound certificates.'
seeds_burned: []
proof_attempt_summary: |
  The run derived a sound finite-horizon switchback theory: an exact worst-case
  auxiliary variance V-dagger with sharp uniform coefficient 8e-4, a conditional
  replacement certificate, an exact B-risk homogeneous-path selector, and
  policy-uniform supported-prior/binomial lower floors. The field-tier lift
  attempted to match the beta-aware oracle upper exponent, but the rough-prior
  low-energy and smooth-block certificates are not complementary: a deterministic
  sparse-switch cadence has zero monochromatic-block certificate while its rough
  energy is of order T times the squared band amplitude. Retry only with a
  genuinely new shifted or multiscale policy-uniform cadence dichotomy; do not
  assume that missing complementarity as a premise.
banked_on: "2026-07-31"
---

# exp_switchback_carryover_adaptation / unknown_decay_adaptation_index — Downgraded

**Topic.** is adaptation to an unknown carryover-decay scale free in switchback experimental design: in the design-based regime with one unit, horizon T, binary assignment path W in {0,1}^T and a FIXED potential-outcome array Y_t : {0,1}^t -> [-B,B] (all randomness in the assignment, no outcome noise), restrict carryover NOT by a distributed-lag functional form but by an impulse-response envelope on the potential-outcome map itself, Yc(w) := { Y : |Y_t(z_{1:t}) - Y_t(z'_{1:t})| <= sum_{l<t} w_l 1{z_{t-l} != z'_{t-l}}; |Y_t| <= B }, and take the nested scale Pc_beta := Yc(w^{(beta)}) with w^{(beta)}_l = C(1+l)^{-(1+beta)} for beta in [beta_lo,beta_hi], so beta' > beta implies Pc_{beta'} subset Pc_beta; for the design-identified GATE_T(Y) = (1/T) sum_t [Y_t(1_{1:t}) - Y_t(0_{1:t})], let D_T be ALL randomized assignment rules L(W_t | W_{1:t-1}, Y^obs_{1:t-1}) (fully sequential rules included, non-adaptive designs a subclass), define the oracle minimax risk R_T(beta) := inf over pi in D_T, inf over theta_hat, sup over Y in Pc_beta of E_pi|theta_hat - GATE_T(Y)| and the ADAPTATION INDEX A_T := inf over pi in D_T, inf over theta_hat, sup over beta in [beta_lo,beta_hi] of (sup over Y in Pc_beta of E_pi|theta_hat - GATE_T(Y)|)/R_T(beta), and settle the dichotomy (K1) A_T -> infinity, so no design — including sequential ones that re-target using realized past outcomes — matches the beta-aware oracle simultaneously up to a T-free constant, adaptation is never free; and (K2) A_T = T^{o(1)}, so knowledge of beta is worth no power of T. The exact orders of A_T and R_T(beta), the optimal block geometry in beta, the multiscale design and selection rule attaining (K2), the two-class construction attaining (K1), and all constants are DELEGATED. This is the min-over-designs-max-over-the-PAIR (array, decay index) problem that Bojinov-Simchi-Levi-Zhao Thm 2 and Yu-Ma-Liu Thm 2 never pose, both holding the carryover order KNOWN

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REVISE

**Banking reason.** d0_5_below_field_policy_uniform_cadence_barrier

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

This is a good problem with sound subfield-tier mathematics, not a refuted
topic. The `solver_blocked` / `retry` classification is intentional: future
work should reuse the finite certificates and lower-bound priors, then attack
the policy-uniform cadence/multiscale lemma directly. Do not present the current
polynomial adaptation bracket as the sharp adaptation frontier.
