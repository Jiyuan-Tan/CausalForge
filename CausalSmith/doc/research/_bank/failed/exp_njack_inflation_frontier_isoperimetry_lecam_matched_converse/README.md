---
qid: exp_njack_inflation_frontier
spec: isoperimetry_lecam_matched_converse
topic: "Sharp inflation frontier for recompute-based conservative variance estimation under local interference. Setting: n-cycle, radius-M local interference (N_i={i-M..i+M}), Bernoulli(1/2) design, IPW direct-effect estimator, deterministic potential outcomes. Focal object: the minimax excess inflation R*(M,n) = inf over the ENTIRE Park-Wager (2604.24017) recompute class of rules (mu,g) -- mu any index-sampling law with S independent of W, g any fixed measurable map of the OBSERVED data (S, W_{-S}, {Y_i : N_i cap S = empty}) that must serve the whole class -- of sup over Y in Ycal_n(M;c0,C0) of E[Vhat]/Var(tauhat), where Ycal_n imposes radius-M interference, constant direct effect tau in [-1/2,1/2] (the Neyman-tight class, so the irreducible Neyman floor vanishes and the entire excess is the framework's own price), |Y_i| <= C0, and the UNIFORM ARC-VARIANCE SANDWICH c0|I| <= Var(sum_{i in I} psi_i) <= C0|I| for every arc |I| >= 2M+1. KERNEL (thin, precise conjecture): R*(M,n) = 1 + Theta(sqrt(M/n)) for 1 <= M <= n^{1-delta}, ATTAINED by the anchor's own uniform-random-block rule at L* asymp sqrt(Mn) with the M-padded recompute proxy; (C1) upper bound for that rule, (C2) converse for EVERY (mu,g) in the class. Converse content: oracle half >= cM/L by Fourier/isoperimetry on the cycle via Lemma 10 (the Fourier support sits on windows of diameter <= 2M+1; the inflation is |M-neighbourhood of S|/|S|, so only long components beat it -- and they enlarge the deletion set D); proxy half >= cL/n by a Le Cam two-point argument on tau (g never sees the deleted units' outcomes, and must use a NUISANCE-RICH indistinguishable subfamily, NOT the bare parametric witness, which reveals tau). Pre-anchor: Park-Wager 2604.24017 has ONLY Lemma 11 -- one-sided monotonicity of the ORACLE half, pointing the wrong way -- plus proxy heuristics, and reports its U-shape in L empirically with oracle-tuned L. Our theorem is not Harshaw-Middleton-Savje 2112.01709 because that is a QUALITATIVE Loewner-order admissibility characterization over QUADRATIC-form bounds under CORRECTLY SPECIFIED exposure mappings, with a generically-infinite admissible frontier, no rate, no interference radius, and no bound on the MAGNITUDE of unavoidable conservativeness -- misspecified exposures is its own stated open problem. Not Lin-Ding 2510.22864 / Gao-Ding JEcon 252 because those are pointwise-in-bandwidth conservativeness with no optimality and no converse. Why non-trivial: the whole literature has upper bounds only; the converse must hold for EVERY index-sampling law including disconnected and multi-scale ones. Why promising: the M=0 case is exactly solvable (inflation = n/(n-L) = 1 + L/(n-L), optimum L=1, recovering the classical Jackknife) and pins the L/n proxy half, while the anchor's own Prop 3 prefactor (L+2M)/L pins the 1+2M/L oracle half. Reject if the frontier collapses to a routine optimization of Prop 3 without an all-rule converse, if a proxy exploiting the constant-effect restriction imputes deleted units better than n^{-1/2}, or if a multi-scale update set beats 1+cM/L at equal deletion cost."
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "The original field-level kernel is genuinely false over the frozen rule class, and no nontrivial same-assumption replacement supports continuing this field-target run."
  - "The boundary class is admissible and nonempty; boundedness plus the exact arc sandwich forces tau=0; the schedule-uniform empty/full proxy is admissible with exact gap epsilon, positive denominator, and inflation exactly one; and Poincare proves the matching universal floor."
  - "Because the frozen domain and entire rule class expressly include this proxy and multiscale update law, the claimed 1+Theta(sqrt(M/n)) frontier is false."
reusable_artifacts:
  - discovery/writeup.tex
  - discovery/solve_thm_block_upper.json
  - discovery/solve_prop_sutva_calibration.json
  - discovery/solve_oeq_all_rule_converse.json
  - orchestrator/decision_log.jsonl
seeds_burned: []
proof_attempt_summary: |
  The run proved the exact M=0 block calibration, a schedule-uniform 1+O(sqrt(M/n)) upper bound for the padded uniform-block rule, and a universal Poincare inflation floor of one. The requested converse collapsed on the admissible c0=C0=1/4 boundary: the assumptions force tau=0, and an empty/full multiscale update law with a single observable proxy attains the floor exactly. The surviving results are useful receipts, but they do not supply the matched all-rule field-level frontier.
banked_on: "2026-07-16"
---

# exp_njack_inflation_frontier / isoperimetry_lecam_matched_converse — Failed

**Topic.** Sharp inflation frontier for recompute-based conservative variance estimation under local interference. Setting: n-cycle, radius-M local interference (N_i={i-M..i+M}), Bernoulli(1/2) design, IPW direct-effect estimator, deterministic potential outcomes. Focal object: the minimax excess inflation R*(M,n) = inf over the ENTIRE Park-Wager (2604.24017) recompute class of rules (mu,g) -- mu any index-sampling law with S independent of W, g any fixed measurable map of the OBSERVED data (S, W_{-S}, {Y_i : N_i cap S = empty}) that must serve the whole class -- of sup over Y in Ycal_n(M;c0,C0) of E[Vhat]/Var(tauhat), where Ycal_n imposes radius-M interference, constant direct effect tau in [-1/2,1/2] (the Neyman-tight class, so the irreducible Neyman floor vanishes and the entire excess is the framework's own price), |Y_i| <= C0, and the UNIFORM ARC-VARIANCE SANDWICH c0|I| <= Var(sum_{i in I} psi_i) <= C0|I| for every arc |I| >= 2M+1. KERNEL (thin, precise conjecture): R*(M,n) = 1 + Theta(sqrt(M/n)) for 1 <= M <= n^{1-delta}, ATTAINED by the anchor's own uniform-random-block rule at L* asymp sqrt(Mn) with the M-padded recompute proxy; (C1) upper bound for that rule, (C2) converse for EVERY (mu,g) in the class. Converse content: oracle half >= cM/L by Fourier/isoperimetry on the cycle via Lemma 10 (the Fourier support sits on windows of diameter <= 2M+1; the inflation is |M-neighbourhood of S|/|S|, so only long components beat it -- and they enlarge the deletion set D); proxy half >= cL/n by a Le Cam two-point argument on tau (g never sees the deleted units' outcomes, and must use a NUISANCE-RICH indistinguishable subfamily, NOT the bare parametric witness, which reveals tau). Pre-anchor: Park-Wager 2604.24017 has ONLY Lemma 11 -- one-sided monotonicity of the ORACLE half, pointing the wrong way -- plus proxy heuristics, and reports its U-shape in L empirically with oracle-tuned L. Our theorem is not Harshaw-Middleton-Savje 2112.01709 because that is a QUALITATIVE Loewner-order admissibility characterization over QUADRATIC-form bounds under CORRECTLY SPECIFIED exposure mappings, with a generically-infinite admissible frontier, no rate, no interference radius, and no bound on the MAGNITUDE of unavoidable conservativeness -- misspecified exposures is its own stated open problem. Not Lin-Ding 2510.22864 / Gao-Ding JEcon 252 because those are pointwise-in-bandwidth conservativeness with no optimality and no converse. Why non-trivial: the whole literature has upper bounds only; the converse must hold for EVERY index-sampling law including disconnected and multi-scale ones. Why promising: the M=0 case is exactly solvable (inflation = n/(n-L) = 1 + L/(n-L), optimum L=1, recovering the classical Jackknife) and pins the L/n proxy half, while the anchor's own Prop 3 prefactor (L+2M)/L pins the 1+2M/L oracle half. Reject if the frontier collapses to a routine optimization of Prop 3 without an all-rule converse, if a proxy exploiting the constant-effect restriction imputes deleted units better than n^{-1/2}, or if a multi-scale update set beats 1+cM/L at equal deletion cost.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The unrestricted all-rule frontier collapses to one on an admissible boundary class, refuting the proposed positive square-root excess lower bound.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — accepted proposal version.
- `discovery/writeup.tex` — Stage 0 derivation, counterexample, and corrected terminal scope.
- `reviews/reviews.jsonl` — per-round proposal-review log.
- `orchestrator/decision_log.jsonl` — D-stage escalation and independent terminal ruling.

## Notes

The padded-block upper theorem and exact boundary-collapse witness may be
reused independently. The original all-rule square-root frontier should not be
re-raised without materially changing the frozen rule or schedule class.
