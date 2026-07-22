---
qid: stat_gformula_composition_minimax
spec: transition_smoothness_elbow
topic: "Minimax rate for the L=2 longitudinal g-formula outside the sqrt(n) regime: the transition-density smoothness as a first-order structural exponent with no single-time-point counterpart. For psi=E[Y(1,1)] under sequential exchangeability and strict overlap, with unknown alpha_1/alpha_2-Holder propensities, beta-Holder final-period outcome regression, and t-Holder (in h_1, L^1(dh_2)) transition density on [0,1]^d, conjecture the minimax RMSE is n^{-1/2} + n^{-4s_1/(4s_1+d)} + n^{-4s_2/(4s_2+d)} with s_1=(alpha_1+t)/2 and s_2=(alpha_2+beta)/2 -- period 1's index carrying the TRANSITION smoothness t in place of the outcome smoothness beta that governs the L=1 problem of Robins-Li-Tchetgen-van der Vaart -- with sharp elbow: sqrt(n)-estimable iff min{alpha_1+t, alpha_2+beta} >= d/2. Deliver (C1) an attaining cross-fitted sequential-DR/HOIF estimator that eliminates the mixed cross-period remainder arising because m_1hat regresses the estimated pseudo-outcome m_2hat; (C2) the matching lower bound via a CHAINED fuzzy-hypothesis construction carrying the period-1 perturbation in the transition density (sign-paired with the pi_1 perturbation), since m_1=E[m_2|H_1,A_1] is not a free parameter and the L=1 two-factor perturbation of (pi,mu) is legal only under variation independence; (C3) the structural separation, witnessed at large finite t on a specified analytic ball: psi is sqrt(n)-estimable whenever alpha_2+beta >= d/2 for arbitrarily small alpha_1>0. Answers the verbatim open problem of Cinelli-Feller-Imbens-Kennedy-Magliacane-Zubizarreta (arXiv 2508.17099): 'optimality for time-varying treatment effects outside the sqrt(n) regime is entirely open, regardless of the model setup.'"
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "constructive_object_missing"
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - "The proved nonmatching first-order bracket does not establish a field-level advance."
  - "The incoming r1 floor is a legal embedding of Robins et al. (2009), Theorem 3.1; variation dependence does not block transfer."
  - "The upper and lower rates remain unmatched, so the minimax rate and sharp elbow remain open."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.pdf
  - discovery/solve_thm_transition_mediated_converse_first_order_bracket.json
  - reviews/d05_terminal_novelty_gonogo_round19.txt
  - orchestrator/decision_log.jsonl
seeds_burned: []
proof_attempt_summary: |
  D0 proved a qualified incoming-transition lower channel, a standard terminal channel,
  and a computable nonmatching first-order upper bound, including a connected rough-transition
  subclass outside Robins et al. (2016) condition (c2). The field claim collapsed because the
  incoming lower rate transfers from Robins et al. (2009), while no attaining higher-order
  estimator was proved. A future retry must close the upper-rate gap rather than rederive r1.
banked_on: "2026-07-17"
---

# stat_gformula_composition_minimax / transition_smoothness_elbow — Downgraded

**Topic.** Minimax rate for the L=2 longitudinal g-formula outside the sqrt(n) regime: the transition-density smoothness as a first-order structural exponent with no single-time-point counterpart. For psi=E[Y(1,1)] under sequential exchangeability and strict overlap, with unknown alpha_1/alpha_2-Holder propensities, beta-Holder final-period outcome regression, and t-Holder (in h_1, L^1(dh_2)) transition density on [0,1]^d, conjecture the minimax RMSE is n^{-1/2} + n^{-4s_1/(4s_1+d)} + n^{-4s_2/(4s_2+d)} with s_1=(alpha_1+t)/2 and s_2=(alpha_2+beta)/2 -- period 1's index carrying the TRANSITION smoothness t in place of the outcome smoothness beta that governs the L=1 problem of Robins-Li-Tchetgen-van der Vaart -- with sharp elbow: sqrt(n)-estimable iff min{alpha_1+t, alpha_2+beta} >= d/2. Deliver (C1) an attaining cross-fitted sequential-DR/HOIF estimator that eliminates the mixed cross-period remainder arising because m_1hat regresses the estimated pseudo-outcome m_2hat; (C2) the matching lower bound via a CHAINED fuzzy-hypothesis construction carrying the period-1 perturbation in the transition density (sign-paired with the pi_1 perturbation), since m_1=E[m_2|H_1,A_1] is not a free parameter and the L=1 two-factor perturbation of (pi,mu) is legal only under variation independence; (C3) the structural separation, witnessed at large finite t on a specified analytic ball: psi is sqrt(n)-estimable whenever alpha_2+beta >= d/2 for arbitrarily small alpha_1>0. Answers the verbatim open problem of Cinelli-Feller-Imbens-Kennedy-Magliacane-Zubizarreta (arXiv 2508.17099): 'optimality for time-varying treatment effects outside the sqrt(n) regime is entirely open, regardless of the model setup.'

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REVISE

**Banking reason.** D0 mathematics is sound, but D0.5 found field novelty unmet: the incoming r1 lower rate embeds Robins et al. (2009) Theorem 3.1, while the upper and lower rates remain unmatched.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — accepted proposal.
- `discovery/writeup.pdf` — final D0 derivation note.
- `reviews/reviews.jsonl` — per-round reviewer log.
- `reviews/d05_terminal_novelty_gonogo_round19.txt` — terminal primary-source novelty audit.
- `orchestrator/decision_log.jsonl` — D-orchestrator decisions.

## Notes

The unpublished Bonvini--Kennedy--Keele abstract was disclosed but did not count
against novelty. The decisive comparator was the published Robins et al. (2009)
MAR lower theorem. This entry is marked retryable only for genuinely new
higher-order upper-bound work.
