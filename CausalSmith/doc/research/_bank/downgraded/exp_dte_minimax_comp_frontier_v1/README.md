---
qid: exp_dte_minimax_comp_frontier
spec: v1
topic: "Resolve the sharp computational minimax frontier for the direct treatment effect under q=2 arbitrary neighborhood interference on known d-regular networks. Define R_2(G) as the infimum worst-case MSE over every assignment law and measurable estimator, and kappa_DTE(d) as the best uniform factor with which a randomized polynomial-time algorithm outputs an implementable design-estimator plus a valid upper risk certificate. Under the Unique Games Conjecture together with NP not contained in BPP, prove kappa_DTE(d)=d^(1/2+o(1)): for every epsilon>0 no d^(1/2-epsilon) approximation works on all sufficiently large d, while a polynomial Conflict Graph Design procedure achieves C*sqrt(d). The lower theorem must be a two-sided value-preserving reduction from regular independent set to the special two-layer DTE maximal-independent-set game, with a low-risk YES design and a high-risk NO Le Cam or dual certificate; the published one-sided alpha lower bound, hardness of a proxy, and hardness for one estimator do not suffice. Output the realizable randomization, modified Horvitz-Thompson estimator, and computable upper certificate, and use Fatemi-Zheleva CauseIS as the consumer whose MIS-based DTE benchmarking changes."
novelty_target: flagship
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The advertised sharp computational frontier, including kappa_DTE(d)=d^(1/2+o(1)), is not proved: there is no polynomial-time general-graph approximation algorithm, no Unique-Games hardness theorem, and no value-preserving reduction."
  - "The equal block-clique result is exact only within an invariant linear subclass; its unrestricted lower and upper endpoints generally remain unmatched, except for a single clique."
  - "These are worthwhile specialized lower-bound and symmetric-family results, but they do not resolve the general computational minimax problem named by the project."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_oeq_general_graph_finite_saddle_certificate.json
  - reviews/review_general.json
  - orchestrator/decision_log.jsonl
seeds_burned: []
proof_attempt_summary: |
  The run first attempted the advertised exact-regular, value-preserving
  reduction and computational frontier, but exhausted that angle without a
  realizable two-sided reduction or hardness witness.  The pivot produced a
  sound all-procedure balanced-biclique lower certificate, a rate-sharp
  complete-bipartite calibration, and equal block-clique SDP and finite-prior
  bounds, including the exact unrestricted single-clique case.  A
  polynomial-support constant-factor two-sided certificate for arbitrary
  graphs remains open, so the achieved result is banked at subfield tier.
token_usage:
  complete: true
  orchestrator_tokens: 643595
  pipeline_codex_tokens: 54983065
  pipeline_claude_tokens: 0
  total_tokens_consumed: 55626660
banked_on: "2026-08-28"
---

# exp_dte_minimax_comp_frontier / v1 — Downgraded

**Topic.** Resolve the sharp computational minimax frontier for the direct treatment effect under q=2 arbitrary neighborhood interference on known d-regular networks. Define R_2(G) as the infimum worst-case MSE over every assignment law and measurable estimator, and kappa_DTE(d) as the best uniform factor with which a randomized polynomial-time algorithm outputs an implementable design-estimator plus a valid upper risk certificate. Under the Unique Games Conjecture together with NP not contained in BPP, prove kappa_DTE(d)=d^(1/2+o(1)): for every epsilon>0 no d^(1/2-epsilon) approximation works on all sufficiently large d, while a polynomial Conflict Graph Design procedure achieves C*sqrt(d). The lower theorem must be a two-sided value-preserving reduction from regular independent set to the special two-layer DTE maximal-independent-set game, with a low-risk YES design and a high-risk NO Le Cam or dual certificate; the published one-sided alpha lower bound, hardness of a proxy, and hardness for one estimator do not suffice. Output the realizable randomization, modified Horvitz-Thompson estimator, and computable upper certificate, and use Fatemi-Zheleva CauseIS as the consumer whose MIS-based DTE benchmarking changes.

**Novelty target.** flagship

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The maximized sound result reaches subfield tier but does not prove the advertised flagship computational frontier.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The terminal boundary review also records archival hygiene that was not
tier-lifting: narrow the Proposition 2.2 cited leaf and its direct consumers,
delete the two obsolete clique calibrations, and synchronize current topic and
novelty metadata without rewriting the historical receipts.  Any reuse should
preserve conditional equal-block equality except at `b=1`, avoid claiming
polynomial-time optimization of `beta_DTE`, and keep the efficient general
two-sided saddle open.
