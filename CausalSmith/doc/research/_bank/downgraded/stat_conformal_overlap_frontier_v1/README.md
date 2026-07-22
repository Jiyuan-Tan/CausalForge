---
qid: stat_conformal_overlap_frontier
spec: v1
topic: "Matched minimax EXCESS-LENGTH rate for distribution-free (conformal) coverage of a stochastic-intervention (modified-treatment-policy / incremental) potential outcome Y^g in [0,1] under a heavy density-ratio tail, regime gamma0 in (1,2). Weighted-conformal weight w=g/pi (density ratio, E[w|X]=1), overlap = the density-ratio tail P(w>u)<=C u^{-gamma0} so E[w^2]=inf. Over class W(gamma0,s,beta) [GPS sup-rate n^{-s/(2s+d)}, outcome regression beta-Holder], the minimax high-probability excess length over the oracle weighted-conformal interval of connected, training-conditionally-(1-alpha)-valid distribution-free intervals is ≍ n^{-rho}, with rho(gamma0,s,beta)=(gamma0-1)*min{a,1/gamma0}, a=s/(2s+d)+beta/(2beta+d): (UPPER) a tail-aware cross-fit DOUBLY-ROBUST-ORTHOGONAL clipped-WCP (clip w at 1/b_n, b_n=n^{-min{a,1/gamma0}}, Neyman-orthogonal conformity score) is training-conditionally valid with high-probability excess length <= n^{-rho}; (LOWER, the core) a Le Cam two-point construction differing only in the thin-overlap heavy-w region forces excess length >= n^{-rho}. Named objects: the conformal excess-length exponent rho and its linear (gamma0-1) density-ratio-tail dependence. The finite-sample distribution-free companion to Dorn arXiv:2504.13273; differs from Yang-Kuchibhotla-Tchetgen 2024 (asymptotic/generic), Verhaeghe 2409.20412 / Schroder 2407.03094 (WCP method, imported coverage, no rate/exponent/converse), and Diaz-Hejazi/Kennedy (asymptotic efficient estimation, no distribution-free coverage)."
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The proposed matched n^{-rho} learned-weight frontier was not supportable; the maximized sound result is a below-field fixed-list robust-WCP degeneracy and support-rich obstruction diagnostic."
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - >-
    thm:sample-regret-degeneracy: The zero-regret repair is a fixed-list
    specialization of the randomized coverage--length gaming pathology already
    attributed to Min--Lu--Li--Zhang--Teng; with a self-defined chance loss and
    a constructed SR-infinity witness, it is a useful diagnostic but does not
    yet establish the field-level frontier advance required by the injected
    floor.
  - >-
    thm:population-length-frontier-degeneracy: The order-one obstruction is
    carefully scoped and usable, but it is an existential support-rich
    counterexample under the newly introduced SR-infinity condition rather than
    a comparison theorem that separates the closest robust-conformal or
    length-optimization result class; it supports a subfield diagnostic, not
    the required field positioning.
reusable_artifacts:
  - path: discovery/core.json
    role: >-
      Authoritative typed core containing the normalized CDF envelope,
      divisible-support population witness, finite-list heavy-tail control, and
      exact-zero marginal-regret construction.
  - path: discovery/writeup.tex
    role: >-
      Maximized proof note; D0 passed whole-paper mathematical, dependency, and
      two-pass TeX validation.
  - path: discovery/writeup.pdf
    role: Verified 26-page rendered proof note.
  - path: reviews/review_math.json
    role: Independent D0.5 mathematical review with verdict pass.
  - path: reviews/review_rubric.json
    role: Field-novelty findings that triggered the downgraded terminal verdict.
  - path: logs/d0_5_verdict_codex_20260716T121924Z.log
    role: Codex terminal-vs-fixable adjudication establishing below-field reachability.
seeds_burned:
  - index: 0
    one_liner: "A matched heavy-tail oracle-excess-length frontier for learned stochastic-intervention WCP, with a shell-local Le Cam converse."
    reason: "The field-tier matched excess-length frontier is unreachable under this frozen kernel; field novelty requires a new criterion, stronger quantile assumptions, list-learning/identification structure, or new comparison theory."
  - index: 1
    one_liner: "A critical-tail (gamma=1) logarithmic correction and an honest adaptation-impossibility theorem for clipped causal WCP."
    reason: "The field-tier matched excess-length frontier is unreachable under this frozen kernel; field novelty requires a new criterion, stronger quantile assumptions, list-learning/identification structure, or new comparison theory."
  - index: 2
    one_liner: "A uniform shell-envelope theorem that makes clipped-WCP length comparisons class-uniform rather than law-specific."
    reason: "The field-tier matched excess-length frontier is unreachable under this frozen kernel; field novelty requires a new criterion, stronger quantile assumptions, list-learning/identification structure, or new comparison theory."
  - index: 3
    one_liner: "Sharp sensitivity bounds for causal conformal prediction when the stochastic-intervention density ratio is only approximately correct."
    reason: "The field-tier matched excess-length frontier is unreachable under this frozen kernel; field novelty requires a new criterion, stronger quantile assumptions, list-learning/identification structure, or new comparison theory."
  - index: 4
    one_liner: "A tail-index-adaptive causal WCP oracle inequality, or a matching adaptation penalty, over gamma in (1,2)."
    reason: "The field-tier matched excess-length frontier is unreachable under this frozen kernel; field novelty requires a new criterion, stronger quantile assumptions, list-learning/identification structure, or new comparison theory."
  - index: 5
    one_liner: "The smallest coverage-target inflation required by an estimated stochastic-intervention ratio, together with a lower bound."
    reason: "The field-tier matched excess-length frontier is unreachable under this frozen kernel; field novelty requires a new criterion, stronger quantile assumptions, list-learning/identification structure, or new comparison theory."
  - index: 6
    one_liner: "A known-ratio heavy-tail benchmark: minimax excess length of exact WCP relative to a specified score oracle."
    reason: "The field-tier matched excess-length frontier is unreachable under this frozen kernel; field novelty requires a new criterion, stronger quantile assumptions, list-learning/identification structure, or new comparison theory."
  - index: 7
    one_liner: "Finite-sample robust WCP under a certified density-ratio uncertainty set, with the certificate's heavy-tail length price."
    reason: "The field-tier matched excess-length frontier is unreachable under this frozen kernel; field novelty requires a new criterion, stronger quantile assumptions, list-learning/identification structure, or new comparison theory."
proof_attempt_summary: |
  The run attempted a matched n^{-rho} excess-length frontier for learned
  stochastic-intervention weighted conformal prediction under a heavy
  density-ratio tail. Exact distribution-free coverage with learned weights and
  the proposed rate/converse did not survive scrutiny; the maximized sound
  replacement proves a normalized finite-list CDF envelope, an SR-infinity
  support-rich order-one connected-length obstruction, and eventual exact-zero
  marginal high-probability regret via randomized repair. D0 and the independent
  math panel passed, but D0.5 found these results below the requested field
  novelty floor; a field-tier continuation needs a new risk/validity criterion,
  stronger quantile structure, list-learning/identification assumptions, or new
  comparison theory.
banked_on: "2026-07-16"
---

# stat_conformal_overlap_frontier / v1 — Downgraded

**Topic.** Matched minimax EXCESS-LENGTH rate for distribution-free (conformal) coverage of a stochastic-intervention (modified-treatment-policy / incremental) potential outcome Y^g in [0,1] under a heavy density-ratio tail, regime gamma0 in (1,2). Weighted-conformal weight w=g/pi (density ratio, E[w|X]=1), overlap = the density-ratio tail P(w>u)<=C u^{-gamma0} so E[w^2]=inf. Over class W(gamma0,s,beta) [GPS sup-rate n^{-s/(2s+d)}, outcome regression beta-Holder], the minimax high-probability excess length over the oracle weighted-conformal interval of connected, training-conditionally-(1-alpha)-valid distribution-free intervals is ≍ n^{-rho}, with rho(gamma0,s,beta)=(gamma0-1)*min{a,1/gamma0}, a=s/(2s+d)+beta/(2beta+d): (UPPER) a tail-aware cross-fit DOUBLY-ROBUST-ORTHOGONAL clipped-WCP (clip w at 1/b_n, b_n=n^{-min{a,1/gamma0}}, Neyman-orthogonal conformity score) is training-conditionally valid with high-probability excess length <= n^{-rho}; (LOWER, the core) a Le Cam two-point construction differing only in the thin-overlap heavy-w region forces excess length >= n^{-rho}. Named objects: the conformal excess-length exponent rho and its linear (gamma0-1) density-ratio-tail dependence. The finite-sample distribution-free companion to Dorn arXiv:2504.13273; differs from Yang-Kuchibhotla-Tchetgen 2024 (asymptotic/generic), Verhaeghe 2409.20412 / Schroder 2407.03094 (WCP method, imported coverage, no rate/exponent/converse), and Diaz-Hejazi/Kennedy (asymptotic efficient estimation, no distribution-free coverage).

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** D0.5: TERMINAL-BELOW-FIELD — faithfulness and mathematics pass, but the fixed-list sample degeneracy and existential SR_infinity population obstruction do not meet the requested field novelty floor.

## Key files

- `stat_conformal_overlap_frontier_v1_state.json` — pipeline state at banking (`banked: true`).
- `stat_conformal_overlap_frontier_v1_proposal.tex` — final proposal version.
- `stat_conformal_overlap_frontier_v1.tex` — derivation note (if Stage 0 ran).
- `stat_conformal_overlap_frontier_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `stat_conformal_overlap_frontier_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

The banked result is sound and useful as a negative diagnostic. Future projects
should reuse its finite-list envelope and counterexamples, but should not
re-propose the learned-weight matched exponent under the same marginal-validity
and symmetric-margin kernel.
