---
qid: stat_rosenbaum_lf_family_minimax
spec: stat
topic: "The least-favorable family of Rosenbaum sensitivity analysis (bridge: matched-study Gamma-sensitivity x Huber-Strassen minimax robust testing): for matched pairs with the alternative separated from the Gamma-null polytope (Q_i(n_i)/Q_i(1) > Gamma_i), the all-tests worst-case power frontier equals the NP frontier of the single extreme-tilt least-favorable pair; for matched sets of size >= 3 the single pair provably fails at high levels (verified level-dependent LF switch, extreme-tilt calibration invalid at alpha=0.7) and is replaced by a level-indexed least-favorable MIXTURE family supported on Q-monotone Gamma-tilts; deliverables: the Rosenbaum validity region A (levels where classical extreme-tilt calibration is minimax-sharp among ALL tests), the design-sensitivity envelope Gamma-tilde* on the common-Gamma ray (ceiling of the statistic-choice program, McNemar-consistent on pairs), and the two-sided strict-improvement region over the Bonferroni-doubled practice (verified strict gap 0.158 at Gamma=2, exact equality at Gamma=1); consumers sensitivitymv/senfm and two-sided sensitivity reporting"
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The field-tier promise requires an implementable level-indexed least-favorable procedure and the exact joint two-sided improvement region, not only a finite diagnostic and Q-known oracle ceiling."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The asserted terminal-block contribution is an LP-duality equivalence for a self-selected support family (D_B=D_V), but the positioning identifies no closest published terminal-block/least-favorable-support workflow or theorem that this certificate improves upon; as written it is a useful finite diagnostic, not a demonstrated field-opening Stat advance."
  - "The Q-known fixed-record oracle boundary follows from an explicit separator below q(m)/q(1) and null-polytope membership above it; the node itself disclaims an estimator, selected statistic, new general design-sensitivity regime, or optimal exponent, so it does not independently clear the injected field novelty floor."
  - "This counterexample has a concrete witness but names no specific published estimator, paper, or workflow that imposes the refuted coordinatewise-monotonicity restriction, so it cannot support the claimed negative-result positioning without a target comparison."
reusable_artifacts:
  - "discovery/core.json — typed theorem graph, exact LP/dual/KKT characterization, pair frontier, validity-region topology, replicated oracle boundary, and dependency metadata."
  - "discovery/writeup.tex — complete proved discovery note with the m=3 alpha=0.7 support switch, 84-vertex monotonicity-loss certificate, and repeated-design separator."
  - "discovery/writeup.pdf — clean 20-page rendered discovery artifact."
  - "discovery/d0_working.json — serialized Stage-0 constructions and exact finite witnesses."
  - "discovery/d0_escalation_log.jsonl — construction/directive history; consult before attempting extensions."
  - "orchestrator/decision_log.jsonl — maximality, D0.5, terminal, and independent Codex-validity receipts."
seeds_burned:
  - index: 0
    one_liner: "Level-indexed least-favorable mixtures characterize the all-tests Rosenbaum power frontier in matched sets with multiple controls."
    reason: "The finite all-tests LP/oracle-boundary package is sound at subfield tier but exhausted as a field-level headline; reuse it only as substrate for a genuinely broader implementable theorem."
proof_attempt_summary: |
  Stage 0 proved the pair all-tests NP frontier, the finite product-vertex LP and least-favorable-mixture dual, exact validity-region topology, a high-level m=3 support switch, a strict monotonicity-loss witness, and the fixed-Q replicated oracle boundary. The math panel passed, but directed D0.R positioning edits could not make the finite LP diagnostic or restricted oracle theorem clear the field novelty floor; an independent gpt-5.6-sol validity gate assessed the achieved tier as subfield. A follow-on field run should reuse these results as lemmas and add a genuinely implementable level-indexed procedure plus the exact joint two-sided improvement region rather than re-proposing the oracle package.
banked_on: "2026-07-17"
---

# stat_rosenbaum_lf_family_minimax / stat — Downgraded

**Topic.** The least-favorable family of Rosenbaum sensitivity analysis (bridge: matched-study Gamma-sensitivity x Huber-Strassen minimax robust testing): for matched pairs with the alternative separated from the Gamma-null polytope (Q_i(n_i)/Q_i(1) > Gamma_i), the all-tests worst-case power frontier equals the NP frontier of the single extreme-tilt least-favorable pair; for matched sets of size >= 3 the single pair provably fails at high levels (verified level-dependent LF switch, extreme-tilt calibration invalid at alpha=0.7) and is replaced by a level-indexed least-favorable MIXTURE family supported on Q-monotone Gamma-tilts; deliverables: the Rosenbaum validity region A (levels where classical extreme-tilt calibration is minimax-sharp among ALL tests), the design-sensitivity envelope Gamma-tilde* on the common-Gamma ray (ceiling of the statistic-choice program, McNemar-consistent on pairs), and the two-sided strict-improvement region over the Bonferroni-doubled practice (verified strict gap 0.158 at Gamma=2, exact equality at Gamma=1); consumers sensitivitymv/senfm and two-sided sensitivity reporting

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** Math PASS, but the finite LP diagnostic and fixed-record Q-known oracle boundary remain below the requested field novelty floor after directed revision and independent validity gating.

## Key files

- `stat_rosenbaum_lf_family_minimax_stat_state.json` — pipeline state at banking (`banked: true`).
- `stat_rosenbaum_lf_family_minimax_stat_proposal.tex` — final proposal version.
- `stat_rosenbaum_lf_family_minimax_stat.tex` — derivation note (if Stage 0 ran).
- `stat_rosenbaum_lf_family_minimax_stat_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `stat_rosenbaum_lf_family_minimax_stat_reviews/` — per-version reviewer JSON files (if present).

## Notes

The mathematics is sound and should be lifted, not re-derived. Seed 0 is burned only as a field-level
headline; the two-sided joint-calibration and practical-statistic seeds remain available for a new run.
