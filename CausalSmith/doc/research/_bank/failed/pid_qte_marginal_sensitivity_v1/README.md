---
qid: pid_qte_marginal_sensitivity
spec: v1
topic: "Sharp partial identification of conditional quantile treatment effects under marginal Rosenbaum-style sensitivity, where the worst-case odds ratio of treatment-assignment is bounded covariate-by-covariate, with closed-form quantile-curve envelopes recovering Manski-Pepper at the trivial bound and point identification under unconfoundedness"
novelty_target: field
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - 'Theorem 1 | Conjectures 1-2 — N-thin-survey: tier=letter below novelty_target=field; the arbitrary-K rank gap and quotient certificate still read as a finite-algebra audit layer over Wang2026 process envelopes plus Winkler1988 moment geometry unless tied to a sharper inferential or identification theorem.'
  - 'Background Lemma A — overall_verdict: already-known; cite: Tan2006/DornGuo2023/MastenPoirierRen2025/Wang2026: bounded likelihood-ratio and marginal-sensitivity CDF/QTE envelope algebra.'
  - 'Conjecture 1 — overall_verdict: already-known (angle1); cite: Wang2026: closed-form sharp CDF envelopes with source marginal sensitivity and sharp quantile/QTE inversion; MastenPoirierRen2025: sharp QTE bounds for relaxation classes including marginal sensitivity.'
  - 'Endpoint noninformation limit — C-sanity: The displayed Gamma=infinity CDF lower bound e_a(x)F_obs(y) cannot hold at the upper support endpoint, where any valid CDF must equal 1; the endpoint-closure convention needs to be stated explicitly.'
  - 'Banked reason: Stage -0.5 NO-PASS after 15 revises; angle=2 v5 verdict=REVISE tier=letter (below novelty_target=field floor).'
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  The proposal attempted to identify a novel 'Tukey-factor tail collapse' for conditional quantile treatment effects (CQTE) under covariate-wise Rosenbaum odds-ratio bounds, targeting a canonical minimal quotient and finite active-rank certificate for threshold-coded CQTE claims. After 3 angles and 9 review iterations (5 on the final angle), the surviving core — Background Lemma A and a rank-separation witness (Theorem 1) — was rated incremental over Wang2026's process-level QTE envelopes and Winkler1988's moment-set geometry, while Conjectures 1 and 2 remained unproved open questions. The proposal consistently landed at tier=letter instead of the required tier=field, blocked by the N-thin-survey flag: the arbitrary-K rank-gap and quotient-certificate layer was judged an audit abstraction over existing envelope results rather than a field-level inferential or identification advance.
banked_on: "2026-05-15"
---

# pid_qte_marginal_sensitivity / v1 — Failed

**Topic.** Sharp partial identification of conditional quantile treatment effects under marginal Rosenbaum-style sensitivity, where the worst-case odds ratio of treatment-assignment is bounded covariate-by-covariate, with closed-form quantile-curve envelopes recovering Manski-Pepper at the trivial bound and point identification under unconfoundedness

**Novelty target.** field

**D-0.5 verdict.** NO-PASS

**D0.5 verdict.** NA

**Banking reason.** D-0.5 NO-PASS after 15 revises; angle=2 v5 verdict=REVISE tier=letter (below novelty_target=field floor).

## Key files

- `pid_qte_marginal_sensitivity_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_qte_marginal_sensitivity_v1_proposal.tex` — final proposal version.
- `pid_qte_marginal_sensitivity_v1.tex` — derivation note (if D0 ran).
- `pid_qte_marginal_sensitivity_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `pid_qte_marginal_sensitivity_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
