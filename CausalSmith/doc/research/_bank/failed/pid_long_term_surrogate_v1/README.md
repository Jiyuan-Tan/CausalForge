---
qid: pid_long_term_surrogate
spec: v1
topic: "Sharp partial identification of long-term ATE when the surrogate-index assumption fails through unobserved post-surrogate drift, using multiple noisy surrogates and a short experimental panel"
novelty_target: field
tier_at_proposal: NO-PASS
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - 'Theorem 1: N-repo — The binary dilation theorem is a simplified version of the archived same-qid transport endpoint machinery, with the hard endpoint projection/pasting issue assumed away.'
  - 'Conjecture 1: N-repo — The flagship kernel still reads as generic finite-support transport sharpness after reducing all short-panel content to [ell_d,u_d]; this is below novelty_target=field.'
  - 'Conjecture 2: N-repo — The point-ID phase diagram is algebra from the dilation interval, not a distinct field-tier surrogate-index theorem.'
  - 'Overall: N-thin-survey — The proposal misses closer repair directions already identified in the rewind context: minimal noisy-panel strict-tightening, common-kernel bridge compatibility, or a sharp counterexample.'
  - 'Stage 0.5 novelty reject: The actual derivation is below the orchestrator floor novelty_target=field. The main proved content is generic finite-LP sharpness, a generic support-face endpoint-extension criterion, a known surrogate-index no-drift corner, and a sign test that is algebraically equivalent to theta_L>0 or theta_U<0 after defining residuals from the sharp endpoints.'
  - 'Stage 0.5 correctness: prop:point-collapse incorrectly infers no drift from rho=0 even though the stated cost c is only nonnegative and may have zero-cost off-diagonal transitions.'
  - 'Stage 0.5 correctness: prop:sign-boundary — r_- and r_+ are defined as mu_SI minus theta_L and theta_U minus mu_SI, making the sign condition tautological after the dilation interval is in hand.'
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  The pipeline attempted a drift-radius phase diagram for sharp long-term surrogate-index ATE bounds under bounded post-surrogate binary drift, anchored to HuangWangYuanZhaoZhang2026's failure mode. Across three angles and thirteen iterations, the derivation repeatedly collapsed to generic finite-LP/support-function machinery: Theorem 1 became a trivial closed-form dilation of terminal-prevalence intervals (Manski-class outer bound), and the two flagship conjectures reduced to algebraic corollaries of that interval rather than a genuine field-tier strict-tightening result. The math area is sound and reviewers named three viable field-tier repair paths — a proved K=2,J=1 strict-tightening criterion, a common-kernel bridge compatibility statement, or a sharp counterexample — but no attempt delivered the promised observed-increment characterization; the derivation was the bottleneck, not the conjecture.
banked_on: "2026-05-15"
---

# pid_long_term_surrogate / v1 — Failed

**Topic.** Sharp partial identification of long-term ATE when the surrogate-index assumption fails through unobserved post-surrogate drift, using multiple noisy surrogates and a short experimental panel

**Novelty target.** field

**D-0.5 verdict.** NO-PASS

**D0.5 verdict.** REJECT

**Banking reason.** D-0.5 NO-PASS after rejection-context-aware reflow: angle 0 v5 cap-exhausted REVISE, angle 1 v1-v5 cap-exhausted REVISE, angle 2 v1 REJECT; topic cannot reach field tier under post-stage-0.5 kernel critique (drift-aware surrogate-panel partial ID collapses to Manski-class outer containment in every survived angle).

## Key files

- `pid_long_term_surrogate_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_long_term_surrogate_v1_proposal.tex` — final proposal version.
- `pid_long_term_surrogate_v1.tex` — derivation note (if D0 ran).
- `pid_long_term_surrogate_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `pid_long_term_surrogate_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
