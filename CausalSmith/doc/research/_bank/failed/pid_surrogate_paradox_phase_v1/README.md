---
qid: pid_surrogate_paradox_phase
spec: v1
topic: "Principal surrogate paradox phase threshold. Pre-anchor check: closest anchors are Frangakis-Rubin principal stratification and surrogate-paradox results such as Chen-Geng-style causal necessity/sufficiency criteria. Why non-trivial? The target is not another Manski principal-strata LP bound: require a finite binary principal-strata witness class with an explicit sign-reversal threshold where the treatment effect on the surrogate is positive in every observable arm but the principal-stratum effect on the outcome flips sign. Why promising? The nonroutine object is a hand-checkable phase threshold plus endpoint-attaining witness family. If the delta reduces to missing-cell bounds, LP duality, or definition-unfold surrogate criteria, pivot or accept field-tier."
novelty_target: flagship
tier_at_proposal: REJECT
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "angle0_v1: Conjecture 1 was C-definitional-unfold; after Theorem 1, T_R(P)>0 iff L_{1R}-U_{0R}<0 is just the lower-endpoint sign of the identified interval."
  - "angle0_v2: Exhibit 9.1 was itself an average surrogate-paradox law, not a sanity check for average-paradox exclusion plus responder-cell harm."
  - "angle1_v1: D-0.5 rejected the pivot as not-publishable with S=0 N=3 C=4."
  - "angle2_v1: D-0.5 rejected the pivot as not-publishable with S=1 N=4 C=4."
  - "angle3_v3: the final reviewer found the ACS/CEP comparator mischaracterized; Gamma_Y was just the aggregate endpoint treatment effect."
  - "angle3_v3: the claimed phase threshold followed by decomposing Gamma_Y and putting nonresponder effects at binary upper bounds, so it was routine bounded-mixture algebra."
reusable_artifacts:
  - path: pid_surrogate_paradox_phase_v1_gaps.json
    kind: literature_map
    one_line: "Useful map of principal-surrogate paradox anchors and nearby failed/candidate bank entries."
  - path: pid_surrogate_paradox_phase_v1_reviews/angle0_v2.json
    kind: counterexample
    one_line: "Numerical refutation of the angle0 witness: the displayed table computes an average endpoint effect of -0.11."
  - path: pid_surrogate_paradox_phase_v1_reviews/angle3_v3.json
    kind: other
    one_line: "Final stop anchor explaining the ACS/CEP mischaracterization and bounded-mixture algebra collapse."
  - path: pid_surrogate_paradox_phase_v1_proposal_angle0_rejected.tex
    kind: witness
    one_line: "Negative example of the tempting responder frontier T_R(P); useful only to avoid the endpoint-sign definitional-unfold trap."
seeds_burned:
  - index: 0
    one_liner: "Introduce a closed-form responder-stratum frontier T_R(P) for binary monotone principal surrogates and conjecture it is necessary and sufficient for positive-observable, negative-responder surrogate-paradox witnesses."
    reason: "D-0.5 reviews found field-tier definitional endpoint algebra, missing/nonverified witnesses, bad comparator/citation anchors, and not-publishable finite-table claims across angles 0-3."
  - index: 1
    one_liner: "Derive observed-table algebraic inequalities deciding whether two binary P(S,Y|Z) tables admit a principal-surrogate paradox witness without reducing to a generic Manski LP."
    reason: "D-0.5 reviews found field-tier definitional endpoint algebra, missing/nonverified witnesses, bad comparator/citation anchors, and not-publishable finite-table claims across angles 0-3."
  - index: 2
    one_liner: "Classify monotonicity, causal necessity, and no-harm restrictions into impossible, shifted-threshold, and observationally-hidden surrogate-paradox regimes."
    reason: "D-0.5 reviews found field-tier definitional endpoint algebra, missing/nonverified witnesses, bad comparator/citation anchors, and not-publishable finite-table claims across angles 0-3."
  - index: 3
    one_liner: "Show average causal sufficiency has a vacuous worst-responder lower bound by an endpoint-attaining finite binary principal-strata witness."
    reason: "D-0.5 reviews found field-tier definitional endpoint algebra, missing/nonverified witnesses, bad comparator/citation anchors, and not-publishable finite-table claims across angles 0-3."
proof_attempt_summary: |
  Attempted a flagship binary principal-surrogate paradox phase theorem with a responder-stratum threshold and endpoint-attaining finite witnesses. The best angle reduced to identified-interval endpoint signs or bounded-mixture algebra, while later pivots either failed finite-table sanity checks or mischaracterized ACS/CEP comparators. Future work should not revive this as a flagship run unless it starts from a verified ACS/CEP or Yin-Liu-Geng-Luo comparator frontier with a hand-derived nonroutine witness/certificate.
banked_on: "2026-05-25"
---

# pid_surrogate_paradox_phase / v1 — Failed

**Topic.** Principal surrogate paradox phase threshold. Pre-anchor check: closest anchors are Frangakis-Rubin principal stratification and surrogate-paradox results such as Chen-Geng-style causal necessity/sufficiency criteria. Why non-trivial? The target is not another Manski principal-strata LP bound: require a finite binary principal-strata witness class with an explicit sign-reversal threshold where the treatment effect on the surrogate is positive in every observable arm but the principal-stratum effect on the outcome flips sign. Why promising? The nonroutine object is a hand-checkable phase threshold plus endpoint-attaining witness family. If the delta reduces to missing-cell bounds, LP duality, or definition-unfold surrogate criteria, pivot or accept field-tier.

**Novelty target.** flagship

**Stage -0.5 verdict.** REJECT

**Stage 0.5 verdict.** NA

**Banking reason.** Stopped early after repeated D-0.5 failures: angle 0 stayed field-tier after three revisions, angles 1 and 2 were not-publishable, and angle 3 stayed field-tier then rejected; the surrogate-paradox phase topic collapsed into routine/broken finite-table algebra rather than a flagship object.

## Key files

- `pid_surrogate_paradox_phase_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_surrogate_paradox_phase_v1_proposal.tex` — final proposal version.
- `pid_surrogate_paradox_phase_v1.tex` — derivation note (if Stage 0 ran).
- `pid_surrogate_paradox_phase_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_surrogate_paradox_phase_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

Reflection: this was a topic/proposal-strength failure. The literature map found real adjacent surrogate-paradox material, but every attempted kernel stayed below the flagship bar or became mathematically incoherent. No pipeline bug was observed after launch; the run was manually stopped after repeated D-0.5 failures and then banked with `bank_entry.ts`.
