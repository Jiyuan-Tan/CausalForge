---
qid: pid_network_iv_exposure
spec: v3
topic: "Flagship generalization of the banked network-exposure partial-ID result: sharp partial identification of complier direct and spillover effects when both the treatment exposure mapping and the instrumental exposure mapping may be misspecified, bridging exposure-mapping robustness with IV noncompliance and producing a computable finite-network sharp bound plus a small worked witness."
novelty_target: flagship
supersedes:
  parent_qid: "pid_network_exposure"
  parent_spec: "v1"
  parent_tier: "candidates"  # tier retired 2026-07-18; parent re-tiered to _bank/downgraded/
  upgrade_axis: "generalization"
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: "constructive_object_missing"
reusable: unknown
reraise_status: retry
gap_reasons:
  - "Conjecture 1: N-no-concrete-witness — strict open-class product-relaxation gap has no valid concrete witness; Exhibit 9.1 is internally inconsistent."
  - "Theorem 1: C-wellposed — target weights are not pinned because T and q depend on the latent take-up table but omit it, and normalization does not match numerator weights."
  - "Theorem 1: C-proof-sketch — claimed finite MILP skips the variable complier denominator and binary-takeup-by-outcome products."
  - "Conjecture 2: C-sanity — hidden edges only to unit 4 with Z_4 fixed at 0 cannot generate r_Z=1 for leaves 1 and 2, so the claimed product/shared values do not follow."
  - "Conjecture 2: C-wellposed — switches Delta notation and invokes projected-polytope valid inequalities although the displayed feasible object is a mixed-integer union."
reusable_artifacts:
  - path: pid_network_iv_exposure_v3_gaps.json
    kind: literature_map
    one_line: "Useful network-IV/interference map: Hoshino-Yanagi 2024, Imai-Jiang-Malani 2021, Vazquez-Bare 2023, Acerenza et al. 2025, Nibbering-Oosterveen 2025, plus parent exposure-misspecification anchors."
  - path: pid_network_iv_exposure_v3_reviews/angle4_v1.json
    kind: counterexample
    one_line: "Reviewer pinpoints why the four-unit hidden-edge witness is infeasible; avoid reusing this witness shape."
  - path: pid_network_iv_exposure_v3_proposal.tex
    kind: other
    one_line: "Final failed proposal; useful only as a warning about promissory dual-map IV LP normalizations."
seeds_burned: []
proof_attempt_summary: |
  Attempted a flagship generalization of `pid_network_exposure/v1` from treatment-exposure misspecification to network IV with noncompliance and a second instrumental exposure map. The literature gap was real and reviewer repeatedly marked repo/published novelty clear, but every promising angle collapsed on the same mathematical burden: no valid non-corner witness and no well-pinned finite LP/MILP normalization. Treat this as a topic-choice failure, not reviewer over-strictness; the next run should avoid network-IV compatibility witnesses unless a concrete witness is constructed by hand first.
banked_on: "2026-05-24"
---

# pid_network_iv_exposure / v3 — Failed

**Topic.** Flagship generalization of the banked network-exposure partial-ID result: sharp partial identification of complier direct and spillover effects when both the treatment exposure mapping and the instrumental exposure mapping may be misspecified, bridging exposure-mapping robustness with IV noncompliance and producing a computable finite-network sharp bound plus a small worked witness.

**Novelty target.** flagship

**Stage -0.5 verdict.** NO-PASS

**Stage 0.5 verdict.** NA

**Banking reason.** Stage -0.5 NO-PASS after 5 angles: network-IV exposure upgrade repeatedly had a plausible literature gap but failed flagship proposal review on uncomputed/infeasible witnesses, promissory transport/frontier objects, and LP well-posedness.

**Supersedes.** pid_network_exposure_v1 (tier=candidates, upgrade_axis=generalization). The parent now lives in `_bank/downgraded/` (the `candidates` tier was retired 2026-07-18 and the parent re-graded subfield) and remains an independent reference; this entry is the flagship upgrade.

## Key files

- `pid_network_iv_exposure_v3_state.json` — pipeline state at banking (`banked: true`).
- `pid_network_iv_exposure_v3_proposal.tex` — final proposal version.
- `pid_network_iv_exposure_v3.tex` — derivation note (if Stage 0 ran).
- `pid_network_iv_exposure_v3_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_network_iv_exposure_v3_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
