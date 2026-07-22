---
qid: eid_proximal_phase
spec: v1
topic: "Sharp identification phase transition for the average treatment effect via proximal causal inference (negative controls) when standard proxy completeness fails. Miao, Geng, and Tchetgen Tchetgen (2018, Biometrika) and Cui, Pu, Shi, Miao, Tchetgen Tchetgen (2024, JASA) established exact point identification of the ATE under unmeasured confounding via the outcome bridge function h(W,A,X) solving E[Y - h(W,A,X) | Z,A,X]=0, provided the completeness condition that g -> E[g(U) | Z,A,X] is injective on a suitable function class. Recent work (Tchetgen Tchetgen, Ying, Cui, Shi, Miao 2024; Kompa, Sturma, Imbens 2024 NBER w34550) studies failure modes when completeness is only approximately satisfied. The flagship question: parametrize completeness by the smallest singular value sigma_min of the projection operator g -> E[g(U) | Z,A,X] restricted to bridge-function residuals, and characterize a sharp phase transition: when sigma_min > sigma_star (a critical threshold computable from the observable proxy distribution and outcome regression), the ATE is exactly point-identified by the proximal IPW/OR estimator; when 0 < sigma_min <= sigma_star, the ATE is identified by a sharp non-trivial interval whose width scales as O(1/sigma_min); when sigma_min = 0 the proximal identification collapses entirely to a Manski-trivial bound. The kernel claim is a sharp closed-form characterization of sigma_star as the smallest singular value of an explicit observable kernel, with strict point/interval/Manski phase boundaries. Recovers Miao-Geng-Tchetgen point identification in the high-completeness regime and provides the first sharp proximal phase transition theorem with computable threshold."
novelty_target: flagship
tier_at_proposal: NO-PASS
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
  # generic selector-range Conjecture 1 unproved and the unqualified 1-D claim
  # explicitly FALSE (radial counterexample) — §1 promise exceeded §3-§13 delivery.
reusable: solver_blocked  # changed from unknown: math is sound/plausible at field
reraise_status: re-raise
  # tier and the proposal cleared repo+published novelty axes at flagship on the
  # accepting round; failure was the derivation/witness step falling short of the
  # flagship floor, not a refuted kernel.
gap_reasons:
  # Verbatim / near-verbatim reviewer phrases (source: reviews.jsonl D0.5 rejects
  # at stage_0.5_to_0, and angle2 v5 D-0.5 review). Two distinct failure points.
  - "The flagship generic selector-range conjecture is not proved; the note proves only a one-dimensional nonradial repair and refutes the unqualified one-dimensional claim."  # D0.5, Proposition 3 / Conjecture 1
  - "The original unqualified one-dimensional conjecture is refuted, and the repair is a nonradial one-dimensional condition rather than a broad generic-class result."  # D0.5, novelty
  - "Assessed derivation tier is at most subfield, below novelty_target=flagship; accepting at a downgraded tier is forbidden by the prompt."  # D0.5, novelty floor
  - "Proposition 4 claims the witness satisfies the generic-stratum condition from Conjecture 2. That is not established and appears false: in the A=0 arm the two bridge rows are identical ... so the rank drop that creates the one-dimensional fiber is destroyed by arbitrarily small perturbations of the observable law."  # D0.5 round 2, correctness
  - "The main mathematics actually delivered is finite convex geometry of the bridge fiber, a null-annihilator criterion, ... a one-dimensional nonradial selector formula, and one explicit binary table. These are coherent diagnostics, but they are not a flagship regime-opening theorem."  # D0.5 round 2, novelty
  - "The statement invokes a common 'efficiency-bound object' for the profiled minimax selected ATE, but §6/§7 define only finite first-order influence functions, not the semiparametric model, tangent space, or variance functional that makes an efficiency bound well-defined."  # angle2 v5 D-0.5, soundness C-wellposed (last blocker before NO-PASS)
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  Attempted a flagship sharp proximal-completeness phase transition for the ATE:
  a closed-form critical singular value sigma_star giving strict point / interval /
  Manski phase boundaries when proxy completeness fails. The original angle reached a
  flagship ACCEPT at proposal (angle 1 v3), but the D0.5 derivation collapsed: the
  generic open-class selector-range Conjecture 1 was never proved, the unqualified
  one-dimensional claim was refuted by a radial counterexample, and the binary witness
  (Prop. 4) fails its own generic-stratum condition (A=0 duplicate proxy rows make the
  rank drop unstable under arbitrarily small perturbations). The pivot to a fresh angle 2
  cycled six revisions, only twice touching flagship (last blocked on an undefined
  efficiency-bound object) before the revision cap exhausted to a NO-PASS@flagship.
  Remains: sound field-tier finite convex geometry (null-annihilator criterion, exact-fiber
  Tikhonov limit, nonradial 1-D selector formula) — but no flagship regime-opening theorem.
banked_on: "2026-05-16"
---

# eid_proximal_phase / v1 — Downgraded

**Topic.** Sharp identification phase transition for the average treatment effect via proximal causal inference (negative controls) when standard proxy completeness fails. Miao, Geng, and Tchetgen Tchetgen (2018, Biometrika) and Cui, Pu, Shi, Miao, Tchetgen Tchetgen (2024, JASA) established exact point identification of the ATE under unmeasured confounding via the outcome bridge function h(W,A,X) solving E[Y - h(W,A,X) | Z,A,X]=0, provided the completeness condition that g -> E[g(U) | Z,A,X] is injective on a suitable function class. Recent work (Tchetgen Tchetgen, Ying, Cui, Shi, Miao 2024; Kompa, Sturma, Imbens 2024 NBER w34550) studies failure modes when completeness is only approximately satisfied. The flagship question: parametrize completeness by the smallest singular value sigma_min of the projection operator g -> E[g(U) | Z,A,X] restricted to bridge-function residuals, and characterize a sharp phase transition: when sigma_min > sigma_star (a critical threshold computable from the observable proxy distribution and outcome regression), the ATE is exactly point-identified by the proximal IPW/OR estimator; when 0 < sigma_min <= sigma_star, the ATE is identified by a sharp non-trivial interval whose width scales as O(1/sigma_min); when sigma_min = 0 the proximal identification collapses entirely to a Manski-trivial bound. The kernel claim is a sharp closed-form characterization of sigma_star as the smallest singular value of an explicit observable kernel, with strict point/interval/Manski phase boundaries. Recovers Miao-Geng-Tchetgen point identification in the high-completeness regime and provides the first sharp proximal phase transition theorem with computable threshold.

**Novelty target.** flagship

**D-0.5 verdict.** NO-PASS

**D0.5 verdict.** REJECT

**Banking reason.** Re-review under widened flagship rubric — D0.5 rejected original derivation, intervention pivoted to fresh angle 2. Angle 2 cycled v0/v2/v3/v4/v5=REVISE@field, v1=REVISE@flagship (single hit), cap exhausted → D-0.5 NO-PASS@flagship. Proximal-completeness kernel briefly tagged flagship under axis (c) extension framing but couldn't hold it across revisions. Math sound at field tier.

## Key files

- `eid_proximal_phase_v1_state.json` — pipeline state at banking (`banked: true`).
- `eid_proximal_phase_v1_proposal.tex` — final proposal version.
- `eid_proximal_phase_v1.tex` — derivation note (if D0 ran).
- `eid_proximal_phase_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `eid_proximal_phase_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
