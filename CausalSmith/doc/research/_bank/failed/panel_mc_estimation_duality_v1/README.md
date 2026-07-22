---
qid: panel_mc_estimation_duality
spec: v1
topic: "Joint identification and matrix-completion estimator for staggered-treatment panels with low-rank unit-time heterogeneity and an explicit recovery-threshold phase transition expressed in observed eigen-gap and treatment-design constants"
novelty_target: flagship
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: "kernel_substituted"
reusable: unknown
reraise_status: retry
gap_reasons:
  - 'Conjecture 1: N-mischar — ''The FariasLiPeng2021 comparison is too weak: that paper already gives tangent/projection identification conditions and a nonrecoverability result for general intervention-pattern ATE recovery, not merely a treated-entry average estimator.'''
  - 'Conjecture 1: N-thin-anchor — ''Tier=field below novelty_target=flagship unless the statement is anchored to the exact FariasLiPeng2021 tangent-space/minimality result and phrased as a strict two-surface extension.'''
  - 'Conjecture 2: N-comparator-drift — ''The handoff maps ChoiKwonLiao2024, ChoiYuan2024, YanWainwright2024, ChernozhukovHansenLiaoZhu2019, and ZhuLiaoHansenChernozhukov2026 to Conjecture 2, but the §8 statement itself is not phrased as a strict tightening against any named comparator.'''
  - 'Corollary no-effect-rank: C-sanity — ''The reduction to ordinary matrix completion is not justified with rho1/eta->0; that makes the effect penalty negligible relative to the vanishing effect and does not force the separable estimator to collapse to the no-effect completion.'''
  - 'Example three-cohort: C-coherence — ''The displayed matrix uses overcomplete factor-derivative coordinates, while §6 defines A_sep using orthonormal tangent bases; the example should quotient out gauge directions or state that it is only a coordinate witness.'''
  - 'Theorem 1 (angle 3): C-sanity — ''The oracle score adds the weighted untreated residual, but Assumption balance equates target nuisance error to weighted untreated nuisance error; expectation becomes target error plus weighted error, not zero, so the displayed double-robust algebra fails unless the sign or assumption is changed.'''
  - 'Conjecture 1 (angle 3): C-wellposed — ''Delta_OLB is defined using B_lr(w;A,B) for an arbitrary factorization M0=AB^T; without an SVD/normalization or invariant tangent-space norm, Delta_OLB is not pinned as a function of P.'''
  - 'Conjecture 2 (angle 3): C-wellposed — ''Gamma_OLB uses singular values of M_hat over the staggered untreated mask O0 and undefined leverage/overlap constants rho(D,r), kappa(D,r); the proposal does not specify the rectangular completion/fill convention needed for the singular values.'''
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  The entry attempted to prove a two-surface separability frontier for staggered panels (target-nullspace defect a_E(P,D) as an iff point-identification certificate for a low-rank treatment-effect surface against a low-rank untreated surface), plus an asymptotically linear separable-completion estimator. The underlying separation problem is mathematically real and repo-novel, but across 5 angles and 20+ reviewer rounds every kernel either collapsed to field-tier incrementality over FariasLiPeng2021's existing tangent-space obstruction (Conjecture 1 flagged N-mischar/N-thin-anchor) or arrived at outright soundness failures (angle 3 REJECT: double-robust score algebra sign error, Delta_OLB gauge invariance broken, Gamma_OLB undefined leverage constants). The oscillation between novelty and correctness failures — concrete observable margin gives field novelty, abstract margin draws correctness fires — is a kernel_substituted pattern: no single stable formulation passed both screens simultaneously.
banked_on: "2026-05-22"
---

# panel_mc_estimation_duality / v1 — Failed

**Topic.** Joint identification and matrix-completion estimator for staggered-treatment panels with low-rank unit-time heterogeneity and an explicit recovery-threshold phase transition expressed in observed eigen-gap and treatment-design constants

**Novelty target.** flagship

**Stage -0.5 verdict.** NO-PASS

**Stage 0.5 verdict.** NA

**Banking reason.** Stage -1.2 NO-PASS @ flagship (D-1.2 effort=medium, reverted from high). 20 reviewer rounds across 4 angles; tier=flagship reached 4 times but never with all flags (S+N+C) clear simultaneously. Final angle=4 v5 REVISE@field S=2 N=3 C=2. Oscillation pattern: when the recovery-threshold scalar is named concretely (e.g. eigen-gap × treatment-design constant) novelty drops to field; when named abstractly, correctness flags fire. Same shape as runs 1 and 3 (kernel_substituted-adjacent but never reached D-0.5 ACCEPT).

## Key files

- `panel_mc_estimation_duality_v1_state.json` — pipeline state at banking (`banked: true`).
- `panel_mc_estimation_duality_v1_proposal.tex` — final proposal version.
- `panel_mc_estimation_duality_v1.tex` — derivation note (if Stage 0 ran).
- `panel_mc_estimation_duality_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `panel_mc_estimation_duality_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
