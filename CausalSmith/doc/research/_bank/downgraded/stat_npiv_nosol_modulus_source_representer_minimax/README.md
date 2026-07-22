---
qid: stat_npiv_nosol_modulus
spec: source_representer_minimax
topic: "intrinsic minimax modulus (functional modulus of continuity) for finite-dimensional functionals of no-solution NPIV least-squares projections, indexed by spectral-decay, source, and functional-representer source classes — the missing converse to the Tikhonov achievability rate of Shen-Kallus et al (arXiv:2604.24660); deliver a sharp intrinsic-modulus characterization with matched lower and upper bounds where available, and claim Tikhonov rate-suboptimality only if an estimator attaining the faster modulus rate is exhibited"
novelty_target: field
tier_at_proposal: REJECT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "N-pub (D-0.5 v4 REJECT): 'After ass:projection-domain, h^Pi solves the projected exact inverse problem T h = g^R, so the Gaussian sequence modulus, envelope, profile rates, Riesz boundary, and Lepski adaptation are subsumed by the exact-solution NPIR/linear-functional literature rather than being a new no-solution frontier.'"
  - "All six results (thm:functional-modulus, prop:representer-envelope, prop:bennett-riesz-recovery, prop:profile-rates, prop:exact-solution-reduction, conj:adaptive-ordered-modulus) graded already-known on BOTH repo and published axes."
  - "Fundamental reduction (framing-independent): the minimum-norm LS solution h-dagger exactly solves the projected normal equation T*T h = T*r (equiv. T h-dagger = g^R = P_range(T) r), so estimating the functional E[h-dagger g] is a classical linear-functional-of-exact-inverse-problem problem with target g^R; the no-solution label does not change the first-order minimax modulus."
reusable_artifacts:
  # None liftable: the kernel is a true-negative (subsumed). The D-1.1 gaps.json
  # (NPIV no-solution open problems) and literature_map remain in the run dir if a
  # FUTURE run targets the genuinely-novel no-solution INFERENCE/orthogonality
  # frontier (a different kernel), which this entry does NOT cover.
seeds_burned: []
proof_attempt_summary: |
  Targeted the intrinsic minimax MODULUS (functional modulus of continuity) for finite-dimensional
  functionals of no-solution NPIV least-squares projections, aiming for the missing converse to
  Shen et al. (2026) achievability. Collapsed at D-0.5: once the well-posedness/summability condition
  is imposed, the LS projection reduces the functional to an exact-solution NPIR linear-functional
  problem (target g^R), whose modulus is classical (Breunig-Johannes/Chen-Reiss/Cai-Low) — so the
  "no-solution" novelty is illusory at the modulus level. The real no-solution novelty (Shen et al.)
  lives in debiased-inference orthogonality / second-order remainder, NOT the first-order modulus.
  Deterrent: do not re-propose a no-solution-MODULUS converse; an inference-frontier kernel is distinct.
banked_on: "2026-06-21"
---

# stat_npiv_nosol_modulus / source_representer_minimax — Downgraded

**Topic.** intrinsic minimax modulus (functional modulus of continuity) for finite-dimensional functionals of no-solution NPIV least-squares projections, indexed by spectral-decay, source, and functional-representer source classes — the missing converse to the Tikhonov achievability rate of Shen-Kallus et al (arXiv:2604.24660); deliver a sharp intrinsic-modulus characterization with matched lower and upper bounds where available, and claim Tikhonov rate-suboptimality only if an estimator attaining the faster modulus rate is exhibited

**Novelty target.** field

**Stage -0.5 verdict.** REJECT

**Stage 0.5 verdict.** NA

**Banking reason.** No-solution NPIV functional minimax MODULUS is subsumed by exact-solution NPIR/linear-functional theory: the least-squares projection h-dagger exactly solves the projected normal equation T h = g^R, so the functional modulus, envelope, profile rates, Riesz boundary, and Lepski adaptation reduce to classical exact-solution functional-modulus results (Breunig-Johannes/Chen-Reiss/Cai-Low). D-0.5 v4 REJECT, all theorems already-known (N-pub). Genuine no-solution novelty (Shen et al.) lives in debiased-inference orthogonality, not the first-order modulus.

## Key files

- `stat_npiv_nosol_modulus_source_representer_minimax_state.json` — pipeline state at banking (`banked: true`).
- `stat_npiv_nosol_modulus_source_representer_minimax_proposal.tex` — final proposal version.
- `stat_npiv_nosol_modulus_source_representer_minimax.tex` — derivation note (if Stage 0 ran).
- `stat_npiv_nosol_modulus_source_representer_minimax_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `stat_npiv_nosol_modulus_source_representer_minimax_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
