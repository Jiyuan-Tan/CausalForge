---
qid: pid_prte_gain_band_functional
spec: ot_band_dual_orthogonal
topic: "Sharp partial identification and Neyman-orthogonal root-n inference for a NON-SEPARABLE policy-relevant functional of the joint gain law Y(1)-Y(0) (focal: the two-sided gain-band psi=E_omega[1{a<=Y(1)-Y(0)<=b}], the policy-affected share whose gain falls in a band, and the induced gain-dispersion index) in the generalized Roy/MTE model of arXiv 2604.12263 with a discrete IV. The anchor's 1-D closed-form quantile-coupling reduction and DML both rest on linearity-in-y; for the non-supermodular band cost separability is lost, so the sharp identified set is the value of a rank-structured constrained OT / linear-fractional LP (Charnes-Cooper) with an analyst-specified copula-sensitivity restriction R(eps) on the finite joint-outcome grid, and inference is rebuilt on the LP-dual optimizer as the Neyman-orthogonal influence function (root-n + asymptotic normality under dual uniqueness; Fang-Santos directional bootstrap otherwise). Extends Rem general_functional / Rem marx-open."
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "tan_blanchet_syrgkanis_2026_prte_ot and ober_reynolds_2023_joint_po_ot provide the closest DML/dual-OT inference templates; fang_santos_2019_directional_inference supplies the nonsmooth resampling framework."
  - "The stated estimator and score do not specify an asymptotic-linear nuisance estimator or a correcting moment; adding the endpoint LP derivative score to a sample LP value can double-count its first-order perturbation, so orthogonality and the CLT do not follow from the listed assumptions."
  - "An arbitrary analyst-specified H_epsilon r<=h_epsilon is not yet a credible empirical sensitivity model; the justification's claim that finite odds-ratio restrictions are polyhedral is generally false because odds ratios are nonlinear in r."
reusable_artifacts: []
seeds_burned: []
proof_attempt_summary: |
  The discovery phase developed a finite response-type common-coupling LP, a binary W_kappa strict-separation witness, and a proposed LP-dual inference route. Independent review found the sensitivity family and Roy restrictions under-specified and the proposed one-step influence expansion potentially double-counted first-order perturbations. Before a faithful D0.5 review, the user judged the remaining result an ordinary extension of the anchor paper with insufficient field-level contribution and directed banking as downgraded; no Lean formalization was attempted.
banked_on: "2026-07-16"
---

# pid_prte_gain_band_functional / ot_band_dual_orthogonal — Downgraded

**Topic.** Sharp partial identification and Neyman-orthogonal root-n inference for a NON-SEPARABLE policy-relevant functional of the joint gain law Y(1)-Y(0) (focal: the two-sided gain-band psi=E_omega[1{a<=Y(1)-Y(0)<=b}], the policy-affected share whose gain falls in a band, and the induced gain-dispersion index) in the generalized Roy/MTE model of arXiv 2604.12263 with a discrete IV. The anchor's 1-D closed-form quantile-coupling reduction and DML both rest on linearity-in-y; for the non-supermodular band cost separability is lost, so the sharp identified set is the value of a rank-structured constrained OT / linear-fractional LP (Charnes-Cooper) with an analyst-specified copula-sensitivity restriction R(eps) on the finite joint-outcome grid, and inference is rebuilt on the LP-dual optimizer as the Neyman-orthogonal influence function (root-n + asymptotic normality under dual uniqueness; Fang-Santos directional bootstrap otherwise). Extends Rem general_functional / Rem marx-open.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** Ordinary extension of the anchor paper with insufficient contribution for the field novelty target.

## Key files

- `pid_prte_gain_band_functional_ot_band_dual_orthogonal_state.json` — pipeline state at banking (`banked: true`).
- `pid_prte_gain_band_functional_ot_band_dual_orthogonal_proposal.tex` — final proposal version.
- `pid_prte_gain_band_functional_ot_band_dual_orthogonal.tex` — derivation note (if Stage 0 ran).
- `pid_prte_gain_band_functional_ot_band_dual_orthogonal_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_prte_gain_band_functional_ot_band_dual_orthogonal_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
