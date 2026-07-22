/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sequential DR (DTR, n = 2) second-order remainder identity

The sequential DR moment functional `m_seqDR(η, z, θ₀)` from
`SeqDRMoment.lean` is Neyman-orthogonal at `(η₀, θ₀)`.  The DML
asymptotic-linearity proof needs the *second-order* algebraic
identity (the n = 2 unrolling — no induction) showing that the
population moment at `η ∈ H_ε` is a sum of two stagewise
cross-product integrals between outcome-regression error and
propensity-score error.

Concretely: for any `η ∈ H_ε`,

    ∫ z, m_seqDR(η, z, θ₀) ∂(P_Z)
      = ∫ s₀ ∂(P_H₀),
          (η.e₀_fn s₀ − S.e₀_val s₀) · w₀(s₀; η, S) ·
            (η.μ₀_fn s₀ − S.μ₀_val s₀)
        + ∫ h ∂(P_H₁),
          (η.e₁_fn h − S.e₁_val h) · w₁(h; η, S) ·
            (η.μ₁_fn h − S.μ₁_val h)

with the stagewise IPW weights

    w₀(s₀; η, S) := 1 / η.e₀_fn s₀                   -- bounded by ε⁻¹
    w₁(h ; η, S) := 1 / (η.e₀_fn h.2.2 · η.e₁_fn h)   -- bounded by ε⁻²

(`h.2.2 = s₀` under the cons-ordered `(s₁, d₀, s₀)` convention).

The choice of `w₁` carries the stage-0 propensity into the integrand
explicitly.  This is the cleanest closed form for the bound file:
`|w₁| ≤ ε⁻²` pointwise on `H_ε`, and `∫ … dP_H₁` already incorporates
the law of `(S₁, D₀, S₀)` — no extra residualisation is needed.

Mirrors the structure of `Estimation/ATE/RemainderIdentity.lean` —
the headline `aipw_remainder_identity` collapses the AIPW moment to
a single integral over `S.P_X`; here we collapse the sequential DR
moment to a *sum* of two integrals, one per stage marginal.

Downstream `RemainderBound.lean` consumes this identity via
Cauchy–Schwarz componentwise.
-/

import Causalean.Estimation.DTR.RemainderIdentity.Helpers

/-!
Proves the stagewise cross-product remainder identity for sequential doubly
robust DTR scores. The identity decomposes the population moment error into
nuisance-error products for the dynamic treatment rule.
-/

namespace Causalean
namespace Estimation
namespace DTR

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO

namespace DTREstimationSystem

variable {P : POSystem} {δ : Type} {γ : Fin 2 → Type}
  [MeasurableSpace δ] [MeasurableSingletonClass δ]
  [∀ k, MeasurableSpace (γ k)]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-! ## Stage-0 cross-product remainder

The stage-0 cross-product collects the part of the population moment that
expands into a single integral over `P_H₀`.  Schematically it captures the
AIPW-style cancellation between the stage-0 plug-in `μ₀_fn − μ₀_val` and the
indicator-vs-propensity correction `1{D₀ = dbar 0} − e₀_val` after pulling
through `(historyBundle 0).sigma`.

Stage-0 weight:  `w₀(s₀; η, S) := 1 / η.e₀_fn s₀`,
bounded by `ε⁻¹` on `H_ε`.  The stage-0 cross-product is folded directly
into the monolithic headline proof below; no standalone stage-0 lemma is
exported. -/

/-! ## Stage-1 cross-product remainder

Stage-1 weight:  `w₁(h; η, S) := 1 / (η.e₀_fn h.2.2 · η.e₁_fn h)`,
bounded by `ε⁻²` on `H_ε`.  Note this brings the stage-0 propensity
`η.e₀_fn (s₀)` into the integrand — a deliberate shape choice so the
final integral is `∂(S.P_H₁)` (the joint marginal of `(S₁, D₀, S₀)`),
matching the bundle ordering and avoiding an auxiliary residualisation
step.  As with stage 0, this contribution is folded into the monolithic
headline proof below rather than exported as a standalone lemma. -/

/-! ## Headline two-stage remainder identity

Combines the stage-0 and stage-1 cross-product integrals into the n = 2
sequential DR remainder identity. -/

/-- **Sequential DR (DTR, n = 2) remainder identity.**

Expanding the population sequential DR moment around the true nuisance
`S.η₀` cancels the zeroth and first-order terms (Neyman orthogonality)
and leaves a *sum* of two stagewise cross-product integrals, one per
history marginal.

Stage-0 weight: `1 / η.e₀_fn s₀` (bounded by `ε⁻¹` on `H_ε`).
Stage-1 weight: `1 / (η.e₀_fn h.2.2 · η.e₁_fn h)` (bounded by `ε⁻²`).

The stage-1 weight intentionally carries `η.e₀_fn` into the integrand;
this avoids introducing an auxiliary measure or a residualisation step
and lets the integral live directly against `S.P_H₁`.  Downstream
`RemainderBound.lean` applies Cauchy–Schwarz to each summand
componentwise. -/
lemma seqDR_remainder_identity
    (S : DTREstimationSystem P δ γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPODTRSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPODTRSystem.factualY ω) ^ 2) P.μ)
    (_h_yd2 : ∀ dbar : Fin 2 → δ, Integrable
      (fun ω => (S.toPODTRSystem.Y_of dbar ω) ^ 2) P.μ)
    (η : DTRNuisanceVec₂ δ γ) (hη : η ∈ DTREstimationSystem.H_ε ε)
    (hΔμ₀_memLp : MemLp (fun s₀ => η.μ₀_fn s₀ - S.μ₀_val s₀) 2 S.P_H₀)
    (hΔμ₁_memLp : MemLp (fun h => η.μ₁_fn h - S.μ₁_val h) 2 S.P_H₁)
    (hΔe₀_memLp : MemLp (fun s₀ => η.e₀_fn s₀ - S.e₀_val s₀) 2 S.P_H₀)
    (hΔe₁_memLp : MemLp (fun h => η.e₁_fn h - S.e₁_val h) 2 S.P_H₁) :
    ∫ z, S.seqDRMomentFunctional η z S.θ₀ ∂(S.P_Z)
      =
      (∫ s₀, (η.e₀_fn s₀ - S.e₀_val s₀)
              * (1 / η.e₀_fn s₀)
              * (η.μ₀_fn s₀ - S.μ₀_val s₀) ∂(S.P_H₀))
        +
      (∫ h, indEq h.2.1 (S.dbar 0)
            * (η.e₁_fn h - S.e₁_val h)
            * (1 / (η.e₀_fn h.2.2 * η.e₁_fn h))
            * (η.μ₁_fn h - S.μ₁_val h) ∂(S.P_H₁)) := by
  let S0 : P.Ω → γ 0 := S.toPODTRSystem.factualS ⟨0, by decide⟩
  let H1 : P.Ω → γ 1 × δ × γ 0 := fun ω =>
    (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
     S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
     S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)
  let Y : P.Ω → ℝ := S.toPODTRSystem.factualY
  let I0 : P.Ω → ℝ :=
    (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
      (S.dbar ⟨0, by decide⟩)
  let I1 : P.Ω → ℝ :=
    (S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator
      (S.dbar ⟨1, by decide⟩)
  let M0 : P.Ω → ℝ := fun ω => S.μ₀_val (S0 ω)
  let M1 : P.Ω → ℝ := fun ω => S.μ₁_val (H1 ω)
  let dμ0 : P.Ω → ℝ := fun ω => η.μ₀_fn (S0 ω) - S.μ₀_val (S0 ω)
  let dμ1 : P.Ω → ℝ := fun ω => η.μ₁_fn (H1 ω) - S.μ₁_val (H1 ω)
  let G0 : P.Ω → ℝ := fun ω => 1 / η.e₀_fn (S0 ω)
  let G1 : P.Ω → ℝ := fun ω => 1 / (η.e₀_fn (S0 ω) * η.e₁_fn (H1 ω))
  let base : P.Ω → ℝ := fun ω => M0 ω - S.θ₀
  let R0 : P.Ω → ℝ := fun ω => I0 ω * (M1 ω - M0 ω)
  let R1 : P.Ω → ℝ := fun ω => I0 ω * (I1 ω * (Y ω - M1 ω))
  let r0 : P.Ω → ℝ := fun ω => G0 ω * R0 ω
  let r1 : P.Ω → ℝ := fun ω => G1 ω * R1 ω
  let i0 : P.Ω → ℝ := fun ω => I0 ω * G0 ω * dμ0 ω
  let i10 : P.Ω → ℝ := fun ω => I0 ω * G0 ω * dμ1 ω
  let i11 : P.Ω → ℝ := fun ω => I0 ω * I1 ω * G1 ω * dμ1 ω
  let p0 : P.Ω → ℝ := fun ω =>
    (dμ0 ω / η.e₀_fn (S0 ω)) * S.e₀_val (S0 ω)
  let p1 : P.Ω → ℝ := fun ω =>
    indEq (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω) (S.dbar ⟨0, by decide⟩) *
      (dμ1 ω / (η.e₀_fn (S0 ω) * η.e₁_fn (H1 ω))) * S.e₁_val (H1 ω)
  let crossInd : P.Ω → ℝ := fun ω => dμ0 ω + i10 ω - i0 ω - i11 ω
  let crossProp : P.Ω → ℝ := fun ω => dμ0 ω + i10 ω - p0 ω - p1 ω
  let rem0 : γ 0 → ℝ := fun s₀ =>
    (η.e₀_fn s₀ - S.e₀_val s₀) * (1 / η.e₀_fn s₀) *
      (η.μ₀_fn s₀ - S.μ₀_val s₀)
  let rem1 : γ 1 × δ × γ 0 → ℝ := fun h =>
    indEq h.2.1 (S.dbar 0) *
      (η.e₁_fn h - S.e₁_val h) *
      (1 / (η.e₀_fn h.2.2 * η.e₁_fn h)) *
      (η.μ₁_fn h - S.μ₁_val h)
  let remΩ : P.Ω → ℝ := fun ω => rem0 (S0 ω) + rem1 (H1 ω)
  have hS0_meas : Measurable S0 := by
    dsimp [S0]
    exact S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩
  have hH1_meas : Measurable H1 := by
    dsimp [H1]
    exact (S.toPODTRSystem.measurable_factualS ⟨1, by decide⟩).prod
      ((S.toPODTRSystem.measurable_factualD ⟨0, by decide⟩).prod
        (S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩))
  have hM0_int : Integrable M0 P.μ := by
    let B0 := S.toPODTRSystem.historyBundle 0 (by decide)
    exact (B0.integrable_condExpGiven (S.toPODTRSystem.Y_of S.dbar)).congr
      (by simpa [B0, M0, S0] using S.μ₀_compat hA)
  have hM1_int : Integrable M1 P.μ := by
    let B1 := S.toPODTRSystem.historyBundle 1 (by decide)
    have hM1_L2 : MemLp M1 2 P.μ := by
      simpa [M1, H1] using (S.stageOneReg_memLp h_overlap h_y2).ae_eq
        (S.μ₁_val_comp_eq_stageOneReg).symm
    exact hM1_L2.integrable (by norm_num)
  have hM0_meas : Measurable M0 := by
    dsimp [M0]
    exact S.μ₀_meas.comp hS0_meas
  have hM1_meas : Measurable M1 := by
    dsimp [M1]
    exact S.μ₁_meas.comp hH1_meas
  have hI0M0_int : Integrable (fun ω => I0 ω * M0 ω) P.μ := by
    have h := (S.toPODTRSystem.dVar ⟨0, by decide⟩).integrable_mul_indicator
      (S.dbar ⟨0, by decide⟩) hM0_int hM0_meas
    exact h.congr (Filter.Eventually.of_forall (fun ω => by simp [I0, M0, mul_comm]))
  have hI0M1_int : Integrable (fun ω => I0 ω * M1 ω) P.μ := by
    have h := (S.toPODTRSystem.dVar ⟨0, by decide⟩).integrable_mul_indicator
      (S.dbar ⟨0, by decide⟩) hM1_int hM1_meas
    exact h.congr (Filter.Eventually.of_forall (fun ω => by simp [I0, M1, mul_comm]))
  have hR0_int : Integrable R0 P.μ := by
    have hsub := hI0M1_int.sub hI0M0_int
    refine hsub.congr ?_
    exact Filter.Eventually.of_forall (fun ω => by
      simp [R0]
      ring)
  have hI1Y_int : Integrable (fun ω => I1 ω * Y ω) P.μ := by
    have h := (S.toPODTRSystem.dVar ⟨1, by decide⟩).integrable_mul_indicator
      (S.dbar ⟨1, by decide⟩) hA.integrable_factualY
      S.toPODTRSystem.measurable_factualY
    exact h.congr (Filter.Eventually.of_forall (fun ω => by simp [I1, Y, mul_comm]))
  have hI1M1_int : Integrable (fun ω => I1 ω * M1 ω) P.μ := by
    have h := (S.toPODTRSystem.dVar ⟨1, by decide⟩).integrable_mul_indicator
      (S.dbar ⟨1, by decide⟩) hM1_int hM1_meas
    exact h.congr (Filter.Eventually.of_forall (fun ω => by simp [I1, M1, mul_comm]))
  have hI1_res_int :
      Integrable (fun ω => I1 ω * (Y ω - M1 ω)) P.μ := by
    have hsub := hI1Y_int.sub hI1M1_int
    refine hsub.congr ?_
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Pi.sub_apply]
      ring)
  have hI1_res_meas : Measurable (fun ω => I1 ω * (Y ω - M1 ω)) := by
    exact ((S.toPODTRSystem.dVar ⟨1, by decide⟩).measurable_indicator
      (S.dbar ⟨1, by decide⟩)).mul
      (S.toPODTRSystem.measurable_factualY.sub hM1_meas)
  have hR1_int : Integrable R1 P.μ := by
    have h := (S.toPODTRSystem.dVar ⟨0, by decide⟩).integrable_mul_indicator
      (S.dbar ⟨0, by decide⟩) hI1_res_int hI1_res_meas
    exact h.congr (Filter.Eventually.of_forall (fun ω => by
      change (I1 ω * (Y ω - M1 ω)) * I0 ω = R1 ω
      simp [R1]
      ring))
  have hη0_lower : ∀ s₀, ε ≤ η.e₀_fn s₀ := fun s₀ => (hη.1 s₀).1
  have hη1_lower : ∀ h, ε ≤ η.e₁_fn h := fun h => (hη.2 h).1
  have hη0_pos : ∀ s₀, 0 < η.e₀_fn s₀ :=
    fun s₀ => lt_of_lt_of_le h_overlap.1 (hη0_lower s₀)
  have hη1_pos : ∀ h, 0 < η.e₁_fn h :=
    fun h => lt_of_lt_of_le h_overlap.1 (hη1_lower h)
  have hG0_meas : Measurable G0 := by
    dsimp [G0]
    exact measurable_const.div (η.e₀_meas.comp hS0_meas)
  have hG1_meas : Measurable G1 := by
    dsimp [G1]
    exact measurable_const.div ((η.e₀_meas.comp hS0_meas).mul
      (η.e₁_meas.comp hH1_meas))
  have hG0_bound : ∀ᵐ ω ∂P.μ, ‖G0 ω‖ ≤ ε⁻¹ := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hle : (η.e₀_fn (S0 ω))⁻¹ ≤ ε⁻¹ :=
      (inv_le_inv₀ (hη0_pos (S0 ω)) h_overlap.1).2 (hη0_lower (S0 ω))
    change ‖1 / η.e₀_fn (S0 ω)‖ ≤ ε⁻¹
    rw [norm_div, norm_one, Real.norm_eq_abs, abs_of_pos (hη0_pos (S0 ω))]
    simpa [one_div] using hle
  have hG1_bound : ∀ᵐ ω ∂P.μ, ‖G1 ω‖ ≤ (ε * ε)⁻¹ := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hpos0 : 0 < η.e₀_fn (S0 ω) := hη0_pos (S0 ω)
    have hpos1 : 0 < η.e₁_fn (H1 ω) := hη1_pos (H1 ω)
    have hprod_le : ε * ε ≤ η.e₀_fn (S0 ω) * η.e₁_fn (H1 ω) :=
      mul_le_mul (hη0_lower (S0 ω)) (hη1_lower (H1 ω))
        h_overlap.1.le hpos0.le
    have hle : (η.e₀_fn (S0 ω) * η.e₁_fn (H1 ω))⁻¹ ≤ (ε * ε)⁻¹ :=
      (inv_le_inv₀ (mul_pos hpos0 hpos1)
        (mul_pos h_overlap.1 h_overlap.1)).2 hprod_le
    change ‖1 / (η.e₀_fn (S0 ω) * η.e₁_fn (H1 ω))‖ ≤ (ε * ε)⁻¹
    rw [norm_div, norm_one, Real.norm_eq_abs, abs_of_pos (mul_pos hpos0 hpos1)]
    simpa [one_div] using hle
  have hr0_int : Integrable r0 P.μ := by
    exact hR0_int.bdd_mul hG0_meas.aestronglyMeasurable hG0_bound
  have hr1_int : Integrable r1 P.μ := by
    exact hR1_int.bdd_mul hG1_meas.aestronglyMeasurable hG1_bound
  have hi0_int : Integrable i0 P.μ := by
    simpa [i0, I0, G0, dμ0, S0, mul_assoc] using
      indicator_weighted_delta_mu0_integrable S h_overlap.1 η hη hΔμ₀_memLp
  have hi10_int : Integrable i10 P.μ := by
    simpa [i10, I0, G0, dμ1, H1, S0, mul_assoc] using
      indicator_weighted_delta_mu1_stage0_integrable S h_overlap.1 η hη hΔμ₁_memLp
  have hi11_int : Integrable i11 P.μ := by
    simpa [i11, I0, I1, G1, dμ1, H1, S0, mul_assoc] using
      indicator_weighted_delta_mu1_stage1_integrable S h_overlap.1 η hη hΔμ₁_memLp
  have hdμ0_L2 : MemLp dμ0 2 P.μ := by
    have hd := MemLp.comp_of_map (f := S0) hΔμ₀_memLp hS0_meas.aemeasurable
    simpa [dμ0, S0, DTREstimationSystem.P_H₀] using hd
  have hdμ1_L2 : MemLp dμ1 2 P.μ := by
    have hd := MemLp.comp_of_map (f := H1) hΔμ₁_memLp hH1_meas.aemeasurable
    simpa [dμ1, H1, DTREstimationSystem.P_H₁] using hd
  have hdμ0_int : Integrable dμ0 P.μ := hdμ0_L2.integrable (by norm_num)
  have hdμ1_int : Integrable dμ1 P.μ := hdμ1_L2.integrable (by norm_num)
  have hbase_int : Integrable base P.μ := by
    simpa [base] using hM0_int.sub (integrable_const S.θ₀)
  have hcrossInd_int : Integrable crossInd P.μ := by
    simpa [crossInd, sub_eq_add_neg, add_assoc] using
      ((hdμ0_int.add hi10_int).sub hi0_int).sub hi11_int
  have hbase_zero : ∫ ω, base ω ∂P.μ = 0 := by
    have hθ : S.θ₀ = ∫ ω, M0 ω ∂P.μ := by
      simpa [M0, S0] using theta_zero_factualS₀_integral S hA
    have hconst : (∫ _ : P.Ω, S.θ₀ ∂P.μ) = S.θ₀ := by
      haveI : IsProbabilityMeasure P.μ := inferInstance
      simp
    calc
      ∫ ω, base ω ∂P.μ
          = (∫ ω, M0 ω ∂P.μ) - ∫ _ : P.Ω, S.θ₀ ∂P.μ := by
            rw [show base = (fun ω => M0 ω - S.θ₀) from rfl]
            exact integral_sub hM0_int (integrable_const S.θ₀)
      _ = S.θ₀ - S.θ₀ := by rw [← hθ, hconst]
      _ = 0 := by ring
  have hr0_zero : ∫ ω, r0 ω ∂P.μ = 0 := by
    have hg_meas : Measurable (fun s₀ => 1 / η.e₀_fn s₀) :=
      measurable_const.div η.e₀_meas
    have h_int : Integrable
        (fun ω => (1 / η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) *
          ((S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
              (S.dbar ⟨0, by decide⟩) ω *
            (S.μ₁_val
                (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
                 S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
                 S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) -
              S.μ₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)))) P.μ := by
      simpa [S0, H1, G0, R0, r0, I0, M0, M1, mul_assoc] using hr0_int
    calc
      ∫ ω, r0 ω ∂P.μ
          = ∫ ω, (1 / η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) *
            ((S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
                (S.dbar ⟨0, by decide⟩) ω *
              (S.μ₁_val
                  (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
                   S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
                   S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) -
                S.μ₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))) ∂P.μ := by
            apply MeasureTheory.integral_congr_ae
            exact Filter.Eventually.of_forall (fun ω => by
              simp [r0, G0, R0, I0, M0, M1, S0, H1])
      _ = 0 := by
            simpa using
              weighted_residual_integral_zero_stage0 S h_overlap hA h_y2
                (fun s₀ => 1 / η.e₀_fn s₀) hg_meas h_int
  have hr1_zero : ∫ ω, r1 ω ∂P.μ = 0 := by
    have hg_meas : Measurable (fun h : γ 1 × δ × γ 0 =>
        1 / (η.e₀_fn h.2.2 * η.e₁_fn h)) :=
      measurable_const.div ((η.e₀_meas.comp measurable_snd.snd).mul η.e₁_meas)
    have h_int : Integrable
        (fun ω => (1 / (η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
            η.e₁_fn
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))) *
          ((S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
              (S.dbar ⟨0, by decide⟩) ω *
           ((S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator
              (S.dbar ⟨1, by decide⟩) ω *
            (S.toPODTRSystem.factualY ω -
              S.μ₁_val
                (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
                 S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
                 S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))))) P.μ := by
      simpa [S0, H1, G1, R1, r1, I0, I1, M1, Y, mul_assoc] using hr1_int
    calc
      ∫ ω, r1 ω ∂P.μ
          = ∫ ω, (1 / (η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
              η.e₁_fn
                (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
                 S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
                 S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))) *
            ((S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
                (S.dbar ⟨0, by decide⟩) ω *
             ((S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator
                (S.dbar ⟨1, by decide⟩) ω *
              (S.toPODTRSystem.factualY ω -
                S.μ₁_val
                  (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
                   S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
                   S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)))) ∂P.μ := by
            apply MeasureTheory.integral_congr_ae
            exact Filter.Eventually.of_forall (fun ω => by
              simp [r1, G1, R1, I0, I1, M1, Y, S0, H1])
      _ = 0 := by
            simpa using
              weighted_residual_integral_zero_stage1 S h_overlap hA h_y2
                (fun h : γ 1 × δ × γ 0 =>
                  1 / (η.e₀_fn h.2.2 * η.e₁_fn h)) hg_meas h_int
  have hmoment_eq :
      (fun ω => S.seqDRMomentFunctional η (S.factualZ ω) S.θ₀)
        =ᵐ[P.μ] (fun ω => base ω + r0 ω + r1 ω + crossInd ω) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hI0eq :
        indEq (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)
            (S.dbar ⟨0, by decide⟩) = I0 ω := by
      simpa [I0] using indEq_factualD0_eq_indicator S ω
    have hI1eq :
        indEq (S.toPODTRSystem.factualD ⟨1, by decide⟩ ω)
            (S.dbar ⟨1, by decide⟩) = I1 ω := by
      simpa [I1] using indEq_factualD1_eq_indicator S ω
    have hI0eqn :
        indEq (S.toPODTRSystem.factualD 0 ω) (S.dbar 0) = I0 ω := by
      simpa using hI0eq
    have hI1eqn :
        indEq (S.toPODTRSystem.factualD 1 ω) (S.dbar 1) = I1 ω := by
      simpa using hI1eq
    change S.seqDRMomentFunctional η (S.factualZ ω) S.θ₀ =
      base ω + r0 ω + r1 ω + crossInd ω
    simp [DTREstimationSystem.seqDRMomentFunctional, Causalean.Estimation.DTR.seqDRMoment,
      DTREstimationSystem.factualZ, projS₀, projD₀, projS₁, projD₁, projY, histH₁,
      hI0eqn, hI1eqn, S0, H1, Y, I0, I1, M0, M1, G0, G1, R0, R1, r0, r1,
      dμ0, dμ1, i0, i10, i11, crossInd, base, div_eq_mul_inv]
    ring
  have hpushZ :
      ∫ z, S.seqDRMomentFunctional η z S.θ₀ ∂(S.P_Z)
        = ∫ ω, S.seqDRMomentFunctional η (S.factualZ ω) S.θ₀ ∂P.μ := by
    unfold DTREstimationSystem.P_Z
    rw [MeasureTheory.integral_map S.measurable_factualZ.aemeasurable
      (S.measurable_seqDRMomentFunctional η S.θ₀).aestronglyMeasurable]
  have hΩ_to_cross :
      ∫ ω, S.seqDRMomentFunctional η (S.factualZ ω) S.θ₀ ∂P.μ
        = ∫ ω, crossInd ω ∂P.μ := by
    calc
      ∫ ω, S.seqDRMomentFunctional η (S.factualZ ω) S.θ₀ ∂P.μ
          = ∫ ω, base ω + r0 ω + r1 ω + crossInd ω ∂P.μ :=
            MeasureTheory.integral_congr_ae hmoment_eq
      _ = (((∫ ω, base ω ∂P.μ) + ∫ ω, r0 ω ∂P.μ) +
            ∫ ω, r1 ω ∂P.μ) + ∫ ω, crossInd ω ∂P.μ := by
            have h2 :
                ∫ ω, (base ω + r0 ω) + r1 ω ∂P.μ =
                  (∫ ω, base ω + r0 ω ∂P.μ) + ∫ ω, r1 ω ∂P.μ := by
              simpa [Pi.add_apply] using
                integral_add (μ := P.μ) (f := fun ω => base ω + r0 ω)
                  (g := r1) (hbase_int.add hr0_int) hr1_int
            have h3 :
                ∫ ω, base ω + r0 ω ∂P.μ =
                  (∫ ω, base ω ∂P.μ) + ∫ ω, r0 ω ∂P.μ := by
              simpa [Pi.add_apply] using
                integral_add (μ := P.μ) (f := base) (g := r0) hbase_int hr0_int
            calc
              ∫ ω, base ω + r0 ω + r1 ω + crossInd ω ∂P.μ
                  = (∫ ω, (base ω + r0 ω) + r1 ω ∂P.μ) +
                      ∫ ω, crossInd ω ∂P.μ := by
                    simpa [Pi.add_apply, add_assoc] using
                      integral_add (μ := P.μ)
                        (f := fun ω => (base ω + r0 ω) + r1 ω) (g := crossInd)
                        ((hbase_int.add hr0_int).add hr1_int) hcrossInd_int
              _ = (((∫ ω, base ω ∂P.μ) + ∫ ω, r0 ω ∂P.μ) +
                    ∫ ω, r1 ω ∂P.μ) + ∫ ω, crossInd ω ∂P.μ := by
                    rw [h2, h3]
      _ = ∫ ω, crossInd ω ∂P.μ := by
            rw [hbase_zero, hr0_zero, hr1_zero]
            ring
  have hp0_int : Integrable p0 P.μ := by
    let V0 : P.Ω → ℝ := fun ω => S.e₀_val (S0 ω) / η.e₀_fn (S0 ω)
    have hV0_meas : Measurable V0 := by
      dsimp [V0]
      exact (S.e₀_meas.comp hS0_meas).div (η.e₀_meas.comp hS0_meas)
    have hV0_bound : ∀ᵐ ω ∂P.μ, ‖V0 ω‖ ≤ ε⁻¹ := by
      refine Filter.Eventually.of_forall ?_
      intro ω
      have hposη : 0 < η.e₀_fn (S0 ω) := hη0_pos (S0 ω)
      have hinv : (η.e₀_fn (S0 ω))⁻¹ ≤ ε⁻¹ :=
        (inv_le_inv₀ hposη h_overlap.1).2 (hη0_lower (S0 ω))
      have hS_abs : |S.e₀_val (S0 ω)| ≤ 1 := by
        rw [abs_of_pos (S.e₀_pos (S0 ω))]
        exact (S.e₀_lt_one (S0 ω)).le
      calc
        ‖V0 ω‖ = |S.e₀_val (S0 ω)| * |(η.e₀_fn (S0 ω))⁻¹| := by
          simp [V0, Real.norm_eq_abs, div_eq_mul_inv]
        _ = |S.e₀_val (S0 ω)| * (η.e₀_fn (S0 ω))⁻¹ := by
          rw [abs_of_pos (inv_pos.mpr hposη)]
        _ ≤ 1 * (η.e₀_fn (S0 ω))⁻¹ := by
          exact mul_le_mul_of_nonneg_right hS_abs (inv_nonneg.mpr hposη.le)
        _ ≤ 1 * ε⁻¹ := by
          exact mul_le_mul_of_nonneg_left hinv zero_le_one
        _ = ε⁻¹ := by ring
    have hp : Integrable (fun ω => V0 ω * dμ0 ω) P.μ :=
      hdμ0_int.bdd_mul hV0_meas.aestronglyMeasurable hV0_bound
    exact hp.congr (Filter.Eventually.of_forall (fun ω => by
      simp [p0, V0, dμ0, S0]
      ring))
  have hp1_int : Integrable p1 P.μ := by
    let V1 : P.Ω → ℝ := fun ω =>
      indEq (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω) (S.dbar ⟨0, by decide⟩) *
        (S.e₁_val (H1 ω) / (η.e₀_fn (S0 ω) * η.e₁_fn (H1 ω)))
    have hInd_meas : Measurable
        (fun ω => indEq (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)
          (S.dbar ⟨0, by decide⟩)) := by
      simpa [I0] using ((S.toPODTRSystem.dVar ⟨0, by decide⟩).measurable_indicator
        (S.dbar ⟨0, by decide⟩))
    have hV1_meas : Measurable V1 := by
      dsimp [V1]
      exact hInd_meas.mul
        ((S.e₁_meas.comp hH1_meas).div
          ((η.e₀_meas.comp hS0_meas).mul (η.e₁_meas.comp hH1_meas)))
    have hV1_bound : ∀ᵐ ω ∂P.μ, ‖V1 ω‖ ≤ (ε * ε)⁻¹ := by
      refine Filter.Eventually.of_forall ?_
      intro ω
      have hpos0 : 0 < η.e₀_fn (S0 ω) := hη0_pos (S0 ω)
      have hpos1 : 0 < η.e₁_fn (H1 ω) := hη1_pos (H1 ω)
      have hprod_pos : 0 < η.e₀_fn (S0 ω) * η.e₁_fn (H1 ω) :=
        mul_pos hpos0 hpos1
      have hprod_le : ε * ε ≤ η.e₀_fn (S0 ω) * η.e₁_fn (H1 ω) :=
        mul_le_mul (hη0_lower (S0 ω)) (hη1_lower (H1 ω))
          h_overlap.1.le hpos0.le
      have hinv : (η.e₀_fn (S0 ω) * η.e₁_fn (H1 ω))⁻¹ ≤ (ε * ε)⁻¹ :=
        (inv_le_inv₀ hprod_pos (mul_pos h_overlap.1 h_overlap.1)).2 hprod_le
      have hS_abs : |S.e₁_val (H1 ω)| ≤ 1 := by
        rw [abs_of_pos (S.e₁_pos (H1 ω))]
        exact (S.e₁_lt_one (H1 ω)).le
      have hInd_abs :
          |indEq (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)
            (S.dbar ⟨0, by decide⟩)| ≤ 1 := by
        unfold indEq
        split <;> simp
      have hratio_norm :
          ‖S.e₁_val (H1 ω) / (η.e₀_fn (S0 ω) * η.e₁_fn (H1 ω))‖
            ≤ (ε * ε)⁻¹ := by
        calc
          ‖S.e₁_val (H1 ω) / (η.e₀_fn (S0 ω) * η.e₁_fn (H1 ω))‖
              = |S.e₁_val (H1 ω)| / |η.e₀_fn (S0 ω) * η.e₁_fn (H1 ω)| := by
                rw [Real.norm_eq_abs, abs_div]
          _ = |S.e₁_val (H1 ω)| * (η.e₀_fn (S0 ω) * η.e₁_fn (H1 ω))⁻¹ := by
                rw [abs_of_pos hprod_pos, div_eq_mul_inv]
          _ ≤ 1 * (η.e₀_fn (S0 ω) * η.e₁_fn (H1 ω))⁻¹ := by
                exact mul_le_mul_of_nonneg_right hS_abs (inv_nonneg.mpr hprod_pos.le)
          _ ≤ 1 * (ε * ε)⁻¹ := by
                exact mul_le_mul_of_nonneg_left hinv zero_le_one
          _ = (ε * ε)⁻¹ := by ring
      calc
        ‖V1 ω‖ =
            ‖indEq (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)
              (S.dbar ⟨0, by decide⟩)‖ *
            ‖S.e₁_val (H1 ω) / (η.e₀_fn (S0 ω) * η.e₁_fn (H1 ω))‖ := by
          simp [V1, norm_mul]
        _ ≤ 1 * (ε * ε)⁻¹ := by
          exact mul_le_mul
            (by simpa [Real.norm_eq_abs] using hInd_abs)
            hratio_norm (norm_nonneg _) zero_le_one
        _ = (ε * ε)⁻¹ := by ring
    have hp : Integrable (fun ω => V1 ω * dμ1 ω) P.μ :=
      hdμ1_int.bdd_mul hV1_meas.aestronglyMeasurable hV1_bound
    exact hp.congr (Filter.Eventually.of_forall (fun ω => by
      simp [p1, V1, dμ1, S0, H1]
      ring))
  have hcrossProp_int : Integrable crossProp P.μ := by
    simpa [crossProp, sub_eq_add_neg, add_assoc] using
      ((hdμ0_int.add hi10_int).sub hp0_int).sub hp1_int
  have hcross_to_prop :
      ∫ ω, crossInd ω ∂P.μ = ∫ ω, crossProp ω ∂P.μ := by
    have hi0_prop : ∫ ω, i0 ω ∂P.μ = ∫ ω, p0 ω ∂P.μ := by
      have hf_meas : Measurable
          (fun s₀ => (η.μ₀_fn s₀ - S.μ₀_val s₀) / η.e₀_fn s₀) :=
        (η.μ₀_meas.sub S.μ₀_meas).div η.e₀_meas
      have hf_ind_int : Integrable
          (fun ω => ((η.μ₀_fn (S0 ω) - S.μ₀_val (S0 ω)) /
            η.e₀_fn (S0 ω)) * I0 ω) P.μ := by
        refine hi0_int.congr ?_
        exact Filter.Eventually.of_forall (fun ω => by
          simp [i0, I0, G0, dμ0, S0]
          ring)
      calc
        ∫ ω, i0 ω ∂P.μ
            = ∫ ω, ((η.μ₀_fn (S0 ω) - S.μ₀_val (S0 ω)) /
                η.e₀_fn (S0 ω)) * I0 ω ∂P.μ := by
              apply MeasureTheory.integral_congr_ae
              exact Filter.Eventually.of_forall (fun ω => by
                simp [i0, I0, G0, dμ0, S0]
                ring)
        _ = ∫ ω, ((η.μ₀_fn (S0 ω) - S.μ₀_val (S0 ω)) /
                η.e₀_fn (S0 ω)) * S.e₀_val (S0 ω) ∂P.μ := by
              simpa [S0, I0] using
                indicator_to_propScore_integral_stage0 S
                  (fun s₀ => (η.μ₀_fn s₀ - S.μ₀_val s₀) / η.e₀_fn s₀)
                  hf_meas hf_ind_int
        _ = ∫ ω, p0 ω ∂P.μ := by
              apply MeasureTheory.integral_congr_ae
              exact Filter.Eventually.of_forall (fun ω => by simp [p0, dμ0, S0])
    have hi11_prop : ∫ ω, i11 ω ∂P.μ = ∫ ω, p1 ω ∂P.μ := by
      have hf_meas : Measurable
          (fun h : γ 1 × δ × γ 0 =>
            indEq h.2.1 (S.dbar 0) *
              ((η.μ₁_fn h - S.μ₁_val h) / (η.e₀_fn h.2.2 * η.e₁_fn h))) := by
        have hind : Measurable (fun h : γ 1 × δ × γ 0 => indEq h.2.1 (S.dbar 0)) := by
          have hset : MeasurableSet {x : δ | x = S.dbar 0} := MeasurableSet.singleton _
          have hbase : Measurable (Set.indicator {x : δ | x = S.dbar 0}
              (fun _ => (1 : ℝ))) := measurable_const.indicator hset
          have heq : (fun x : δ => indEq x (S.dbar 0)) =
              Set.indicator {x : δ | x = S.dbar 0} (fun _ => (1 : ℝ)) := by
            funext x
            unfold indEq
            by_cases hx : x = S.dbar 0 <;> simp [hx]
          exact (heq ▸ hbase).comp measurable_snd.fst
        exact hind.mul ((η.μ₁_meas.sub S.μ₁_meas).div
          ((η.e₀_meas.comp measurable_snd.snd).mul η.e₁_meas))
      have hf_ind_int : Integrable
          (fun ω => (indEq (H1 ω).2.1 (S.dbar 0) *
              ((η.μ₁_fn (H1 ω) - S.μ₁_val (H1 ω)) /
                (η.e₀_fn (H1 ω).2.2 * η.e₁_fn (H1 ω)))) * I1 ω) P.μ := by
        refine hi11_int.congr ?_
        exact Filter.Eventually.of_forall (fun ω => by
          have hI0eq :
              indEq (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)
                  (S.dbar ⟨0, by decide⟩) = I0 ω := by
            simpa [I0] using indEq_factualD0_eq_indicator S ω
          have hI0eqn :
              indEq (S.toPODTRSystem.factualD 0 ω) (S.dbar 0) = I0 ω := by
            simpa using hI0eq
          simp [i11, I0, I1, G1, dμ1, H1, S0, hI0eqn]
          ring)
      calc
        ∫ ω, i11 ω ∂P.μ
            = ∫ ω, (indEq (H1 ω).2.1 (S.dbar 0) *
                ((η.μ₁_fn (H1 ω) - S.μ₁_val (H1 ω)) /
                  (η.e₀_fn (H1 ω).2.2 * η.e₁_fn (H1 ω)))) * I1 ω ∂P.μ := by
              apply MeasureTheory.integral_congr_ae
              exact Filter.Eventually.of_forall (fun ω => by
                have hI0eq :
                    indEq (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)
                        (S.dbar ⟨0, by decide⟩) = I0 ω := by
                  simpa [I0] using indEq_factualD0_eq_indicator S ω
                have hI0eqn :
                    indEq (S.toPODTRSystem.factualD 0 ω) (S.dbar 0) = I0 ω := by
                  simpa using hI0eq
                simp [i11, I0, I1, G1, dμ1, H1, S0, hI0eqn]
                ring)
        _ = ∫ ω, (indEq (H1 ω).2.1 (S.dbar 0) *
                ((η.μ₁_fn (H1 ω) - S.μ₁_val (H1 ω)) /
                  (η.e₀_fn (H1 ω).2.2 * η.e₁_fn (H1 ω)))) *
                S.e₁_val (H1 ω) ∂P.μ := by
              simpa [H1, I1] using
                indicator_to_propScore_integral_stage1 S
                  (fun h : γ 1 × δ × γ 0 =>
                    indEq h.2.1 (S.dbar 0) *
                      ((η.μ₁_fn h - S.μ₁_val h) /
                        (η.e₀_fn h.2.2 * η.e₁_fn h)))
                  hf_meas hf_ind_int
        _ = ∫ ω, p1 ω ∂P.μ := by
              apply MeasureTheory.integral_congr_ae
              exact Filter.Eventually.of_forall (fun ω => by simp [p1, dμ1, H1, S0])
    calc
      ∫ ω, crossInd ω ∂P.μ
          = ((∫ ω, dμ0 ω ∂P.μ) + ∫ ω, i10 ω ∂P.μ) -
              ∫ ω, i0 ω ∂P.μ - ∫ ω, i11 ω ∂P.μ := by
            have h2 :
                ∫ ω, dμ0 ω + i10 ω - i0 ω ∂P.μ =
                  (∫ ω, dμ0 ω + i10 ω ∂P.μ) - ∫ ω, i0 ω ∂P.μ := by
              simpa [Pi.sub_apply] using
                integral_sub (μ := P.μ) (f := fun ω => dμ0 ω + i10 ω) (g := i0)
                  (hdμ0_int.add hi10_int) hi0_int
            have h3 :
                ∫ ω, dμ0 ω + i10 ω ∂P.μ =
                  (∫ ω, dμ0 ω ∂P.μ) + ∫ ω, i10 ω ∂P.μ := by
              simpa [Pi.add_apply] using
                integral_add (μ := P.μ) (f := dμ0) (g := i10) hdμ0_int hi10_int
            calc
              ∫ ω, crossInd ω ∂P.μ
                  = ∫ ω, (dμ0 ω + i10 ω - i0 ω) - i11 ω ∂P.μ := by
                    apply MeasureTheory.integral_congr_ae
                    exact Filter.Eventually.of_forall (fun ω => by simp [crossInd])
              _ = (∫ ω, dμ0 ω + i10 ω - i0 ω ∂P.μ) -
                    ∫ ω, i11 ω ∂P.μ := by
                    simpa [Pi.sub_apply] using
                      integral_sub (μ := P.μ)
                        (f := fun ω => dμ0 ω + i10 ω - i0 ω) (g := i11)
                        ((hdμ0_int.add hi10_int).sub hi0_int) hi11_int
              _ = ((∫ ω, dμ0 ω ∂P.μ) + ∫ ω, i10 ω ∂P.μ) -
                    ∫ ω, i0 ω ∂P.μ - ∫ ω, i11 ω ∂P.μ := by
                    rw [h2, h3]
      _ = ((∫ ω, dμ0 ω ∂P.μ) + ∫ ω, i10 ω ∂P.μ) -
              ∫ ω, p0 ω ∂P.μ - ∫ ω, p1 ω ∂P.μ := by
            rw [hi0_prop, hi11_prop]
      _ = ∫ ω, crossProp ω ∂P.μ := by
            have h2 :
                ∫ ω, dμ0 ω + i10 ω - p0 ω ∂P.μ =
                  (∫ ω, dμ0 ω + i10 ω ∂P.μ) - ∫ ω, p0 ω ∂P.μ := by
              simpa [Pi.sub_apply] using
                integral_sub (μ := P.μ) (f := fun ω => dμ0 ω + i10 ω) (g := p0)
                  (hdμ0_int.add hi10_int) hp0_int
            have h3 :
                ∫ ω, dμ0 ω + i10 ω ∂P.μ =
                  (∫ ω, dμ0 ω ∂P.μ) + ∫ ω, i10 ω ∂P.μ := by
              simpa [Pi.add_apply] using
                integral_add (μ := P.μ) (f := dμ0) (g := i10) hdμ0_int hi10_int
            calc
              ((∫ ω, dμ0 ω ∂P.μ) + ∫ ω, i10 ω ∂P.μ) -
                  ∫ ω, p0 ω ∂P.μ - ∫ ω, p1 ω ∂P.μ
                  = (∫ ω, dμ0 ω + i10 ω - p0 ω ∂P.μ) -
                      ∫ ω, p1 ω ∂P.μ := by
                    rw [h2, h3]
              _ = ∫ ω, (dμ0 ω + i10 ω - p0 ω) - p1 ω ∂P.μ := by
                    simpa [Pi.sub_apply] using
                      (integral_sub (μ := P.μ)
                        (f := fun ω => dμ0 ω + i10 ω - p0 ω) (g := p1)
                        ((hdμ0_int.add hi10_int).sub hp0_int) hp1_int).symm
              _ = ∫ ω, crossProp ω ∂P.μ := by
                    apply MeasureTheory.integral_congr_ae
                    exact Filter.Eventually.of_forall (fun ω => by simp [crossProp])
  have hcrossProp_eq_rem : crossProp =ᵐ[P.μ] remΩ := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hI0eq :
        indEq (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)
            (S.dbar ⟨0, by decide⟩) = I0 ω := by
      simpa [I0] using indEq_factualD0_eq_indicator S ω
    have hI0eqn :
        indEq (S.toPODTRSystem.factualD 0 ω) (S.dbar 0) = I0 ω := by
      simpa using hI0eq
    have hden0 : η.e₀_fn (S0 ω) ≠ 0 := (hη0_pos (S0 ω)).ne'
    have hden1 : η.e₁_fn (H1 ω) ≠ 0 := (hη1_pos (H1 ω)).ne'
    have hden01 : η.e₀_fn (S0 ω) * η.e₁_fn (H1 ω) ≠ 0 :=
      mul_ne_zero hden0 hden1
    have hden0n :
        η.e₀_fn (S.toPODTRSystem.factualS 0 ω) ≠ 0 := by
      simpa [S0] using hden0
    have hden1n :
        η.e₁_fn
          (S.toPODTRSystem.factualS 1 ω,
           S.toPODTRSystem.factualD 0 ω,
           S.toPODTRSystem.factualS 0 ω) ≠ 0 := by
      simpa [H1] using hden1
    have hden01n :
        η.e₀_fn (S.toPODTRSystem.factualS 0 ω) *
          η.e₁_fn
            (S.toPODTRSystem.factualS 1 ω,
             S.toPODTRSystem.factualD 0 ω,
             S.toPODTRSystem.factualS 0 ω) ≠ 0 :=
      mul_ne_zero hden0n hden1n
    simp [crossProp, remΩ, rem0, rem1, p0, p1, i10, G0, dμ0, dμ1, S0, H1,
      hI0eqn, div_eq_mul_inv]
    field_simp [hden0, hden1, hden01, hden0n, hden1n, hden01n]
    ring
  have hrem0_meas : Measurable rem0 := by
    dsimp [rem0]
    exact (((η.e₀_meas.sub S.e₀_meas).mul (measurable_const.div η.e₀_meas)).mul
      (η.μ₀_meas.sub S.μ₀_meas))
  have hrem1_meas : Measurable rem1 := by
    have hind : Measurable (fun h : γ 1 × δ × γ 0 => indEq h.2.1 (S.dbar 0)) := by
      have hset : MeasurableSet {x : δ | x = S.dbar 0} := MeasurableSet.singleton _
      have hbase : Measurable (Set.indicator {x : δ | x = S.dbar 0}
          (fun _ => (1 : ℝ))) := measurable_const.indicator hset
      have heq : (fun x : δ => indEq x (S.dbar 0)) =
          Set.indicator {x : δ | x = S.dbar 0} (fun _ => (1 : ℝ)) := by
        funext x
        unfold indEq
        by_cases hx : x = S.dbar 0 <;> simp [hx]
      exact (heq ▸ hbase).comp measurable_snd.fst
    dsimp [rem1]
    exact (((hind.mul (η.e₁_meas.sub S.e₁_meas)).mul
      (measurable_const.div ((η.e₀_meas.comp measurable_snd.snd).mul η.e₁_meas))).mul
        (η.μ₁_meas.sub S.μ₁_meas))
  haveI : ENNReal.HolderTriple (2 : ENNReal) (2 : ENNReal) (1 : ENNReal) := by
    constructor
    simpa using ENNReal.inv_two_add_inv_two
  haveI : IsFiniteMeasure S.P_H₀ := by
    unfold DTREstimationSystem.P_H₀
    infer_instance
  haveI : IsFiniteMeasure S.P_H₁ := by
    unfold DTREstimationSystem.P_H₁
    infer_instance
  have hprod0_int : Integrable
      (fun s₀ => (η.μ₀_fn s₀ - S.μ₀_val s₀) *
        (η.e₀_fn s₀ - S.e₀_val s₀)) S.P_H₀ := by
    have hmul : MemLp
        (fun s₀ => (η.μ₀_fn s₀ - S.μ₀_val s₀) *
          (η.e₀_fn s₀ - S.e₀_val s₀)) 1 S.P_H₀ := by
      exact hΔe₀_memLp.mul hΔμ₀_memLp
    exact hmul.integrable (by norm_num)
  have hprod1_int : Integrable
      (fun h => (η.μ₁_fn h - S.μ₁_val h) *
        (η.e₁_fn h - S.e₁_val h)) S.P_H₁ := by
    have hmul : MemLp
        (fun h => (η.μ₁_fn h - S.μ₁_val h) *
          (η.e₁_fn h - S.e₁_val h)) 1 S.P_H₁ := by
      exact hΔe₁_memLp.mul hΔμ₁_memLp
    exact hmul.integrable (by norm_num)
  have hrem0_int : Integrable rem0 S.P_H₀ := by
    have hbound : ∀ᵐ s₀ ∂S.P_H₀,
        ‖(1 / η.e₀_fn s₀)‖ ≤ ε⁻¹ := by
      refine Filter.Eventually.of_forall ?_
      intro s₀
      have hle : (η.e₀_fn s₀)⁻¹ ≤ ε⁻¹ :=
        (inv_le_inv₀ (hη0_pos s₀) h_overlap.1).2 (hη0_lower s₀)
      rw [norm_div, norm_one, Real.norm_eq_abs, abs_of_pos (hη0_pos s₀)]
      simpa [one_div] using hle
    have hprod := hprod0_int.bdd_mul
      (measurable_const.div η.e₀_meas).aestronglyMeasurable hbound
    exact hprod.congr (Filter.Eventually.of_forall (fun s₀ => by
      simp [rem0]
      ring))
  have hrem1_int : Integrable rem1 S.P_H₁ := by
    let W : γ 1 × δ × γ 0 → ℝ := fun h =>
      indEq h.2.1 (S.dbar 0) * (1 / (η.e₀_fn h.2.2 * η.e₁_fn h))
    have hW_meas : Measurable W := by
      have hind : Measurable (fun h : γ 1 × δ × γ 0 => indEq h.2.1 (S.dbar 0)) := by
        have hset : MeasurableSet {x : δ | x = S.dbar 0} := MeasurableSet.singleton _
        have hbase : Measurable (Set.indicator {x : δ | x = S.dbar 0}
            (fun _ => (1 : ℝ))) := measurable_const.indicator hset
        have heq : (fun x : δ => indEq x (S.dbar 0)) =
            Set.indicator {x : δ | x = S.dbar 0} (fun _ => (1 : ℝ)) := by
          funext x
          unfold indEq
          by_cases hx : x = S.dbar 0 <;> simp [hx]
        exact (heq ▸ hbase).comp measurable_snd.fst
      exact hind.mul (measurable_const.div
        ((η.e₀_meas.comp measurable_snd.snd).mul η.e₁_meas))
    have hW_bound : ∀ᵐ h ∂S.P_H₁, ‖W h‖ ≤ (ε * ε)⁻¹ := by
      refine Filter.Eventually.of_forall ?_
      intro h
      have hpos0 : 0 < η.e₀_fn h.2.2 := hη0_pos h.2.2
      have hpos1 : 0 < η.e₁_fn h := hη1_pos h
      have hprod_pos : 0 < η.e₀_fn h.2.2 * η.e₁_fn h := mul_pos hpos0 hpos1
      have hprod_le : ε * ε ≤ η.e₀_fn h.2.2 * η.e₁_fn h :=
        mul_le_mul (hη0_lower h.2.2) (hη1_lower h)
          h_overlap.1.le hpos0.le
      have hinv : (η.e₀_fn h.2.2 * η.e₁_fn h)⁻¹ ≤ (ε * ε)⁻¹ :=
        (inv_le_inv₀ hprod_pos (mul_pos h_overlap.1 h_overlap.1)).2 hprod_le
      have hind : |indEq h.2.1 (S.dbar 0)| ≤ 1 := by
        unfold indEq
        split <;> simp
      calc
        ‖W h‖ =
            |indEq h.2.1 (S.dbar 0)| *
              |(η.e₀_fn h.2.2 * η.e₁_fn h)⁻¹| := by
          simp [W, div_eq_mul_inv, Real.norm_eq_abs, abs_mul]
        _ = |indEq h.2.1 (S.dbar 0)| *
              (η.e₀_fn h.2.2 * η.e₁_fn h)⁻¹ := by
          rw [abs_of_pos (inv_pos.mpr hprod_pos)]
        _ ≤ 1 * (η.e₀_fn h.2.2 * η.e₁_fn h)⁻¹ := by
          exact mul_le_mul_of_nonneg_right hind (inv_nonneg.mpr hprod_pos.le)
        _ ≤ 1 * (ε * ε)⁻¹ := by
          exact mul_le_mul_of_nonneg_left hinv zero_le_one
        _ = (ε * ε)⁻¹ := by ring
    have hprod := hprod1_int.bdd_mul hW_meas.aestronglyMeasurable hW_bound
    exact hprod.congr (Filter.Eventually.of_forall (fun h => by
      simp [rem1, W]
      ring))
  have hrem_to_Z :
      ∫ ω, remΩ ω ∂P.μ =
        ∫ z, rem0 (projS₀ z) + rem1 (histH₁ z) ∂(S.P_Z) := by
    have hZ_meas : Measurable
        (fun z : γ 0 × δ × γ 1 × δ × ℝ => rem0 (projS₀ z) + rem1 (histH₁ z)) :=
      (hrem0_meas.comp measurable_projS₀).add (hrem1_meas.comp measurable_histH₁)
    have hmap :
        ∫ z, rem0 (projS₀ z) + rem1 (histH₁ z) ∂(S.P_Z)
          = ∫ ω, rem0 (projS₀ (S.factualZ ω)) + rem1 (histH₁ (S.factualZ ω)) ∂P.μ := by
      unfold DTREstimationSystem.P_Z
      rw [MeasureTheory.integral_map S.measurable_factualZ.aemeasurable
        hZ_meas.aestronglyMeasurable]
    calc
      ∫ ω, remΩ ω ∂P.μ
          = ∫ ω, rem0 (projS₀ (S.factualZ ω)) + rem1 (histH₁ (S.factualZ ω)) ∂P.μ := by
            apply MeasureTheory.integral_congr_ae
            exact Filter.Eventually.of_forall (fun ω => by
              simp [remΩ, S0, H1, DTREstimationSystem.factualZ, projS₀,
                projD₀, projS₁, histH₁])
      _ = ∫ z, rem0 (projS₀ z) + rem1 (histH₁ z) ∂(S.P_Z) := hmap.symm
  have hsplit :
      ∫ z, rem0 (projS₀ z) + rem1 (histH₁ z) ∂(S.P_Z)
        =
        ∫ s₀, rem0 s₀ ∂(S.P_H₀) + ∫ h, rem1 h ∂(S.P_H₁) :=
    split_stage_history_integral S rem0 rem1 hrem0_meas hrem1_meas hrem0_int hrem1_int
  calc
    ∫ z, S.seqDRMomentFunctional η z S.θ₀ ∂(S.P_Z)
        = ∫ ω, S.seqDRMomentFunctional η (S.factualZ ω) S.θ₀ ∂P.μ := hpushZ
    _ = ∫ ω, crossInd ω ∂P.μ := hΩ_to_cross
    _ = ∫ ω, crossProp ω ∂P.μ := hcross_to_prop
    _ = ∫ ω, remΩ ω ∂P.μ := MeasureTheory.integral_congr_ae hcrossProp_eq_rem
    _ = ∫ z, rem0 (projS₀ z) + rem1 (histH₁ z) ∂(S.P_Z) := hrem_to_Z
    _ = ∫ s₀, rem0 s₀ ∂(S.P_H₀) + ∫ h, rem1 h ∂(S.P_H₁) := hsplit


end DTREstimationSystem

end DTR
end Estimation
end Causalean
