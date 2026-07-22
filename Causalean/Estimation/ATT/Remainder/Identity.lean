import Causalean.Estimation.ATT.Score.MeanZero
import Causalean.Estimation.ATT.Score.FiniteVar

/-!
Establishes the exact second-order remainder formula for the ATT AIPW moment.
The identity reduces the population moment error to products of propensity and
outcome-regression nuisance errors under the back-door ATT setup.
-/

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# AIPW second-order remainder identity (ATT)

This file isolates the *exact algebraic identity* underlying the ATT AIPW
remainder bound.  Expanding

    m_AIPW(η, z, θ₀)
      = A · (Y − μ̂₀(X))
        − (1 − A) · (ê(X) / (1 − ê(X))) · (Y − μ̂₀(X))
        − A · θ₀

around the truth `η₀ = (μ₀_val, e_val)` and integrating against `P_Z` cancels
the zeroth and first-order terms (Neyman orthogonality), leaving a *single*
cross-product:

    ∫ m_AIPW(η, z, θ₀) dP_Z
      = ∫ ((ê − e_val) / (1 − ê)) · (μ̂₀ − μ₀_val) dP_X.

Compared to the ATE counterpart in `Estimation/ATE/Remainder/Identity.lean`,
the ATT remainder has only **one** μ-residual (the control-arm
`μ₀ = E[Y(0) | X]`); the treated-arm contribution to the moment is
`A · (Y − μ̂₀)`, which, under unconfoundedness, integrates to
`E[e_val · (μ₀_val − μ̂₀)]` regardless of `ê` — so the only `ê`-error appears
through the IPW correction term, weighted by `1/(1 − ê)`.

This is essentially Hahn (1998) Theorem 1, equation 7, in its second-order
form.

The proof reduces `Y − μ₀_val(X)`-type residuals to σ(X)-conditional zero-means
via `μ₀_compat` (the control-arm version of `cate_backdoor`) and applies the
score pull-out lemmas from `ScorePullout.lean`.
-/

/-!
This file establishes the exact second-order remainder formula for the
augmented inverse-probability weighted estimator of the average treatment effect
on the treated, reducing estimation error to the product of propensity-score
and control-outcome-regression errors.
-/

namespace Causalean
namespace Estimation
namespace ATT

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO
open Causalean.Estimation.ATE.BackdoorEstimationSystem (projX projA projY indA)

namespace TreatedEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- **AIPW remainder identity (ATT).**

Under the one-sided ATT back-door assumption bundle, one-sided upper overlap,
positive marginal treatment probability, second moments on `Y` and `Y(0)`, L²
residual hypotheses for `μ̂₀ − μ₀_val` and `ê − e_val`, a.e. nuisance-side
one-sided overlap, and an integrability witness on the IPW arm, the population AIPW
moment at any
`η ∈ H_ε` equals the single cross-product

    ∫ ((ê(x) − e_val(x)) / (1 − ê(x))) · (μ̂₀(x) − μ₀_val(x)) dP_X.

Unlike the ATE identity (which has a sum over arms with weights
`1/ê + 1/(1 − ê)`), the ATT identity carries the explicit `(1 − ê)⁻¹`
factor — there is only one `ê`-divisor because only the control arm is
re-weighted in the ATT AIPW form. -/
-- Outline:
-- 1. Push `∫ … dP_Z` back to `∫ … dP.μ` via `integral_map`.
-- 2. Decompose the AIPW moment around `η₀` into:
--    (a) `m(η₀, z, θ₀)`, mean zero by `aipw_mean_zero_ATT`;
--    (b) `A · (μ₀_val(X) − μ̂₀(X))`, whose integral against `P.μ` factors
--        through `propScore true =ᵐ e_val ∘ factualX` into
--        `∫ e_val · (μ₀_val − μ̂₀) dP_X`;
--    (c) `−(1 − A) · (ê/(1 − ê)) · (Y − μ̂₀(X))
--          + (1 − A) · (e_val/(1 − e_val)) · (Y − μ₀_val(X))`,
--        which reduces (via `weighted_residual_false_integral_zero` on the
--        `Y − μ₀_val` half and the σ(X)-pull-out for the `Y − μ̂₀` half) to
--        `−∫ (ê/(1 − ê)) · (1 − e_val) · (μ₀_val − μ̂₀) dP_X`.
-- 3. Combine: the integrand simplifies to
--    `(e_val(1 − ê) − ê(1 − e_val))/(1 − ê) · (μ₀_val − μ̂₀)
--      = ((e_val − ê)/(1 − ê)) · (μ₀_val − μ̂₀)
--      = ((ê − e_val)/(1 − ê)) · (μ̂₀ − μ₀_val)`.
theorem aipw_remainder_identity_ATT
    (S : TreatedEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.OneSidedOverlap ε)
    (hA : S.toPOBackdoorSystem.ATTAssumptions)
    (hπ_pos : 0 < S.π_val)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_y0_2 : Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD false ω) ^ 2) P.μ)
    (η : TreatedNuisanceVec γ) (hη : η ∈ H_ε S ε)
    (hΔμ₀_memLp : MemLp (fun x => η.μ₀_fn x - S.μ₀_val x) 2 S.P_X)
    (hΔe_memLp : MemLp (fun x => η.e_fn x - S.e_val x) 2 S.P_X)
    (hIPW : Integrable (fun z =>
        (1 - indA z) * (η.e_fn (projX z) / (1 - η.e_fn (projX z)))
          * (projY z - η.μ₀_fn (projX z))) S.P_Z) :
    ∫ z, aipwMomentATTFunctional η z S.θ₀ ∂(S.P_Z)
      = ∫ x,
          (η.e_fn x - S.e_val x) / (1 - η.e_fn x)
            * (η.μ₀_fn x - S.μ₀_val x)
            ∂(S.P_X) := by
  let X : P.Ω → γ := S.toPOBackdoorSystem.factualX
  let Y : P.Ω → ℝ := S.toPOBackdoorSystem.factualY
  let A : P.Ω → ℝ := S.toPOBackdoorSystem.dVar.indicator true
  let F : P.Ω → ℝ := S.toPOBackdoorSystem.dVar.indicator false
  let dμ : P.Ω → ℝ := fun ω => η.μ₀_fn (X ω) - S.μ₀_val (X ω)
  let gηX : P.Ω → ℝ := fun ω => η.e_fn (X ω) / (1 - η.e_fn (X ω))
  let g₀X : P.Ω → ℝ := fun ω => S.e_val (X ω) / (1 - S.e_val (X ω))
  let truth : P.Ω → ℝ := fun ω =>
    aipwMomentATT (S.factualZ ω) S.μ₀_val S.e_val S.θ₀
  let cand : P.Ω → ℝ := fun ω =>
    aipwMomentATTFunctional η (S.factualZ ω) S.θ₀
  let resid : P.Ω → ℝ := fun ω => (gηX ω - g₀X ω) * (F ω * (Y ω - S.μ₀_val (X ω)))
  let crossInd : P.Ω → ℝ := fun ω => -A ω * dμ ω + F ω * gηX ω * dμ ω
  let crossProp : P.Ω → ℝ := fun ω =>
    -S.e_val (X ω) * dμ ω + (1 - S.e_val (X ω)) * gηX ω * dμ ω
  let remΩ : P.Ω → ℝ := fun ω =>
    (η.e_fn (X ω) - S.e_val (X ω)) / (1 - η.e_fn (X ω)) * dμ ω
  let remX : γ → ℝ := fun x =>
    (η.e_fn x - S.e_val x) / (1 - η.e_fn x) *
      (η.μ₀_fn x - S.μ₀_val x)
  haveI : IsFiniteMeasure S.P_Z := by
    unfold TreatedEstimationSystem.P_Z
    infer_instance
  haveI : IsFiniteMeasure S.P_X := by
    unfold TreatedEstimationSystem.P_X
    infer_instance
  have hindA_true : ∀ ω, indA (S.factualZ ω) = A ω := by
    intro ω
    by_cases hD : S.toPOBackdoorSystem.factualD ω = true
    · have hInd : A ω = 1 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_one hD
      simp [TreatedEstimationSystem.factualZ, indA, projA, A, hD, hInd]
    · have hF : S.toPOBackdoorSystem.factualD ω = false := by
        cases h' : S.toPOBackdoorSystem.factualD ω <;> simp [h'] at hD ⊢
      have hInd : A ω = 0 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_zero (x := true) hD
      simp [TreatedEstimationSystem.factualZ, indA, projA, A, hD, hInd]
  have hfalse_ind : ∀ ω, 1 - A ω = F ω := by
    intro ω
    have hsum : A ω + F ω = 1 := by
      simpa [A, F] using
        S.toPOBackdoorSystem.dVar.indicator_add_indicator_not ω
    linarith
  have hη_X : ∀ᵐ ω ∂P.μ, η.e_fn (X ω) ≤ 1 - ε := by
    simpa [X] using H_ε_overlap_factualX S hη
  have hY_L2 : MemLp Y 2 P.μ := by
    dsimp [Y]
    exact
      (memLp_two_iff_integrable_sq
        S.toPOBackdoorSystem.measurable_factualY.aestronglyMeasurable).2 h_y2
  have hμ₀_L2 : MemLp (fun ω => S.μ₀_val (X ω)) 2 P.μ := by
    have hY0_L2 : MemLp (S.toPOBackdoorSystem.YofD false) 2 P.μ := by
      exact
        (memLp_two_iff_integrable_sq
          (S.toPOBackdoorSystem.measurable_YofD false).aestronglyMeasurable).2 h_y0_2
    have hcond_L2 :
        MemLp (P.μ[S.toPOBackdoorSystem.YofD false |
          S.toPOBackdoorSystem.sigmaX]) 2 P.μ :=
      hY0_L2.condExp
    exact hcond_L2.ae_eq (by
      simpa [X] using S.μ₀_compat hA)
  have hdμ_L2 : MemLp dμ 2 P.μ := by
    have hd :=
      MemLp.comp_of_map (f := S.toPOBackdoorSystem.factualX) hΔμ₀_memLp
        S.toPOBackdoorSystem.measurable_factualX.aemeasurable
    simpa [dμ, X] using hd
  have hdμ_int : Integrable dμ P.μ := hdμ_L2.integrable (by norm_num)
  have hA_meas : Measurable A := by
    simpa [A] using S.toPOBackdoorSystem.dVar.measurable_indicator true
  have hF_meas : Measurable F := by
    simpa [F] using S.toPOBackdoorSystem.dVar.measurable_indicator false
  have hA_bound : ∀ᵐ ω ∂P.μ, ‖A ω‖ ≤ (1 : ℝ) := by
    filter_upwards with ω
    by_cases hD : S.toPOBackdoorSystem.factualD ω = true
    · have hInd : A ω = 1 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_one hD
      simp [hInd]
    · have hInd : A ω = 0 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_zero (x := true) hD
      simp [hInd]
  have hF_bound : ∀ᵐ ω ∂P.μ, ‖F ω‖ ≤ (1 : ℝ) := by
    filter_upwards with ω
    by_cases hD : S.toPOBackdoorSystem.factualD ω = false
    · have hInd : F ω = 1 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_one hD
      simp [hInd]
    · have hInd : F ω = 0 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_zero (x := false) hD
      simp [hInd]
  have hA_Linf : MemLp A ⊤ P.μ :=
    MemLp.of_bound hA_meas.aestronglyMeasurable (1 : ℝ) hA_bound
  have hF_Linf : MemLp F ⊤ P.μ :=
    MemLp.of_bound hF_meas.aestronglyMeasurable (1 : ℝ) hF_bound
  have htreatedη_int : Integrable (fun ω => A ω * (Y ω - η.μ₀_fn (X ω))) P.μ := by
    have hημ_L2 : MemLp (fun ω => η.μ₀_fn (X ω)) 2 P.μ := by
      have hsum := hdμ_L2.add hμ₀_L2
      refine hsum.ae_eq ?_
      filter_upwards with ω
      simp [dμ]
    have hL2 : MemLp (fun ω => A ω * (Y ω - η.μ₀_fn (X ω))) 2 P.μ := by
      simpa [mul_comm] using (hY_L2.sub hημ_L2).mul hA_Linf
    exact hL2.integrable (by norm_num)
  have htreated₀_int : Integrable (fun ω => A ω * (Y ω - S.μ₀_val (X ω))) P.μ := by
    have hL2 : MemLp (fun ω => A ω * (Y ω - S.μ₀_val (X ω))) 2 P.μ := by
      simpa [mul_comm] using (hY_L2.sub hμ₀_L2).mul hA_Linf
    exact hL2.integrable (by norm_num)
  have hAθ_int : Integrable (fun ω => A ω * S.θ₀) P.μ := by
    have hL2 : MemLp (fun ω => A ω * S.θ₀) 2 P.μ := by
      exact MemLp.mul' (p := ⊤) (q := 2) (r := 2)
        (memLp_const (α := P.Ω) S.θ₀) hA_Linf
    exact hL2.integrable (by norm_num)
  have hIPWΩ : Integrable (fun ω => F ω * gηX ω * (Y ω - η.μ₀_fn (X ω))) P.μ := by
    have hmap :
        Integrable
          (fun ω =>
            (1 - indA (S.factualZ ω)) *
              (η.e_fn (projX (S.factualZ ω)) /
                (1 - η.e_fn (projX (S.factualZ ω)))) *
              (projY (S.factualZ ω) - η.μ₀_fn (projX (S.factualZ ω)))) P.μ := by
      exact (MeasureTheory.integrable_map_measure
        hIPW.aestronglyMeasurable S.measurable_factualZ.aemeasurable).1 hIPW
    refine hmap.congr ?_
    filter_upwards with ω
    have hnot : 1 - indA (S.factualZ ω) = F ω := by
      rw [hindA_true ω, hfalse_ind ω]
    dsimp [gηX, X, Y]
    rw [hnot]
    rfl
  have hη_comp_int : Integrable cand P.μ := by
    have hsum := (htreatedη_int.sub hIPWΩ).sub hAθ_int
    refine hsum.congr ?_
    filter_upwards with ω
    unfold cand aipwMomentATTFunctional aipwMomentATT
    rw [hindA_true ω, hfalse_ind ω]
    simp [TreatedEstimationSystem.factualZ, projX, projY, A, F, X, Y, gηX]
  have htruth_sq :
      Integrable
        (fun z => (aipwMomentATT z S.μ₀_val S.e_val S.θ₀) ^ 2) S.P_Z :=
    aipw_finite_var_ATT S h_overlap hA h_y2 h_y0_2
  have htruth_meas :
      Measurable (fun z => aipwMomentATT z S.μ₀_val S.e_val S.θ₀) := by
    simpa [aipwMomentATTFunctional, η₀] using
      (measurable_aipwMomentATTFunctional (η := S.η₀) (θ := S.θ₀))
  have htruth_L2 :
      MemLp (fun z => aipwMomentATT z S.μ₀_val S.e_val S.θ₀) 2 S.P_Z :=
    (memLp_two_iff_integrable_sq htruth_meas.aestronglyMeasurable).2 htruth_sq
  have htruthPZ_int :
      Integrable (fun z => aipwMomentATT z S.μ₀_val S.e_val S.θ₀) S.P_Z :=
    htruth_L2.integrable (by norm_num)
  have htruth_int : Integrable truth P.μ := by
    exact (MeasureTheory.integrable_map_measure htruth_meas.aestronglyMeasurable
      S.measurable_factualZ.aemeasurable).1 (by
        simpa [TreatedEstimationSystem.P_Z] using htruthPZ_int)
  have hfalse₀_int :
      Integrable (fun ω => F ω * g₀X ω * (Y ω - S.μ₀_val (X ω))) P.μ := by
    have hcomb : Integrable (fun ω =>
        A ω * (Y ω - S.μ₀_val (X ω)) - truth ω - A ω * S.θ₀) P.μ :=
      (htreated₀_int.sub htruth_int).sub hAθ_int
    refine hcomb.congr ?_
    filter_upwards with ω
    unfold truth aipwMomentATT
    rw [hindA_true ω, hfalse_ind ω]
    simp [TreatedEstimationSystem.factualZ, projX, projY, A, F, X, Y, g₀X]
    ring
  have hIPW₀ : Integrable (fun ω =>
        (1 - S.toPOBackdoorSystem.dVar.indicator true ω)
          * (S.toPOBackdoorSystem.propScore true ω
              / (1 - S.toPOBackdoorSystem.propScore true ω))
          * (S.toPOBackdoorSystem.factualY ω
              - S.toPOBackdoorSystem.adjustedCE false ω)) P.μ := by
    refine hfalse₀_int.congr ?_
    filter_upwards [S.e_compat, S.μ₀_compat hA,
      S.control_cate_backdoor hA] with ω he hμ hcat
    have hμ_eq : S.μ₀_val (X ω) =
        S.toPOBackdoorSystem.adjustedCE false ω := by
      have hcate_eq : S.toPOBackdoorSystem.CATE false ω =
          S.μ₀_val (S.toPOBackdoorSystem.factualX ω) := by
        simpa [POBackdoorSystem.CATE] using hμ
      rw [← hcate_eq, hcat]
    have he_eq : S.e_val (X ω) = S.toPOBackdoorSystem.propScore true ω := by
      simpa [X] using he.symm
    have hfalse_eq :
        S.toPOBackdoorSystem.dVar.indicator false ω =
          1 - S.toPOBackdoorSystem.dVar.indicator true ω := by
      simpa [A, F] using (hfalse_ind ω).symm
    dsimp [F, g₀X, X, Y]
    rw [he_eq, hμ_eq, hfalse_eq]
  have htruth_zero :
      ∫ z, aipwMomentATT z S.μ₀_val S.e_val S.θ₀ ∂(S.P_Z) = 0 :=
    aipw_mean_zero_ATT S hA hπ_pos hIPW₀
  have htruth_zero_Ω : ∫ ω, truth ω ∂P.μ = 0 := by
    have hmap :
        ∫ z, aipwMomentATT z S.μ₀_val S.e_val S.θ₀ ∂(S.P_Z)
          = ∫ ω, truth ω ∂P.μ := by
      unfold TreatedEstimationSystem.P_Z
      exact MeasureTheory.integral_map S.measurable_factualZ.aemeasurable
        htruth_meas.aestronglyMeasurable
    simpa [hmap] using htruth_zero
  have hpushη :
      ∫ z, aipwMomentATTFunctional η z S.θ₀ ∂(S.P_Z)
        = ∫ ω, cand ω ∂P.μ := by
    unfold TreatedEstimationSystem.P_Z
    exact MeasureTheory.integral_map S.measurable_factualZ.aemeasurable
      (measurable_aipwMomentATTFunctional η S.θ₀).aestronglyMeasurable
  have hde_prod_int : Integrable
      (fun x => (η.e_fn x - S.e_val x) * (η.μ₀_fn x - S.μ₀_val x)) S.P_X := by
    haveI : ENNReal.HolderTriple (2 : ENNReal) (2 : ENNReal) (1 : ENNReal) := by
      constructor
      simpa using ENNReal.inv_two_add_inv_two
    have hmul : MemLp
        (fun x => (η.e_fn x - S.e_val x) * (η.μ₀_fn x - S.μ₀_val x)) 1 S.P_X :=
      by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          hΔμ₀_memLp.mul hΔe_memLp
    exact hmul.integrable (by norm_num)
  have hden_inv_Linf : MemLp (fun x => (1 - η.e_fn x)⁻¹) ⊤ S.P_X := by
    refine MemLp.of_bound ?_ ε⁻¹ ?_
    · exact (measurable_const.sub η.e_meas).inv.aestronglyMeasurable
    · filter_upwards [hη.1] with x hηx
      have hden : ε ≤ 1 - η.e_fn x := by linarith [hηx]
      have hη_false_pos_x : 0 < 1 - η.e_fn x := lt_of_lt_of_le h_overlap.1 hden
      have hle : (1 - η.e_fn x)⁻¹ ≤ ε⁻¹ :=
        (inv_le_inv₀ hη_false_pos_x h_overlap.1).2 hden
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hη_false_pos_x)]
      exact hle
  have hremX_int : Integrable remX S.P_X := by
    have hL1 : MemLp remX 1 S.P_X := by
      have hprod_L1 : MemLp
          (fun x => (η.e_fn x - S.e_val x) * (η.μ₀_fn x - S.μ₀_val x)) 1 S.P_X := by
        haveI : ENNReal.HolderTriple (2 : ENNReal) (2 : ENNReal) (1 : ENNReal) := by
          constructor
          simpa using ENNReal.inv_two_add_inv_two
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          hΔμ₀_memLp.mul hΔe_memLp
      have h := MemLp.mul' (p := 1) (q := ⊤) (r := 1)
        hden_inv_Linf hprod_L1
      refine h.ae_eq ?_
      filter_upwards with x
      dsimp [remX]
      rw [div_eq_mul_inv]
      ring
    exact hL1.integrable (by norm_num)
  have hremΩ_int : Integrable remΩ P.μ := by
    have hrem_meas : AEStronglyMeasurable remX S.P_X := by
      dsimp [remX]
      exact (((η.e_meas.sub S.e_meas).div (measurable_const.sub η.e_meas)).mul
        (η.μ₀_meas.sub S.μ₀_meas)).aestronglyMeasurable
    have hcomp := (MeasureTheory.integrable_map_measure hrem_meas
      S.toPOBackdoorSystem.measurable_factualX.aemeasurable).1 (by
        simpa [TreatedEstimationSystem.P_X] using hremX_int)
    simpa [TreatedEstimationSystem.P_X, remΩ, remX, X, dμ] using hcomp
  have hAdμ_int : Integrable (fun ω => A ω * dμ ω) P.μ := by
    have hL2 : MemLp (fun ω => A ω * dμ ω) 2 P.μ := by
      simpa [mul_comm] using hdμ_L2.mul hA_Linf
    exact hL2.integrable (by norm_num)
  have he_bound_px : ∀ᵐ x ∂S.P_X, ‖S.e_val x‖ ≤ (1 : ℝ) := by
    have hset : MeasurableSet {x : γ | ‖S.e_val x‖ ≤ (1 : ℝ)} := by
      exact measurableSet_Iic.preimage S.e_meas.norm
    unfold TreatedEstimationSystem.P_X
    rw [MeasureTheory.ae_map_iff S.toPOBackdoorSystem.measurable_factualX.aemeasurable hset]
    filter_upwards [S.propScore_true_nonneg_ae, hA.overlapControl, S.e_compat] with
      ω hnonneg hupper he
    have heq : S.e_val (S.toPOBackdoorSystem.factualX ω) =
        S.toPOBackdoorSystem.propScore true ω := he.symm
    rw [heq, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hnonneg], by linarith [hupper.le]⟩
  have he_Linf : MemLp S.e_val ⊤ S.P_X :=
    MemLp.of_bound S.e_meas.aestronglyMeasurable (1 : ℝ) he_bound_px
  have he_dμ_int : Integrable (fun ω => S.e_val (X ω) * dμ ω) P.μ := by
    have hpx_L2 : MemLp
        (fun x => S.e_val x * (η.μ₀_fn x - S.μ₀_val x)) 2 S.P_X := by
      exact hΔμ₀_memLp.mul he_Linf
    have hpx_int : Integrable
        (fun x => S.e_val x * (η.μ₀_fn x - S.μ₀_val x)) S.P_X :=
      hpx_L2.integrable (by norm_num)
    have hpx_meas : AEStronglyMeasurable
        (fun x => S.e_val x * (η.μ₀_fn x - S.μ₀_val x)) S.P_X :=
      (S.e_meas.mul (η.μ₀_meas.sub S.μ₀_meas)).aestronglyMeasurable
    have hcomp := (MeasureTheory.integrable_map_measure hpx_meas
      S.toPOBackdoorSystem.measurable_factualX.aemeasurable).1 (by
        simpa [TreatedEstimationSystem.P_X] using hpx_int)
    simpa [X, dμ] using hcomp
  have hresid_int : Integrable resid P.μ := by
    have hsum : Integrable (fun ω =>
        F ω * gηX ω * (Y ω - η.μ₀_fn (X ω)) +
        F ω * gηX ω * dμ ω -
        F ω * g₀X ω * (Y ω - S.μ₀_val (X ω))) P.μ := by
      have hgηdμ : Integrable (fun ω => F ω * gηX ω * dμ ω) P.μ := by
        have hηe_L2 : MemLp η.e_fn 2 S.P_X := by
          have hsum := hΔe_memLp.add (he_Linf.mono_exponent (by norm_num))
          refine hsum.ae_eq ?_
          filter_upwards with x
          simp only [Pi.add_apply]
          ring
        have hηe_dμ_L1 : MemLp
            (fun x => (η.μ₀_fn x - S.μ₀_val x) * η.e_fn x) 1 S.P_X := by
          haveI : ENNReal.HolderTriple (2 : ENNReal) (2 : ENNReal) (1 : ENNReal) := by
            constructor
            simpa using ENNReal.inv_two_add_inv_two
          exact (hηe_L2.mul hΔμ₀_memLp :
            MemLp (fun x => (η.μ₀_fn x - S.μ₀_val x) * η.e_fn x) 1 S.P_X)
        have hgηdμX_L1 : MemLp
            (fun x => (η.e_fn x / (1 - η.e_fn x)) *
              (η.μ₀_fn x - S.μ₀_val x)) 1 S.P_X := by
          have h := MemLp.mul' (p := 1) (q := ⊤) (r := 1)
            hden_inv_Linf hηe_dμ_L1
          refine h.ae_eq ?_
          filter_upwards with x
          rw [div_eq_mul_inv]
          ring
        have hgηdμX_int : Integrable
            (fun x => (η.e_fn x / (1 - η.e_fn x)) *
              (η.μ₀_fn x - S.μ₀_val x)) S.P_X :=
          hgηdμX_L1.integrable (by norm_num)
        have hgηdμΩ_int : Integrable (fun ω => gηX ω * dμ ω) P.μ := by
          have hgηdμX_meas : AEStronglyMeasurable
              (fun x => (η.e_fn x / (1 - η.e_fn x)) *
                (η.μ₀_fn x - S.μ₀_val x)) S.P_X :=
            ((η.e_meas.div (measurable_const.sub η.e_meas)).mul
              (η.μ₀_meas.sub S.μ₀_meas)).aestronglyMeasurable
          have hcomp := (MeasureTheory.integrable_map_measure hgηdμX_meas
            S.toPOBackdoorSystem.measurable_factualX.aemeasurable).1 (by
              simpa [TreatedEstimationSystem.P_X] using hgηdμX_int)
          simpa [TreatedEstimationSystem.P_X, gηX, dμ, X] using hcomp
        have hL1 : MemLp (fun ω => (gηX ω * dμ ω) * F ω) 1 P.μ := by
          have hbase : MemLp (fun ω => gηX ω * dμ ω) 1 P.μ :=
            memLp_one_iff_integrable.2 hgηdμΩ_int
          have h := MemLp.mul' (p := 1) (q := ⊤) (r := 1)
            hF_Linf hbase
          refine h.ae_eq ?_
          filter_upwards with ω
          ring
        exact (hL1.integrable (by norm_num)).congr
          (Filter.Eventually.of_forall fun ω => by ring)
      exact (hIPWΩ.add hgηdμ).sub hfalse₀_int
    refine hsum.congr ?_
    filter_upwards with ω
    dsimp [resid, gηX, g₀X, dμ]
    ring
  have hresid_zero : ∫ ω, resid ω ∂P.μ = 0 := by
    have hg_meas : Measurable (fun x =>
        η.e_fn x / (1 - η.e_fn x) - S.e_val x / (1 - S.e_val x)) :=
      (η.e_meas.div (measurable_const.sub η.e_meas)).sub
        (S.e_meas.div (measurable_const.sub S.e_meas))
    have h_int : Integrable
        (fun ω => (η.e_fn (X ω) / (1 - η.e_fn (X ω)) -
            S.e_val (X ω) / (1 - S.e_val (X ω))) *
          (F ω * (Y ω - S.μ₀_val (X ω)))) P.μ := by
      simpa [resid, gηX, g₀X, F, X, Y] using hresid_int
    simpa [resid, gηX, g₀X, F, X, Y] using
      weighted_residual_false_integral_zero S hA
        (fun x => η.e_fn x / (1 - η.e_fn x) - S.e_val x / (1 - S.e_val x))
        hg_meas h_int
  have hdecomp : cand =ᵐ[P.μ] fun ω => truth ω + crossInd ω - resid ω := by
    filter_upwards with ω
    unfold cand truth crossInd resid aipwMomentATTFunctional aipwMomentATT
    rw [hindA_true ω, hfalse_ind ω]
    simp [TreatedEstimationSystem.factualZ, projX, projY, A, F, X, Y, dμ, gηX, g₀X]
    ring
  have hcrossInd_int : Integrable crossInd P.μ := by
    have hci : Integrable (fun ω => cand ω - truth ω + resid ω) P.μ :=
      (hη_comp_int.sub htruth_int).add hresid_int
    refine hci.congr ?_
    filter_upwards [hdecomp] with ω hω
    rw [hω]
    ring
  have hcross_eq :
      ∫ ω, crossInd ω ∂P.μ = ∫ ω, crossProp ω ∂P.μ := by
    have hA_part :
        ∫ ω, (- (η.μ₀_fn (X ω) - S.μ₀_val (X ω))) * A ω ∂P.μ
          = ∫ ω, (- (η.μ₀_fn (X ω) - S.μ₀_val (X ω))) *
              S.e_val (X ω) ∂P.μ := by
      have hf_meas : Measurable (fun x => - (η.μ₀_fn x - S.μ₀_val x)) :=
        (η.μ₀_meas.sub S.μ₀_meas).neg
      have hf_ind_int : Integrable
          (fun ω => (-(η.μ₀_fn (X ω) - S.μ₀_val (X ω))) * A ω) P.μ := by
        have hneg : Integrable (fun ω => -(A ω * dμ ω)) P.μ := hAdμ_int.neg
        refine hneg.congr ?_
        filter_upwards with ω
        dsimp [dμ]
        ring
      simpa [X, A] using
        indicator_to_propScore_integral S hA true
          (fun x => - (η.μ₀_fn x - S.μ₀_val x)) hf_meas hf_ind_int
    have hF_part :
        ∫ ω, ((η.e_fn (X ω) / (1 - η.e_fn (X ω))) *
            (η.μ₀_fn (X ω) - S.μ₀_val (X ω))) * F ω ∂P.μ
          = ∫ ω, ((η.e_fn (X ω) / (1 - η.e_fn (X ω))) *
            (η.μ₀_fn (X ω) - S.μ₀_val (X ω))) *
              (1 - S.e_val (X ω)) ∂P.μ := by
      have hf_meas : Measurable (fun x =>
          (η.e_fn x / (1 - η.e_fn x)) * (η.μ₀_fn x - S.μ₀_val x)) :=
        (η.e_meas.div (measurable_const.sub η.e_meas)).mul
          (η.μ₀_meas.sub S.μ₀_meas)
      have hf_ind_int : Integrable
          (fun ω => ((η.e_fn (X ω) / (1 - η.e_fn (X ω))) *
            (η.μ₀_fn (X ω) - S.μ₀_val (X ω))) * F ω) P.μ := by
        have h := hcrossInd_int.add hAdμ_int
        refine h.congr ?_
        filter_upwards with ω
        dsimp [crossInd, dμ, gηX]
        ring
      simpa [X, F] using
        indicator_to_propScore_integral S hA false
          (fun x => (η.e_fn x / (1 - η.e_fn x)) *
            (η.μ₀_fn x - S.μ₀_val x)) hf_meas hf_ind_int
    calc
      ∫ ω, crossInd ω ∂P.μ
          = ∫ ω, (-(η.μ₀_fn (X ω) - S.μ₀_val (X ω))) * A ω +
              ((η.e_fn (X ω) / (1 - η.e_fn (X ω))) *
                (η.μ₀_fn (X ω) - S.μ₀_val (X ω))) * F ω ∂P.μ := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with ω
            dsimp [crossInd, dμ, gηX]
            ring
      _ = (∫ ω, (-(η.μ₀_fn (X ω) - S.μ₀_val (X ω))) * A ω ∂P.μ) +
            ∫ ω, ((η.e_fn (X ω) / (1 - η.e_fn (X ω))) *
                (η.μ₀_fn (X ω) - S.μ₀_val (X ω))) * F ω ∂P.μ := by
            rw [integral_add]
            · have hneg : Integrable (fun ω => -(A ω * dμ ω)) P.μ :=
                hAdμ_int.neg
              refine hneg.congr ?_
              filter_upwards with ω
              dsimp [dμ]
              ring
            · exact by
                have h := hcrossInd_int.add hAdμ_int
                refine h.congr ?_
                filter_upwards with ω
                dsimp [crossInd, dμ, gηX]
                ring
      _ = (∫ ω, (-(η.μ₀_fn (X ω) - S.μ₀_val (X ω))) *
              S.e_val (X ω) ∂P.μ) +
            ∫ ω, ((η.e_fn (X ω) / (1 - η.e_fn (X ω))) *
                (η.μ₀_fn (X ω) - S.μ₀_val (X ω))) *
                  (1 - S.e_val (X ω)) ∂P.μ := by
            rw [hA_part, hF_part]
      _ = ∫ ω, crossProp ω ∂P.μ := by
            have hfirst_int : Integrable
                (fun ω => (-(η.μ₀_fn (X ω) - S.μ₀_val (X ω))) *
                  S.e_val (X ω)) P.μ := by
              have hneg : Integrable (fun ω => -(S.e_val (X ω) * dμ ω)) P.μ :=
                he_dμ_int.neg
              refine hneg.congr ?_
              filter_upwards with ω
              dsimp [dμ]
              ring
            have hsecond_int : Integrable
                (fun ω => ((η.e_fn (X ω) / (1 - η.e_fn (X ω))) *
                    (η.μ₀_fn (X ω) - S.μ₀_val (X ω))) *
                      (1 - S.e_val (X ω))) P.μ := by
              refine (hremΩ_int.add he_dμ_int).congr ?_
              filter_upwards [hη_X] with ω hηω
              have hden_pos : 0 < 1 - η.e_fn (X ω) := by
                have hden_le : ε ≤ 1 - η.e_fn (X ω) := by linarith [hηω]
                exact lt_of_lt_of_le h_overlap.1 hden_le
              have hden : 1 - η.e_fn (X ω) ≠ 0 := hden_pos.ne'
              have hden' :
                  1 - η.e_fn (S.toPOBackdoorSystem.factualX ω) ≠ 0 := by
                simpa [X] using hden
              dsimp [remΩ, dμ, X]
              field_simp [hden']
              ring
            rw [← integral_add hfirst_int hsecond_int]
            apply MeasureTheory.integral_congr_ae
            filter_upwards with ω
            dsimp [crossProp, dμ, gηX]
            ring
  have hcrossProp_eq_rem : crossProp =ᵐ[P.μ] remΩ := by
    filter_upwards [hη_X] with ω hηω
    have hden_pos : 0 < 1 - η.e_fn (X ω) := by
      have hden_le : ε ≤ 1 - η.e_fn (X ω) := by linarith [hηω]
      exact lt_of_lt_of_le h_overlap.1 hden_le
    have hden : 1 - η.e_fn (X ω) ≠ 0 := hden_pos.ne'
    dsimp [crossProp, remΩ, dμ, gηX]
    field_simp [hden]
    ring
  have hrem_push : ∫ ω, remΩ ω ∂P.μ = ∫ x, remX x ∂(S.P_X) := by
    rw [TreatedEstimationSystem.P_X]
    have hrem_meas : Measurable remX := by
      dsimp [remX]
      exact (((η.e_meas.sub S.e_meas).div (measurable_const.sub η.e_meas)).mul
        (η.μ₀_meas.sub S.μ₀_meas))
    rw [MeasureTheory.integral_map S.toPOBackdoorSystem.measurable_factualX.aemeasurable
      hrem_meas.aestronglyMeasurable]
  calc
    ∫ z, aipwMomentATTFunctional η z S.θ₀ ∂(S.P_Z)
        = ∫ ω, cand ω ∂P.μ := hpushη
    _ = ∫ ω, truth ω + crossInd ω - resid ω ∂P.μ :=
          MeasureTheory.integral_congr_ae hdecomp
    _ = ∫ ω, (truth + crossInd) ω - resid ω ∂P.μ := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with ω
          rfl
    _ = (∫ ω, truth ω ∂P.μ) + (∫ ω, crossInd ω ∂P.μ) -
          (∫ ω, resid ω ∂P.μ) := by
          rw [integral_sub (htruth_int.add hcrossInd_int) hresid_int]
          rw [show (fun a => (truth + crossInd) a) =
              (fun a => truth a + crossInd a) by
            funext a
            rfl]
          rw [integral_add htruth_int hcrossInd_int]
    _ = ∫ ω, crossInd ω ∂P.μ := by
          rw [htruth_zero_Ω, hresid_zero]
          ring
    _ = ∫ ω, crossProp ω ∂P.μ := hcross_eq
    _ = ∫ ω, remΩ ω ∂P.μ := MeasureTheory.integral_congr_ae hcrossProp_eq_rem
    _ = ∫ x, remX x ∂(S.P_X) := hrem_push

end TreatedEstimationSystem

end ATT
end Estimation
end Causalean
