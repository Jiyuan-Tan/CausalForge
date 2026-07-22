/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# AIPW second-order remainder bound (ATT)

This file contains the quantitative `L²(P_X) × L²(P_X)` cross-product bound on
the ATT AIPW remainder.  The exact remainder identity is established in
`Remainder/Identity.lean`; here we apply Cauchy–Schwarz to the resulting single
cross-product (one factor `μ̂₀ − μ₀_val`, one factor `ê − e_val`) and bound the
`(1 − ê)⁻¹` weight by `1/ε` under one-sided overlap `ê ≤ 1 − ε`.

Compared to the ATE bound (`Estimation/ATE/Remainder/Bound.lean`), the ATT
remainder has only **one** product `‖Δμ₀‖ · ‖Δe‖` rather than a sum over arms;
the constant simplifies accordingly.
-/

import Causalean.Estimation.ATT.Remainder.Identity
import Causalean.Stat.Limit.Convergence
import Causalean.Stat.Orthogonality.ConditionalOp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-! # AIPW Remainder Bound (ATT)

This file turns the exact augmented inverse-probability weighted remainder
identity for the average treatment effect on the treated into a quantitative
second-order bound. It bounds the population moment error by the product of the
control-outcome-regression error and the propensity-score error under one-sided
overlap, using the constant `aipw_rem_const_ATT ε = 1 / ε`.

The public results are `aipw_remainder_bound_ATT`, the deterministic L² product
bound, and `aipw_remainder_op_ATT`, the stochastic `o_p(n^{-1/2})` consequence
used by the ATT double-machine-learning theorem. Parallel to
`Estimation/ATE/Remainder/Bound.lean`. -/

namespace Causalean
namespace Estimation
namespace ATT

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat

namespace TreatedEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- **AIPW remainder constant for one-sided overlap `ε` (ATT version).**

Under `ê ≤ 1 − ε`, the IPW reweighting `1/(1 − ê)` is bounded by `1/ε`;
combined with the single cross-product from `aipw_remainder_identity_ATT`,
this gives the L² product bound below. -/
noncomputable def aipw_rem_const_ATT (ε : ℝ) : ℝ := 1 / ε

/-! ## Headline remainder bound -/

/-- **AIPW remainder bound (ATT).**

Under the one-sided ATT back-door assumption bundle, a.e. one-sided upper overlap,
and integrability hypotheses, the population AIPW moment at any
`η ∈ H_ε` is bounded by

    `aipw_rem_const_ATT ε * ‖μ̂₀ − μ₀_val‖_{L²(P_X)} * ‖ê − e_val‖_{L²(P_X)}`,

where `aipw_rem_const_ATT ε = 1/ε`.  Direct corollary of
`aipw_remainder_identity_ATT` plus Cauchy–Schwarz on the single cross-product,
using `(1 − ê)⁻¹ ≤ 1/ε`. -/
-- Outline:
-- 1. Apply `aipw_remainder_identity_ATT` to rewrite
--    `|∫ m_AIPW(η, z, θ₀) dP_Z|` as `|∫ ((ê − e_val)/(1 − ê))·(μ̂₀ − μ₀_val) dP_X|`.
-- 2. Bound `|((ê − e_val)/(1 − ê))·(μ̂₀ − μ₀_val)| ≤ (1/ε)·|(ê − e_val)·(μ̂₀ − μ₀_val)|`
--    `P_X`-a.e. on `H_ε` (since `ê ≤ 1 − ε ⇒ 1/(1 − ê) ≤ 1/ε`).
-- 3. Apply `integral_abs_mul_le_eLpNorm_mul_eLpNorm` to the product
--    `(ê − e_val) · (μ̂₀ − μ₀_val)` to obtain the L² product bound.
theorem aipw_remainder_bound_ATT
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
        (1 - Causalean.Estimation.ATE.BackdoorEstimationSystem.indA z)
          * (η.e_fn (Causalean.Estimation.ATE.BackdoorEstimationSystem.projX z)
              / (1 - η.e_fn
                  (Causalean.Estimation.ATE.BackdoorEstimationSystem.projX z)))
          * (Causalean.Estimation.ATE.BackdoorEstimationSystem.projY z
              - η.μ₀_fn
                  (Causalean.Estimation.ATE.BackdoorEstimationSystem.projX z)))
        S.P_Z) :
    |∫ z, aipwMomentATTFunctional η z S.θ₀ ∂(S.P_Z)|
      ≤ aipw_rem_const_ATT ε *
          (eLpNorm (fun x => η.μ₀_fn x - S.μ₀_val x) 2 S.P_X).toReal *
          (eLpNorm (fun x => η.e_fn x - S.e_val x) 2 S.P_X).toReal := by
  let dμ : γ → ℝ := fun x => η.μ₀_fn x - S.μ₀_val x
  let de : γ → ℝ := fun x => η.e_fn x - S.e_val x
  let rem : γ → ℝ := fun x => (de x / (1 - η.e_fn x)) * dμ x
  let bound : γ → ℝ := fun x => aipw_rem_const_ATT ε * |de x * dμ x|
  have hC_nonneg : 0 ≤ aipw_rem_const_ATT ε := by
    unfold aipw_rem_const_ATT
    exact one_div_nonneg.mpr h_overlap.1.le
  have hpoint : ∀ᵐ x ∂S.P_X, |rem x| ≤ bound x := by
    filter_upwards [hη.1] with x hηx
    have hden : ε ≤ 1 - η.e_fn x := by linarith [hηx]
    have hη_false_pos_x : 0 < 1 - η.e_fn x := lt_of_lt_of_le h_overlap.1 hden
    have hinv_le : (1 - η.e_fn x)⁻¹ ≤ ε⁻¹ :=
      (inv_le_inv₀ hη_false_pos_x h_overlap.1).2 hden
    have hinv_abs_le : |(1 - η.e_fn x)⁻¹| ≤ aipw_rem_const_ATT ε := by
      rw [abs_of_pos (inv_pos.mpr hη_false_pos_x)]
      simpa [aipw_rem_const_ATT, one_div] using hinv_le
    calc
      |rem x| = |de x * dμ x| * |(1 - η.e_fn x)⁻¹| := by
        rw [show rem x = de x * dμ x * (1 - η.e_fn x)⁻¹ by
          dsimp [rem]
          rw [div_eq_mul_inv]
          ring]
        simp [abs_mul]
      _ ≤ |de x * dμ x| * aipw_rem_const_ATT ε :=
        mul_le_mul_of_nonneg_left hinv_abs_le (abs_nonneg _)
      _ = bound x := by ring
  haveI : ENNReal.HolderTriple (2 : ENNReal) (2 : ENNReal) (1 : ENNReal) := by
    constructor
    simpa using ENNReal.inv_two_add_inv_two
  haveI : IsFiniteMeasure S.P_X := by
    unfold TreatedEstimationSystem.P_X
    infer_instance
  have hprod_int : Integrable (fun x => de x * dμ x) S.P_X := by
    have hmul : MemLp (fun x => de x * dμ x) 1 S.P_X := by
      simpa [dμ, de, mul_comm] using hΔe_memLp.mul hΔμ₀_memLp
    exact hmul.integrable (by norm_num)
  have hbound_int : Integrable bound S.P_X := by
    simpa [bound] using hprod_int.norm.const_mul (aipw_rem_const_ATT ε)
  have hrem_meas : Measurable rem := by
    dsimp [rem, dμ, de]
    exact ((η.e_meas.sub S.e_meas).div (measurable_const.sub η.e_meas)).mul
      ((η.μ₀_meas).sub S.μ₀_meas)
  have hrem_abs_int : Integrable (fun x => |rem x|) S.P_X :=
    hbound_int.mono' (by
      simpa [Real.norm_eq_abs] using hrem_meas.norm.aestronglyMeasurable)
      (by
        filter_upwards [hpoint] with x hx
        simpa [Real.norm_eq_abs] using hx)
  have hCS :
      ∫ x, |de x * dμ x| ∂(S.P_X)
        ≤ (eLpNorm dμ 2 S.P_X).toReal * (eLpNorm de 2 S.P_X).toReal := by
    have h := integral_abs_mul_le_eLpNorm_mul_eLpNorm
      (ν := S.P_X) hΔμ₀_memLp hΔe_memLp
    simpa [dμ, de, mul_comm] using h
  have hident := aipw_remainder_identity_ATT S h_overlap hA hπ_pos h_y2 h_y0_2
    η hη hΔμ₀_memLp hΔe_memLp hIPW
  calc
    |∫ z, aipwMomentATTFunctional η z S.θ₀ ∂(S.P_Z)|
        = |∫ x, rem x ∂(S.P_X)| := by
          rw [hident]
    _ ≤ ∫ x, |rem x| ∂(S.P_X) :=
          MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ x, bound x ∂(S.P_X) :=
          integral_mono_ae hrem_abs_int hbound_int hpoint
    _ = aipw_rem_const_ATT ε * (∫ x, |de x * dμ x| ∂(S.P_X)) := by
          rw [show bound = (fun x => aipw_rem_const_ATT ε * ‖de x * dμ x‖) by
            funext x
            simp [bound, Real.norm_eq_abs]]
          rw [integral_const_mul]
          simp [Real.norm_eq_abs]
    _ ≤ aipw_rem_const_ATT ε *
          ((eLpNorm dμ 2 S.P_X).toReal * (eLpNorm de 2 S.P_X).toReal) :=
          mul_le_mul_of_nonneg_left hCS hC_nonneg
    _ = aipw_rem_const_ATT ε *
          (eLpNorm (fun x => η.μ₀_fn x - S.μ₀_val x) 2 S.P_X).toReal *
          (eLpNorm (fun x => η.e_fn x - S.e_val x) 2 S.P_X).toReal := by
          simp [dμ, de]
          ring

/-! ## Stochastic-order corollary

If `η̂(n) ∈ H_ε` realize the L²-product rate at `n^{-1/2}`, the population AIPW
moment at the random nuisance is `o_p(n^{-1/2})`. -/

/-- **AIPW remainder is `o_p(n^{-1/2})` under the ATT product rate.**

Direct consequence of `aipw_remainder_bound_ATT` plus closure of `IsLittleOp`
under constant scaling.  The ATT version drops the sum over arms in the ATE
counterpart `aipw_remainder_op` because the ATT identity has a single
cross-product. -/
-- Outline:
-- 1. Apply `aipw_remainder_bound_ATT` pointwise in `(n, ω)` to get
--    `|∫ m_AIPW(η_hat n ω, z, θ₀) dP_Z| ≤ C(ε) · prodTerm n ω`.
-- 2. Conclude `IsLittleOp (∫ m …) (n^{-1/2}) P.μ` via
--    `IsLittleOp.of_abs_le_const_mul` applied to `h_product_rate`.
theorem aipw_remainder_op_ATT
    (S : TreatedEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.OneSidedOverlap ε)
    (hA : S.toPOBackdoorSystem.ATTAssumptions)
    (hπ_pos : 0 < S.π_val)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_y0_2 : Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD false ω) ^ 2) P.μ)
    (η_hat : ℕ → P.Ω → TreatedNuisanceVec γ)
    (h_in_H : ∀ n ω, η_hat n ω ∈ H_ε S ε)
    (hΔμ₀_memLp :
      ∀ n ω, MemLp
        (fun x => (η_hat n ω).μ₀_fn x - S.μ₀_val x) 2 S.P_X)
    (hΔe_memLp :
      ∀ n ω, MemLp
        (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X)
    (hIPW : ∀ n ω, Integrable (fun z =>
        (1 - Causalean.Estimation.ATE.BackdoorEstimationSystem.indA z)
          * ((η_hat n ω).e_fn
                (Causalean.Estimation.ATE.BackdoorEstimationSystem.projX z)
              / (1 - (η_hat n ω).e_fn
                  (Causalean.Estimation.ATE.BackdoorEstimationSystem.projX z)))
          * (Causalean.Estimation.ATE.BackdoorEstimationSystem.projY z
              - (η_hat n ω).μ₀_fn
                  (Causalean.Estimation.ATE.BackdoorEstimationSystem.projX z)))
        S.P_Z)
    (h_product_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun x =>
              (η_hat n ω).μ₀_fn x - S.μ₀_val x) 2 S.P_X).toReal *
            (eLpNorm (fun x =>
              (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal)
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ) :
    IsLittleOp
      (fun n ω => ∫ z, aipwMomentATTFunctional (η_hat n ω) z S.θ₀ ∂(S.P_Z))
      (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ := by
  let rn : ℕ → ℝ := fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))
  let prodTerm : ℕ → P.Ω → ℝ := fun n ω =>
    (eLpNorm (fun x =>
        (η_hat n ω).μ₀_fn x - S.μ₀_val x) 2 S.P_X).toReal *
      (eLpNorm (fun x =>
        (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal
  have hCpos : 0 < aipw_rem_const_ATT ε := by
    unfold aipw_rem_const_ATT
    exact one_div_pos.mpr h_overlap.1
  refine IsLittleOp.of_abs_le_const_mul (μ := P.μ) hCpos
    (by simpa [prodTerm, rn] using h_product_rate) ?_
  intro n ω
  have hprod_nonneg : 0 ≤ prodTerm n ω := by
    exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hbound := aipw_remainder_bound_ATT S h_overlap hA hπ_pos h_y2 h_y0_2
    (η_hat n ω) (h_in_H n ω) (hΔμ₀_memLp n ω) (hΔe_memLp n ω)
    (hIPW n ω)
  have habs_prod : |prodTerm n ω| = prodTerm n ω :=
    abs_of_nonneg hprod_nonneg
  calc
    |∫ z, aipwMomentATTFunctional (η_hat n ω) z S.θ₀ ∂(S.P_Z)|
        ≤ aipw_rem_const_ATT ε *
            (eLpNorm (fun x =>
              (η_hat n ω).μ₀_fn x - S.μ₀_val x) 2 S.P_X).toReal *
            (eLpNorm (fun x =>
              (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal := hbound
    _ = aipw_rem_const_ATT ε * prodTerm n ω := by
          simp [prodTerm]
          ring
    _ = aipw_rem_const_ATT ε * |prodTerm n ω| := by
          rw [habs_prod]

end TreatedEstimationSystem

end ATT
end Estimation
end Causalean
