/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# AIPW second-order remainder bound

This file contains the quantitative remainder bounds after the exact remainder
identity is established in `Remainder/Identity.lean`.
-/

import Causalean.Estimation.ATE.Remainder.Identity
import Causalean.Stat.Limit.Convergence
import Causalean.Stat.Orthogonality.ConditionalOp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Order.Group.Lattice

/-! # AIPW Remainder Bound

This file turns the exact augmented inverse-probability weighted remainder
identity into a quantitative second-order bound. It bounds the population
moment error by the product of the outcome-regression error and the propensity
score error, which is the analytic rate condition used by double machine
learning for the average treatment effect.

The headline theorem `aipw_remainder_bound` applies the identity from
`Remainder/Identity.lean` and Cauchy-Schwarz to obtain an L² product bound
under strict overlap.  The corollary `aipw_remainder_op` lifts that bound to
an `o_p(n^{-1/2})` population-moment remainder for random nuisance estimators.
-/

namespace Causalean
namespace Estimation
namespace ATE

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat

namespace BackdoorEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- The integrated AIPW remainder is bounded by a strict-overlap constant
times the product of outcome-regression and propensity-score L² errors.

This is the quantitative Cauchy-Schwarz step applied after the exact remainder identity. -/
theorem aipw_remainder_bound
    (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (η : NuisanceVec γ) (hη : η ∈ H_ε_aeL2 S ε)
    (hΔμ_memLp :
      ∀ a, MemLp (fun x => η.μ_fn a x - S.μ_val a x) 2 S.P_X)
    (hΔe_memLp : MemLp (fun x => η.e_fn x - S.e_val x) 2 S.P_X) :
    |∫ z, aipwMomentFunctional η z S.θ₀ ∂(S.P_Z)|
      ≤ aipw_rem_const ε *
          ∑ a : Bool,
            (eLpNorm (fun x => η.μ_fn a x - S.μ_val a x) 2 S.P_X).toReal *
              (eLpNorm (fun x => η.e_fn x - S.e_val x) 2 S.P_X).toReal := by
  let dμT : γ → ℝ := fun x => η.μ_fn true x - S.μ_val true x
  let dμF : γ → ℝ := fun x => η.μ_fn false x - S.μ_val false x
  let de : γ → ℝ := fun x => η.e_fn x - S.e_val x
  let rem : γ → ℝ := fun x =>
    de x * (dμT x / η.e_fn x + dμF x / (1 - η.e_fn x))
  let bound : γ → ℝ := fun x =>
    aipw_rem_const ε * |dμT x * de x| +
      aipw_rem_const ε * |dμF x * de x|
  have hC_ge_inv : ε⁻¹ ≤ aipw_rem_const ε := by
    unfold aipw_rem_const
    have hpos : 0 < ε := h_overlap.1
    have hone : 0 < 1 - ε := by linarith [h_overlap.2.1]
    have hden : 0 < ε * (1 - ε) := mul_pos hpos hone
    rw [div_eq_mul_inv]
    field_simp [hpos.ne', hden.ne']
    nlinarith [h_overlap.2.1]
  have hC_nonneg : 0 ≤ aipw_rem_const ε :=
    (inv_nonneg.mpr h_overlap.1.le).trans hC_ge_inv
  have hpoint : ∀ᵐ x ∂S.P_X, |rem x| ≤ bound x := by
    filter_upwards [hη.1] with x hηx
    have hη_pos_x : 0 < η.e_fn x := lt_of_lt_of_le h_overlap.1 hηx.1
    have hη_false_pos_x : 0 < 1 - η.e_fn x := by
      have : ε ≤ 1 - η.e_fn x := by linarith [hηx.2]
      exact lt_of_lt_of_le h_overlap.1 this
    have hdenT : η.e_fn x ≠ 0 := hη_pos_x.ne'
    have hdenF : 1 - η.e_fn x ≠ 0 := hη_false_pos_x.ne'
    have hinvT : |(η.e_fn x)⁻¹| ≤ aipw_rem_const ε := by
      have hle : (η.e_fn x)⁻¹ ≤ ε⁻¹ :=
        (inv_le_inv₀ hη_pos_x h_overlap.1).2 hηx.1
      rw [abs_of_pos (inv_pos.mpr hη_pos_x)]
      exact hle.trans hC_ge_inv
    have hinvF : |(1 - η.e_fn x)⁻¹| ≤ aipw_rem_const ε := by
      have hden : ε ≤ 1 - η.e_fn x := by linarith [hηx.2]
      have hle : (1 - η.e_fn x)⁻¹ ≤ ε⁻¹ :=
        (inv_le_inv₀ hη_false_pos_x h_overlap.1).2 hden
      rw [abs_of_pos (inv_pos.mpr hη_false_pos_x)]
      exact hle.trans hC_ge_inv
    have hT :
        |de x * (dμT x / η.e_fn x)| ≤
          aipw_rem_const ε * |dμT x * de x| := by
      calc
        |de x * (dμT x / η.e_fn x)|
            = |dμT x * de x| * |(η.e_fn x)⁻¹| := by
              rw [div_eq_mul_inv]
              simp [abs_mul, mul_assoc, mul_left_comm, mul_comm]
        _ ≤ |dμT x * de x| * aipw_rem_const ε :=
              mul_le_mul_of_nonneg_left hinvT (abs_nonneg _)
        _ = aipw_rem_const ε * |dμT x * de x| := by ring
    have hF :
        |de x * (dμF x / (1 - η.e_fn x))| ≤
          aipw_rem_const ε * |dμF x * de x| := by
      calc
        |de x * (dμF x / (1 - η.e_fn x))|
            = |dμF x * de x| * |(1 - η.e_fn x)⁻¹| := by
              rw [div_eq_mul_inv]
              simp [abs_mul, mul_assoc, mul_left_comm, mul_comm]
        _ ≤ |dμF x * de x| * aipw_rem_const ε :=
              mul_le_mul_of_nonneg_left hinvF (abs_nonneg _)
        _ = aipw_rem_const ε * |dμF x * de x| := by ring
    calc
      |rem x| = |de x * (dμT x / η.e_fn x) +
          de x * (dμF x / (1 - η.e_fn x))| := by
            simp [rem, mul_add]
      _ ≤ |de x * (dμT x / η.e_fn x)| +
          |de x * (dμF x / (1 - η.e_fn x))| :=
            abs_add_le _ _
      _ ≤ bound x := by
            dsimp [bound]
            exact add_le_add hT hF
  haveI : ENNReal.HolderTriple (2 : ENNReal) (2 : ENNReal) (1 : ENNReal) := by
    constructor
    simpa using ENNReal.inv_two_add_inv_two
  haveI : IsFiniteMeasure S.P_X := by
    unfold BackdoorEstimationSystem.P_X
    infer_instance
  have hprodT_int : Integrable (fun x => dμT x * de x) S.P_X := by
    have hmul : MemLp (fun x => dμT x * de x) 1 S.P_X := by
      simpa [dμT, de, mul_comm] using (hΔμ_memLp true).mul hΔe_memLp
    exact hmul.integrable (by norm_num)
  have hprodF_int : Integrable (fun x => dμF x * de x) S.P_X := by
    have hmul : MemLp (fun x => dμF x * de x) 1 S.P_X := by
      simpa [dμF, de, mul_comm] using (hΔμ_memLp false).mul hΔe_memLp
    exact hmul.integrable (by norm_num)
  have hbound_int : Integrable bound S.P_X := by
    simpa [bound] using
      ((hprodT_int.norm.const_mul (aipw_rem_const ε)).add
        (hprodF_int.norm.const_mul (aipw_rem_const ε)))
  have hrem_meas : Measurable rem := by
    dsimp [rem, dμT, dμF, de]
    exact ((η.e_meas.sub S.e_meas).mul
      ((((η.μ_meas true).sub (S.μ_meas true)).div η.e_meas).add
        (((η.μ_meas false).sub (S.μ_meas false)).div
          (measurable_const.sub η.e_meas))))
  have hrem_abs_int : Integrable (fun x => |rem x|) S.P_X :=
    hbound_int.mono' hrem_meas.abs.aestronglyMeasurable
      (by
        filter_upwards [hpoint] with x hx
        simpa [Real.norm_eq_abs] using hx)
  have hCS_T :
      ∫ x, |dμT x * de x| ∂(S.P_X)
        ≤ (eLpNorm dμT 2 S.P_X).toReal * (eLpNorm de 2 S.P_X).toReal := by
    simpa [dμT, de] using
      integral_abs_mul_le_eLpNorm_mul_eLpNorm
        (ν := S.P_X) (hΔμ_memLp true) hΔe_memLp
  have hCS_F :
      ∫ x, |dμF x * de x| ∂(S.P_X)
        ≤ (eLpNorm dμF 2 S.P_X).toReal * (eLpNorm de 2 S.P_X).toReal := by
    simpa [dμF, de] using
      integral_abs_mul_le_eLpNorm_mul_eLpNorm
        (ν := S.P_X) (hΔμ_memLp false) hΔe_memLp
  have hident := aipw_remainder_identity S h_overlap hA h_y2 h_yd2 η hη
    hΔμ_memLp
  calc
    |∫ z, aipwMomentFunctional η z S.θ₀ ∂(S.P_Z)|
        = |∫ x, rem x ∂(S.P_X)| := by
          rw [hident]
    _ ≤ ∫ x, |rem x| ∂(S.P_X) :=
          MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ x, bound x ∂(S.P_X) :=
          integral_mono_ae hrem_abs_int hbound_int hpoint
    _ = aipw_rem_const ε * (∫ x, |dμT x * de x| ∂(S.P_X)) +
          aipw_rem_const ε * (∫ x, |dμF x * de x| ∂(S.P_X)) := by
          rw [show bound = (fun x =>
            aipw_rem_const ε * |dμT x * de x| +
              aipw_rem_const ε * |dμF x * de x|) from rfl]
          change ∫ x, aipw_rem_const ε * |dμT x * de x| +
              aipw_rem_const ε * |dμF x * de x| ∂S.P_X =
            aipw_rem_const ε * (∫ x, |dμT x * de x| ∂S.P_X) +
              aipw_rem_const ε * (∫ x, |dμF x * de x| ∂S.P_X)
          rw [show (fun x => aipw_rem_const ε * |dμT x * de x| +
                aipw_rem_const ε * |dμF x * de x|) =
              (fun x => aipw_rem_const ε * ‖dμT x * de x‖ +
                aipw_rem_const ε * ‖dμF x * de x‖) by
            funext x
            simp [Real.norm_eq_abs]]
          rw [integral_add (hprodT_int.norm.const_mul (aipw_rem_const ε))
            (hprodF_int.norm.const_mul (aipw_rem_const ε))]
          rw [integral_const_mul, integral_const_mul]
          simp [Real.norm_eq_abs]
    _ ≤ aipw_rem_const ε *
          ((eLpNorm dμT 2 S.P_X).toReal * (eLpNorm de 2 S.P_X).toReal) +
        aipw_rem_const ε *
          ((eLpNorm dμF 2 S.P_X).toReal * (eLpNorm de 2 S.P_X).toReal) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hCS_T hC_nonneg)
            (mul_le_mul_of_nonneg_left hCS_F hC_nonneg)
    _ = aipw_rem_const ε *
          ∑ a : Bool,
            (eLpNorm (fun x => η.μ_fn a x - S.μ_val a x) 2 S.P_X).toReal *
              (eLpNorm (fun x => η.e_fn x - S.e_val x) 2 S.P_X).toReal := by
          simp [dμT, dμF, de]
          ring

/-! ## Stochastic-order corollary used by DML

If `μ̂(n)` and `ê(n)` realize `H_ε_aeL2` and satisfy the L²-product rate
hypothesis at `n^{-1/2}`, then the population AIPW moment at the random
nuisance is `o_p(n^{-1/2})`.  This is the form consumed at
`DML.lean:152` (the `R₁` cross-term). -/

/-- **AIPW remainder is `o_p(n^{-1/2})` under the product rate.**

If `(μ̂(n), ê(n)) ∈ H_ε_aeL2` for all `n, ω` and the L²-product rate
`‖μ̂(n)(a,·) − μ_val(a,·)‖₂ · ‖ê(n) − e_val‖₂ = o_p(n^{-1/2})` holds for each
`a ∈ {0, 1}`, then the population AIPW moment at the random nuisance is
`o_p(n^{-1/2})` under `μ`.  Direct consequence of `aipw_remainder_bound`
plus closure of `IsLittleOp` under finite sums and constant scaling. -/
theorem aipw_remainder_op
    (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (η_hat : ℕ → P.Ω → NuisanceVec γ)
    (h_in_H : ∀ n ω, η_hat n ω ∈ H_ε_aeL2 S ε)
    (hΔμ_memLp :
      ∀ n ω a, MemLp
        (fun x => (η_hat n ω).μ_fn a x - S.μ_val a x) 2 S.P_X)
    (hΔe_memLp :
      ∀ n ω, MemLp (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X)
    (h_product_rate :
      ∀ a : Bool,
        IsLittleOp
          (fun n ω =>
            (eLpNorm (fun x =>
                (η_hat n ω).μ_fn a x - S.μ_val a x) 2 S.P_X).toReal *
              (eLpNorm (fun x =>
                (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal)
          (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ) :
    IsLittleOp
      (fun n ω => ∫ z, aipwMomentFunctional (η_hat n ω) z S.θ₀ ∂(S.P_Z))
      (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ := by
  let rn : ℕ → ℝ := fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))
  let prodTerm : Bool → ℕ → P.Ω → ℝ := fun a n ω =>
    (eLpNorm (fun x =>
        (η_hat n ω).μ_fn a x - S.μ_val a x) 2 S.P_X).toReal *
      (eLpNorm (fun x =>
        (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal
  have hrn_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ rn n := by
    filter_upwards with n
    exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hsum_rate :
      IsLittleOp
        (fun n ω => ∑ a : Bool, prodTerm a n ω) rn P.μ := by
    simpa [prodTerm, rn] using
      IsLittleOp.add_eventually_nonneg_rate (μ := P.μ) hrn_nonneg
        (h_product_rate true) (h_product_rate false)
  have hCpos : 0 < aipw_rem_const ε := by
    unfold aipw_rem_const
    have hden_pos : 0 < ε * (1 - ε) := by
      have h1 : 0 < 1 - ε := by linarith [h_overlap.2.1]
      exact mul_pos h_overlap.1 h1
    positivity
  refine IsLittleOp.of_abs_le_const_mul (μ := P.μ) hCpos hsum_rate ?_
  intro n ω
  have hsum_nonneg :
      0 ≤ ∑ a : Bool, prodTerm a n ω := by
    refine Finset.sum_nonneg ?_
    intro a ha
    exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hbound := aipw_remainder_bound S h_overlap hA h_y2 h_yd2
    (η_hat n ω) (h_in_H n ω) (hΔμ_memLp n ω) (hΔe_memLp n ω)
  have hsum_nonneg' : 0 ≤ prodTerm true n ω + prodTerm false n ω := by
    simpa [prodTerm] using hsum_nonneg
  have habs_sum' :
      |prodTerm true n ω + prodTerm false n ω| =
        prodTerm true n ω + prodTerm false n ω :=
    abs_of_nonneg hsum_nonneg'
  simpa [prodTerm, rn, habs_sum'] using hbound

end BackdoorEstimationSystem

end ATE
end Estimation
end Causalean
