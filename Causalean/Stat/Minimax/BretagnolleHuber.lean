/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bretagnolle–Huber inequality: testing affinity floored by `exp(-KL)`

The **Bretagnolle–Huber inequality** (Bretagnolle & Huber, 1979) bounds the
two-point testing affinity `1 - tvDist μ ν` from below by `½·exp(-KL(μ,ν))`.  It
is the arbitrary-budget strengthening of Pinsker's inequality
(`Causalean/Stat/Minimax/Pinsker.lean`): Pinsker (`tvDist ≤ √(KL/2)`) yields a
positive testing floor only when `KL < 2`, whereas Bretagnolle–Huber gives a
positive floor for *every* finite KL budget.  It is the standard tool for Le Cam
two-point minimax lower bounds whose construction operates at an `O(1)` (not
vanishing) KL budget.

Like Pinsker, the bare `∀` form is false (if `μ ⊥ ν` then `klDiv = ⊤`,
`(⊤).toReal = 0`, so the left side is `½` while the affinity is `0`); the genuine
hypotheses are `μ ≪ ν` and `klDiv μ ν ≠ ⊤`, exactly mirroring
`pinskerBound_of_ac_of_ne_top`.

## Proof route (the Bhattacharyya/Hellinger affinity layer, built here)

Write `p = (dμ/dν).toReal` and `ρ = ∫ √p ∂ν` (the Bhattacharyya/Hellinger
affinity).  Then:

* **Affinity lower bound** (`integral_min_le_one_sub_tvDist`):
  `∫ min(p,1) ∂ν ≤ 1 - tvDist μ ν`, from the Scheffé `≤` inequality
  (`tvDist_le_half_integral_abs_rnDeriv`) and `∫ min(p,1) ∂ν = 1 - ½∫|p-1|∂ν`.
* **Cauchy–Schwarz** (`sq_bhattacharyya_le_two_mul_integral_min`):
  `ρ² ≤ 2·∫ min(p,1) ∂ν`, since `(∫√(min·max))² ≤ (∫min)(∫max)` and
  `∫ max(p,1) ∂ν ≤ 2`.
* **Jensen / Bhattacharyya** (`exp_neg_half_klDiv_le_bhattacharyya`):
  `exp(-½·KL) ≤ ρ`, since `ρ = ∫ exp(-½·llr) ∂μ` (change of variables) and
  `exp(∫ -½·llr ∂μ) ≤ ∫ exp(-½·llr) ∂μ` (Jensen, `convexOn_exp`).

Chaining: `½·exp(-KL) ≤ ½·ρ² ≤ ∫ min(p,1) ∂ν ≤ 1 - tvDist μ ν`.

## Main result

* `bretagnolle_huber_affinity` — `½·exp(-(klDiv μ ν).toReal) ≤ 1 - tvDist μ ν`
  for probability measures `μ ≪ ν` with `klDiv μ ν ≠ ⊤`.
-/

import Causalean.Stat.Minimax.Scheffe
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Bretagnolle-Huber inequality

This module builds the Bhattacharyya/Hellinger affinity layer used to prove the
Bretagnolle-Huber inequality.  The auxiliary results
`integral_min_le_one_sub_tvDist`, `sq_bhattacharyya_le_two_mul_integral_min`,
and `exp_neg_half_klDiv_le_bhattacharyya` combine Scheffe, Cauchy-Schwarz, and
Jensen steps; the headline theorem `bretagnolle_huber_affinity` gives the
two-point testing floor `1 - tvDist μ ν >= (1/2) * exp(-KL(μ,ν))` for absolutely
continuous probability measures with finite KL divergence.
-/

namespace Causalean.Stat

open MeasureTheory Real
open scoped ENNReal

open InformationTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### A scalar identity for the change of variables

`y · exp(-½ log y) = √y` for `y ≥ 0`; the engine of the change of variables
`∫ √p ∂ν = ∫ exp(-½·llr) ∂μ`. -/

/-- For `y ≥ 0`, `y * exp(-(1/2)·log y) = √y`. -/
theorem mul_exp_neg_half_log {y : ℝ} (hy : 0 ≤ y) :
    y * Real.exp (-(1 / 2) * Real.log y) = Real.sqrt y := by
  rcases eq_or_lt_of_le hy with h0 | h0
  · simp [← h0]
  · -- y > 0
    have hsqrt : Real.sqrt y = Real.exp ((1 / 2) * Real.log y) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos h0]
      ring_nf
    rw [hsqrt]
    nth_rewrite 1 [← Real.exp_log h0]
    rw [← Real.exp_add]
    ring_nf

/-- `√y ≤ (y + 1)/2` for `y ≥ 0` (AM–GM); used to dominate `√p` by an integrable
function. -/
theorem sqrt_le_half_add_one {y : ℝ} (hy : 0 ≤ y) :
    Real.sqrt y ≤ (y + 1) / 2 := by
  have hs : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hsq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
  nlinarith [sq_nonneg (Real.sqrt y - 1), hsq]

section Affinity

variable (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Abbreviation: the Radon–Nikodym density `p = (dμ/dν).toReal`. -/
local notation3 "p" => fun x => (μ.rnDeriv ν x).toReal

/-- `√p` is `ν`-integrable (dominated by `(p+1)/2`). -/
@[fun_prop]
theorem integrable_sqrt_rnDeriv :
    Integrable (fun x => Real.sqrt ((μ.rnDeriv ν x).toReal)) ν := by
  have hp : Integrable (fun x => (μ.rnDeriv ν x).toReal) ν :=
    Measure.integrable_toReal_rnDeriv
  have hmeas : AEStronglyMeasurable
      (fun x => Real.sqrt ((μ.rnDeriv ν x).toReal)) ν := by
    apply Measurable.aestronglyMeasurable
    exact (Measure.measurable_rnDeriv μ ν).ennreal_toReal.sqrt
  refine Integrable.mono' (g := fun x => ((μ.rnDeriv ν x).toReal + 1) / 2)
    ((hp.add (integrable_const 1)).div_const 2) hmeas ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact sqrt_le_half_add_one ENNReal.toReal_nonneg

/-- **Affinity lower bound.**  `∫ min(p,1) ∂ν ≤ 1 - tvDist μ ν`.  Derived from
Scheffé's `≤` inequality together with `∫ min(p,1) ∂ν = 1 - ½∫|p-1|∂ν`. -/
theorem integral_min_le_one_sub_tvDist (hac : μ ≪ ν) :
    ∫ x, min ((μ.rnDeriv ν x).toReal) 1 ∂ν ≤ 1 - tvDist μ ν := by
  set q : Ω → ℝ := fun x => (μ.rnDeriv ν x).toReal with hq_def
  have hp_int : Integrable q ν := Measure.integrable_toReal_rnDeriv
  have hp_one : ∫ x, q x ∂ν = 1 := by
    rw [hq_def, Measure.integral_toReal_rnDeriv hac, measureReal_def, measure_univ]
    simp
  have habs_int : Integrable (fun x => |q x - 1|) ν :=
    (hp_int.sub (integrable_const 1)).abs
  -- min(q,1) = (q + 1 - |q - 1|)/2 pointwise
  have hmin_eq : ∀ x, min (q x) 1 = (q x + 1 - |q x - 1|) / 2 := by
    intro x; rcases le_total (q x) 1 with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
  have hmin_int : Integrable (fun x => min (q x) 1) ν := by
    refine (((hp_int.add (integrable_const 1)).sub habs_int).div_const 2).congr ?_
    exact Filter.Eventually.of_forall fun x => (hmin_eq x).symm
  have hone : ∫ _ : Ω, (1 : ℝ) ∂ν = 1 := by
    rw [integral_const, measureReal_def, measure_univ]; simp
  have hint_min : ∫ x, min (q x) 1 ∂ν = 1 - (1/2) * ∫ x, |q x - 1| ∂ν := by
    have heq : (fun x => min (q x) 1)
        = fun x => (q x + 1) / 2 - |q x - 1| / 2 := by
      funext x; rw [hmin_eq x]; ring
    calc ∫ x, min (q x) 1 ∂ν
        = ∫ x, ((q x + 1) / 2 - |q x - 1| / 2) ∂ν := by rw [heq]
      _ = (∫ x, (q x + 1) / 2 ∂ν) - ∫ x, |q x - 1| / 2 ∂ν :=
            integral_sub ((hp_int.add (integrable_const 1)).div_const 2)
              (habs_int.div_const 2)
      _ = ((∫ x, (q x + 1) ∂ν) / 2) - (∫ x, |q x - 1| ∂ν) / 2 := by
            rw [integral_div, integral_div]
      _ = 1 - (1/2) * ∫ x, |q x - 1| ∂ν := by
            rw [integral_add hp_int (integrable_const 1), hp_one, hone]; ring
  have hscheffe := tvDist_le_half_integral_abs_rnDeriv μ ν hac
  rw [hint_min]
  linarith [hscheffe]

/-- **Cauchy–Schwarz / Bhattacharyya step.**
`(∫ √p ∂ν)² ≤ 2·∫ min(p,1) ∂ν`. -/
theorem sq_bhattacharyya_le_two_mul_integral_min (hac : μ ≪ ν) :
    (∫ x, Real.sqrt ((μ.rnDeriv ν x).toReal) ∂ν) ^ 2
      ≤ 2 * ∫ x, min ((μ.rnDeriv ν x).toReal) 1 ∂ν := by
  set q : Ω → ℝ := fun x => (μ.rnDeriv ν x).toReal with hq_def
  set f₁ : Ω → ℝ := fun x => Real.sqrt (min (q x) 1) with hf₁_def
  set f₂ : Ω → ℝ := fun x => Real.sqrt (max (q x) 1) with hf₂_def
  have hq_nonneg : ∀ x, 0 ≤ q x := by
    intro x
    rw [hq_def]
    exact ENNReal.toReal_nonneg
  have hmin_nonneg : ∀ x, 0 ≤ min (q x) 1 := fun x => le_min (hq_nonneg x) zero_le_one
  have hmax_nonneg : ∀ x, 0 ≤ max (q x) 1 := fun x =>
    le_trans zero_le_one (le_max_right (q x) 1)
  have hp_int : Integrable q ν := by
    rw [hq_def]
    exact Measure.integrable_toReal_rnDeriv
  have hp_integral_one : ∫ x, q x ∂ν = 1 := by
    rw [hq_def, Measure.integral_toReal_rnDeriv hac, measureReal_def, measure_univ]
    simp
  have hmin_meas : AEStronglyMeasurable (fun x => min (q x) 1) ν := by
    rw [hq_def]
    exact ((Measure.measurable_rnDeriv μ ν).ennreal_toReal.min measurable_const)
      |>.aestronglyMeasurable
  have hmax_meas : AEStronglyMeasurable (fun x => max (q x) 1) ν := by
    rw [hq_def]
    exact ((Measure.measurable_rnDeriv μ ν).ennreal_toReal.max measurable_const)
      |>.aestronglyMeasurable
  have hmin_int : Integrable (fun x => min (q x) 1) ν := by
    refine Integrable.mono' hp_int hmin_meas ?_
    exact Filter.Eventually.of_forall fun x => by
      have h : min (q x) 1 ≤ q x := min_le_left (q x) 1
      simp [Real.norm_eq_abs, abs_of_nonneg (hmin_nonneg x), h]
  have hmax_int : Integrable (fun x => max (q x) 1) ν := by
    refine Integrable.mono' (hp_int.add (integrable_const 1)) hmax_meas ?_
    exact Filter.Eventually.of_forall fun x => by
      have h : max (q x) 1 ≤ q x + 1 :=
        max_le (by linarith [hq_nonneg x]) (by linarith [hq_nonneg x])
      simpa [Real.norm_eq_abs, abs_of_nonneg (hmax_nonneg x), Pi.add_apply] using h
  have hf₁_meas : AEStronglyMeasurable f₁ ν := by
    rw [hf₁_def, hq_def]
    exact ((Measure.measurable_rnDeriv μ ν).ennreal_toReal.min measurable_const)
      |>.sqrt.aestronglyMeasurable
  have hf₂_meas : AEStronglyMeasurable f₂ ν := by
    rw [hf₂_def, hq_def]
    exact ((Measure.measurable_rnDeriv μ ν).ennreal_toReal.max measurable_const)
      |>.sqrt.aestronglyMeasurable
  have hf₁_sq_int : Integrable (fun x => f₁ x ^ 2) ν := by
    refine hmin_int.congr (Filter.Eventually.of_forall fun x => ?_)
    rw [hf₁_def]
    exact (Real.sq_sqrt (hmin_nonneg x)).symm
  have hf₂_sq_int : Integrable (fun x => f₂ x ^ 2) ν := by
    refine hmax_int.congr (Filter.Eventually.of_forall fun x => ?_)
    rw [hf₂_def]
    exact (Real.sq_sqrt (hmax_nonneg x)).symm
  have hf₁L2 : MemLp f₁ (ENNReal.ofReal 2) ν := by
    simpa using (memLp_two_iff_integrable_sq hf₁_meas).2 hf₁_sq_int
  have hf₂L2 : MemLp f₂ (ENNReal.ofReal 2) ν := by
    simpa using (memLp_two_iff_integrable_sq hf₂_meas).2 hf₂_sq_int
  have hf₁_nonneg : 0 ≤ᵐ[ν] f₁ := Filter.Eventually.of_forall fun x => by
    rw [hf₁_def]
    exact Real.sqrt_nonneg _
  have hf₂_nonneg : 0 ≤ᵐ[ν] f₂ := Filter.Eventually.of_forall fun x => by
    rw [hf₂_def]
    exact Real.sqrt_nonneg _
  have hholder :
      ∫ x, f₁ x * f₂ x ∂ν
        ≤ (∫ x, f₁ x ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ))
          * (∫ x, f₂ x ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) :=
    integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      hf₁_nonneg hf₂_nonneg hf₁L2 hf₂L2
  have hprod : ∀ x, f₁ x * f₂ x = Real.sqrt (q x) := by
    intro x
    rw [hf₁_def, hf₂_def,
      ← Real.sqrt_mul (hmin_nonneg x) (max (q x) 1)]
    have hminmax : min (q x) 1 * max (q x) 1 = q x := by
      rcases le_total (q x) 1 with h | h
      · rw [min_eq_left h, max_eq_right h, mul_one]
      · rw [min_eq_right h, max_eq_left h, one_mul]
    rw [hminmax]
  have hLHS : ∫ x, f₁ x * f₂ x ∂ν = ∫ x, Real.sqrt (q x) ∂ν := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hprod
  set A : ℝ := ∫ x, min (q x) 1 ∂ν with hA_def
  set B : ℝ := ∫ x, max (q x) 1 ∂ν with hB_def
  have hf₁_rpow : ∫ x, f₁ x ^ (2 : ℝ) ∂ν = A := by
    rw [hA_def]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      rw [hf₁_def]
      change Real.sqrt (min (q x) 1) ^ (2 : ℝ) = min (q x) 1
      rw [Real.rpow_two]
      exact Real.sq_sqrt (hmin_nonneg x)
  have hf₂_rpow : ∫ x, f₂ x ^ (2 : ℝ) ∂ν = B := by
    rw [hB_def]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      rw [hf₂_def]
      change Real.sqrt (max (q x) 1) ^ (2 : ℝ) = max (q x) 1
      rw [Real.rpow_two]
      exact Real.sq_sqrt (hmax_nonneg x)
  have hA_nonneg : 0 ≤ A := by
    rw [hA_def]
    exact integral_nonneg hmin_nonneg
  have hB_nonneg : 0 ≤ B := by
    rw [hB_def]
    exact integral_nonneg hmax_nonneg
  have hsqrt_bound : ∫ x, Real.sqrt (q x) ∂ν ≤ Real.sqrt A * Real.sqrt B := by
    rw [hLHS, hf₁_rpow, hf₂_rpow] at hholder
    have hrpow_A : A ^ (1 / (2 : ℝ)) = Real.sqrt A :=
      (Real.sqrt_eq_rpow A).symm
    have hrpow_B : B ^ (1 / (2 : ℝ)) = Real.sqrt B :=
      (Real.sqrt_eq_rpow B).symm
    rw [hrpow_A, hrpow_B] at hholder
    exact hholder
  have hB_le_two : B ≤ 2 := by
    have hdom_int : Integrable (fun x => q x + 1) ν := hp_int.add (integrable_const 1)
    have hle_int : ∫ x, max (q x) 1 ∂ν ≤ ∫ x, q x + 1 ∂ν :=
      integral_mono_ae hmax_int hdom_int (Filter.Eventually.of_forall fun x => by
        change max (q x) 1 ≤ q x + 1
        exact max_le (by linarith [hq_nonneg x]) (by linarith [hq_nonneg x]))
    calc
      B = ∫ x, max (q x) 1 ∂ν := by rw [hB_def]
      _ ≤ ∫ x, q x + 1 ∂ν := hle_int
      _ = 2 := by
        rw [integral_add hp_int (integrable_const 1), hp_integral_one]
        norm_num
  have hsqrt_int_nonneg : 0 ≤ ∫ x, Real.sqrt (q x) ∂ν :=
    integral_nonneg fun x => Real.sqrt_nonneg _
  have hsq_le : (∫ x, Real.sqrt (q x) ∂ν) ^ 2 ≤ (Real.sqrt A * Real.sqrt B) ^ 2 := by
    nlinarith [hsqrt_bound, hsqrt_int_nonneg, Real.sqrt_nonneg A, Real.sqrt_nonneg B]
  have hsqrt_prod_sq : (Real.sqrt A * Real.sqrt B) ^ 2 = A * B := by
    rw [mul_pow, Real.sq_sqrt hA_nonneg, Real.sq_sqrt hB_nonneg]
  have hAB_le : A * B ≤ 2 * A := by
    nlinarith [hA_nonneg, hB_le_two]
  calc
    (∫ x, Real.sqrt ((μ.rnDeriv ν x).toReal) ∂ν) ^ 2
        = (∫ x, Real.sqrt (q x) ∂ν) ^ 2 := by rw [hq_def]
    _ ≤ (Real.sqrt A * Real.sqrt B) ^ 2 := hsq_le
    _ = A * B := hsqrt_prod_sq
    _ ≤ 2 * A := hAB_le
    _ = 2 * ∫ x, min ((μ.rnDeriv ν x).toReal) 1 ∂ν := by rw [hA_def, hq_def]

/-- **Jensen / Bhattacharyya step.**  `exp(-½·KL) ≤ ∫ √p ∂ν`. -/
theorem exp_neg_half_klDiv_le_bhattacharyya (hac : μ ≪ ν)
    (hint : Integrable (llr μ ν) μ) :
    Real.exp (-(1 / 2) * (klDiv μ ν).toReal)
      ≤ ∫ x, Real.sqrt ((μ.rnDeriv ν x).toReal) ∂ν := by
  have hK : (klDiv μ ν).toReal = ∫ a, llr μ ν a ∂μ :=
    InformationTheory.toReal_klDiv_of_measure_eq hac (by simp [measure_univ])
  have hCOV :
      ∫ x, Real.sqrt ((μ.rnDeriv ν x).toReal) ∂ν
        = ∫ x, Real.exp (-(1 / 2) * llr μ ν x) ∂μ := by
    have hcov0 :
        ∫ x, (μ.rnDeriv ν x).toReal • Real.exp (-(1 / 2) * llr μ ν x) ∂ν
          = ∫ x, Real.exp (-(1 / 2) * llr μ ν x) ∂μ :=
      MeasureTheory.integral_rnDeriv_smul hac
    have hcov_lhs :
        ∫ x, (μ.rnDeriv ν x).toReal • Real.exp (-(1 / 2) * llr μ ν x) ∂ν
          = ∫ x, Real.sqrt ((μ.rnDeriv ν x).toReal) ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change (μ.rnDeriv ν x).toReal
            * Real.exp (-(1 / 2) * Real.log (μ.rnDeriv ν x).toReal)
          = Real.sqrt ((μ.rnDeriv ν x).toReal)
        exact mul_exp_neg_half_log ENNReal.toReal_nonneg
    calc
      ∫ x, Real.sqrt ((μ.rnDeriv ν x).toReal) ∂ν
          = ∫ x, (μ.rnDeriv ν x).toReal • Real.exp (-(1 / 2) * llr μ ν x) ∂ν :=
            hcov_lhs.symm
      _ = ∫ x, Real.exp (-(1 / 2) * llr μ ν x) ∂μ := hcov0
  have hfi : Integrable (fun x => (-(1 / 2 : ℝ)) * llr μ ν x) μ :=
    hint.const_mul (-(1 / 2 : ℝ))
  have hgi : Integrable (fun x => Real.exp (-(1 / 2) * llr μ ν x)) μ := by
    refine (integrable_rnDeriv_smul_iff hac).mp ?_
    refine (integrable_sqrt_rnDeriv μ ν).congr (Filter.Eventually.of_forall fun x => ?_)
    change Real.sqrt ((μ.rnDeriv ν x).toReal)
      = (μ.rnDeriv ν x).toReal
        * Real.exp (-(1 / 2) * Real.log (μ.rnDeriv ν x).toReal)
    exact (mul_exp_neg_half_log ENNReal.toReal_nonneg).symm
  have hfs : ∀ᵐ x ∂μ, (-(1 / 2 : ℝ)) * llr μ ν x ∈ (Set.univ : Set ℝ) :=
    Filter.Eventually.of_forall fun x => Set.mem_univ _
  have hJensen :
      Real.exp (∫ x, (-(1 / 2 : ℝ)) * llr μ ν x ∂μ)
        ≤ ∫ x, Real.exp (-(1 / 2) * llr μ ν x) ∂μ := by
    simpa only [Function.comp_apply] using
      (convexOn_exp.map_integral_le
        (μ := μ) (f := fun x => (-(1 / 2 : ℝ)) * llr μ ν x)
        Real.continuous_exp.continuousOn isClosed_univ hfs hfi
        (by simpa only [Function.comp_def] using hgi))
  have harg :
      ∫ x, (-(1 / 2 : ℝ)) * llr μ ν x ∂μ
        = -(1 / 2) * (klDiv μ ν).toReal := by
    rw [integral_const_mul, ← hK]
  calc
    Real.exp (-(1 / 2) * (klDiv μ ν).toReal)
        = Real.exp (∫ x, (-(1 / 2 : ℝ)) * llr μ ν x ∂μ) := by rw [harg]
    _ ≤ ∫ x, Real.exp (-(1 / 2) * llr μ ν x) ∂μ := hJensen
    _ = ∫ x, Real.sqrt ((μ.rnDeriv ν x).toReal) ∂ν := hCOV.symm

end Affinity

/-- **Bretagnolle–Huber inequality.**  For probability measures `μ`, `ν` such that
[`μ` is absolutely continuous with respect to `ν`](hyp:hac) and [their Kullback–Leibler
divergence is finite](hyp:hfin), [the two-point testing affinity `1 − tvDist μ ν` is at least
`½·exp(-KL(μ‖ν))`](goal):

  `(1/2)·exp(-(klDiv μ ν).toReal) ≤ 1 - tvDist μ ν`.

Unlike Pinsker's inequality (`pinskerBound_of_ac_of_ne_top`), the floor is
positive for *every* finite KL budget, so it powers Le Cam two-point lower bounds
at an `O(1)` KL budget. -/
theorem bretagnolle_huber_affinity (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hfin : klDiv μ ν ≠ ⊤) :
    (1 / 2 : ℝ) * Real.exp (-(klDiv μ ν).toReal) ≤ 1 - tvDist μ ν := by
  set K : ℝ := (klDiv μ ν).toReal with hK_def
  set ρ : ℝ := ∫ x, Real.sqrt ((μ.rnDeriv ν x).toReal) ∂ν with hρ_def
  have hint : Integrable (llr μ ν) μ := (klDiv_ne_top_iff.mp hfin).2
  have hρ_nonneg : 0 ≤ ρ := by
    rw [hρ_def]; exact integral_nonneg fun x => Real.sqrt_nonneg _
  have hL3 : Real.exp (-(1 / 2) * K) ≤ ρ :=
    exp_neg_half_klDiv_le_bhattacharyya μ ν hac hint
  -- square it: exp(-K) ≤ ρ²
  have hexp_sq : Real.exp (-K) = Real.exp (-(1 / 2) * K) ^ 2 := by
    have hsum : -K = -(1 / 2) * K + -(1 / 2) * K := by ring
    rw [sq, ← Real.exp_add, ← hsum]
  have hsq : Real.exp (-K) ≤ ρ ^ 2 := by
    rw [hexp_sq]
    nlinarith [hL3, Real.exp_nonneg (-(1 / 2) * K), hρ_nonneg]
  -- Cauchy–Schwarz + affinity
  have hL2 : ρ ^ 2 ≤ 2 * ∫ x, min ((μ.rnDeriv ν x).toReal) 1 ∂ν := by
    rw [hρ_def]; exact sq_bhattacharyya_le_two_mul_integral_min μ ν hac
  have hL1 : ∫ x, min ((μ.rnDeriv ν x).toReal) 1 ∂ν ≤ 1 - tvDist μ ν :=
    integral_min_le_one_sub_tvDist μ ν hac
  rw [hK_def]
  linarith [hsq, hL2, hL1]

end Causalean.Stat
