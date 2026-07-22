/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.Probability.StdNormalCDF

/-!
# Standard normal survival integral and truncated first moment

This file proves two one-dimensional identities for the named standard-normal
density `stdNormalPDF` and CDF `stdNormalCDF`:

* `integral_Ioi_stdNormalPDF`: the survival integral
  `∫_{c}^∞ φ(t) dt = 1 - Φ(c)`;
* `integral_Ioi_id_mul_stdNormalPDF`: the truncated first moment
  `∫_{c}^∞ t * φ(t) dt = φ(c)`.

The moment identity follows from `d/dt[-φ(t)] = t * φ(t)` and supplies the
closed-form Gaussian tail moment used by sensitivity calculations. -/

namespace Causalean.Mathlib

open MeasureTheory ProbabilityTheory Real Filter Topology

/-- **The standard-normal survival integral:** `∫_{c}^∞ φ(t) dt = 1 − Φ(c)`. -/
lemma integral_Ioi_stdNormalPDF (c : ℝ) :
    ∫ t in Set.Ioi c, stdNormalPDF t = 1 - stdNormalCDF c := by
  have hmeasure := ProbabilityTheory.gaussianReal_apply_eq_integral
    (μ := 0) (v := 1) (by norm_num) (Set.Ioi c)
  have hnonneg_g : 0 ≤ ∫ t in Set.Ioi c, gaussianPDFReal 0 1 t := by
    exact integral_nonneg fun t => gaussianPDFReal_nonneg 0 1 t
  have hset_g :
      ∫ t in Set.Ioi c, gaussianPDFReal 0 1 t =
        (gaussianReal 0 1).real (Set.Ioi c) := by
    rw [MeasureTheory.measureReal_def]
    rw [hmeasure]
    exact (ENNReal.toReal_ofReal hnonneg_g).symm
  have hset :
      ∫ t in Set.Ioi c, stdNormalPDF t = (gaussianReal 0 1).real (Set.Ioi c) := by
    simpa [stdNormalPDF] using hset_g
  have hcompl :
      (gaussianReal 0 1).real (Set.Ioi c) =
        1 - (gaussianReal 0 1).real (Set.Iic c) := by
    have h := MeasureTheory.measureReal_compl
      (μ := gaussianReal 0 1) (s := Set.Iic c) measurableSet_Iic
    simpa [Set.compl_Iic, MeasureTheory.probReal_univ] using h
  have hcdf : (gaussianReal 0 1).real (Set.Iic c) = stdNormalCDF c := by
    rw [stdNormalCDF, ProbabilityTheory.cdf_eq_real]
  rw [hset, hcompl, hcdf]

/-- **The standard-normal truncated first moment:** `∫_{c}^∞ t·φ(t) dt = φ(c)`.
Because `d/dt[−φ(t)] = t·φ(t)` for the standard normal, the truncated mean integrates to
the density value at the cutoff. This is the identity behind the closed-form Gaussian MSM
half-width. -/
lemma integral_Ioi_id_mul_stdNormalPDF (c : ℝ) :
    ∫ t in Set.Ioi c, t * stdNormalPDF t = stdNormalPDF c := by
  let phi : ℝ → ℝ := fun x => Real.exp (-x ^ 2 / 2)
  have phi_pos : ∀ x : ℝ, 0 < phi x := fun x => Real.exp_pos _
  have phi_continuous : Continuous phi := by
    dsimp [phi]
    fun_prop
  have gaussianPDFReal_eq : ∀ x : ℝ,
      gaussianPDFReal 0 1 x = (Real.sqrt (2 * π))⁻¹ * phi x := by
    intro x
    unfold gaussianPDFReal
    dsimp [phi]
    congr 2
    · norm_num
    · ring
  have neg_phi_hasDerivAt :
      ∀ x : ℝ, HasDerivAt (fun y => -phi y) (x * phi x) x := by
    intro x
    dsimp [phi]
    have hpow : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
      have := ((hasDerivAt_pow 2 x).div_const 2).neg
      simpa [neg_div, pow_one] using this.congr_deriv (by ring)
    have hcomp : HasDerivAt (fun y => Real.exp (-y ^ 2 / 2))
        (Real.exp (-x ^ 2 / 2) * (-x)) x := (Real.hasDerivAt_exp _).comp x hpow
    have := hcomp.neg
    convert this using 1
    ring
  have abs_le_exp_sq_div_four : ∀ x : ℝ, |x| ≤ Real.exp (x ^ 2 / 4) := by
    intro x
    have h1 : |x| ≤ 1 + x ^ 2 / 4 := by
      nlinarith [sq_nonneg (|x| / 2 - 1), sq_abs x, abs_nonneg x]
    exact h1.trans (by have := Real.add_one_le_exp (x ^ 2 / 4); linarith)
  have x_mul_phi_integrable : Integrable (fun x : ℝ => x * phi x) := by
    have hdom : Integrable (fun x : ℝ => Real.exp (-(1/4 : ℝ) * x ^ 2)) :=
      integrable_exp_neg_mul_sq (by norm_num)
    refine hdom.mono' ((continuous_id.mul phi_continuous).aestronglyMeasurable) ?_
    filter_upwards with x
    have hexp : phi x = Real.exp (-(1/2 : ℝ) * x ^ 2) := by
      dsimp [phi]
      ring_nf
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (phi_pos x).le, hexp]
    calc |x| * Real.exp (-(1/2 : ℝ) * x ^ 2)
        ≤ Real.exp (x ^ 2 / 4) * Real.exp (-(1/2 : ℝ) * x ^ 2) := by
          gcongr
          exact abs_le_exp_sq_div_four x
      _ = Real.exp (-(1/4 : ℝ) * x ^ 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
  have mul_phi_integrableOn_Ioi : IntegrableOn (fun x => x * phi x) (Set.Ioi c) := by
    exact x_mul_phi_integrable.integrableOn
  have neg_phi_tendsto_atTop :
      Filter.Tendsto (fun x => -phi x) Filter.atTop (nhds 0) := by
    have : Filter.Tendsto phi Filter.atTop (nhds 0) := by
      dsimp [phi]
      have hsq : Filter.Tendsto (fun x : ℝ => x ^ 2) Filter.atTop Filter.atTop := by
        exact Filter.tendsto_pow_atTop (α := ℝ) (n := 2) (by norm_num)
      have h2 :
          Filter.Tendsto (fun x : ℝ => -x ^ 2 / 2) Filter.atTop Filter.atBot := by
        apply Filter.Tendsto.atBot_div_const (by norm_num)
        exact Filter.tendsto_neg_atBot_iff.mpr hsq
      exact Real.tendsto_exp_atBot.comp h2
    simpa using this.neg
  have integral_Ioi_mul_phi : ∫ x in Set.Ioi c, x * phi x = phi c := by
    have := integral_Ioi_of_hasDerivAt_of_tendsto'
      (f := fun y => -phi y) (f' := fun x => x * phi x) (a := c) (m := 0)
      (fun x _ => neg_phi_hasDerivAt x) mul_phi_integrableOn_Ioi neg_phi_tendsto_atTop
    simpa using this
  calc
    ∫ t in Set.Ioi c, t * stdNormalPDF t
        = ∫ t in Set.Ioi c, (Real.sqrt (2 * π))⁻¹ * (t * phi t) := by
          congr 1
          ext t
          rw [stdNormalPDF, gaussianPDFReal_eq]
          ring
    _ = (Real.sqrt (2 * π))⁻¹ * ∫ t in Set.Ioi c, t * phi t := by
          rw [integral_const_mul]
    _ = (Real.sqrt (2 * π))⁻¹ * phi c := by
          rw [integral_Ioi_mul_phi]
    _ = stdNormalPDF c := by
          rw [stdNormalPDF, gaussianPDFReal_eq]

end Causalean.Mathlib
