/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Variance decomposition on a product probability space

This file provides the law of total variance in an explicit form for a statistic of two
independent coordinates, using its within-slice variances and slice means.
-/

open MeasureTheory ProbabilityTheory

namespace Causalean.Mathlib.Probability

/-- For independent coordinates with laws `μ` and `ν`, and a real-valued statistic `F` on the
product that is [square-integrable under the product law](hyp:hF), suppose that [almost every
slice of `F` along the first coordinate, at a fixed value of the second coordinate, is
square-integrable](hyp:hsection), that [the map `m` of slice means is square-integrable under
`ν`](hyp:hm), and that [`m` records the correct slice means: the integral of `F` over the first
coordinate at almost every value of the second coordinate equals `m` there](hyp:hmean). Then
[the variance of `F` under the product measure equals the `ν`-average of the within-slice
variances of `F` plus the variance, across the second coordinate, of the slice-mean map
`m`](goal). -/
lemma variance_prod_eq_integral_variance_add
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (μ : Measure Ω) (ν : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : Ω × T → ℝ) (m : T → ℝ)
    (hF : MemLp F 2 (μ.prod ν))
    (hsection : ∀ᵐ t ∂ν, MemLp (fun s => F (s, t)) 2 μ)
    (hm : MemLp m 2 ν)
    (hmean : ∀ᵐ t ∂ν, (∫ s, F (s, t) ∂μ) = m t) :
    variance F (μ.prod ν) =
      (∫ t, variance (fun s => F (s, t)) μ ∂ν) +
        variance m ν := by
  have hFsq : Integrable (fun z => F z ^ 2) (μ.prod ν) :=
    hF.integrable_sq
  have hinnerSq :
      Integrable (fun t => ∫ s, F (s, t) ^ 2 ∂μ) ν := by
    simpa only [Function.uncurry_apply_pair] using hFsq.integral_prod_right
  have hvariance :
      (fun t => variance (fun s => F (s, t)) μ) =ᵐ[ν]
        fun t => (∫ s, F (s, t) ^ 2 ∂μ) - (m t) ^ 2 := by
    filter_upwards [hsection, hmean] with t htsection htmean
    rw [variance_eq_sub htsection, htmean]
    simp only [Pi.pow_apply]
  rw [variance_eq_sub hF, variance_eq_sub hm]
  rw [integral_congr_ae hvariance]
  simp only [Pi.pow_apply]
  rw [integral_sub hinnerSq hm.integrable_sq]
  rw [integral_prod_symm _ hFsq]
  have hFint : Integrable F (μ.prod ν) := hF.integrable (by norm_num)
  rw [integral_prod_symm _ hFint]
  rw [integral_congr_ae hmean]
  ring

end Causalean.Mathlib.Probability
