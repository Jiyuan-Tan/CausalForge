/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Probability.Moments.Variance

/-!
# Chebyshev bounds with a supplied variance envelope

This module provides a real-valued Chebyshev probability bound for one
square-integrable statistic whose mean is known and whose variance has a
supplied upper bound. This differs from `iid_sum_chebyshev`, which specializes
to an i.i.d. sum with its exact variance and states the result as an `ENNReal`
measure bound.
-/

namespace Causalean.Stat.Concentration

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A square-integrable statistic with known mean and variance at most a supplied envelope exceeds
an absolute deviation threshold with probability at most the envelope divided by the squared
threshold. -/
lemma probability_abs_sub_mean_gt_le
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsFiniteMeasure Q] (F : Ω → ℝ) (mean v a : ℝ)
    (hF : MemLp F 2 Q) (ha : 0 < a)
    (hmean : (∫ x, F x ∂Q) = mean)
    (hvar : variance F Q ≤ v) :
    (Q {x | a < |F x - mean|}).toReal ≤ v / a ^ 2 := by
  have hcheb := meas_ge_le_variance_div_sq hF ha
  have hsub :
      {x | a < |F x - mean|} ⊆
        {x | a ≤ |F x - ∫ y, F y ∂Q|} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [hmean]
    exact hx.le
  calc
    (Q {x | a < |F x - mean|}).toReal ≤
        (Q {x | a ≤ |F x - ∫ y, F y ∂Q|}).toReal :=
      measureReal_mono hsub
    _ ≤ (ENNReal.ofReal (variance F Q / a ^ 2)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
    _ = variance F Q / a ^ 2 := by
      rw [ENNReal.toReal_ofReal]
      exact div_nonneg (variance_nonneg _ _) (sq_nonneg _)
    _ ≤ v / a ^ 2 := by
      exact div_le_div_of_nonneg_right hvar (sq_nonneg _)

end Causalean.Stat.Concentration
