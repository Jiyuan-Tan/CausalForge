/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Lasso.Finite

/-! # Lasso — soft-thresholding closed form

The scalar soft-thresholding identity: `S_λ(a)` is the exact minimizer of the
one-dimensional penalized objective `(u − a)² + 2λ|u|`.  This is the per-coordinate
proximal step that underlies closed-form lasso calculations in orthonormal
coordinates.
-/

namespace Causalean.ML

open BigOperators

/-- For `λ ≥ 0`, the soft-thresholded value `S_λ(a)` minimizes the one-dimensional
penalized least-squares objective `u ↦ (u − a)² + 2λ|u|`. -/
theorem softThreshold_isMinOn {lam : ℝ} (hlam : 0 ≤ lam) (a : ℝ) :
    ∀ u : ℝ, (softThreshold lam a - a) ^ 2 + 2 * lam * |softThreshold lam a|
      ≤ (u - a) ^ 2 + 2 * lam * |u| := by
  intro u
  by_cases hpos : lam < a
  · have hS : softThreshold lam a = a - lam := by
      unfold softThreshold
      have h1 : max (a - lam) 0 = a - lam := max_eq_left (sub_nonneg.mpr hpos.le)
      have h2 : max (-a - lam) 0 = 0 := by
        refine max_eq_right ?_
        linarith
      rw [h1, h2, sub_zero]
    have hAbsS : |a - lam| = a - lam := abs_of_nonneg (sub_nonneg.mpr hpos.le)
    rw [hS, hAbsS]
    by_cases hu : 0 ≤ u
    · rw [abs_of_nonneg hu]
      nlinarith [sq_nonneg (u - (a - lam))]
    · rw [abs_of_nonpos (le_of_not_ge hu)]
      nlinarith [sq_nonneg (u - (a - lam))]
  · by_cases hneg : a < -lam
    · have hS : softThreshold lam a = a + lam := by
        unfold softThreshold
        have h1 : max (a - lam) 0 = 0 := by
          refine max_eq_right ?_
          linarith
        have h2 : max (-a - lam) 0 = -a - lam := by
          refine max_eq_left ?_
          linarith
        rw [h1, h2]
        ring
      have hAbsS : |a + lam| = -(a + lam) := by
        exact abs_of_nonpos (by linarith)
      rw [hS, hAbsS]
      by_cases hu : 0 ≤ u
      · rw [abs_of_nonneg hu]
        nlinarith [sq_nonneg (u - (a + lam))]
      · rw [abs_of_nonpos (le_of_not_ge hu)]
        nlinarith [sq_nonneg (u - (a + lam))]
    · have hS : softThreshold lam a = 0 := by
        unfold softThreshold
        have hle1 : a - lam ≤ 0 := by linarith
        have hle2 : -a - lam ≤ 0 := by linarith
        rw [max_eq_right hle1, max_eq_right hle2, sub_self]
      rw [hS, abs_zero]
      by_cases hu : 0 ≤ u
      · rw [abs_of_nonneg hu]
        nlinarith [sq_nonneg u]
      · rw [abs_of_nonpos (le_of_not_ge hu)]
        nlinarith [sq_nonneg u]

end Causalean.ML
