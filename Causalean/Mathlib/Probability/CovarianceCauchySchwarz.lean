/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Cauchy–Schwarz for covariance

Mathlib provides covariance, variance, and the bilinear/quadratic identities relating them, but no
Cauchy–Schwarz bound `Cov(X,Y)² ≤ Var X · Var Y`.  This file supplies it, together with the
absolute-value form `|Cov(X,Y)| ≤ √(Var X) · √(Var Y)`.  The proof is the classical discriminant
argument: the variance of `X − t·Y` is a nonnegative quadratic in `t`, whose nonnegativity forces
the discriminant to be nonpositive.
-/

import Mathlib.Probability.Moments.Variance

/-! # Cauchy–Schwarz for covariance

For square-integrable statistics `X` and `Y` on a probability space, the squared covariance is at
most the product of the variances (`covariance_sq_le_variance_mul`), equivalently the absolute
covariance is at most the product of the standard deviations (`abs_covariance_le_sqrt_mul`).  This
is the covariance form of the Cauchy–Schwarz inequality, filling a gap in Mathlib's covariance API.
-/

open MeasureTheory ProbabilityTheory

namespace Causalean.Mathlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Cauchy–Schwarz for covariance (squared form).** For square-integrable statistics on a
probability space, the squared covariance is at most the product of the two variances. -/
theorem covariance_sq_le_variance_mul [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    covariance X Y μ ^ 2 ≤ variance X μ * variance Y μ := by
  have hquad : ∀ t : ℝ,
      0 ≤ variance X μ - 2 * t * covariance X Y μ + t ^ 2 * variance Y μ := by
    intro t
    have hsub : MemLp (t • Y) 2 μ := hY.const_smul t
    have h := variance_nonneg (fun ω => X ω - (t • Y) ω) μ
    rw [variance_fun_sub hX hsub, variance_smul, covariance_smul_right] at h
    simpa [Pi.smul_apply, smul_eq_mul, mul_assoc] using h
  by_cases hvar : variance Y μ = 0
  · have hcov : covariance X Y μ = 0 := by
      by_contra hcov
      have h := hquad ((variance X μ + 1) / (2 * covariance X Y μ))
      rw [hvar] at h
      have hvalue :
          variance X μ - 2 * ((variance X μ + 1) / (2 * covariance X Y μ)) *
            covariance X Y μ = -1 := by
        field_simp [hcov]
        ring
      rw [hvalue] at h
      norm_num at h
    simp [hvar, hcov]
  · have hvarpos : 0 < variance Y μ :=
      lt_of_le_of_ne (variance_nonneg Y μ) (Ne.symm hvar)
    apply (div_le_iff₀ hvarpos).mp
    have h := hquad (covariance X Y μ / variance Y μ)
    have hvalue :
        variance X μ - 2 * (covariance X Y μ / variance Y μ) * covariance X Y μ +
          (covariance X Y μ / variance Y μ) ^ 2 * variance Y μ =
            variance X μ - covariance X Y μ ^ 2 / variance Y μ := by
      field_simp [hvar]
      ring
    rw [hvalue] at h
    linarith

/-- **Cauchy–Schwarz for covariance.** For square-integrable statistics on a probability space, the
absolute covariance is at most the product of the standard deviations,
`|Cov(X,Y)| ≤ √(Var X) · √(Var Y)`. -/
theorem abs_covariance_le_sqrt_mul [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    |covariance X Y μ| ≤ Real.sqrt (variance X μ) * Real.sqrt (variance Y μ) := by
  have h := covariance_sq_le_variance_mul hX hY
  rw [← Real.sqrt_mul (variance_nonneg X μ), ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h

end Causalean.Mathlib
