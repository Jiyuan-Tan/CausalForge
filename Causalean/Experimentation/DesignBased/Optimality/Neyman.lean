/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Neyman optimal allocation

For a two-arm experiment the randomization variance of the difference-in-means estimator, as a
function of the treatment fraction `x ∈ (0,1)`, has the form `A/x + B/(1−x)` with `A, B > 0` the
treated- and control-arm outcome variances.  **Neyman allocation** is the choice of `x` minimizing
this variance.  This file proves the analytic heart of the result: `A/x + B/(1−x)` is bounded below
by `(√A + √B)²` on `(0,1)`, and attains that minimum at the **Neyman fraction**
`x* = √A / (√A + √B)`, which therefore splits the sample in proportion to the arms' standard
deviations.
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Neyman allocation

Neyman allocation minimizes the two-arm variance proxy by assigning in proportion to
standard deviations.

The definitions `neymanFraction` and `neymanOptimalValue` package the optimizer
`sqrt A / (sqrt A + sqrt B)` and the value `(sqrt A + sqrt B)^2`.  Theorems
`neyman_allocation_lower_bound`, `neyman_allocation_eq_at_fraction`, and
`neyman_allocation_isMinimizer` prove the lower bound, show equality at the Neyman
fraction, and state the resulting minimization property on the interval `(0, 1)`.
-/

open scoped BigOperators

namespace Causalean
namespace Experimentation
namespace DesignBased

/-- The **Neyman-fraction formula**: `√A / (√A + √B)`, the treatment fraction that minimizes
the two-arm variance `A/x + B/(1−x)` when the arm variances are positive. -/
noncomputable def neymanFraction (A B : ℝ) : ℝ := Real.sqrt A / (Real.sqrt A + Real.sqrt B)

/-- The **Neyman optimal-value formula**: `(√A + √B)²`, the minimized two-arm variance when
the arm variances are positive. -/
noncomputable def neymanOptimalValue (A B : ℝ) : ℝ := (Real.sqrt A + Real.sqrt B) ^ 2

/-- **Neyman allocation lower bound.** For positive arm variances `A, B` and any treatment fraction
`x ∈ (0,1)`, the two-arm variance is at least `(√A + √B)²`. -/
theorem neyman_allocation_lower_bound {A B x : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hx0 : 0 < x) (hx1 : x < 1) :
    neymanOptimalValue A B ≤ A / x + B / (1 - x) := by
  -- A/x + B/(1−x) − (√A+√B)² = (√(A(1−x)/x) − √(Bx/(1−x)))² ≥ 0  (the cross term √(AB) cancels x).
  unfold neymanOptimalValue
  have hx1' : 0 < 1 - x := sub_pos.mpr hx1
  have hxne : x ≠ 0 := ne_of_gt hx0
  have h1xne : 1 - x ≠ 0 := ne_of_gt hx1'
  have hden : 0 < x * (1 - x) := mul_pos hx0 hx1'
  have hcommon : A / x + B / (1 - x) =
      (A * (1 - x) + B * x) / (x * (1 - x)) := by
    field_simp [hxne, h1xne]
  rw [hcommon]
  rw [le_div_iff₀ hden]
  have hsqA : Real.sqrt A ^ 2 = A := Real.sq_sqrt (le_of_lt hA)
  have hsqB : Real.sqrt B ^ 2 = B := Real.sq_sqrt (le_of_lt hB)
  nlinarith [sq_nonneg (Real.sqrt A - (Real.sqrt A + Real.sqrt B) * x)]

/-- The Neyman fraction lies in `(0,1)`. -/
theorem neymanFraction_mem_Ioo {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    0 < neymanFraction A B ∧ neymanFraction A B < 1 := by
  unfold neymanFraction
  have hs : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have ht : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  constructor
  · exact div_pos hs (add_pos hs ht)
  · exact (div_lt_one (add_pos hs ht)).2
      (lt_add_of_pos_right (Real.sqrt A) ht)

/-- **Neyman allocation optimum.** At the Neyman fraction the two-arm variance equals its lower
bound `(√A + √B)²`; hence the Neyman fraction minimizes the variance over `(0,1)`. -/
theorem neyman_allocation_eq_at_fraction {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    A / neymanFraction A B + B / (1 - neymanFraction A B) = neymanOptimalValue A B := by
  unfold neymanFraction neymanOptimalValue
  have hs : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have ht : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  have hsum : Real.sqrt A + Real.sqrt B ≠ 0 := ne_of_gt (add_pos hs ht)
  have hsne : Real.sqrt A ≠ 0 := ne_of_gt hs
  have htne : Real.sqrt B ≠ 0 := ne_of_gt ht
  have hsub : 1 - Real.sqrt A / (Real.sqrt A + Real.sqrt B) =
      Real.sqrt B / (Real.sqrt A + Real.sqrt B) := by
    field_simp [hsum]
    ring
  rw [hsub]
  field_simp [hsum, hsne, htne]
  ring_nf
  rw [Real.sq_sqrt (le_of_lt hA), Real.sq_sqrt (le_of_lt hB)]
  ring

/-- The Neyman fraction is a minimizer: its two-arm variance is no larger than the variance at
any treatment fraction in `(0,1)`. -/
theorem neyman_allocation_isMinimizer {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∀ x, 0 < x → x < 1 →
      A / neymanFraction A B + B / (1 - neymanFraction A B) ≤ A / x + B / (1 - x) := by
  intro x hx0 hx1
  rw [neyman_allocation_eq_at_fraction hA hB]
  exact neyman_allocation_lower_bound hA hB hx0 hx1

end DesignBased
end Experimentation
end Causalean
