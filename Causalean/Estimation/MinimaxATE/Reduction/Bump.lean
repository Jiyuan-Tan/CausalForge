/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE estimation: `l2sq` algebra and Rademacher bumps

Small reusable algebra lemmas about the squared `L²(P_X)` distance `l2sq` and
constant-magnitude (Rademacher) bumps.  These are used to verify class-membership
(`InClass`) in the structure-agnostic lower-bound construction: a perturbation of a
nuisance by `δ` times a sign function `σ` (with `(σ x)² = 1`) moves the `L²` distance
by exactly `δ²`, which lands a Rademacher bump on the boundary of the budget class.
-/

import Causalean.Estimation.MinimaxATE.Model

/-! # Squared-Distance Bump Algebra

This file provides finite squared-distance identities for functions on a covariate
space.  It proves the basic algebraic facts `l2sq_self`, `l2sq_comm`, and `l2sq_nonneg`, then
records the Rademacher-bump identity `l2sq_bump`: if `a x = b x + δ * σ x` and every sign satisfies
`(σ x)^2 = 1`, then the squared distance from `a` to `b` is exactly `δ^2` on a nonempty finite
space.  This is the reusable membership calculation for lower-bound perturbations that are placed
on the boundary of an `InClass` budget. -/

namespace Causalean.Estimation.MinimaxATE

open scoped BigOperators

variable {C : Type*} [Fintype C]

/-- `l2sq` of a function with itself is zero. -/
theorem l2sq_self (a : C → ℝ) : l2sq a a = 0 := by
  simp [l2sq]

/-- `l2sq` is symmetric. -/
theorem l2sq_comm (a b : C → ℝ) : l2sq a b = l2sq b a := by
  rw [l2sq, l2sq]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- `l2sq` is nonnegative. -/
theorem l2sq_nonneg (a b : C → ℝ) : 0 ≤ l2sq a b := by
  rw [l2sq]
  refine mul_nonneg ?_ ?_
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact Finset.sum_nonneg fun x _ => sq_nonneg _

/-- **Constant-magnitude (Rademacher) bump.** If `a` differs from `b` by `δ` times a
sign function `σ` with `(σ x)² = 1` everywhere, then `l2sq a b = δ²` (for nonempty `C`).
This is exactly what makes a Rademacher-bump perturbation land on the boundary of the
nuisance class `ℱ(ε,·)` when `δ = √ε`. -/
theorem l2sq_bump [Nonempty C] (b : C → ℝ) (δ : ℝ) (σ : C → ℝ)
    (hσ : ∀ x, (σ x) ^ 2 = 1) :
    l2sq (fun x => b x + δ * σ x) b = δ ^ 2 := by
  have hC : (Fintype.card C : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [l2sq]
  have hsum : ∑ x : C, ((b x + δ * σ x) - b x) ^ 2 = ∑ _x : C, δ ^ 2 := by
    apply Finset.sum_congr rfl
    intro x _
    have : ((b x + δ * σ x) - b x) ^ 2 = δ ^ 2 * (σ x) ^ 2 := by ring
    rw [this, hσ x, mul_one]
  rw [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

end Causalean.Estimation.MinimaxATE
