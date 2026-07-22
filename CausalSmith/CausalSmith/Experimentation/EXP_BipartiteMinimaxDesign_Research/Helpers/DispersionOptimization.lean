/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Optimization facts for the unbounded dispersion certificate
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers.DispersionConstruction

set_option linter.style.longLine false

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

-- @node: reciprocalBarrier
/-- The one-coordinate additive surrogate barrier. -/
noncomputable def reciprocalBarrier (x : ℝ) : ℝ := x⁻¹ + (1 - x)⁻¹

-- @node: reciprocalBarrierSlope
/-- The derivative of `reciprocalBarrier` at an interior point. -/
noncomputable def reciprocalBarrierSlope (r : ℝ) : ℝ := -(r⁻¹ ^ 2) + (1 - r)⁻¹ ^ 2

-- @node: reciprocalBarrier_tangent_gap
lemma reciprocalBarrier_tangent_gap {x r : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    reciprocalBarrier r + reciprocalBarrierSlope r * (x - r) ≤ reciprocalBarrier x := by
  have hxn : x ≠ 0 := ne_of_gt hx0
  have hrn : r ≠ 0 := ne_of_gt hr0
  have h1xn : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
  have h1rn : 1 - r ≠ 0 := ne_of_gt (sub_pos.mpr hr1)
  have hA : 0 < r ^ 2 + 2 * r * x - 2 * r - x + 1 := by
    by_cases hhalf : r ≤ 1 / 2
    · have hc : 0 ≤ (1 - 2 * r) * (1 - x) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [sq_pos_of_pos hr0]
    · have hc : 0 ≤ (2 * r - 1) * x :=
        mul_nonneg (by linarith) (le_of_lt hx0)
      nlinarith [sq_pos_of_pos (sub_pos.mpr hr1)]
  have hgap :
      reciprocalBarrier x -
          (reciprocalBarrier r + reciprocalBarrierSlope r * (x - r)) =
        (x - r) ^ 2 * (r ^ 2 + 2 * r * x - 2 * r - x + 1) /
          (r ^ 2 * x * (1 - r) ^ 2 * (1 - x)) := by
    rw [reciprocalBarrier, reciprocalBarrier, reciprocalBarrierSlope, inv_pow]
    field_simp
    ring
  apply sub_nonneg.mp
  rw [hgap]
  apply div_nonneg
  · exact mul_nonneg (sq_nonneg _) (le_of_lt hA)
  · exact le_of_lt (mul_pos
      (mul_pos (mul_pos (sq_pos_of_pos hr0) hx0) (sq_pos_of_pos (sub_pos.mpr hr1)))
      (sub_pos.mpr hx1))

-- @node: reciprocalBarrier_tangent_eq_iff
/-- The reciprocal barrier equals its tangent-line lower bound at the mean propensity exactly when every propensity equals that mean. -/
lemma reciprocalBarrier_tangent_eq_iff {x r : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    reciprocalBarrier r + reciprocalBarrierSlope r * (x - r) = reciprocalBarrier x ↔
      x = r := by
  have hxn : x ≠ 0 := ne_of_gt hx0
  have hrn : r ≠ 0 := ne_of_gt hr0
  have h1xn : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
  have h1rn : 1 - r ≠ 0 := ne_of_gt (sub_pos.mpr hr1)
  have hA : 0 < r ^ 2 + 2 * r * x - 2 * r - x + 1 := by
    by_cases hhalf : r ≤ 1 / 2
    · have hc : 0 ≤ (1 - 2 * r) * (1 - x) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [sq_pos_of_pos hr0]
    · have hc : 0 ≤ (2 * r - 1) * x :=
        mul_nonneg (by linarith) (le_of_lt hx0)
      nlinarith [sq_pos_of_pos (sub_pos.mpr hr1)]
  have hgap :
      reciprocalBarrier x -
          (reciprocalBarrier r + reciprocalBarrierSlope r * (x - r)) =
        (x - r) ^ 2 * (r ^ 2 + 2 * r * x - 2 * r - x + 1) /
          (r ^ 2 * x * (1 - r) ^ 2 * (1 - x)) := by
    rw [reciprocalBarrier, reciprocalBarrier, reciprocalBarrierSlope, inv_pow]
    field_simp
    ring
  constructor
  · intro h
    have hz : reciprocalBarrier x -
        (reciprocalBarrier r + reciprocalBarrierSlope r * (x - r)) = 0 := by
      linarith
    rw [hgap, div_eq_zero_iff] at hz
    rcases hz with hnum | hden
    · rcases mul_eq_zero.mp hnum with hs | hAz
      · exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
      · exact False.elim ((ne_of_gt hA) hAz)
    · have hdenne : r ^ 2 * x * (1 - r) ^ 2 * (1 - x) ≠ 0 := by
        positivity
      exact False.elim (hdenne hden)
  · rintro rfl
    ring

-- @node: reciprocalBarrier_sum_minimized_at_mean
/-- Among propensities with a fixed average, the sum of reciprocal barriers is minimized at the common mean propensity. -/
lemma reciprocalBarrier_sum_minimized_at_mean {K : Type*} [Fintype K]
    (p : K → ℝ) (r : ℝ) (hp0 : ∀ k, 0 < p k) (hp1 : ∀ k, p k < 1)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hmean : ∑ k, p k = (Fintype.card K : ℝ) * r) :
    (Fintype.card K : ℝ) * reciprocalBarrier r ≤ ∑ k, reciprocalBarrier (p k) := by
  calc
    (Fintype.card K : ℝ) * reciprocalBarrier r
        = ∑ k : K, (reciprocalBarrier r + reciprocalBarrierSlope r * (p k - r)) := by
          rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
          simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, card_univ, hmean]
          ring
    _ ≤ ∑ k, reciprocalBarrier (p k) := by
      exact sum_le_sum fun k _ => reciprocalBarrier_tangent_gap (hp0 k) (hp1 k) hr0 hr1

-- @node: reciprocalBarrier_sum_unique_minimizer
/-- The common-mean propensity vector is the unique minimizer of the reciprocal-barrier sum among vectors with the same average. -/
lemma reciprocalBarrier_sum_unique_minimizer {K : Type*} [Fintype K]
    (p : K → ℝ) (r : ℝ) (hp0 : ∀ k, 0 < p k) (hp1 : ∀ k, p k < 1)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hmean : ∑ k, p k = (Fintype.card K : ℝ) * r)
    (hle : ∑ k, reciprocalBarrier (p k) ≤
      (Fintype.card K : ℝ) * reciprocalBarrier r) :
    p = fun _ => r := by
  funext k
  have hsum := reciprocalBarrier_sum_minimized_at_mean p r hp0 hp1 hr0 hr1 hmean
  have heq : ∑ j : K, reciprocalBarrier (p j) =
      (Fintype.card K : ℝ) * reciprocalBarrier r := le_antisymm hle hsum
  have hterm : ∀ j ∈ (univ : Finset K),
      reciprocalBarrier r + reciprocalBarrierSlope r * (p j - r) ≤
        reciprocalBarrier (p j) := fun j _ =>
    reciprocalBarrier_tangent_gap (hp0 j) (hp1 j) hr0 hr1
  have hsumTang : ∑ j : K,
      (reciprocalBarrier r + reciprocalBarrierSlope r * (p j - r)) =
        (Fintype.card K : ℝ) * reciprocalBarrier r := by
    rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
    simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, card_univ, hmean]
    ring
  have hk := (sum_eq_sum_iff_of_le hterm).mp (hsumTang.trans heq.symm) k (mem_univ k)
  exact (reciprocalBarrier_tangent_eq_iff (hp0 k) (hp1 k) hr0 hr1).mp hk

end CausalSmith.Experimentation.BipartiteMinimaxDesign
