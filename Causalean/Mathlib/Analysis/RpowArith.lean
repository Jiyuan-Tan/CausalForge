/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Small real-power arithmetic helpers

This file provides reusable arithmetic identities and inequalities for real
powers and square roots, especially for sample-size factors and negative
exponents. The main lemmas identify reciprocals with real powers
(`inv_eq_rpow_neg_one`), factor `(A / n) ^ p` into an `A` part
and an `n` part (`div_rpow_of_nonneg_of_pos`), bound nonpositive powers of natural casts
(`rpow_natCast_nonpos_le_one`), and rewrite `q⁻¹ * sqrt q` as `q ^ (-1/2)`
(`inv_mul_sqrt_eq_rpow_neg_half`).
-/

namespace Causalean.Mathlib.RpowArith

/-- The reciprocal of any real number is its real power with exponent negative one. -/
lemma inv_eq_rpow_neg_one (x : ℝ) : x⁻¹ = x ^ (-1 : ℝ) := by
  rw [Real.rpow_neg_one]

/-- **Factoring a real power of a quotient.** For [a nonnegative numerator `A`](hyp:hA) and [a
strictly positive denominator `n`](hyp:hn), [the real power `(A/n)^p` equals `A^p` times `n`
raised to the power `−p`](goal), for any real exponent `p`. -/
lemma div_rpow_of_nonneg_of_pos
    (A p n : ℝ) (hA : 0 ≤ A) (hn : 0 < n) :
    (A / n) ^ p = A ^ p * n ^ (-p) := by
  have hnnonneg : 0 ≤ n := le_of_lt hn
  have hinv_nonneg : 0 ≤ n⁻¹ := inv_nonneg.mpr hnnonneg
  have hinv := inv_eq_rpow_neg_one n
  calc
    (A / n) ^ p = (A * n⁻¹) ^ p := by
      rw [div_eq_mul_inv]
    _ = A ^ p * (n⁻¹) ^ p := by
      rw [Real.mul_rpow hA hinv_nonneg]
    _ = A ^ p * (n ^ (-1 : ℝ)) ^ p := by
      rw [hinv]
    _ = A ^ p * n ^ ((-1 : ℝ) * p) := by
      rw [Real.rpow_mul hnnonneg]
    _ = A ^ p * n ^ (-p) := by
      congr 1
      ring_nf

/-- **Nonpositive real power of a natural number is at most one.** For [a nonpositive real exponent
`e`](hyp:he), [the real power of any natural-number cast raised to `e` is at most `1`](goal). -/
lemma rpow_natCast_nonpos_le_one
    (n : ℕ) (e : ℝ) (he : e ≤ 0) :
    (n : ℝ) ^ e ≤ 1 := by
  cases n with
  | zero =>
    by_cases he_zero : e = 0
    · simp [he_zero]
    · simp [Real.zero_rpow he_zero]
  | succ n =>
    have hn_ge_one : 1 ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
    exact Real.rpow_le_one_of_one_le_of_nonpos hn_ge_one he

/-- **Reciprocal times square root as a negative-half power.** For [a nonnegative real number
`q`](hyp:hq), [the reciprocal of `q` times the square root of `q` equals `q` raised to the power
`−1/2`](goal). -/
lemma inv_mul_sqrt_eq_rpow_neg_half (q : ℝ) (hq : 0 ≤ q) :
    q⁻¹ * Real.sqrt q = q ^ (-(1 / 2 : ℝ)) := by
  rcases hq.eq_or_lt with rfl | hq
  · simp
  · calc
      q⁻¹ * Real.sqrt q = q ^ (-1 : ℝ) * q ^ (1 / (2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow]
        rw [Real.rpow_neg hq.le, Real.rpow_one]
      _ = q ^ ((-1 : ℝ) + 1 / (2 : ℝ)) := by
        rw [← Real.rpow_add hq]
      _ = q ^ (-(1 / 2 : ℝ)) := by ring_nf

end Causalean.Mathlib.RpowArith
