/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Small real-power arithmetic helpers

Model-agnostic `Real.rpow`/`Real.sqrt` algebra, staged here (CausalSmith side) out
of the policy-regret rate derivation.  Each statement is pure real analysis over
free variables — no statistical model and no calibration-specific exponents.
Promotion to `Causalean/` is gated on a second consumer.
-/

namespace CausalSmith.Mathlib.RpowArith

/-- `n⁻¹ = n^(-1)` as a real power, for `0 < n`. -/
lemma natCast_inv_eq_rpow_neg_one (n : ℕ) (hn : 0 < n) :
    ((n : ℝ)⁻¹) = (n : ℝ) ^ (-1 : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnnonneg : 0 ≤ (n : ℝ) := le_of_lt hnpos
  rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num]
  rw [Real.rpow_neg hnnonneg]
  rw [Real.rpow_one]

/-- Pull a `1/n` factor out of a real power: `(A/n)^(p/2) = A^(p/2)·n^(-p/2)`. -/
lemma div_natCast_rpow
    (A p : ℝ) (n : ℕ) (hA : 0 ≤ A) (hn : 0 < n) :
    (A / (n : ℝ)) ^ (p / 2) = A ^ (p / 2) * (n : ℝ) ^ (-(p / 2)) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnnonneg : 0 ≤ (n : ℝ) := le_of_lt hnpos
  have hinv_nonneg : 0 ≤ ((n : ℝ)⁻¹) := inv_nonneg.mpr hnnonneg
  have hinv := natCast_inv_eq_rpow_neg_one n hn
  calc
    (A / (n : ℝ)) ^ (p / 2) = (A * (n : ℝ)⁻¹) ^ (p / 2) := by
      rw [div_eq_mul_inv]
    _ = A ^ (p / 2) * ((n : ℝ)⁻¹) ^ (p / 2) := by
      rw [Real.mul_rpow hA hinv_nonneg]
    _ = A ^ (p / 2) * ((n : ℝ) ^ (-1 : ℝ)) ^ (p / 2) := by
      rw [hinv]
    _ = A ^ (p / 2) * (n : ℝ) ^ ((-1 : ℝ) * (p / 2)) := by
      rw [Real.rpow_mul hnnonneg]
    _ = A ^ (p / 2) * (n : ℝ) ^ (-(p / 2)) := by
      congr 1
      ring_nf

/-- A nonpositive real power of `n ≥ 1` is at most `1`. -/
lemma rpow_natCast_nonpos_le_one
    (n : ℕ) (e : ℝ) (hn : 0 < n) (he : e ≤ 0) :
    (n : ℝ) ^ e ≤ 1 := by
  have hn_ge_one : 1 ≤ (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hn)
  exact Real.rpow_le_one_of_one_le_of_nonpos hn_ge_one he

/-- `q⁻¹·√q = q^(-1/2)` for `0 < q`. -/
lemma inv_mul_sqrt_eq_rpow_neg_half (q : ℝ) (hq : 0 < q) :
    q⁻¹ * Real.sqrt q = q ^ (-(1 / 2 : ℝ)) := by
  have hq_nonneg : 0 ≤ q := le_of_lt hq
  calc
    q⁻¹ * Real.sqrt q = q ^ (-1 : ℝ) * q ^ (1 / (2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      rw [Real.rpow_neg hq_nonneg, Real.rpow_one]
    _ = q ^ ((-1 : ℝ) + 1 / (2 : ℝ)) := by
      rw [← Real.rpow_add hq]
    _ = q ^ (-(1 / 2 : ℝ)) := by ring_nf

end CausalSmith.Mathlib.RpowArith
