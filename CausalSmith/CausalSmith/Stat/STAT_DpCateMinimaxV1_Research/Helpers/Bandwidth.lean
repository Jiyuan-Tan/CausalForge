/- Copyright (c) 2026 Jiyuan Tan. All rights reserved. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace CausalSmith.Stat.DpCateMinimax

lemma exists_power_bandwidth (p gamma A r : ℝ)
    (hp : 0 < p) (hgamma : 0 < gamma) (hA : 0 ≤ A) (hr : 0 < r) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ a ≤ r ∧ a ≤ 1 ∧
      ∀ x : ℝ, 1 ≤ x →
        let h := a * x ^ (-(1 / p))
        0 < h ∧ h ≤ r ∧ h ≤ 1 ∧
        c * x ^ (-(gamma / p)) ≤ h ^ gamma ∧
        A * x * h ^ p ≤ 1 / 8 := by
  let t := (1 / (8 * (A + 1))) ^ (1 / p)
  let a := min (min r 1) t
  let c := a ^ gamma
  have hden : 0 < 8 * (A + 1) := by positivity
  have ht : 0 < t := Real.rpow_pos_of_pos (one_div_pos.mpr hden) _
  have ha : 0 < a := lt_min (lt_min hr zero_lt_one) ht
  have har : a ≤ r := le_trans (min_le_left _ _) (min_le_left _ _)
  have ha1 : a ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hat : a ≤ t := min_le_right _ _
  have hc : 0 < c := Real.rpow_pos_of_pos ha _
  refine ⟨a, c, ha, hc, har, ha1, ?_⟩
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  let h := a * x ^ (-(1 / p))
  have hxpow0 : 0 < x ^ (-(1 / p)) := Real.rpow_pos_of_pos hx0 _
  have hxpow1 : x ^ (-(1 / p)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx (neg_nonpos.mpr (one_div_nonneg.mpr hp.le))
  have hh : 0 < h := mul_pos ha hxpow0
  have hha : h ≤ a := by dsimp [h]; simpa using mul_le_of_le_one_right ha.le hxpow1
  have hrate : h ^ gamma = c * x ^ (-(gamma / p)) := by
    dsimp [h, c]
    rw [Real.mul_rpow ha.le hxpow0.le, ← Real.rpow_mul hx0.le]
    congr 1
    ring_nf
  have hatpow : a ^ p ≤ t ^ p := Real.rpow_le_rpow ha.le hat hp.le
  have htpow : t ^ p = 1 / (8 * (A + 1)) := by
    dsimp [t]
    rw [← Real.rpow_mul (one_div_pos.mpr hden).le]
    rw [show 1 / p * p = 1 by field_simp]
    simp
  have hbudget_eq : x * h ^ p = a ^ p := by
    dsimp [h]
    rw [Real.mul_rpow ha.le hxpow0.le, ← Real.rpow_mul hx0.le]
    have : -(1 / p) * p = -1 := by field_simp
    rw [this, Real.rpow_neg_one]
    field_simp
  refine ⟨hh, hha.trans har, hha.trans ha1, ?_, ?_⟩
  · rw [hrate]
  · rw [mul_assoc, hbudget_eq]
    calc
      A * a ^ p ≤ A * (1 / (8 * (A + 1))) :=
        mul_le_mul_of_nonneg_left (hatpow.trans_eq htpow) hA
      _ ≤ 1 / 8 := by
        have hfrac : A / (A + 1) ≤ 1 :=
          (div_le_one (by positivity : 0 < A + 1)).2 (by linarith)
        calc
          A * (1 / (8 * (A + 1))) = (1 / 8) * (A / (A + 1)) := by
            field_simp [ne_of_gt (by positivity : 0 < A + 1)]
          _ ≤ (1 / 8) * 1 := mul_le_mul_of_nonneg_left hfrac (by norm_num)
          _ = 1 / 8 := by ring

end CausalSmith.Stat.DpCateMinimax
