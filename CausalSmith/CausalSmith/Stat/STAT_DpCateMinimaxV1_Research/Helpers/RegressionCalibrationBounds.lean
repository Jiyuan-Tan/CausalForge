/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Private-regression calibration bandwidth bounds

Real-power identities and monotonicity bounds used by the private-regression
calibration algebra.
-/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace CausalSmith.Stat.DpCateMinimax

-- @node: private_regression_privacy_bandwidth_identities
lemma private_regression_privacy_bandwidth_identities (x gamma : ℝ) (d : ℕ)
    (hx : 0 < x) (hgamma : 0 < gamma) :
    let h := x ^ (-(1 / (gamma + (d : ℝ))))
    h ^ gamma = x ^ (-(gamma / (gamma + (d : ℝ)))) ∧
      1 / (x * h ^ (d : ℝ)) = x ^ (-(gamma / (gamma + (d : ℝ)))) := by
  dsimp
  have hden : gamma + (d : ℝ) ≠ 0 := by positivity
  constructor
  · rw [← Real.rpow_mul hx.le]
    congr 1
    field_simp
  · have hmul :
        x * x ^ (-(1 / (gamma + (d : ℝ))) * (d : ℝ)) =
          x ^ (1 + (-(1 / (gamma + (d : ℝ))) * (d : ℝ))) := by
        calc
          _ = x ^ 1 * x ^ (-(1 / (gamma + (d : ℝ))) * (d : ℝ)) := by
            rw [Real.rpow_one]
          _ = _ := (Real.rpow_add hx 1 _).symm
    calc
      1 / (x * (x ^ (-(1 / (gamma + (d : ℝ))))) ^ (d : ℝ)) =
          1 / (x * x ^ (-(1 / (gamma + (d : ℝ))) * (d : ℝ))) := by
            rw [← Real.rpow_mul hx.le]
      _ = 1 / x ^ (1 + (-(1 / (gamma + (d : ℝ))) * (d : ℝ))) := by rw [hmul]
      _ = x ^ (-(1 + (-(1 / (gamma + (d : ℝ))) * (d : ℝ)))) := by
            rw [one_div, Real.rpow_neg hx.le]
      _ = x ^ (-(gamma / (gamma + (d : ℝ)))) := by
            congr 1
            field_simp
            ring

-- @node: private_regression_sampling_bandwidth_identities
lemma private_regression_sampling_bandwidth_identities (x gamma : ℝ) (d : ℕ)
    (hx : 0 < x) (hgamma : 0 < gamma) :
    let h := x ^ (-(1 / (2 * gamma + (d : ℝ))))
    h ^ gamma = x ^ (-(gamma / (2 * gamma + (d : ℝ)))) ∧
      (x * h ^ (d : ℝ)) ^ (-(1 / 2 : ℝ)) =
        x ^ (-(gamma / (2 * gamma + (d : ℝ)))) := by
  dsimp
  have hden : 2 * gamma + (d : ℝ) ≠ 0 := by positivity
  constructor
  · rw [← Real.rpow_mul hx.le]
    congr 1
    field_simp
  · rw [← Real.rpow_mul hx.le]
    have hmul :
        x * x ^ (-(1 / (2 * gamma + (d : ℝ))) * (d : ℝ)) =
          x ^ (1 + (-(1 / (2 * gamma + (d : ℝ))) * (d : ℝ))) := by
        calc
          _ = x ^ 1 * x ^ (-(1 / (2 * gamma + (d : ℝ))) * (d : ℝ)) := by
            rw [Real.rpow_one]
          _ = _ := (Real.rpow_add hx 1 _).symm
    rw [hmul, ← Real.rpow_mul hx.le]
    congr 1
    field_simp
    ring

-- @node: private_regression_sampling_objective_lower
lemma private_regression_sampling_objective_lower (x h gamma : ℝ) (d : ℕ)
    (hx : 0 < x) (hh : 0 < h) (hgamma : 0 < gamma) :
    x ^ (-(gamma / (2 * gamma + (d : ℝ))))
      ≤ h ^ gamma + (x * h ^ (d : ℝ)) ^ (-(1 / 2 : ℝ)) := by
  let h0 := x ^ (-(1 / (2 * gamma + (d : ℝ))))
  have hh0 : 0 < h0 := Real.rpow_pos_of_pos hx _
  have hid0 := private_regression_sampling_bandwidth_identities x gamma d hx hgamma
  by_cases hle : h0 ≤ h
  · have hpw : h0 ^ gamma ≤ h ^ gamma :=
      Real.rpow_le_rpow hh0.le hle hgamma.le
    rw [hid0.1.symm]
    exact hpw.trans (le_add_of_nonneg_right
      (Real.rpow_nonneg (mul_nonneg hx.le (Real.rpow_nonneg hh.le _)) _))
  · have hlt : h < h0 := lt_of_not_ge hle
    have hdpow : h ^ (d : ℝ) ≤ h0 ^ (d : ℝ) :=
      Real.rpow_le_rpow hh.le hlt.le (Nat.cast_nonneg d)
    have hbase : x * h ^ (d : ℝ) ≤ x * h0 ^ (d : ℝ) :=
      mul_le_mul_of_nonneg_left hdpow hx.le
    have hbasepos : 0 < x * h ^ (d : ℝ) :=
      mul_pos hx (Real.rpow_pos_of_pos hh _)
    have hnoise : (x * h0 ^ (d : ℝ)) ^ (-(1 / 2 : ℝ))
        ≤ (x * h ^ (d : ℝ)) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hbasepos hbase (by norm_num)
    rw [hid0.2.symm]
    exact hnoise.trans (le_add_of_nonneg_left (Real.rpow_nonneg hh.le _))

-- @node: private_regression_privacy_objective_lower
lemma private_regression_privacy_objective_lower (x h gamma : ℝ) (d : ℕ)
    (hx : 0 < x) (hh : 0 < h) (hgamma : 0 < gamma) :
    x ^ (-(gamma / (gamma + (d : ℝ))))
      ≤ h ^ gamma + 1 / (x * h ^ (d : ℝ)) := by
  let hp := x ^ (-(1 / (gamma + (d : ℝ))))
  have hhp : 0 < hp := Real.rpow_pos_of_pos hx _
  have hidp := private_regression_privacy_bandwidth_identities x gamma d hx hgamma
  by_cases hle : hp ≤ h
  · have hpw : hp ^ gamma ≤ h ^ gamma :=
      Real.rpow_le_rpow hhp.le hle hgamma.le
    rw [hidp.1.symm]
    exact hpw.trans (le_add_of_nonneg_right (one_div_nonneg.mpr (by positivity)))
  · have hlt : h < hp := lt_of_not_ge hle
    have hdpow : h ^ (d : ℝ) ≤ hp ^ (d : ℝ) :=
      Real.rpow_le_rpow hh.le hlt.le (Nat.cast_nonneg d)
    have hbase : x * h ^ (d : ℝ) ≤ x * hp ^ (d : ℝ) :=
      mul_le_mul_of_nonneg_left hdpow hx.le
    have hbasepos : 0 < x * h ^ (d : ℝ) :=
      mul_pos hx (Real.rpow_pos_of_pos hh _)
    have hinv : 1 / (x * hp ^ (d : ℝ)) ≤ 1 / (x * h ^ (d : ℝ)) :=
      one_div_le_one_div_of_le hbasepos hbase
    rw [hidp.2.symm]
    exact hinv.trans (le_add_of_nonneg_left (Real.rpow_nonneg hh.le _))

-- @node: private_regression_max_bandwidth_bound
lemma private_regression_max_bandwidth_bound (x y gamma : ℝ) (d : ℕ)
    (hx : 0 < x) (hy : 0 < y) (hgamma : 0 < gamma) :
    let h0 := x ^ (-(1 / (2 * gamma + (d : ℝ))))
    let hp := y ^ (-(1 / (gamma + (d : ℝ))))
    let H := max h0 hp
    let R := max (x ^ (-(gamma / (2 * gamma + (d : ℝ)))))
      (y ^ (-(gamma / (gamma + (d : ℝ)))))
    H ^ gamma = R ∧
      H ^ gamma + (x * H ^ (d : ℝ)) ^ (-(1 / 2 : ℝ))
          + 1 / (y * H ^ (d : ℝ)) ≤ 3 * R := by
  dsimp
  have hh0 : 0 < x ^ (-(1 / (2 * gamma + (d : ℝ)))) :=
    Real.rpow_pos_of_pos hx _
  have hhp : 0 < y ^ (-(1 / (gamma + (d : ℝ)))) :=
    Real.rpow_pos_of_pos hy _
  have hid0 := private_regression_sampling_bandwidth_identities x gamma d hx hgamma
  have hidp := private_regression_privacy_bandwidth_identities y gamma d hy hgamma
  have hHpow :
      (max (x ^ (-(1 / (2 * gamma + (d : ℝ)))))
        (y ^ (-(1 / (gamma + (d : ℝ)))))) ^ gamma =
      max (x ^ (-(gamma / (2 * gamma + (d : ℝ)))))
        (y ^ (-(gamma / (gamma + (d : ℝ))))) := by
    rcases le_total
        (x ^ (-(1 / (2 * gamma + (d : ℝ)))))
        (y ^ (-(1 / (gamma + (d : ℝ))))) with hle | hle
    · rw [max_eq_right hle, max_eq_right]
      · exact hidp.1
      · rw [← hid0.1, ← hidp.1]
        exact Real.rpow_le_rpow hh0.le hle hgamma.le
    · rw [max_eq_left hle, max_eq_left]
      · exact hid0.1
      · rw [← hid0.1, ← hidp.1]
        exact Real.rpow_le_rpow hhp.le hle hgamma.le
  constructor
  · exact hHpow
  · have hbase0 :
        x * (x ^ (-(1 / (2 * gamma + (d : ℝ))))) ^ (d : ℝ) ≤
          x * (max (x ^ (-(1 / (2 * gamma + (d : ℝ)))))
            (y ^ (-(1 / (gamma + (d : ℝ)))))) ^ (d : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hx.le
      exact Real.rpow_le_rpow hh0.le (le_max_left _ _) (Nat.cast_nonneg d)
    have hnoise :
        (x * (max (x ^ (-(1 / (2 * gamma + (d : ℝ)))))
          (y ^ (-(1 / (gamma + (d : ℝ)))))) ^ (d : ℝ)) ^ (-(1 / 2 : ℝ))
          ≤ x ^ (-(gamma / (2 * gamma + (d : ℝ)))) := by
      rw [← hid0.2]
      exact Real.rpow_le_rpow_of_nonpos
        (mul_pos hx (Real.rpow_pos_of_pos hh0 _)) hbase0 (by norm_num)
    have hbasep :
        y * (y ^ (-(1 / (gamma + (d : ℝ))))) ^ (d : ℝ) ≤
          y * (max (x ^ (-(1 / (2 * gamma + (d : ℝ)))))
            (y ^ (-(1 / (gamma + (d : ℝ)))))) ^ (d : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hy.le
      exact Real.rpow_le_rpow hhp.le (le_max_right _ _) (Nat.cast_nonneg d)
    have hpriv :
        1 / (y * (max (x ^ (-(1 / (2 * gamma + (d : ℝ)))))
          (y ^ (-(1 / (gamma + (d : ℝ)))))) ^ (d : ℝ))
          ≤ y ^ (-(gamma / (gamma + (d : ℝ)))) := by
      rw [← hidp.2]
      exact one_div_le_one_div_of_le
        (mul_pos hy (Real.rpow_pos_of_pos hhp _)) hbasep
    rw [hHpow]
    have ha := le_max_left
      (x ^ (-(gamma / (2 * gamma + (d : ℝ)))))
      (y ^ (-(gamma / (gamma + (d : ℝ)))))
    have hb := le_max_right
      (x ^ (-(gamma / (2 * gamma + (d : ℝ)))))
      (y ^ (-(gamma / (gamma + (d : ℝ)))))
    linarith

end CausalSmith.Stat.DpCateMinimax
