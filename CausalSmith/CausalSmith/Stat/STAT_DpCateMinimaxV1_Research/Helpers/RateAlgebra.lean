/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Central-DP CATE minimax: private-regression calibration algebra

Stage-2 scaffold. The pure real rate algebra collapsing the private-regression
calibration `r_n^{regDP}` (`lem:private_regression_calibration_algebra`) by the
bandwidth split at `h₀ = n^{-1/(2γ+d)}`, `h_p = (n ε_n)^{-1/(γ+d)}`.
-/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Basic
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.RegressionCalibrationBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace CausalSmith.Stat.DpCateMinimax


-- @node: lem:private-regression-calibration-algebra
/-- **Private-regression calibration algebra (crux).** The frozen calibration is
order-equivalent to the two-branch rate:
`r_n^{regDP} ≍ n^{-γ/(2γ+d)} ∨ (n ε_n)^{-γ/(γ+d)}`, with comparison constants
`c, C` depending ONLY on the fixed regularity parameters `r₀, γ, d` — hence
quantified OUTERMOST, before the budget sequences `ε_n, δ_n` (not after, which would
let them depend on the entire privacy sequences). -/
lemma private_regression_calibration_algebra {d : ℕ} (r0 gamma : ℝ)
    (hgamma : 0 < gamma) (hr0 : 0 < r0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (eps del : ℕ → ℝ), PrivacyBudget eps del →
      ∀ᶠ n : ℕ in Filter.atTop,
        c * max ((n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ)))))
              (((n : ℝ) * eps n) ^ (-(gamma / (gamma + (d : ℝ)))))
            ≤ privateRegressionCalibration n r0 gamma d (eps n)
          ∧ privateRegressionCalibration n r0 gamma d (eps n)
            ≤ C * max ((n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ)))))
                (((n : ℝ) * eps n) ^ (-(gamma / (gamma + (d : ℝ))))) := by
  let rd := r0 ^ (d : ℝ)
  let rg := r0 ^ gamma
  let K := rg + rd ^ (-(1 / 2 : ℝ)) + 1 / rd
  let C := 3 + K / rg
  have hrd : 0 < rd := Real.rpow_pos_of_pos hr0 _
  have hrg : 0 < rg := Real.rpow_pos_of_pos hr0 _
  have hK : 0 < K := by dsimp [K]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨1, C, by norm_num, hC, ?_⟩
  intro eps del hbudget
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hx : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hbudgetn := hbudget n hn
  have hyone : 1 ≤ (n : ℝ) * eps n := by
    calc
      1 = (n : ℝ) * (n : ℝ)⁻¹ := (mul_inv_cancel₀ hx.ne').symm
      _ ≤ (n : ℝ) * eps n := mul_le_mul_of_nonneg_left hbudgetn.1 hx.le
  have hy : 0 < (n : ℝ) * eps n := lt_of_lt_of_le zero_lt_one hyone
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  let hw0 : {h : ℝ // 0 < h ∧ h ≤ r0} := ⟨r0, hr0, le_rfl⟩
  letI : Nonempty {h : ℝ // 0 < h ∧ h ≤ r0} := ⟨hw0⟩
  let R := max ((n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ)))))
    (((n : ℝ) * eps n) ^ (-(gamma / (gamma + (d : ℝ)))))
  have hR : 0 ≤ R := (Real.rpow_nonneg hx.le _).trans (le_max_left _ _)
  have hlower : R ≤ privateRegressionCalibration n r0 gamma d (eps n) := by
    rw [privateRegressionCalibration]
    refine le_ciInf fun h => ?_
    have hsamp := private_regression_sampling_objective_lower
      (n : ℝ) h.1 gamma d hx h.2.1 hgamma
    have hpriv := private_regression_privacy_objective_lower
      ((n : ℝ) * eps n) h.1 gamma d hy h.2.1 hgamma
    apply max_le
    · dsimp
      have hpowpos : 0 < h.1 ^ (d : ℝ) := Real.rpow_pos_of_pos h.2.1 _
      have hlast : 0 ≤ 1 / ((n : ℝ) * eps n * h.1 ^ (d : ℝ)) :=
        one_div_nonneg.mpr (mul_nonneg hy.le hpowpos.le)
      linarith
    · dsimp
      have hmiddle : 0 ≤ ((n : ℝ) * h.1 ^ (d : ℝ)) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_nonneg (mul_nonneg hx.le (Real.rpow_nonneg h.2.1.le _)) _
      linarith
  constructor
  · simpa [R] using hlower
  · let h0 := (n : ℝ) ^ (-(1 / (2 * gamma + (d : ℝ))))
    let hp := ((n : ℝ) * eps n) ^ (-(1 / (gamma + (d : ℝ))))
    let H := max h0 hp
    have hh0 : 0 < h0 := Real.rpow_pos_of_pos hx _
    have hhp : 0 < hp := Real.rpow_pos_of_pos hy _
    have hH : 0 < H := lt_of_lt_of_le hh0 (le_max_left _ _)
    have hmax := private_regression_max_bandwidth_bound
      (n : ℝ) ((n : ℝ) * eps n) gamma d hx hy hgamma
    have hHpow : H ^ gamma = R := by simpa [h0, hp, H, R] using hmax.1
    have hbdd : BddBelow (Set.range fun h : {h : ℝ // 0 < h ∧ h ≤ r0} =>
        h.1 ^ gamma + ((n : ℝ) * h.1 ^ (d : ℝ)) ^ (-(1 / 2 : ℝ))
          + 1 / ((n : ℝ) * eps n * h.1 ^ (d : ℝ))) := by
      refine ⟨0, ?_⟩
      rintro z ⟨h, rfl⟩
      have hpowpos : 0 < h.1 ^ (d : ℝ) := Real.rpow_pos_of_pos h.2.1 _
      have hsnonneg :
          0 ≤ ((n : ℝ) * h.1 ^ (d : ℝ)) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_nonneg (mul_nonneg hx.le hpowpos.le) _
      have hpnonneg : 0 ≤ 1 / ((n : ℝ) * eps n * h.1 ^ (d : ℝ)) :=
        one_div_nonneg.mpr (mul_nonneg hy.le hpowpos.le)
      exact add_nonneg (add_nonneg (Real.rpow_nonneg h.2.1.le _) hsnonneg) hpnonneg
    by_cases hHr0 : H ≤ r0
    · let hw : {h : ℝ // 0 < h ∧ h ≤ r0} := ⟨H, hH, hHr0⟩
      rw [privateRegressionCalibration]
      calc
        (⨅ h : {h : ℝ // 0 < h ∧ h ≤ r0},
            h.1 ^ gamma + ((n : ℝ) * h.1 ^ (d : ℝ)) ^ (-(1 / 2 : ℝ))
              + 1 / ((n : ℝ) * eps n * h.1 ^ (d : ℝ)))
            ≤ hw.1 ^ gamma + ((n : ℝ) * hw.1 ^ (d : ℝ)) ^ (-(1 / 2 : ℝ))
              + 1 / ((n : ℝ) * eps n * hw.1 ^ (d : ℝ)) := ciInf_le hbdd hw
        _ ≤ 3 * R := by
          simpa [hw, h0, hp, H, R, mul_assoc] using hmax.2
        _ ≤ C * R := by
          exact mul_le_mul_of_nonneg_right
            (by dsimp [C]; linarith [div_nonneg hK.le hrg.le]) hR
    · have hrH : r0 ≤ H := le_of_lt (lt_of_not_ge hHr0)
      let hw : {h : ℝ // 0 < h ∧ h ≤ r0} := ⟨r0, hr0, le_rfl⟩
      have hrd_le_x : rd ≤ (n : ℝ) * rd := by
        calc
          rd = 1 * rd := by ring
          _ ≤ (n : ℝ) * rd := mul_le_mul_of_nonneg_right hnreal hrd.le
      have hsamp :
          ((n : ℝ) * r0 ^ (d : ℝ)) ^ (-(1 / 2 : ℝ)) ≤ rd ^ (-(1 / 2 : ℝ)) := by
        dsimp [rd] at hrd_le_x ⊢
        exact Real.rpow_le_rpow_of_nonpos hrd hrd_le_x (by norm_num)
      have hrd_le_y : rd ≤ ((n : ℝ) * eps n) * rd := by
        calc
          rd = 1 * rd := by ring
          _ ≤ ((n : ℝ) * eps n) * rd := mul_le_mul_of_nonneg_right hyone hrd.le
      have hpriv :
          1 / ((n : ℝ) * eps n * r0 ^ (d : ℝ)) ≤ 1 / rd := by
        dsimp [rd] at hrd_le_y ⊢
        exact one_div_le_one_div_of_le hrd hrd_le_y
      have hobjK :
          r0 ^ gamma + ((n : ℝ) * r0 ^ (d : ℝ)) ^ (-(1 / 2 : ℝ))
              + 1 / ((n : ℝ) * eps n * r0 ^ (d : ℝ)) ≤ K := by
        dsimp [K, rg, rd]
        linarith
      have hrgR : rg ≤ R := by
        rw [← hHpow]
        dsimp [rg]
        exact Real.rpow_le_rpow hr0.le hrH hgamma.le
      have hKfactor : K = (K / rg) * rg := by field_simp
      have hKR : K ≤ (K / rg) * R := by
        calc
          K = (K / rg) * rg := hKfactor
          _ ≤ (K / rg) * R :=
            mul_le_mul_of_nonneg_left hrgR (div_nonneg hK.le hrg.le)
      rw [privateRegressionCalibration]
      calc
        (⨅ h : {h : ℝ // 0 < h ∧ h ≤ r0},
            h.1 ^ gamma + ((n : ℝ) * h.1 ^ (d : ℝ)) ^ (-(1 / 2 : ℝ))
              + 1 / ((n : ℝ) * eps n * h.1 ^ (d : ℝ)))
            ≤ hw.1 ^ gamma + ((n : ℝ) * hw.1 ^ (d : ℝ)) ^ (-(1 / 2 : ℝ))
              + 1 / ((n : ℝ) * eps n * hw.1 ^ (d : ℝ)) := ciInf_le hbdd hw
        _ ≤ K := by simpa [hw] using hobjK
        _ ≤ (K / rg) * R := hKR
        _ ≤ C * R := by
          apply mul_le_mul_of_nonneg_right _ hR
          dsimp [C]
          linarith

end CausalSmith.Stat.DpCateMinimax
