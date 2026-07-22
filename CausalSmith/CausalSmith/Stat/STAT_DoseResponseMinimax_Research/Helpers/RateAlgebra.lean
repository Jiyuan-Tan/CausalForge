/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dose-response minimax: published-rate algebra

Stage-2 scaffold. The pure real-power identities collapsing the published
benchmark `ρ_n` in the smooth-covariate (`s ≥ d/4`) and deficient (`0 < s < d/4`)
regimes. Every proof body is `sorry`.
-/

import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace CausalSmith.Stat.DoseResponseMinimax

-- @node: lem:rho-oracle-regime-algebra
/-- Smooth-covariate collapse: if `0 < α`, `0 < s`, and `d ≤ 4 s` (i.e. `s ≥ d/4`),
then `ρ_n = n^{-2α/(2α+1)}` for every `n ≥ 1`. -/
lemma rho_oracle_regime_algebra (n : ℕ) (alpha s : ℝ) (d : ℕ)
    (halpha : 0 < alpha) (hs : 0 < s) (hsd : (d : ℝ) ≤ 4 * s) (hn : 1 ≤ n) :
    publishedHoifRate n alpha s d = (n : ℝ) ^ (-(2 * alpha / (2 * alpha + 1))) := by
  by_cases hn1 : n = 1
  · subst n
    simp [publishedHoifRate]
  · have hnat : 1 < n := by omega
    have hbase : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hnat
    have hs4 : 0 < 4 * s := by positivity
    have hdfrac : (d : ℝ) / (4 * s) ≤ 1 := by
      rw [div_le_one hs4]
      simpa using hsd
    have hden_pos : 0 < 1 + (d : ℝ) / (4 * s) + 1 / alpha := by positivity
    have hden_le : 1 + (d : ℝ) / (4 * s) + 1 / alpha ≤ 2 + 1 / alpha := by
      linarith
    have hfrac :
        2 / (2 + 1 / alpha) ≤ 2 / (1 + (d : ℝ) / (4 * s) + 1 / alpha) := by
      exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hden_pos hden_le
    have hid : 2 / (2 + 1 / alpha) = 2 * alpha / (2 * alpha + 1) := by
      field_simp [halpha.ne']
    have hexp : 2 * alpha / (2 * alpha + 1)
        ≤ 2 / (1 + (d : ℝ) / (4 * s) + 1 / alpha) := by
      rwa [← hid]
    have hpow : (n : ℝ) ^ (-(2 / (1 + (d : ℝ) / (4 * s) + 1 / alpha)))
        ≤ (n : ℝ) ^ (-(2 * alpha / (2 * alpha + 1))) := by
      rw [Real.rpow_le_rpow_left_iff hbase]
      linarith
    rw [publishedHoifRate]
    exact max_eq_left hpow

-- @node: lem:rho-deficient-regime-algebra
/-- Deficient-covariate collapse: if `0 < α`, `0 < s`, and `4 s < d` (i.e.
`0 < s < d/4`), then `ρ_n = n^{-2/(1 + d/(4s) + 1/α)}` for every `n ≥ 1`, and the
deficient exponent is strictly smaller than the oracle exponent. -/
lemma rho_deficient_regime_algebra (n : ℕ) (alpha s : ℝ) (d : ℕ)
    (halpha : 0 < alpha) (hs : 0 < s) (hsd : 4 * s < (d : ℝ)) (hn : 1 ≤ n) :
    publishedHoifRate n alpha s d
        = (n : ℝ) ^ (-(2 / (1 + (d : ℝ) / (4 * s) + 1 / alpha)))
      ∧ 2 / (1 + (d : ℝ) / (4 * s) + 1 / alpha) < 2 * alpha / (2 * alpha + 1) := by
  have hs4 : 0 < 4 * s := by positivity
  have hone_lt : 1 < (d : ℝ) / (4 * s) := by
    rw [one_lt_div hs4]
    simpa using hsd
  have hden_pos : 0 < 2 + 1 / alpha := by positivity
  have hden_lt : 2 + 1 / alpha < 1 + (d : ℝ) / (4 * s) + 1 / alpha := by
    linarith
  have hfrac :
      2 / (1 + (d : ℝ) / (4 * s) + 1 / alpha) < 2 / (2 + 1 / alpha) := by
    exact div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 2) hden_pos hden_lt
  have hid : 2 / (2 + 1 / alpha) = 2 * alpha / (2 * alpha + 1) := by
    field_simp [halpha.ne']
  have hexp : 2 / (1 + (d : ℝ) / (4 * s) + 1 / alpha)
      < 2 * alpha / (2 * alpha + 1) := by
    rwa [hid] at hfrac
  constructor
  · by_cases hn1 : n = 1
    · subst n
      simp [publishedHoifRate]
    · have hnat : 1 < n := by omega
      have hbase : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hnat
      have hpow : (n : ℝ) ^ (-(2 * alpha / (2 * alpha + 1)))
          ≤ (n : ℝ) ^ (-(2 / (1 + (d : ℝ) / (4 * s) + 1 / alpha))) := by
        rw [Real.rpow_le_rpow_left_iff hbase]
        linarith
      rw [publishedHoifRate]
      exact max_eq_right hpow
  · exact hexp

end CausalSmith.Stat.DoseResponseMinimax
