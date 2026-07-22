/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Asymptotics for the unbounded dispersion certificate
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers.DispersionEnvelope
import Mathlib.Analysis.SpecificLimits.Basic

set_option linter.style.longLine false

open Filter

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

-- @node: dispersionD_tendsto_atTop
/-- The number of core outcomes in the dispersion construction diverges as the construction index grows. -/
lemma dispersionD_tendsto_atTop : Tendsto dispersionD atTop atTop := by
  apply tendsto_atTop_mono (fun n => ?_) tendsto_id
  unfold dispersionD dispersionT
  calc
    n ≤ n + 1 := Nat.le_succ n
    _ = 1 * (n + 1) := by omega
    _ ≤ (n + 1) * (n + 1) := Nat.mul_le_mul_right (n + 1) (by omega)
    _ = (n + 1) ^ 2 := by ring

-- @node: dispersion_geometric_lower_bound
/-- Eventually, a geometric lower bound controls the ratio formed by the dispersion construction's homogeneous and comparison envelope terms. -/
lemma dispersion_geometric_lower_bound {ε : ℝ} (hε : EpsilonAdmissible ε) :
    ∀ᶠ n in atTop,
      (1 / 3 : ℝ) * ((2 * dispersionRho ε)⁻¹ ^ dispersionD n) ≤
        (dispersionRho ε)⁻¹ ^ dispersionD n /
          ((2 : ℝ) ^ (dispersionD n + 1) +
            2 * reciprocalBarrier (dispersionFillerRho ε)) := by
  have htwo : Tendsto (fun n : ℕ => (2 : ℝ) ^ dispersionD n) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
      dispersionD_tendsto_atTop
  have hC := htwo.eventually_ge_atTop (2 * reciprocalBarrier (dispersionFillerRho ε))
  filter_upwards [hC] with n hn
  have hr := dispersionRho_bounds hε
  have hr0 : 0 < dispersionRho ε := lt_trans hε.1 hr.1
  have hf := dispersionFillerRho_bounds hε
  have hf0 : 0 < dispersionFillerRho ε := lt_trans hε.1 hf.1
  have hf1 : dispersionFillerRho ε < 1 := lt_trans hf.2 (by norm_num)
  have hden : 0 < (2 : ℝ) ^ (dispersionD n + 1) +
      2 * reciprocalBarrier (dispersionFillerRho ε) := by
    exact add_pos (pow_pos (by norm_num) _)
      (mul_pos (by norm_num) (reciprocalBarrier_pos hf0 hf1))
  apply (le_div_iff₀ hden).2
  have hbase : (dispersionRho ε)⁻¹ = 2 * (2 * dispersionRho ε)⁻¹ := by
    field_simp
  rw [hbase, mul_pow, pow_succ]
  have hb0 : 0 ≤ (2 * dispersionRho ε)⁻¹ ^ dispersionD n := by positivity
  have hp2 : 0 < (2 : ℝ) ^ dispersionD n := by positivity
  nlinarith

-- @node: dispersionApproxRatio_tendsto_atTop
/-- The approximation ratio of the dispersion construction diverges to infinity as the construction index grows. -/
lemma dispersionApproxRatio_tendsto_atTop {ε : ℝ} (hε : EpsilonAdmissible ε) :
    Tendsto (fun n => approxRatio (dispersionExperiment n) ε (dispersionBudget n ε))
      atTop atTop := by
  have hr := dispersionRho_bounds hε
  have hbase : 1 < (2 * dispersionRho ε)⁻¹ := by
    rw [one_lt_inv₀] <;> nlinarith [hε.1, hr.1, hr.2]
  have hgeom : Tendsto
      (fun n => (1 / 3 : ℝ) * ((2 * dispersionRho ε)⁻¹ ^ dispersionD n))
      atTop atTop := by
    exact ((tendsto_pow_atTop_atTop_of_one_lt hbase).comp dispersionD_tendsto_atTop).const_mul_atTop
      (by norm_num)
  apply tendsto_atTop_mono' atTop ?_ hgeom
  filter_upwards [dispersion_geometric_lower_bound hε] with n hn
  exact hn.trans (dispersion_approxRatio_lower_bound n hε)

end CausalSmith.Experimentation.BipartiteMinimaxDesign
