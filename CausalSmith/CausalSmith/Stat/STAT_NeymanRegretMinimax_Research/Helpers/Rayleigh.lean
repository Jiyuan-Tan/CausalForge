/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Rayleigh quotient algebra for the Neyman local-information program

Pure finite-dimensional algebra used by `Helpers.ScoreProgram`.
-/

import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Basic

namespace CausalSmith.Stat.NeymanRegretMinimax

open MeasureTheory
open scoped BigOperators Topology

-- @node: diagonal_rayleigh_sSup
/-- Algebraic Rayleigh quotient for a two-dimensional diagonal positive quadratic
form.  This is the finite-dimensional calculation used by
`local_complexity_rayleigh` after `arm_score_program_solution` identifies the
local information form. -/
lemma diagonal_rayleigh_sSup (c a b α β : ℝ) (hc : 0 < c) (ha : 0 < a) (hb : 0 < b)
    (hlin : α ≠ 0 ∨ β ≠ 0) :
    sSup {v | ∃ x y : ℝ,
      0 < a * y ^ 2 + b * x ^ 2
        ∧ α * y + β * x ≠ 0
        ∧ v = c * ((α * y + β * x) ^ 2 / (a * y ^ 2 + b * x ^ 2))}
      = c * (α ^ 2 / a + β ^ 2 / b) := by
  let K : ℝ := α ^ 2 / a + β ^ 2 / b
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hb_ne : b ≠ 0 := ne_of_gt hb
  have hab_pos : 0 < a * b := mul_pos ha hb
  have hab_ne : a * b ≠ 0 := ne_of_gt hab_pos
  have hK_pos : 0 < K := by
    dsimp [K]
    cases hlin with
    | inl hα =>
        exact add_pos_of_pos_of_nonneg (div_pos (sq_pos_of_ne_zero hα) ha)
          (div_nonneg (sq_nonneg _) (le_of_lt hb))
    | inr hβ =>
        exact add_pos_of_nonneg_of_pos (div_nonneg (sq_nonneg _) (le_of_lt ha))
          (div_pos (sq_pos_of_ne_zero hβ) hb)
  have hupper :
      ∀ v ∈ {v | ∃ x y : ℝ,
        0 < a * y ^ 2 + b * x ^ 2
          ∧ α * y + β * x ≠ 0
          ∧ v = c * ((α * y + β * x) ^ 2 / (a * y ^ 2 + b * x ^ 2))}, v ≤ c * K := by
    intro v hv
    rcases hv with ⟨x, y, hqpos, _hlinxy, rfl⟩
    have hq_ne : a * y ^ 2 + b * x ^ 2 ≠ 0 := ne_of_gt hqpos
    have hineq :
        (α * y + β * x) ^ 2 ≤ K * (a * y ^ 2 + b * x ^ 2) := by
      have hnonneg :
          0 ≤ (b * α * x - a * β * y) ^ 2 / (a * b) := by
        exact div_nonneg (sq_nonneg _) (le_of_lt hab_pos)
      have hid :
          K * (a * y ^ 2 + b * x ^ 2) - (α * y + β * x) ^ 2
            = (b * α * x - a * β * y) ^ 2 / (a * b) := by
        dsimp [K]
        field_simp [ha_ne, hb_ne, hab_ne]
        ring
      nlinarith [hnonneg, hid]
    have hdiv := div_le_div_of_nonneg_right hineq (le_of_lt hqpos)
    have hcancel :
        K * (a * y ^ 2 + b * x ^ 2) / (a * y ^ 2 + b * x ^ 2) = K := by
      field_simp [hq_ne]
    exact mul_le_mul_of_nonneg_left (by simpa [hcancel] using hdiv) (le_of_lt hc)
  have hK_mem :
      c * K ∈ {v | ∃ x y : ℝ,
        0 < a * y ^ 2 + b * x ^ 2
          ∧ α * y + β * x ≠ 0
          ∧ v = c * ((α * y + β * x) ^ 2 / (a * y ^ 2 + b * x ^ 2))} := by
    have hq_eq : a * (α / a) ^ 2 + b * (β / b) ^ 2 = K := by
      dsimp [K]
      field_simp [ha_ne, hb_ne]
    have hl_eq : α * (α / a) + β * (β / b) = K := by
      dsimp [K]
      field_simp [ha_ne, hb_ne]
    refine ⟨β / b, α / a, ?_, ?_, ?_⟩
    · rwa [hq_eq]
    · intro hzero
      have : K = 0 := by
        rwa [hl_eq] at hzero
      exact (ne_of_gt hK_pos) this
    · rw [hl_eq, hq_eq]
      field_simp [ne_of_gt hK_pos]
  have hnonempty :
      {v | ∃ x y : ℝ,
        0 < a * y ^ 2 + b * x ^ 2
          ∧ α * y + β * x ≠ 0
          ∧ v = c * ((α * y + β * x) ^ 2 / (a * y ^ 2 + b * x ^ 2))}.Nonempty :=
    ⟨c * K, hK_mem⟩
  have hBdd :
      BddAbove {v | ∃ x y : ℝ,
        0 < a * y ^ 2 + b * x ^ 2
          ∧ α * y + β * x ≠ 0
          ∧ v = c * ((α * y + β * x) ^ 2 / (a * y ^ 2 + b * x ^ 2))} := by
    exact ⟨c * K, hupper⟩
  refine le_antisymm ?_ ?_
  · exact csSup_le hnonempty hupper
  · exact le_csSup hBdd hK_mem

end CausalSmith.Stat.NeymanRegretMinimax
