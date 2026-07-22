/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Denominator-kernel asymptotic rate
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers.DenominatorMoment

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open scoped Topology
open Filter

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

variable {Ox : ℕ → Type*} [∀ n, Fintype (Ox n)]

-- @node: denominatorKernelBound_div_card_tendsto_zero
/-- If the number of outcomes diverges and the propensity floor stays eventually positive, the denominator-kernel bound divided by the number of outcomes converges to zero. -/
lemma denominatorKernelBound_div_card_tendsto_zero
    (ε : ℕ → ℝ) (dbar : ℝ)
    (hcardO : Tendsto (fun n => Fintype.card (Ox n)) atTop atTop)
    (hε : ∀ n, EpsilonAdmissible (ε n))
    (hεfloor : ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ᶠ n in atTop, ε0 ≤ ε n) :
    Tendsto (fun n => denominatorKernelBound (ε n) dbar / (Fintype.card (Ox n) : ℝ))
      atTop (𝓝 0) := by
  rcases hεfloor with ⟨ε0, hε0_pos, hε0_ev⟩
  let C : ℝ := denominatorKernelBound ε0 dbar
  have hcard_real : Tendsto (fun n => (Fintype.card (Ox n) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcardO
  have hinv : Tendsto (fun n => ((Fintype.card (Ox n) : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hcard_real
  have hupper :
      Tendsto (fun n => C * ((Fintype.card (Ox n) : ℝ)⁻¹)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hinv)
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards with n
    exact div_nonneg (denominatorKernelBound_nonneg (hε n).1) (by positivity)
  · filter_upwards [hε0_ev] with n hfloor
    have hkernel_le : denominatorKernelBound (ε n) dbar ≤ C := by
      dsimp [C]
      exact denominatorKernelBound_le_of_floor hε0_pos hfloor (hε n)
    calc
      denominatorKernelBound (ε n) dbar / (Fintype.card (Ox n) : ℝ)
          = denominatorKernelBound (ε n) dbar *
              ((Fintype.card (Ox n) : ℝ)⁻¹) := by ring
      _ ≤ C * ((Fintype.card (Ox n) : ℝ)⁻¹) := by
          exact mul_le_mul_of_nonneg_right hkernel_le (inv_nonneg.mpr (by positivity))

end CausalSmith.Experimentation.BipartiteMinimaxDesign
