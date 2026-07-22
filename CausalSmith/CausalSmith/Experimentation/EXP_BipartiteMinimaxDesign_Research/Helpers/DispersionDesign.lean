/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Designs used by the unbounded dispersion certificate
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers.DispersionOptimization
import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.TSurrogateCertificate

set_option linter.style.longLine false

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

-- @node: dispersionRho
/-- Interior homogeneous propensity used by the surrogate. -/
noncomputable def dispersionRho (ε : ℝ) : ℝ := (ε + 1 / 2) / 2

-- @node: dispersionFillerRho
/-- Filler propensity that compensates for moving clique coordinates to `1/2`. -/
noncomputable def dispersionFillerRho (ε : ℝ) : ℝ :=
  (3 * dispersionRho ε - 1 / 2) / 2

-- @node: dispersionBudget
/-- The homogeneous expected-treatment budget. -/
noncomputable def dispersionBudget (n : ℕ) (ε : ℝ) : ℝ :=
  (Fintype.card (DispersionIntervention n) : ℝ) * dispersionRho ε

-- @node: dispersionHomogeneousDesign
/-- The constant propensity vector selected by the additive surrogate. -/
noncomputable def dispersionHomogeneousDesign (n : ℕ) (ε : ℝ) :
    DispersionIntervention n → ℝ := fun _ => dispersionRho ε

-- @node: dispersionComparisonDesign
/-- The feasible comparison: fair coins on the clique and compensated fillers. -/
noncomputable def dispersionComparisonDesign (n : ℕ) (ε : ℝ) :
    DispersionIntervention n → ℝ
  | Sum.inl _ => 1 / 2
  | Sum.inr _ => dispersionFillerRho ε

-- @node: dispersionRho_bounds
lemma dispersionRho_bounds {ε : ℝ} (hε : EpsilonAdmissible ε) :
    ε < dispersionRho ε ∧ dispersionRho ε < 1 / 2 := by
  rcases hε with ⟨h0, h2⟩
  unfold dispersionRho
  constructor <;> linarith

-- @node: dispersionFillerRho_bounds
lemma dispersionFillerRho_bounds {ε : ℝ} (hε : EpsilonAdmissible ε) :
    ε < dispersionFillerRho ε ∧ dispersionFillerRho ε < 1 / 2 := by
  rcases hε with ⟨h0, h2⟩
  unfold dispersionFillerRho dispersionRho
  constructor <;> linarith

-- @node: dispersionBudget_admissible
/-- The dispersion construction's homogeneous expected-treatment budget satisfies the admissibility requirements for the stated propensity floor. -/
lemma dispersionBudget_admissible (n : ℕ) {ε : ℝ} (hε : EpsilonAdmissible ε) :
    BudgetAdmissible (I := DispersionIntervention n) ε (dispersionBudget n ε) := by
  have hr := dispersionRho_bounds hε
  unfold BudgetAdmissible dispersionBudget
  constructor
  · exact mul_le_mul_of_nonneg_left hr.1.le (Nat.cast_nonneg _)
  · have : dispersionRho ε ≤ 1 - ε := by
      rcases hε with ⟨h0, h2⟩
      linarith [hr.2]
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)

-- @node: dispersionHomogeneousDesign_feasible
/-- The constant-propensity dispersion design is feasible for its associated budget and propensity floor. -/
lemma dispersionHomogeneousDesign_feasible (n : ℕ) {ε : ℝ}
    (hε : EpsilonAdmissible ε) :
    FeasibleDesign ε (dispersionBudget n ε) (dispersionHomogeneousDesign n ε) := by
  have hr := dispersionRho_bounds hε
  constructor
  · intro k
    change 0 ≤ dispersionRho ε ∧ dispersionRho ε ≤ 1
    constructor <;> linarith [hε.1, hr.2]
  · exact hε
  · intro k
    change ε ≤ dispersionRho ε ∧ dispersionRho ε ≤ 1 - ε
    constructor
    · exact hr.1.le
    · linarith [hε.1, hr.2]
  · simp [BudgetBalance, dispersionBudget, dispersionHomogeneousDesign]

-- @node: dispersionComparisonDesign_feasible
/-- The clique-and-filler comparison design is feasible for the same dispersion budget and propensity floor. -/
lemma dispersionComparisonDesign_feasible (n : ℕ) {ε : ℝ}
    (hε : EpsilonAdmissible ε) :
    FeasibleDesign ε (dispersionBudget n ε) (dispersionComparisonDesign n ε) := by
  have hf := dispersionFillerRho_bounds hε
  have hhalf : ε < 1 / 2 := hε.2
  constructor
  · intro k
    cases k with
    | inl k => simp [dispersionComparisonDesign]; linarith
    | inr k => simp [dispersionComparisonDesign]; constructor <;> linarith [hε.1]
  · exact hε
  · intro k
    cases k with
    | inl k => simp [dispersionComparisonDesign]; constructor <;> linarith
    | inr k => simp [dispersionComparisonDesign]; constructor <;> linarith
  · unfold BudgetBalance dispersionBudget
    rw [Fintype.sum_sum_type]
    simp [dispersionComparisonDesign, dispersionFillerRho]
    ring

-- @node: dispersion_surrogateObjective_eq_weighted_sum
/-- In the dispersion construction, the surrogate objective is a constant weight times the sum of reciprocal barriers over interventions. -/
lemma dispersion_surrogateObjective_eq_weighted_sum (n : ℕ)
    (p : DispersionIntervention n → ℝ) :
    (dispersionExperiment n).surrogateObjective p =
      ((Fintype.card (DispersionOutcome n) : ℝ)⁻¹ * dispersionD n) *
        ∑ k, reciprocalBarrier (p k) := by
  unfold BipartiteExperiment.surrogateObjective reciprocalBarrier
  calc
    ∑ k, (dispersionExperiment n).hWeight k * ((p k)⁻¹ + (1 - p k)⁻¹) =
        ∑ k, ((Fintype.card (DispersionOutcome n) : ℝ)⁻¹ * dispersionD n) *
          ((p k)⁻¹ + (1 - p k)⁻¹) := by
      apply sum_congr rfl
      intro k _
      congr 1
      cases k with
      | inl k => exact dispersionExperiment_hWeight_core n k
      | inr k => exact dispersionExperiment_hWeight_filler n k
    _ = ((Fintype.card (DispersionOutcome n) : ℝ)⁻¹ * dispersionD n) *
        ∑ k, ((p k)⁻¹ + (1 - p k)⁻¹) := by
      rw [mul_sum]

-- @node: dispersion_surrogateDesign_eq_homogeneous
/-- The surrogate-optimal design for the dispersion construction is exactly the constant homogeneous-propensity design. -/
lemma dispersion_surrogateDesign_eq_homogeneous (n : ℕ) {ε : ℝ}
    (hε : EpsilonAdmissible ε) :
    surrogateDesign (dispersionExperiment n) ε (dispersionBudget n ε) =
      dispersionHomogeneousDesign n ε := by
  let E := dispersionExperiment n
  let B := dispersionBudget n ε
  let ps := surrogateDesign E ε B
  have hs := surrogateDesign_feasible_minimizes E ε B hε.1 hε.2
    (dispersionBudget_admissible n hε)
  have hh := dispersionHomogeneousDesign_feasible n hε
  have hmin := hs.2 (dispersionHomogeneousDesign n ε) hh
  rw [dispersion_surrogateObjective_eq_weighted_sum,
    dispersion_surrogateObjective_eq_weighted_sum] at hmin
  have hw : 0 < (Fintype.card (DispersionOutcome n) : ℝ)⁻¹ * dispersionD n := by
    have hO : Nonempty (DispersionOutcome n) :=
      ⟨Sum.inl ⟨0, dispersionD_pos n⟩⟩
    exact mul_pos (inv_pos.mpr (Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr hO)))
      (Nat.cast_pos.mpr (dispersionD_pos n))
  have hsumle : ∑ k, reciprocalBarrier (ps k) ≤
      (Fintype.card (DispersionIntervention n) : ℝ) *
        reciprocalBarrier (dispersionRho ε) := by
    apply (mul_le_mul_iff_of_pos_left hw).mp
    simpa [ps, E, B, dispersionHomogeneousDesign] using hmin
  have hp0 : ∀ k, 0 < ps k := fun k =>
    lt_of_lt_of_le hε.1 (hs.1.floor k).1
  have hp1 : ∀ k, ps k < 1 := fun k => by
    linarith [(hs.1.floor k).2, hε.1]
  have hr := dispersionRho_bounds hε
  have hmean : ∑ k, ps k =
      (Fintype.card (DispersionIntervention n) : ℝ) * dispersionRho ε := by
    exact hs.1.budget
  simpa [ps, E, B, dispersionHomogeneousDesign] using
    reciprocalBarrier_sum_unique_minimizer ps (dispersionRho ε) hp0 hp1
      (lt_trans hε.1 hr.1) (lt_trans hr.2 (by norm_num)) hmean hsumle

end CausalSmith.Experimentation.BipartiteMinimaxDesign
