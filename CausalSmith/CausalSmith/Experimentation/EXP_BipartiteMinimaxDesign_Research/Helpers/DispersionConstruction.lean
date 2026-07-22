/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The clique-and-fillers graph for the unbounded dispersion certificate
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Envelope

set_option linter.style.longLine false

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

-- @node: dispersionT
/-- The stage parameter, shifted so that every stage is nonempty. -/
def dispersionT (n : ℕ) : ℕ := n + 1

-- @node: dispersionD
/-- The size `d=t²` of the growing clique. -/
def dispersionD (n : ℕ) : ℕ := dispersionT n ^ 2

-- @node: DispersionIntervention
/-- Clique interventions together with `2d` filler interventions. -/
abbrev DispersionIntervention (n : ℕ) := Fin (dispersionD n) ⊕ Fin (2 * dispersionD n)

-- @node: DispersionOutcome
/-- `d` clique outcomes and `t` copies for each filler intervention. -/
abbrev DispersionOutcome (n : ℕ) :=
  Fin (dispersionD n) ⊕ (Fin (2 * dispersionD n) × Fin (dispersionT n))

-- @node: dispersionCore
/-- The clique intervention block as a finset in the full intervention type. -/
def dispersionCore (n : ℕ) : Finset (DispersionIntervention n) :=
  Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩

-- @node: mem_dispersionCore_inl
@[simp] lemma mem_dispersionCore_inl (n : ℕ) (a : Fin (dispersionD n)) :
    Sum.inl a ∈ dispersionCore n := by
  simp [dispersionCore]

-- @node: mem_dispersionCore_inr
@[simp] lemma mem_dispersionCore_inr (n : ℕ) (f : Fin (2 * dispersionD n)) :
    Sum.inr f ∉ dispersionCore n := by
  simp [dispersionCore]

-- @node: dispersionCore_card
@[simp] lemma dispersionCore_card (n : ℕ) :
    (dispersionCore n).card = dispersionD n := by
  simp [dispersionCore]

-- @node: dispersionExperiment
/-- The graph whose clique outcomes see every clique intervention and whose filler
outcomes see their associated filler intervention only. -/
noncomputable def dispersionExperiment (n : ℕ) :
    BipartiteExperiment (DispersionIntervention n) (DispersionOutcome n) := by
  classical
  exact {
    N := fun i => match i with
      | Sum.inl _ => dispersionCore n
      | Sum.inr fr => {Sum.inr fr.1}
    Yfun := fun _ _ => 0
  }

-- @node: dispersionExperiment_N_core
lemma dispersionExperiment_N_core (n : ℕ) (i : Fin (dispersionD n)) :
    (dispersionExperiment n).N (Sum.inl i) =
      dispersionCore n := by
  rfl

-- @node: dispersionExperiment_N_filler
/-- Every filler outcome is connected to precisely its designated filler intervention. -/
lemma dispersionExperiment_N_filler (n : ℕ)
    (f : Fin (2 * dispersionD n)) (r : Fin (dispersionT n)) :
    (dispersionExperiment n).N (Sum.inr (f, r)) = {Sum.inr f} := by
  rfl

-- @node: dispersionExperiment_sdeg_core
/-- Every core outcome in the dispersion construction has the stated squared core-degree value. -/
lemma dispersionExperiment_sdeg_core (n : ℕ) (a : Fin (dispersionD n)) :
    (dispersionExperiment n).sdeg (Sum.inl a) = dispersionD n := by
  unfold BipartiteExperiment.sdeg BipartiteExperiment.M
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_sum_type]
  simp [dispersionExperiment, dispersionCore]

-- @node: dispersionExperiment_sdeg_filler
/-- Every filler outcome in the dispersion construction has squared degree one. -/
lemma dispersionExperiment_sdeg_filler (n : ℕ) (f : Fin (2 * dispersionD n)) :
    (dispersionExperiment n).sdeg (Sum.inr f) = dispersionT n := by
  unfold BipartiteExperiment.sdeg BipartiteExperiment.M
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  simp [dispersionExperiment, dispersionCore]

-- @node: dispersionExperiment_shared_core
/-- Any two core outcomes share exactly the full core intervention set. -/
lemma dispersionExperiment_shared_core (n : ℕ)
    (i j : Fin (dispersionD n)) :
    (dispersionExperiment n).shared (Sum.inl i) (Sum.inl j) =
      dispersionCore n := by
  simp [BipartiteExperiment.shared, dispersionExperiment, dispersionCore]

-- @node: dispersionExperiment_shared_filler
/-- Two filler outcomes share their designated intervention exactly when they have the same filler label. -/
lemma dispersionExperiment_shared_filler (n : ℕ)
    (f g : Fin (2 * dispersionD n)) (r s : Fin (dispersionT n)) :
    (dispersionExperiment n).shared (Sum.inr (f, r)) (Sum.inr (g, s)) =
      if f = g then {Sum.inr f} else ∅ := by
  classical
  split_ifs with h
  · subst g
    simp [BipartiteExperiment.shared, dispersionExperiment]
  · simp [BipartiteExperiment.shared, dispersionExperiment, h]

-- @node: dispersionExperiment_shared_core_filler
/-- A core outcome and a filler outcome share no interventions. -/
lemma dispersionExperiment_shared_core_filler (n : ℕ)
    (i : Fin (dispersionD n)) (f : Fin (2 * dispersionD n)) (r : Fin (dispersionT n)) :
    (dispersionExperiment n).shared (Sum.inl i) (Sum.inr (f, r)) = ∅ := by
  simp [BipartiteExperiment.shared, dispersionExperiment, dispersionCore]

-- @node: dispersionExperiment_shared_filler_core
/-- A filler outcome and a core outcome share no interventions. -/
lemma dispersionExperiment_shared_filler_core (n : ℕ)
    (f : Fin (2 * dispersionD n)) (r : Fin (dispersionT n)) (i : Fin (dispersionD n)) :
    (dispersionExperiment n).shared (Sum.inr (f, r)) (Sum.inl i) = ∅ := by
  simp [BipartiteExperiment.shared, dispersionExperiment, dispersionCore]

-- @node: dispersionExperiment_hWeight_core
/-- Each core intervention has the stated common exposure weight in the dispersion construction. -/
lemma dispersionExperiment_hWeight_core (n : ℕ) (a : Fin (dispersionD n)) :
    (dispersionExperiment n).hWeight (Sum.inl a) =
      (Fintype.card (DispersionOutcome n) : ℝ)⁻¹ * dispersionD n := by
  unfold BipartiteExperiment.hWeight
  congr 1
  have hterm (i j : DispersionOutcome n) :
      (if Sum.inl a ∈ (dispersionExperiment n).shared i j then
        (((dispersionExperiment n).shared i j).card : ℝ)⁻¹ else 0) =
        match i, j with
        | Sum.inl _, Sum.inl _ => (dispersionD n : ℝ)⁻¹
        | _, _ => 0 := by
    rcases i with i | ⟨f, r⟩ <;> rcases j with j | ⟨g, s⟩
    · simp [dispersionExperiment_shared_core]
    · simp [dispersionExperiment_shared_core_filler]
    · simp [dispersionExperiment_shared_filler_core]
    · by_cases hfg : f = g
      · subst g
        simp [dispersionExperiment_shared_filler]
      · simp [dispersionExperiment_shared_filler, hfg]
  simp_rw [hterm]
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Finset.sum_const_zero, add_zero]
  have hdN : 0 < dispersionD n := by simp [dispersionD, dispersionT]
  have hd : (dispersionD n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdN)
  simp [hd]

-- @node: dispersionExperiment_hWeight_filler
/-- Each filler intervention has the stated exposure weight in the dispersion construction. -/
lemma dispersionExperiment_hWeight_filler (n : ℕ) (f : Fin (2 * dispersionD n)) :
    (dispersionExperiment n).hWeight (Sum.inr f) =
      (Fintype.card (DispersionOutcome n) : ℝ)⁻¹ * dispersionD n := by
  unfold BipartiteExperiment.hWeight
  congr 1
  have hterm (i j : DispersionOutcome n) :
      (if Sum.inr f ∈ (dispersionExperiment n).shared i j then
        (((dispersionExperiment n).shared i j).card : ℝ)⁻¹ else 0) =
        match i, j with
        | Sum.inr (g, _), Sum.inr (h, _) => if f = g ∧ g = h then 1 else 0
        | _, _ => 0 := by
    rcases i with i | ⟨g, r⟩ <;> rcases j with j | ⟨h, s⟩
    · simp [dispersionExperiment_shared_core]
    · simp [dispersionExperiment_shared_core_filler]
    · simp [dispersionExperiment_shared_filler_core]
    · by_cases hgh : g = h
      · subst h
        simp [dispersionExperiment_shared_filler]
      · simp [dispersionExperiment_shared_filler, hgh]
  simp_rw [hterm]
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Finset.sum_const_zero, add_zero, zero_add]
  calc
    (∑ x, ∑ x₁, ∑ x₂, ∑ x₃, if f = x ∧ x = x₂ then (1 : ℝ) else 0) =
        ∑ x, ∑ _x₁ : Fin (dispersionT n), ∑ x₂,
          (dispersionT n : ℝ) * (if f = x ∧ x = x₂ then 1 else 0) := by
      apply Fintype.sum_congr
      intro x
      apply Fintype.sum_congr
      intro x₁
      apply Fintype.sum_congr
      intro x₂
      simp
    _ = ∑ x, ∑ _x₁ : Fin (dispersionT n),
        if f = x then (dispersionT n : ℝ) else 0 := by
      apply Fintype.sum_congr
      intro x
      apply Fintype.sum_congr
      intro x₁
      by_cases hx : f = x
      · subst x
        simp
      · simp [hx]
    _ = (dispersionT n : ℝ) ^ 2 := by
      simp
      ring
    _ = (dispersionD n : ℝ) := by norm_num [dispersionD]

-- @node: dispersionD_pos
/-- The number of core outcomes in the dispersion construction is positive. -/
lemma dispersionD_pos (n : ℕ) : 0 < dispersionD n := by
  simp [dispersionD, dispersionT]

-- @node: dispersionExperiment_degree_energy
/-- The degree-energy of the dispersion experiment has the stated closed-form value. -/
lemma dispersionExperiment_degree_energy (n : ℕ) :
    ∑ k, ((dispersionExperiment n).sdeg k : ℝ) ^ 2 =
      (dispersionD n : ℝ) * (dispersionD n : ℝ) ^ 2 +
        (2 * dispersionD n : ℕ) * (dispersionT n : ℝ) ^ 2 := by
  rw [Fintype.sum_sum_type]
  simp [dispersionExperiment_sdeg_core, dispersionExperiment_sdeg_filler]

-- @node: dispersionExperiment_degree_energy_pos
/-- The degree-energy of the dispersion experiment is strictly positive. -/
lemma dispersionExperiment_degree_energy_pos (n : ℕ) :
    0 < ∑ k, ((dispersionExperiment n).sdeg k : ℝ) ^ 2 := by
  rw [dispersionExperiment_degree_energy]
  have hd : 0 < (dispersionD n : ℝ) := by exact_mod_cast dispersionD_pos n
  positivity

-- @node: dispersionExperiment_hWeight_eq
/-- All interventions in the dispersion experiment have the same exposure weight. -/
lemma dispersionExperiment_hWeight_eq (n : ℕ)
    (k l : DispersionIntervention n) :
    (dispersionExperiment n).hWeight k = (dispersionExperiment n).hWeight l := by
  rcases k with k | k <;> rcases l with l | l
  all_goals simp only [dispersionExperiment_hWeight_core,
    dispersionExperiment_hWeight_filler]

-- @node: dispersionExperiment_hWeight_pos
/-- Every intervention has strictly positive exposure weight in the dispersion experiment. -/
lemma dispersionExperiment_hWeight_pos (n : ℕ) (k : DispersionIntervention n) :
    0 < (dispersionExperiment n).hWeight k := by
  rcases k with k | k <;>
    simp only [dispersionExperiment_hWeight_core, dispersionExperiment_hWeight_filler]
  all_goals
    have hO : Nonempty (DispersionOutcome n) :=
      ⟨Sum.inl ⟨0, dispersionD_pos n⟩⟩
    exact mul_pos (inv_pos.mpr (Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr hO)))
      (Nat.cast_pos.mpr (dispersionD_pos n))

-- @node: dispersionExperiment_boundedOutcomeDegree
/-- The dispersion experiment satisfies the stated bounded-outcome-degree condition. -/
lemma dispersionExperiment_boundedOutcomeDegree (n : ℕ) :
    BoundedOutcomeDegree (dispersionExperiment n) (dispersionD n : ℝ) := by
  constructor
  · exact_mod_cast dispersionD_pos n
  · intro i
    cases i with
    | inl i => simp [dispersionExperiment, dispersionCore]
    | inr fr =>
      simp [dispersionExperiment]
      exact_mod_cast dispersionD_pos n

end CausalSmith.Experimentation.BipartiteMinimaxDesign
