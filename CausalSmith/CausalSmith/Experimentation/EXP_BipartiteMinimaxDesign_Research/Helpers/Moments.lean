/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bernoulli exposure moment algebra for the bipartite minimax design

Finite-product moment identities for the all-treated/all-control exposure
indicators used by the heterogeneous Hajek linearization.
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Basic

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedSimpArgs false

open scoped BigOperators
open Finset
open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.UnknownInterference

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

variable {I O Ω : Type*} [Fintype I] [Fintype O] [Fintype Ω] [DecidableEq I]

-- @node: prod_ite_disjoint
/-- For disjoint intervention sets, the product that uses one factor on the first set and another on the second factors into the two separate products. -/
lemma prod_ite_disjoint (S T : Finset I) (hST : Disjoint S T) (a b : I → ℝ) :
    (∏ k : I, if k ∈ S then a k else if k ∈ T then b k else 1)
      = (∏ k ∈ S, a k) * (∏ k ∈ T, b k) := by
  classical
  rw [show (∏ k ∈ S, a k) = ∏ k : I, if k ∈ S then a k else 1 by
    simpa using (Finset.prod_ite_mem_eq (s := S) (f := a)).symm]
  rw [show (∏ k ∈ T, b k) = ∏ k : I, if k ∈ T then b k else 1 by
    simpa using (Finset.prod_ite_mem_eq (s := T) (f := b)).symm]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  by_cases hS : k ∈ S
  · have hT : k ∉ T := fun hT => Finset.disjoint_left.mp hST hS hT
    simp [hS, hT]
  · by_cases hT : k ∈ T <;> simp [hS, hT]

-- @node: treat_prod_mul_eq_union
/-- The product of two all-treated exposure indicators equals the all-treated indicator for the union of their intervention sets. -/
lemma treat_prod_mul_eq_union (S T : Finset I) (z : I → Bool) :
    (∏ k ∈ S, (if z k then (1 : ℝ) else 0)) *
        (∏ k ∈ T, (if z k then (1 : ℝ) else 0))
      = ∏ k ∈ S ∪ T, (if z k then (1 : ℝ) else 0) := by
  classical
  rw [show (∏ k ∈ S, (if z k then (1 : ℝ) else 0))
      = ∏ k : I, if k ∈ S then (if z k then (1 : ℝ) else 0) else 1 by
        simpa using (Finset.prod_ite_mem_eq (s := S)
          (f := fun k => if z k then (1 : ℝ) else 0)).symm]
  rw [show (∏ k ∈ T, (if z k then (1 : ℝ) else 0))
      = ∏ k : I, if k ∈ T then (if z k then (1 : ℝ) else 0) else 1 by
        simpa using (Finset.prod_ite_mem_eq (s := T)
          (f := fun k => if z k then (1 : ℝ) else 0)).symm]
  rw [← Finset.prod_mul_distrib]
  rw [show (∏ k : I, (if k ∈ S then (if z k then (1 : ℝ) else 0) else 1) *
        (if k ∈ T then (if z k then (1 : ℝ) else 0) else 1))
      = ∏ k : I, if k ∈ S ∪ T then (if z k then (1 : ℝ) else 0) else 1 by
        apply Finset.prod_congr rfl
        intro k _
        by_cases hS : k ∈ S <;> by_cases hT : k ∈ T <;>
          cases hz : z k <;> simp [hS, hT, hz]]
  simpa using (Finset.prod_ite_mem_eq (s := S ∪ T)
    (f := fun k => if z k then (1 : ℝ) else 0))

-- @node: ctrl_prod_mul_eq_union
/-- The product of two all-control exposure indicators equals the all-control indicator for the union of their intervention sets. -/
lemma ctrl_prod_mul_eq_union (S T : Finset I) (z : I → Bool) :
    (∏ k ∈ S, (if z k then (0 : ℝ) else 1)) *
        (∏ k ∈ T, (if z k then (0 : ℝ) else 1))
      = ∏ k ∈ S ∪ T, (if z k then (0 : ℝ) else 1) := by
  classical
  rw [show (∏ k ∈ S, (if z k then (0 : ℝ) else 1))
      = ∏ k : I, if k ∈ S then (if z k then (0 : ℝ) else 1) else 1 by
        simpa using (Finset.prod_ite_mem_eq (s := S)
          (f := fun k => if z k then (0 : ℝ) else 1)).symm]
  rw [show (∏ k ∈ T, (if z k then (0 : ℝ) else 1))
      = ∏ k : I, if k ∈ T then (if z k then (0 : ℝ) else 1) else 1 by
        simpa using (Finset.prod_ite_mem_eq (s := T)
          (f := fun k => if z k then (0 : ℝ) else 1)).symm]
  rw [← Finset.prod_mul_distrib]
  rw [show (∏ k : I, (if k ∈ S then (if z k then (0 : ℝ) else 1) else 1) *
        (if k ∈ T then (if z k then (0 : ℝ) else 1) else 1))
      = ∏ k : I, if k ∈ S ∪ T then (if z k then (0 : ℝ) else 1) else 1 by
        apply Finset.prod_congr rfl
        intro k _
        by_cases hS : k ∈ S <;> by_cases hT : k ∈ T <;>
          cases hz : z k <;> simp [hS, hT, hz]]
  simpa using (Finset.prod_ite_mem_eq (s := S ∪ T)
    (f := fun k => if z k then (0 : ℝ) else 1))

-- @node: treat_ctrl_prod_eq_zero_of_inter_nonempty
/-- If two intervention sets overlap, their all-treated and all-control exposure indicators cannot both equal one, so their product is zero. -/
lemma treat_ctrl_prod_eq_zero_of_inter_nonempty {S T : Finset I} (h : 0 < (S ∩ T).card)
    (z : I → Bool) :
    (∏ k ∈ S, (if z k then (1 : ℝ) else 0)) *
        (∏ k ∈ T, (if z k then (0 : ℝ) else 1)) = 0 := by
  classical
  rcases Finset.card_pos.mp h with ⟨k, hk⟩
  have hkS : k ∈ S := Finset.mem_of_mem_inter_left hk
  have hkT : k ∈ T := Finset.mem_of_mem_inter_right hk
  by_cases hz : z k
  · have hctrl : (∏ l ∈ T, (if z l then (0 : ℝ) else 1)) = 0 := by
      apply Finset.prod_eq_zero hkT
      simp [hz]
    simp [hctrl]
  · have htreat : (∏ l ∈ S, (if z l then (1 : ℝ) else 0)) = 0 := by
      apply Finset.prod_eq_zero hkS
      simp [hz]
    simp [htreat]

-- @node: treat_ctrl_prod_eq_mixed_of_disjoint
/-- For disjoint sets, the product of an all-treated indicator and an all-control indicator is the indicator for that mixed assignment pattern. -/
lemma treat_ctrl_prod_eq_mixed_of_disjoint {S T : Finset I} (hST : Disjoint S T)
    (z : I → Bool) :
    (∏ k ∈ S, (if z k then (1 : ℝ) else 0)) *
        (∏ k ∈ T, (if z k then (0 : ℝ) else 1))
      = ∏ k : I,
          if k ∈ S then (if z k then (1 : ℝ) else 0)
          else if k ∈ T then (if z k then (0 : ℝ) else 1) else 1 := by
  classical
  rw [show (∏ k ∈ S, (if z k then (1 : ℝ) else 0))
      = ∏ k : I, if k ∈ S then (if z k then (1 : ℝ) else 0) else 1 by
        simpa using (Finset.prod_ite_mem_eq (s := S)
          (f := fun k => if z k then (1 : ℝ) else 0)).symm]
  rw [show (∏ k ∈ T, (if z k then (0 : ℝ) else 1))
      = ∏ k : I, if k ∈ T then (if z k then (0 : ℝ) else 1) else 1 by
        simpa using (Finset.prod_ite_mem_eq (s := T)
          (f := fun k => if z k then (0 : ℝ) else 1)).symm]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  by_cases hS : k ∈ S
  · have hT : k ∉ T := fun hT => Finset.disjoint_left.mp hST hS hT
    cases hz : z k <;> simp [hS, hT, hz]
  · by_cases hT : k ∈ T <;> cases hz : z k <;> simp [hS, hT, hz]

-- @node: bernoulli_E_treat_prod
/-- Under independent Bernoulli assignment, the probability that all interventions in a set are treated is the product of their treatment probabilities. -/
lemma bernoulli_E_treat_prod (p : I → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    (S : Finset I) :
    (bernoulliDesign p hp0 hp1).E
        (fun z => ∏ k ∈ S, (if z k then (1 : ℝ) else 0))
      = ∏ k ∈ S, p k := by
  classical
  rw [show (fun z : I → Bool => ∏ k ∈ S, (if z k then (1 : ℝ) else 0))
      = (fun z => ∏ k : I,
          (fun (k : I) (b : Bool) =>
            if k ∈ S then (if b then (1 : ℝ) else 0) else 1) k (z k)) by
        funext z
        simpa using (Finset.prod_ite_mem_eq (s := S)
          (f := fun k => if z k then (1 : ℝ) else 0)).symm]
  unfold bernoulliDesign
  rw [FiniteDesign.E_prod_prod (fun i => coinDesign (p i) (hp0 i) (hp1 i))
    (fun k b => if k ∈ S then (if b then (1 : ℝ) else 0) else 1)]
  trans ∏ x : I, if x ∈ S then p x else 1
  · apply Finset.prod_congr rfl
    intro x _
    by_cases h : x ∈ S <;> simp [coinDesign_E, h]
  · simpa using (Finset.prod_ite_mem_eq (s := S) (f := p))

-- @node: bernoulli_E_ctrl_prod
/-- Under independent Bernoulli assignment, the probability that all interventions in a set are controlled is the product of their control probabilities. -/
lemma bernoulli_E_ctrl_prod (p : I → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    (S : Finset I) :
    (bernoulliDesign p hp0 hp1).E
        (fun z => ∏ k ∈ S, (if z k then (0 : ℝ) else 1))
      = ∏ k ∈ S, (1 - p k) := by
  classical
  rw [show (fun z : I → Bool => ∏ k ∈ S, (if z k then (0 : ℝ) else 1))
      = (fun z => ∏ k : I,
          (fun (k : I) (b : Bool) =>
            if k ∈ S then (if b then (0 : ℝ) else 1) else 1) k (z k)) by
        funext z
        simpa using (Finset.prod_ite_mem_eq (s := S)
          (f := fun k => if z k then (0 : ℝ) else 1)).symm]
  unfold bernoulliDesign
  rw [FiniteDesign.E_prod_prod (fun i => coinDesign (p i) (hp0 i) (hp1 i))
    (fun k b => if k ∈ S then (if b then (0 : ℝ) else 1) else 1)]
  trans ∏ x : I, if x ∈ S then (1 - p x) else 1
  · apply Finset.prod_congr rfl
    intro x _
    by_cases h : x ∈ S <;> simp [coinDesign_E, h]
  · simpa using (Finset.prod_ite_mem_eq (s := S) (f := fun k => 1 - p k))

-- @node: bernoulli_E_treat_mul_treat
/-- Under independent Bernoulli assignment, the expected product of two all-treated exposure indicators is the product of treatment probabilities over their union. -/
lemma bernoulli_E_treat_mul_treat (p : I → ℝ) (hp0 : ∀ k, 0 ≤ p k)
    (hp1 : ∀ k, p k ≤ 1) (S T : Finset I) :
    (bernoulliDesign p hp0 hp1).E
        (fun z => (∏ k ∈ S, (if z k then (1 : ℝ) else 0)) *
          (∏ k ∈ T, (if z k then (1 : ℝ) else 0)))
      = ∏ k ∈ S ∪ T, p k := by
  rw [(bernoulliDesign p hp0 hp1).E_congr
    (fun z => treat_prod_mul_eq_union S T z)]
  exact bernoulli_E_treat_prod p hp0 hp1 (S ∪ T)

-- @node: bernoulli_E_ctrl_mul_ctrl
/-- Under independent Bernoulli assignment, the expected product of two all-control exposure indicators is the product of control probabilities over their union. -/
lemma bernoulli_E_ctrl_mul_ctrl (p : I → ℝ) (hp0 : ∀ k, 0 ≤ p k)
    (hp1 : ∀ k, p k ≤ 1) (S T : Finset I) :
    (bernoulliDesign p hp0 hp1).E
        (fun z => (∏ k ∈ S, (if z k then (0 : ℝ) else 1)) *
          (∏ k ∈ T, (if z k then (0 : ℝ) else 1)))
      = ∏ k ∈ S ∪ T, (1 - p k) := by
  rw [(bernoulliDesign p hp0 hp1).E_congr
    (fun z => ctrl_prod_mul_eq_union S T z)]
  exact bernoulli_E_ctrl_prod p hp0 hp1 (S ∪ T)

/-- A one-unit Bernoulli assignment distribution is unchanged when its treatment probability and
the corresponding conditions that it lies between zero and one are replaced by equal ones. -/
add_decl_doc Causalean.Experimentation.UnknownInterference.coinDesign.congr_simp

end CausalSmith.Experimentation.BipartiteMinimaxDesign
