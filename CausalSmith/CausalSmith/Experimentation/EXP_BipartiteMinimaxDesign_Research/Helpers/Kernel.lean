/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Exposure-kernel identities for the bipartite minimax design

Exact Bernoulli moment identities for the centered all-treated/all-control
exposure ratios, assembled into the pairwise linearization kernel.
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers.Moments
import Causalean.Experimentation.DesignBased.RatioLinearization

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedSimpArgs false

open scoped BigOperators
open Finset
open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.DesignBased.FiniteDesign
open Causalean.Experimentation.UnknownInterference

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

variable {I O Ω : Type*} [Fintype I] [Fintype O] [Fintype Ω] [DecidableEq I]

-- @node: prod_union_div_prod_prod_eq_prod_inter_inv
/-- When no relevant factor is zero, the product over a union divided by the two setwise products equals the product of inverse factors over the overlap. -/
lemma prod_union_div_prod_prod_eq_prod_inter_inv (S T : Finset I) (f : I → ℝ)
    (hne : ∀ k ∈ S ∪ T, f k ≠ 0) :
    (∏ k ∈ S ∪ T, f k) / ((∏ k ∈ S, f k) * (∏ k ∈ T, f k))
      = ∏ k ∈ S ∩ T, (f k)⁻¹ := by
  classical
  have hU_ne : (∏ k ∈ S ∪ T, f k) ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  have hA_ne : (∏ k ∈ S ∩ T, f k) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact hne k (Finset.mem_union_left T (Finset.mem_of_mem_inter_left hk))
  have hden :
      (∏ k ∈ S, f k) * (∏ k ∈ T, f k)
        = (∏ k ∈ S ∪ T, f k) * (∏ k ∈ S ∩ T, f k) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Finset.prod_union_inter (s₁ := S) (s₂ := T) (f := f)).symm
  rw [hden, Finset.prod_inv_distrib]
  field_simp [hU_ne, hA_ne]

-- `E_centered_ratio_mul` and `E_lin_expand` promoted to
-- `Causalean.Experimentation.DesignBased.RatioLinearization` (namespace `FiniteDesign`, opened
-- above); the moment lemmas below now call the Causalean versions.

-- @node: centered_treat_treat_moment
/-- Under independent Bernoulli assignment, the covariance of two centered treated-exposure ratios equals their treated-overlap kernel. -/
lemma centered_treat_treat_moment
    (E : BipartiteExperiment I O) (p : I → ℝ) (hp0 : ∀ k, 0 ≤ p k)
    (hp1 : ∀ k, p k ≤ 1) (hpos : ∀ k, 0 < p k) (i j : O) :
    (bernoulliDesign p hp0 hp1).E
        (fun z => (E.expT z i / E.piT p i - 1) *
          (E.expT z j / E.piT p j - 1))
      = E.r1 p i j := by
  classical
  have hpi_i_pos : 0 < E.piT p i := by
    unfold BipartiteExperiment.piT
    exact Finset.prod_pos (fun k _ => hpos k)
  have hpi_j_pos : 0 < E.piT p j := by
    unfold BipartiteExperiment.piT
    exact Finset.prod_pos (fun k _ => hpos k)
  have hEX : (bernoulliDesign p hp0 hp1).E (fun z => E.expT z i) = E.piT p i := by
    unfold BipartiteExperiment.expT BipartiteExperiment.piT
    exact bernoulli_E_treat_prod p hp0 hp1 (E.N i)
  have hEY : (bernoulliDesign p hp0 hp1).E (fun z => E.expT z j) = E.piT p j := by
    unfold BipartiteExperiment.expT BipartiteExperiment.piT
    exact bernoulli_E_treat_prod p hp0 hp1 (E.N j)
  have hEXY : (bernoulliDesign p hp0 hp1).E (fun z => E.expT z i * E.expT z j)
      = ∏ k ∈ E.N i ∪ E.N j, p k := by
    unfold BipartiteExperiment.expT
    exact bernoulli_E_treat_mul_treat p hp0 hp1 (E.N i) (E.N j)
  rw [E_centered_ratio_mul (D := bernoulliDesign p hp0 hp1)
    (X := fun z => E.expT z i) (Y := fun z => E.expT z j)
    (a := E.piT p i) (b := E.piT p j) (c := ∏ k ∈ E.N i ∪ E.N j, p k)
    (ne_of_gt hpi_i_pos) (ne_of_gt hpi_j_pos) hEX hEY hEXY]
  unfold BipartiteExperiment.r1 BipartiteExperiment.piT BipartiteExperiment.shared
  by_cases hcard : 0 < #(E.N i ∩ E.N j)
  · simp [hcard]
    rw [prod_union_div_prod_prod_eq_prod_inter_inv]
    · rw [Finset.prod_inv_distrib]
    · intro k _
      exact ne_of_gt (hpos k)
  · have hdisj : Disjoint (E.N i) (E.N j) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hcard)
    have hratio :
        (∏ k ∈ E.N i ∪ E.N j, p k) /
            ((∏ k ∈ E.N i, p k) * (∏ k ∈ E.N j, p k)) = 1 := by
      have hden :
          (∏ k ∈ E.N i ∪ E.N j, p k) = (∏ k ∈ E.N i, p k) * (∏ k ∈ E.N j, p k) := by
        rw [Finset.prod_union hdisj]
      rw [hden]
      have hi_ne : (∏ k ∈ E.N i, p k) ≠ 0 := by
        exact ne_of_gt (Finset.prod_pos (fun k _ => hpos k))
      have hj_ne : (∏ k ∈ E.N j, p k) ≠ 0 := by
        exact ne_of_gt (Finset.prod_pos (fun k _ => hpos k))
      field_simp [hi_ne, hj_ne]
    simp [hcard, hratio]

-- @node: centered_ctrl_ctrl_moment
/-- Under independent Bernoulli assignment, the covariance of two centered control-exposure ratios equals their control-overlap kernel. -/
lemma centered_ctrl_ctrl_moment
    (E : BipartiteExperiment I O) (p : I → ℝ) (hp0 : ∀ k, 0 ≤ p k)
    (hp1 : ∀ k, p k ≤ 1) (hlt : ∀ k, p k < 1) (i j : O) :
    (bernoulliDesign p hp0 hp1).E
        (fun z => (E.expC z i / E.piC p i - 1) *
          (E.expC z j / E.piC p j - 1))
      = E.r0 p i j := by
  classical
  have hpi_i_pos : 0 < E.piC p i := by
    unfold BipartiteExperiment.piC
    exact Finset.prod_pos (fun k _ => sub_pos.mpr (hlt k))
  have hpi_j_pos : 0 < E.piC p j := by
    unfold BipartiteExperiment.piC
    exact Finset.prod_pos (fun k _ => sub_pos.mpr (hlt k))
  have hEX : (bernoulliDesign p hp0 hp1).E (fun z => E.expC z i) = E.piC p i := by
    unfold BipartiteExperiment.expC BipartiteExperiment.piC
    exact bernoulli_E_ctrl_prod p hp0 hp1 (E.N i)
  have hEY : (bernoulliDesign p hp0 hp1).E (fun z => E.expC z j) = E.piC p j := by
    unfold BipartiteExperiment.expC BipartiteExperiment.piC
    exact bernoulli_E_ctrl_prod p hp0 hp1 (E.N j)
  have hEXY : (bernoulliDesign p hp0 hp1).E (fun z => E.expC z i * E.expC z j)
      = ∏ k ∈ E.N i ∪ E.N j, (1 - p k) := by
    unfold BipartiteExperiment.expC
    exact bernoulli_E_ctrl_mul_ctrl p hp0 hp1 (E.N i) (E.N j)
  rw [E_centered_ratio_mul (D := bernoulliDesign p hp0 hp1)
    (X := fun z => E.expC z i) (Y := fun z => E.expC z j)
    (a := E.piC p i) (b := E.piC p j)
    (c := ∏ k ∈ E.N i ∪ E.N j, (1 - p k))
    (ne_of_gt hpi_i_pos) (ne_of_gt hpi_j_pos) hEX hEY hEXY]
  unfold BipartiteExperiment.r0 BipartiteExperiment.piC BipartiteExperiment.shared
  by_cases hcard : 0 < #(E.N i ∩ E.N j)
  · simp [hcard]
    rw [prod_union_div_prod_prod_eq_prod_inter_inv]
    · rw [Finset.prod_inv_distrib]
    · intro k _
      exact ne_of_gt (sub_pos.mpr (hlt k))
  · have hdisj : Disjoint (E.N i) (E.N j) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hcard)
    have hratio :
        (∏ k ∈ E.N i ∪ E.N j, (1 - p k)) /
            ((∏ k ∈ E.N i, (1 - p k)) * (∏ k ∈ E.N j, (1 - p k))) = 1 := by
      have hden :
          (∏ k ∈ E.N i ∪ E.N j, (1 - p k))
            = (∏ k ∈ E.N i, (1 - p k)) * (∏ k ∈ E.N j, (1 - p k)) := by
        rw [Finset.prod_union hdisj]
      rw [hden]
      have hi_ne : (∏ k ∈ E.N i, (1 - p k)) ≠ 0 := by
        exact ne_of_gt (Finset.prod_pos (fun k _ => sub_pos.mpr (hlt k)))
      have hj_ne : (∏ k ∈ E.N j, (1 - p k)) ≠ 0 := by
        exact ne_of_gt (Finset.prod_pos (fun k _ => sub_pos.mpr (hlt k)))
      field_simp [hi_ne, hj_ne]
    simp [hcard, hratio]

-- @node: centered_treat_ctrl_moment
/-- Under independent Bernoulli assignment, the mixed treated-control centered-ratio moment equals minus the mixed overlap kernel. -/
lemma centered_treat_ctrl_moment
    (E : BipartiteExperiment I O) (p : I → ℝ) (hp0 : ∀ k, 0 ≤ p k)
    (hp1 : ∀ k, p k ≤ 1) (hpos : ∀ k, 0 < p k) (hlt : ∀ k, p k < 1) (i j : O) :
    (bernoulliDesign p hp0 hp1).E
        (fun z => (E.expT z i / E.piT p i - 1) *
          (E.expC z j / E.piC p j - 1))
      = -E.r10 i j := by
  classical
  have hpiT_pos : 0 < E.piT p i := by
    unfold BipartiteExperiment.piT
    exact Finset.prod_pos (fun k _ => hpos k)
  have hpiC_pos : 0 < E.piC p j := by
    unfold BipartiteExperiment.piC
    exact Finset.prod_pos (fun k _ => sub_pos.mpr (hlt k))
  have hEX : (bernoulliDesign p hp0 hp1).E (fun z => E.expT z i) = E.piT p i := by
    unfold BipartiteExperiment.expT BipartiteExperiment.piT
    exact bernoulli_E_treat_prod p hp0 hp1 (E.N i)
  have hEY : (bernoulliDesign p hp0 hp1).E (fun z => E.expC z j) = E.piC p j := by
    unfold BipartiteExperiment.expC BipartiteExperiment.piC
    exact bernoulli_E_ctrl_prod p hp0 hp1 (E.N j)
  by_cases hcard : 0 < #(E.N i ∩ E.N j)
  · have hEXY : (bernoulliDesign p hp0 hp1).E (fun z => E.expT z i * E.expC z j) = 0 := by
      rw [(bernoulliDesign p hp0 hp1).E_congr]
      · exact (bernoulliDesign p hp0 hp1).E_const 0
      · intro z
        unfold BipartiteExperiment.expT BipartiteExperiment.expC
        exact treat_ctrl_prod_eq_zero_of_inter_nonempty hcard z
    rw [E_centered_ratio_mul (D := bernoulliDesign p hp0 hp1)
      (X := fun z => E.expT z i) (Y := fun z => E.expC z j)
      (a := E.piT p i) (b := E.piC p j) (c := 0)
      (ne_of_gt hpiT_pos) (ne_of_gt hpiC_pos) hEX hEY hEXY]
    unfold BipartiteExperiment.r10 BipartiteExperiment.shared
    simp [hcard]
  · have hdisj : Disjoint (E.N i) (E.N j) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hcard)
    have hEXY : (bernoulliDesign p hp0 hp1).E (fun z => E.expT z i * E.expC z j)
        = E.piT p i * E.piC p j := by
      unfold BipartiteExperiment.expT BipartiteExperiment.expC
        BipartiteExperiment.piT BipartiteExperiment.piC
      rw [(bernoulliDesign p hp0 hp1).E_congr]
      · unfold bernoulliDesign
        rw [FiniteDesign.E_prod_prod (fun i => coinDesign (p i) (hp0 i) (hp1 i))
          (fun k b => if k ∈ E.N i then (if b then (1 : ℝ) else 0)
            else if k ∈ E.N j then (if b then (0 : ℝ) else 1) else 1)]
        trans ∏ k : I, if k ∈ E.N i then p k else if k ∈ E.N j then (1 - p k) else 1
        · apply Finset.prod_congr rfl
          intro k _
          by_cases hkS : k ∈ E.N i <;> by_cases hkT : k ∈ E.N j <;>
            simp [coinDesign_E, hkS, hkT]
        · exact prod_ite_disjoint (E.N i) (E.N j) hdisj p (fun k => 1 - p k)
      · intro z
        exact treat_ctrl_prod_eq_mixed_of_disjoint hdisj z
    rw [E_centered_ratio_mul (D := bernoulliDesign p hp0 hp1)
      (X := fun z => E.expT z i) (Y := fun z => E.expC z j)
      (a := E.piT p i) (b := E.piC p j) (c := E.piT p i * E.piC p j)
      (ne_of_gt hpiT_pos) (ne_of_gt hpiC_pos) hEX hEY hEXY]
    unfold BipartiteExperiment.r10 BipartiteExperiment.shared
    have hratio : E.piT p i * E.piC p j / (E.piT p i * E.piC p j) = 1 := by
      field_simp [ne_of_gt hpiT_pos, ne_of_gt hpiC_pos]
    simp [hcard, hratio]

end CausalSmith.Experimentation.BipartiteMinimaxDesign
