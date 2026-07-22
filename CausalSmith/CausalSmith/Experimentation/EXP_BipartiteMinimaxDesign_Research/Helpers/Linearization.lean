/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Linearization moment identities for the bipartite minimax design
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers.Kernel

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

-- `E_centered_ratio` promoted to `Causalean.Experimentation.DesignBased.RatioLinearization`
-- (namespace `FiniteDesign`, opened above); `linScore_mean_zero` below calls the Causalean version.

-- @node: linScore_mean_zero
/-- Each outcome's Hájek linearization score has expectation zero under the heterogeneous independent Bernoulli design. -/
lemma linScore_mean_zero
    (E : BipartiteExperiment I O)
    (D : FiniteDesign (I → Bool)) (p : I → ℝ) (hp0 : ∀ k, 0 ≤ p k)
    (hp1 : ∀ k, p k ≤ 1) (hpos : ∀ k, 0 < p k) (hlt : ∀ k, p k < 1)
    (hBern : IndepHeteroBernoulli D p hp0 hp1) (i : O) :
    D.E (fun z => E.linScore p z i) = 0 := by
  rw [hBern]
  unfold BipartiteExperiment.linScore
  have hpiT_pos : 0 < E.piT p i := by
    unfold BipartiteExperiment.piT
    exact Finset.prod_pos (fun k _ => hpos k)
  have hpiC_pos : 0 < E.piC p i := by
    unfold BipartiteExperiment.piC
    exact Finset.prod_pos (fun k _ => sub_pos.mpr (hlt k))
  have hET : (bernoulliDesign p hp0 hp1).E (fun z => E.expT z i) = E.piT p i := by
    unfold BipartiteExperiment.expT BipartiteExperiment.piT
    exact bernoulli_E_treat_prod p hp0 hp1 (E.N i)
  have hEC : (bernoulliDesign p hp0 hp1).E (fun z => E.expC z i) = E.piC p i := by
    unfold BipartiteExperiment.expC BipartiteExperiment.piC
    exact bernoulli_E_ctrl_prod p hp0 hp1 (E.N i)
  have hA : (bernoulliDesign p hp0 hp1).E (fun z => E.expT z i / E.piT p i - 1) = 0 :=
    E_centered_ratio _ _ _ (ne_of_gt hpiT_pos) hET
  have hB : (bernoulliDesign p hp0 hp1).E (fun z => E.expC z i / E.piC p i - 1) = 0 :=
    E_centered_ratio _ _ _ (ne_of_gt hpiC_pos) hEC
  rw [(bernoulliDesign p hp0 hp1).E_sub]
  rw [(bernoulliDesign p hp0 hp1).E_mul_const, (bernoulliDesign p hp0 hp1).E_mul_const]
  rw [hA, hB]
  ring

-- @node: r10_comm
/-- The mixed overlap kernel is symmetric in the two outcomes. -/
lemma r10_comm (E : BipartiteExperiment I O) (i j : O) : E.r10 j i = E.r10 i j := by
  simp [BipartiteExperiment.r10, BipartiteExperiment.shared, Finset.inter_comm]

-- @node: cross_sum_symm_r10
/-- Summing the two symmetric mixed terms over all outcome pairs is equal to twice either one of them. -/
lemma cross_sum_symm_r10 (E : BipartiteExperiment I O) (a b : O → ℝ) :
    (∑ i : O, ∑ j : O, E.r10 i j * (a i * b j + b i * a j)) =
      ∑ i : O, ∑ j : O, 2 * E.r10 i j * a i * b j := by
  classical
  have hswap : (∑ i : O, ∑ j : O, E.r10 i j * (b i * a j)) =
      ∑ i : O, ∑ j : O, E.r10 i j * (a i * b j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [r10_comm E i j]
    ring
  calc
    (∑ i : O, ∑ j : O, E.r10 i j * (a i * b j + b i * a j))
        = (∑ i : O, ∑ j : O, E.r10 i j * (a i * b j)) +
            (∑ i : O, ∑ j : O, E.r10 i j * (b i * a j)) := by
          simp_rw [mul_add, Finset.sum_add_distrib]
    _ = (∑ i : O, ∑ j : O, E.r10 i j * (a i * b j)) +
            (∑ i : O, ∑ j : O, E.r10 i j * (a i * b j)) := by rw [hswap]
    _ = ∑ i : O, ∑ j : O, 2 * E.r10 i j * a i * b j := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring

-- @node: linScore_pair_moment
/-- The joint moment of two linearization scores equals the sum of their treated, control, and mixed overlap-kernel contributions. -/
lemma linScore_pair_moment
    (E : BipartiteExperiment I O)
    (D : FiniteDesign (I → Bool)) (p : I → ℝ) (hp0 : ∀ k, 0 ≤ p k)
    (hp1 : ∀ k, p k ≤ 1) (hpos : ∀ k, 0 < p k) (hlt : ∀ k, p k < 1)
    (hBern : IndepHeteroBernoulli D p hp0 hp1) (i j : O) :
    D.E (fun z => E.linScore p z i * E.linScore p z j)
        = E.r1 p i j * (E.Y1 i - E.mu1) * (E.Y1 j - E.mu1)
          + E.r0 p i j * (E.Y0 i - E.mu0) * (E.Y0 j - E.mu0)
          + E.r10 i j * ((E.Y1 i - E.mu1) * (E.Y0 j - E.mu0)
                          + (E.Y0 i - E.mu0) * (E.Y1 j - E.mu1)) := by
  classical
  rw [hBern]
  unfold BipartiteExperiment.linScore
  let A_i : (I → Bool) → ℝ := fun z => E.expT z i / E.piT p i - 1
  let B_i : (I → Bool) → ℝ := fun z => E.expC z i / E.piC p i - 1
  let A_j : (I → Bool) → ℝ := fun z => E.expT z j / E.piT p j - 1
  let B_j : (I → Bool) → ℝ := fun z => E.expC z j / E.piC p j - 1
  have hAA : (bernoulliDesign p hp0 hp1).E (fun z => A_i z * A_j z) = E.r1 p i j :=
    centered_treat_treat_moment E p hp0 hp1 hpos i j
  have hBB : (bernoulliDesign p hp0 hp1).E (fun z => B_i z * B_j z) = E.r0 p i j :=
    centered_ctrl_ctrl_moment E p hp0 hp1 hlt i j
  have hAB : (bernoulliDesign p hp0 hp1).E (fun z => A_i z * B_j z) = -E.r10 i j :=
    centered_treat_ctrl_moment E p hp0 hp1 hpos hlt i j
  have hBA : (bernoulliDesign p hp0 hp1).E (fun z => B_i z * A_j z) = -E.r10 i j := by
    calc (bernoulliDesign p hp0 hp1).E (fun z => B_i z * A_j z)
        = (bernoulliDesign p hp0 hp1).E (fun z => A_j z * B_i z) := by
            exact (bernoulliDesign p hp0 hp1).E_congr (fun z => by ring)
      _ = -E.r10 j i := centered_treat_ctrl_moment E p hp0 hp1 hpos hlt j i
      _ = -E.r10 i j := by rw [r10_comm E i j]
  rw [E_lin_expand (D := bernoulliDesign p hp0 hp1)
    (A := A_i) (B := B_i) (C := A_j) (F := B_j)
    (ai := E.Y1 i - E.mu1) (bi := E.Y0 i - E.mu0)
    (aj := E.Y1 j - E.mu1) (bj := E.Y0 j - E.mu0)
    (AA := E.r1 p i j) (AB := -E.r10 i j) (BA := -E.r10 i j) (BB := E.r0 p i j)
    hAA hAB hBA hBB]
  ring

-- @node: varScale_pair_moments
/-- The variance scale is the average over all outcome pairs of the joint moments of their linearization scores. -/
lemma varScale_pair_moments
    (E : BipartiteExperiment I O)
    (D : FiniteDesign (I → Bool)) (p : I → ℝ) (hp0 : ∀ k, 0 ≤ p k)
    (hp1 : ∀ k, p k ≤ 1) (hpos : ∀ k, 0 < p k) (hlt : ∀ k, p k < 1)
    (hBern : IndepHeteroBernoulli D p hp0 hp1) :
    E.varScale D p = (Fintype.card O : ℝ)⁻¹ * ∑ i, ∑ j,
      D.E (fun z => E.linScore p z i * E.linScore p z j) := by
  classical
  set nR : ℝ := (Fintype.card O : ℝ)
  have hmean : ∀ i, D.E (fun z => E.linScore p z i) = 0 :=
    fun i => linScore_mean_zero E D p hp0 hp1 hpos hlt hBern i
  have hsumfun : (fun z => nR⁻¹ * ∑ i : O, E.linScore p z i) =
      (fun z => ∑ i : O, nR⁻¹ * E.linScore p z i) := by
    funext z
    rw [Finset.mul_sum]
  unfold BipartiteExperiment.varScale
  change nR * D.Var (fun z => nR⁻¹ * ∑ i : O, E.linScore p z i) =
    nR⁻¹ * ∑ i, ∑ j, D.E (fun z => E.linScore p z i * E.linScore p z j)
  rw [D.Var_congr (by intro z; exact congrFun hsumfun z)]
  rw [D.Var_linear_comb Finset.univ (fun _ : O => nR⁻¹) (fun i z => E.linScore p z i)]
  have hcov : ∀ i j, D.Cov (fun z => E.linScore p z i) (fun z => E.linScore p z j)
      = D.E (fun z => E.linScore p z i * E.linScore p z j) := by
    intro i j
    rw [D.Cov_eq, hmean i, hmean j]
    ring
  simp [hcov]
  by_cases hn : nR = 0
  · simp [hn]
  · rw [show (∑ x : O, ∑ y : O,
        nR⁻¹ * nR⁻¹ * D.E (fun z => E.linScore p z x * E.linScore p z y))
        = (nR⁻¹ * nR⁻¹) * (∑ x : O, ∑ y : O,
            D.E (fun z => E.linScore p z x * E.linScore p z y)) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]]
    field_simp [hn]

-- @node: sum_pair_moment_cross_combined
/-- In a double sum, symmetric mixed overlap terms can be combined into twice the one-direction mixed term. -/
lemma sum_pair_moment_cross_combined (E : BipartiteExperiment I O) (A B : O → O → ℝ)
    (a b : O → ℝ) :
    (∑ i : O, ∑ j : O, (A i j + B i j + E.r10 i j * (a i * b j + b i * a j))) =
      ∑ i : O, ∑ j : O, (A i j + B i j + 2 * E.r10 i j * a i * b j) := by
  classical
  have hcross := cross_sum_symm_r10 E a b
  calc
    (∑ i : O, ∑ j : O, (A i j + B i j + E.r10 i j * (a i * b j + b i * a j)))
        = (∑ i : O, ∑ j : O, A i j) + (∑ i : O, ∑ j : O, B i j) +
            (∑ i : O, ∑ j : O, E.r10 i j * (a i * b j + b i * a j)) := by
          simp_rw [Finset.sum_add_distrib]
    _ = (∑ i : O, ∑ j : O, A i j) + (∑ i : O, ∑ j : O, B i j) +
            (∑ i : O, ∑ j : O, 2 * E.r10 i j * a i * b j) := by rw [hcross]
    _ = ∑ i : O, ∑ j : O, (A i j + B i j + 2 * E.r10 i j * a i * b j) := by
          simp_rw [Finset.sum_add_distrib]

-- @node: varScale_homogeneous_formula
/-- The variance scale equals the outcome-pair average of the treated, control, and combined mixed overlap contributions. -/
lemma varScale_homogeneous_formula
    (E : BipartiteExperiment I O)
    (D : FiniteDesign (I → Bool)) (p : I → ℝ) (hp0 : ∀ k, 0 ≤ p k)
    (hp1 : ∀ k, p k ≤ 1) (hpos : ∀ k, 0 < p k) (hlt : ∀ k, p k < 1)
    (hBern : IndepHeteroBernoulli D p hp0 hp1) :
    E.varScale D p = (Fintype.card O : ℝ)⁻¹ * ∑ i, ∑ j,
          (E.r1 p i j * (E.Y1 i - E.mu1) * (E.Y1 j - E.mu1)
           + E.r0 p i j * (E.Y0 i - E.mu0) * (E.Y0 j - E.mu0)
           + 2 * E.r10 i j * (E.Y1 i - E.mu1) * (E.Y0 j - E.mu0)) := by
  rw [varScale_pair_moments E D p hp0 hp1 hpos hlt hBern]
  apply congrArg ((Fintype.card O : ℝ)⁻¹ * ·)
  simp_rw [linScore_pair_moment E D p hp0 hp1 hpos hlt hBern]
  let A : O → O → ℝ := fun i j => E.r1 p i j * (E.Y1 i - E.mu1) * (E.Y1 j - E.mu1)
  let B : O → O → ℝ := fun i j => E.r0 p i j * (E.Y0 i - E.mu0) * (E.Y0 j - E.mu0)
  let a : O → ℝ := fun i => E.Y1 i - E.mu1
  let b : O → ℝ := fun i => E.Y0 i - E.mu0
  have hsum := sum_pair_moment_cross_combined E A B a b
  simpa [A, B, a, b, mul_assoc, mul_left_comm, mul_comm] using hsum

end CausalSmith.Experimentation.BipartiteMinimaxDesign
