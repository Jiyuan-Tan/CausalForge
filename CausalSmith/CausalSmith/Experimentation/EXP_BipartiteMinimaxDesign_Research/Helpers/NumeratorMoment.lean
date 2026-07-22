/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Numerator moment bounds for the bipartite minimax design

The centered exposure-weighted numerators `G₁ = ∑ᵢ (Tᵢ/πᵢ¹)(Y_i^1 − μ₁)` and
`G₀ = ∑ᵢ (Cᵢ/πᵢ⁰)(Y_i^0 − μ₀)` are the leading (linear-score) parts of the two Hájek arms.
This file records that each has design mean zero and design variance `O(card O)`, and hence that
the `√(card O)`-scaled numerators are bounded in probability — the tight factors in the
delta-method ratio-remainder argument (`RatioRemainder.lean`).
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers.DenominatorMoment
import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers.DenominatorControl

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open scoped BigOperators Topology
open Finset Filter
open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.DesignBased.FiniteDesign
open Causalean.Experimentation.UnknownInterference

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]

/-- Centered treated-arm numerator `G₁(z) = ∑ᵢ (T_i(z)/π_i^1)(Y_i^1 − μ₁)`. -/
noncomputable def treatNumerator (E : BipartiteExperiment I O) (p : I → ℝ) (z : I → Bool) : ℝ :=
  ∑ i, E.expT z i / E.piT p i * (E.Y1 i - E.mu1)

/-- Centered control-arm numerator `G₀(z) = ∑ᵢ (C_i(z)/π_i^0)(Y_i^0 − μ₀)`. -/
noncomputable def ctrlNumerator (E : BipartiteExperiment I O) (p : I → ℝ) (z : I → Bool) : ℝ :=
  ∑ i, E.expC z i / E.piC p i * (E.Y0 i - E.mu0)

/-- The treated-arm numerator has design mean zero under the Bernoulli design. -/
lemma treatNumerator_mean_zero (E : BipartiteExperiment I O) (q : I → ℝ)
    (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1) (hpos : ∀ k, 0 < q k) :
    (bernoulliDesign q hq0 hq1).E (fun z => treatNumerator E q z) = 0 := by
  classical
  simp only [treatNumerator]
  rw [(bernoulliDesign q hq0 hq1).E_sum Finset.univ
    (fun i z => E.expT z i / E.piT q i * (E.Y1 i - E.mu1))]
  trans ∑ i : O, (E.Y1 i - E.mu1) * 1
  · apply Finset.sum_congr rfl
    intro i _
    have hpi_pos : 0 < E.piT q i := by
      unfold BipartiteExperiment.piT
      exact Finset.prod_pos (fun k _ => hpos k)
    have hE : (bernoulliDesign q hq0 hq1).E (fun z => E.expT z i) = E.piT q i := by
      unfold BipartiteExperiment.expT BipartiteExperiment.piT
      exact bernoulli_E_treat_prod q hq0 hq1 (E.N i)
    rw [show (fun z => E.expT z i / E.piT q i * (E.Y1 i - E.mu1)) =
        fun z => ((E.Y1 i - E.mu1) * (E.piT q i)⁻¹) * E.expT z i by
          funext z; ring]
    rw [(bernoulliDesign q hq0 hq1).E_const_mul, hE]
    field_simp [(ne_of_gt hpi_pos)]
  · simp only [mul_one]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    unfold BipartiteExperiment.mu1
    rcases eq_or_ne (Fintype.card O : ℝ) 0 with hcard | hcard
    · have hc0 : Fintype.card O = 0 := by exact_mod_cast hcard
      haveI : IsEmpty O := Fintype.card_eq_zero_iff.mp hc0
      simp
    · field_simp
      ring

/-- The control-arm numerator has design mean zero under the Bernoulli design. -/
lemma ctrlNumerator_mean_zero (E : BipartiteExperiment I O) (q : I → ℝ)
    (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1) (hlt : ∀ k, q k < 1) :
    (bernoulliDesign q hq0 hq1).E (fun z => ctrlNumerator E q z) = 0 := by
  classical
  simp only [ctrlNumerator]
  rw [(bernoulliDesign q hq0 hq1).E_sum Finset.univ
    (fun i z => E.expC z i / E.piC q i * (E.Y0 i - E.mu0))]
  trans ∑ i : O, (E.Y0 i - E.mu0) * 1
  · apply Finset.sum_congr rfl
    intro i _
    have hpi_pos : 0 < E.piC q i := by
      unfold BipartiteExperiment.piC
      exact Finset.prod_pos (fun k _ => sub_pos.mpr (hlt k))
    have hE : (bernoulliDesign q hq0 hq1).E (fun z => E.expC z i) = E.piC q i := by
      unfold BipartiteExperiment.expC BipartiteExperiment.piC
      exact bernoulli_E_ctrl_prod q hq0 hq1 (E.N i)
    rw [show (fun z => E.expC z i / E.piC q i * (E.Y0 i - E.mu0)) =
        fun z => ((E.Y0 i - E.mu0) * (E.piC q i)⁻¹) * E.expC z i by
          funext z; ring]
    rw [(bernoulliDesign q hq0 hq1).E_const_mul, hE]
    field_simp [(ne_of_gt hpi_pos)]
  · simp only [mul_one]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    unfold BipartiteExperiment.mu0
    rcases eq_or_ne (Fintype.card O : ℝ) 0 with hcard | hcard
    · have hc0 : Fintype.card O = 0 := by exact_mod_cast hcard
      haveI : IsEmpty O := Fintype.card_eq_zero_iff.mp hc0
      simp
    · field_simp
      ring

/-- The treated-arm numerator has design variance at most
`card O · (4 · D̄ · denominatorKernelBound ε d̄)`. -/
lemma treatNumerator_var_le (E : BipartiteExperiment I O)
    (ε B dbar Dbar : ℝ) (hε0 : 0 < ε) (hε2 : ε < 1 / 2)
    (hbdd : BoundedOutcomes E)
    (hdeg : BoundedOutcomeDegree E dbar) (hdep : BoundedOverlapDependency E Dbar)
    (q : I → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1)
    (hq : FeasibleDesign ε B q) :
    (bernoulliDesign q hq0 hq1).Var (fun z => treatNumerator E q z)
      ≤ (Fintype.card O : ℝ) * (4 * (Dbar * denominatorKernelBound ε dbar)) := by
  classical
  let D := bernoulliDesign q hq0 hq1
  let c : O → ℝ := fun i => E.Y1 i - E.mu1
  let X : O → (I → Bool) → ℝ := fun i z => E.expT z i / E.piT q i
  have hpos : ∀ k, 0 < q k := fun k => lt_of_lt_of_le hε0 (hq.floor k).1
  have hmu : |E.mu1| ≤ 1 := by
    unfold BipartiteExperiment.mu1
    by_cases hcard : (Fintype.card O : ℝ) = 0
    · simp [hcard]
    have hcard_pos : 0 < (Fintype.card O : ℝ) := by
      have hn : 0 < Fintype.card O := Fintype.card_pos_iff.mpr (by
        by_contra hempty
        have hzero : (Fintype.card O : ℝ) = 0 := by
          haveI : IsEmpty O := not_nonempty_iff.mp hempty
          simp
        exact hcard hzero)
      exact_mod_cast hn
    calc
      |(Fintype.card O : ℝ)⁻¹ * ∑ i, E.Y1 i|
          ≤ (Fintype.card O : ℝ)⁻¹ * ∑ _i : O, (1 : ℝ) := by
            rw [abs_mul, abs_of_pos (inv_pos.mpr hcard_pos)]
            exact mul_le_mul_of_nonneg_left
              ((Finset.abs_sum_le_sum_abs _ _).trans
                (Finset.sum_le_sum fun i _ => (hbdd i).1))
              (inv_nonneg.mpr hcard_pos.le)
      _ = 1 := by simp [hcard]
  have hc : ∀ i, |c i| ≤ 2 := by
    intro i
    dsimp [c]
    calc
      |E.Y1 i - E.mu1| ≤ |E.Y1 i| + |E.mu1| := by
        simpa using (abs_sub_le (E.Y1 i) 0 E.mu1)
      _ ≤ 1 + 1 := add_le_add (hbdd i).1 hmu
      _ = 2 := by norm_num
  have hr : ∀ i j, 0 ≤ E.r1 q i j := by
    intro i j
    unfold BipartiteExperiment.r1
    by_cases hcard : 0 < (E.shared i j).card
    · rw [if_pos hcard]
      have hprod : (1 : ℝ) ≤ ∏ k ∈ E.shared i j, (q k)⁻¹ := by
        refine Finset.one_le_prod ?_
        intro k
        exact (one_le_inv₀ (hpos k)).mpr (hq1 k)
      exact sub_nonneg.mpr hprod
    · rw [if_neg hcard]
  have hmeanX : ∀ i, D.E (X i) = 1 := by
    intro i
    have hpi_pos : 0 < E.piT q i := by
      unfold BipartiteExperiment.piT
      exact Finset.prod_pos (fun k _ => hpos k)
    have hE : D.E (fun z => E.expT z i) = E.piT q i := by
      unfold D BipartiteExperiment.expT BipartiteExperiment.piT
      exact bernoulli_E_treat_prod q hq0 hq1 (E.N i)
    change D.E (fun z => E.expT z i / E.piT q i) = 1
    rw [show (fun z => E.expT z i / E.piT q i) =
        fun z => (E.piT q i)⁻¹ * E.expT z i by
          funext z; ring]
    rw [D.E_const_mul, hE]
    field_simp [(ne_of_gt hpi_pos)]
  have hcov : ∀ i j, D.Cov (X i) (X j) = E.r1 q i j := by
    intro i j
    unfold FiniteDesign.Cov
    rw [hmeanX i, hmeanX j]
    change D.E (fun z => (E.expT z i / E.piT q i - 1) *
        (E.expT z j / E.piT q j - 1)) = E.r1 q i j
    unfold D
    exact centered_treat_treat_moment E q hq0 hq1 hpos i j
  have hvar_eq :
      D.Var (fun z => treatNumerator E q z)
        = ∑ i : O, ∑ j : O, c i * c j * E.r1 q i j := by
    have hfun : (fun z => treatNumerator E q z) = fun z => ∑ i : O, c i * X i z := by
      funext z
      unfold treatNumerator
      apply Finset.sum_congr rfl
      intro i _
      dsimp [c, X]
      ring
    rw [D.Var_congr (fun z => congrFun hfun z)]
    rw [D.Var_linear_comb Finset.univ c X]
    simp [hcov]
  have hK_nonneg : 0 ≤ denominatorKernelBound ε dbar := denominatorKernelBound_nonneg hε0
  have hrow : ∀ i, ∑ j : O, E.r1 q i j ≤ Dbar * denominatorKernelBound ε dbar := by
    intro i
    have hpoint : ∀ j : O, E.r1 q i j ≤
        if j ∈ E.overlapNbrs i then denominatorKernelBound ε dbar else 0 := by
      intro j
      by_cases hj : j ∈ E.overlapNbrs i
      · simp [hj, r1_le_denominatorKernelBound E ε B dbar hε0 hε2 hdeg q hq i j]
      · have hnot : ¬ 0 < (E.shared i j).card := by
          simpa [BipartiteExperiment.overlapNbrs] using hj
        have hzero : E.r1 q i j = 0 := by simp [BipartiteExperiment.r1, hnot]
        simp [hj, hzero]
    calc
      ∑ j : O, E.r1 q i j
          ≤ ∑ j : O, if j ∈ E.overlapNbrs i then denominatorKernelBound ε dbar else 0 :=
            Finset.sum_le_sum (fun j _ => hpoint j)
      _ = ∑ j ∈ E.overlapNbrs i, denominatorKernelBound ε dbar := by
            simpa using (Finset.sum_ite_mem (s := (Finset.univ : Finset O))
              (t := E.overlapNbrs i) (f := fun _ => denominatorKernelBound ε dbar))
      _ = ((E.overlapNbrs i).card : ℝ) * denominatorKernelBound ε dbar := by simp
      _ ≤ Dbar * denominatorKernelBound ε dbar :=
            mul_le_mul_of_nonneg_right (hdep.2 i) hK_nonneg
  have hterm : ∀ i j, c i * c j * E.r1 q i j ≤ 4 * E.r1 q i j := by
    intro i j
    have hcc : c i * c j ≤ |c i| * |c j| := by
      calc
        c i * c j ≤ |c i * c j| := le_abs_self _
        _ = |c i| * |c j| := abs_mul _ _
    calc
      c i * c j * E.r1 q i j ≤ |c i| * |c j| * E.r1 q i j :=
        mul_le_mul_of_nonneg_right hcc (hr i j)
      _ ≤ (2 * 2) * E.r1 q i j :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (hc i) (hc j) (abs_nonneg _) (by norm_num)) (hr i j)
      _ = 4 * E.r1 q i j := by ring
  calc
    (bernoulliDesign q hq0 hq1).Var (fun z => treatNumerator E q z)
        = D.Var (fun z => treatNumerator E q z) := rfl
    _ = ∑ i : O, ∑ j : O, c i * c j * E.r1 q i j := hvar_eq
    _ ≤ ∑ i : O, ∑ j : O, 4 * E.r1 q i j :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = 4 * ∑ i : O, ∑ j : O, E.r1 q i j := by
          simp only [Finset.mul_sum]
    _ ≤ 4 * ∑ _i : O, Dbar * denominatorKernelBound ε dbar :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hrow i)) (by norm_num)
    _ = (Fintype.card O : ℝ) * (4 * (Dbar * denominatorKernelBound ε dbar)) := by
          simp [Finset.mul_sum]
          ring

/-- The control-arm numerator has design variance at most
`card O · (4 · D̄ · denominatorKernelBound ε d̄)`. -/
lemma ctrlNumerator_var_le (E : BipartiteExperiment I O)
    (ε B dbar Dbar : ℝ) (hε0 : 0 < ε) (hε2 : ε < 1 / 2)
    (hbdd : BoundedOutcomes E)
    (hdeg : BoundedOutcomeDegree E dbar) (hdep : BoundedOverlapDependency E Dbar)
    (q : I → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1)
    (hq : FeasibleDesign ε B q) :
    (bernoulliDesign q hq0 hq1).Var (fun z => ctrlNumerator E q z)
      ≤ (Fintype.card O : ℝ) * (4 * (Dbar * denominatorKernelBound ε dbar)) := by
  classical
  let D := bernoulliDesign q hq0 hq1
  let c : O → ℝ := fun i => E.Y0 i - E.mu0
  let X : O → (I → Bool) → ℝ := fun i z => E.expC z i / E.piC q i
  have hlt : ∀ k, q k < 1 := fun k => by linarith [(hq.floor k).2, hε0]
  have hmu : |E.mu0| ≤ 1 := by
    unfold BipartiteExperiment.mu0
    by_cases hcard : (Fintype.card O : ℝ) = 0
    · simp [hcard]
    have hcard_pos : 0 < (Fintype.card O : ℝ) := by
      have hn : 0 < Fintype.card O := Fintype.card_pos_iff.mpr (by
        by_contra hempty
        have hzero : (Fintype.card O : ℝ) = 0 := by
          haveI : IsEmpty O := not_nonempty_iff.mp hempty
          simp
        exact hcard hzero)
      exact_mod_cast hn
    calc
      |(Fintype.card O : ℝ)⁻¹ * ∑ i, E.Y0 i|
          ≤ (Fintype.card O : ℝ)⁻¹ * ∑ _i : O, (1 : ℝ) := by
            rw [abs_mul, abs_of_pos (inv_pos.mpr hcard_pos)]
            exact mul_le_mul_of_nonneg_left
              ((Finset.abs_sum_le_sum_abs _ _).trans
                (Finset.sum_le_sum fun i _ => (hbdd i).2))
              (inv_nonneg.mpr hcard_pos.le)
      _ = 1 := by simp [hcard]
  have hc : ∀ i, |c i| ≤ 2 := by
    intro i
    dsimp [c]
    calc
      |E.Y0 i - E.mu0| ≤ |E.Y0 i| + |E.mu0| := by
        simpa using (abs_sub_le (E.Y0 i) 0 E.mu0)
      _ ≤ 1 + 1 := add_le_add (hbdd i).2 hmu
      _ = 2 := by norm_num
  have hr : ∀ i j, 0 ≤ E.r0 q i j := by
    intro i j
    unfold BipartiteExperiment.r0
    by_cases hcard : 0 < (E.shared i j).card
    · rw [if_pos hcard]
      have hprod : (1 : ℝ) ≤ ∏ k ∈ E.shared i j, (1 - q k)⁻¹ := by
        refine Finset.one_le_prod ?_
        intro k
        have hpos1 : 0 < 1 - q k := sub_pos.mpr (hlt k)
        have hle1 : 1 - q k ≤ 1 := by
          simpa using sub_le_self (1 : ℝ) (hq0 k)
        exact (one_le_inv₀ hpos1).mpr hle1
      exact sub_nonneg.mpr hprod
    · rw [if_neg hcard]
  have hmeanX : ∀ i, D.E (X i) = 1 := by
    intro i
    have hpi_pos : 0 < E.piC q i := by
      unfold BipartiteExperiment.piC
      exact Finset.prod_pos (fun k _ => sub_pos.mpr (hlt k))
    have hE : D.E (fun z => E.expC z i) = E.piC q i := by
      unfold D BipartiteExperiment.expC BipartiteExperiment.piC
      exact bernoulli_E_ctrl_prod q hq0 hq1 (E.N i)
    change D.E (fun z => E.expC z i / E.piC q i) = 1
    rw [show (fun z => E.expC z i / E.piC q i) =
        fun z => (E.piC q i)⁻¹ * E.expC z i by
          funext z; ring]
    rw [D.E_const_mul, hE]
    field_simp [(ne_of_gt hpi_pos)]
  have hcov : ∀ i j, D.Cov (X i) (X j) = E.r0 q i j := by
    intro i j
    unfold FiniteDesign.Cov
    rw [hmeanX i, hmeanX j]
    change D.E (fun z => (E.expC z i / E.piC q i - 1) *
        (E.expC z j / E.piC q j - 1)) = E.r0 q i j
    unfold D
    exact centered_ctrl_ctrl_moment E q hq0 hq1 hlt i j
  have hvar_eq :
      D.Var (fun z => ctrlNumerator E q z)
        = ∑ i : O, ∑ j : O, c i * c j * E.r0 q i j := by
    have hfun : (fun z => ctrlNumerator E q z) = fun z => ∑ i : O, c i * X i z := by
      funext z
      unfold ctrlNumerator
      apply Finset.sum_congr rfl
      intro i _
      dsimp [c, X]
      ring
    rw [D.Var_congr (fun z => congrFun hfun z)]
    rw [D.Var_linear_comb Finset.univ c X]
    simp [hcov]
  have hK_nonneg : 0 ≤ denominatorKernelBound ε dbar := denominatorKernelBound_nonneg hε0
  have hrow : ∀ i, ∑ j : O, E.r0 q i j ≤ Dbar * denominatorKernelBound ε dbar := by
    intro i
    have hpoint : ∀ j : O, E.r0 q i j ≤
        if j ∈ E.overlapNbrs i then denominatorKernelBound ε dbar else 0 := by
      intro j
      by_cases hj : j ∈ E.overlapNbrs i
      · simp [hj, r0_le_denominatorKernelBound E ε B dbar hε0 hε2 hdeg q hq i j]
      · have hnot : ¬ 0 < (E.shared i j).card := by
          simpa [BipartiteExperiment.overlapNbrs] using hj
        have hzero : E.r0 q i j = 0 := by simp [BipartiteExperiment.r0, hnot]
        simp [hj, hzero]
    calc
      ∑ j : O, E.r0 q i j
          ≤ ∑ j : O, if j ∈ E.overlapNbrs i then denominatorKernelBound ε dbar else 0 :=
            Finset.sum_le_sum (fun j _ => hpoint j)
      _ = ∑ j ∈ E.overlapNbrs i, denominatorKernelBound ε dbar := by
            simpa using (Finset.sum_ite_mem (s := (Finset.univ : Finset O))
              (t := E.overlapNbrs i) (f := fun _ => denominatorKernelBound ε dbar))
      _ = ((E.overlapNbrs i).card : ℝ) * denominatorKernelBound ε dbar := by simp
      _ ≤ Dbar * denominatorKernelBound ε dbar :=
            mul_le_mul_of_nonneg_right (hdep.2 i) hK_nonneg
  have hterm : ∀ i j, c i * c j * E.r0 q i j ≤ 4 * E.r0 q i j := by
    intro i j
    have hcc : c i * c j ≤ |c i| * |c j| := by
      calc
        c i * c j ≤ |c i * c j| := le_abs_self _
        _ = |c i| * |c j| := abs_mul _ _
    calc
      c i * c j * E.r0 q i j ≤ |c i| * |c j| * E.r0 q i j :=
        mul_le_mul_of_nonneg_right hcc (hr i j)
      _ ≤ (2 * 2) * E.r0 q i j :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (hc i) (hc j) (abs_nonneg _) (by norm_num)) (hr i j)
      _ = 4 * E.r0 q i j := by ring
  calc
    (bernoulliDesign q hq0 hq1).Var (fun z => ctrlNumerator E q z)
        = D.Var (fun z => ctrlNumerator E q z) := rfl
    _ = ∑ i : O, ∑ j : O, c i * c j * E.r0 q i j := hvar_eq
    _ ≤ ∑ i : O, ∑ j : O, 4 * E.r0 q i j :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = 4 * ∑ i : O, ∑ j : O, E.r0 q i j := by
          simp only [Finset.mul_sum]
    _ ≤ 4 * ∑ _i : O, Dbar * denominatorKernelBound ε dbar :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hrow i)) (by norm_num)
    _ = (Fintype.card O : ℝ) * (4 * (Dbar * denominatorKernelBound ε dbar)) := by
          simp [Finset.mul_sum]
          ring

variable {Ix Ox : ℕ → Type*} [∀ n, Fintype (Ix n)] [∀ n, Fintype (Ox n)]
  [∀ n, DecidableEq (Ix n)] [∀ n, DecidableEq (Ox n)]

/-- The `√(card Ox)`-scaled treated-arm numerator is bounded in probability (uniformly tight). -/
lemma treatNumerator_scaled_boundedInProb
    (E : ∀ n, BipartiteExperiment (Ix n) (Ox n))
    (D : ∀ n, FiniteDesign (Ix n → Bool)) (p : ∀ n, Ix n → ℝ)
    (hp0 : ∀ n k, 0 ≤ p n k) (hp1 : ∀ n k, p n k ≤ 1)
    (ε B : ℕ → ℝ) (dbar Dbar : ℝ)
    (hBern : ∀ n, IndepHeteroBernoulli (D n) (p n) (hp0 n) (hp1 n))
    (hbdd : ∀ n, BoundedOutcomes (E n))
    (hdeg : ∀ n, BoundedOutcomeDegree (E n) dbar)
    (hdep : ∀ n, BoundedOverlapDependency (E n) Dbar)
    (hfeas : ∀ n, FeasibleDesign (ε n) (B n) (p n))
    (hε : ∀ n, EpsilonAdmissible (ε n))
    (hεfloor : ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ᶠ n in atTop, ε0 ≤ ε n) :
    BoundedInProb D (fun n z =>
      (Real.sqrt (Fintype.card (Ox n)))⁻¹ * treatNumerator (E n) (p n) z) := by
  classical
  rcases hεfloor with ⟨ε0, hε0, hfloor⟩
  apply FiniteDesign.boundedInProb_of_var_bound D _
    (V := 4 * (Dbar * denominatorKernelBound ε0 dbar)) (c := 0)
  · filter_upwards [hfloor] with n hε0le
    have hpos : ∀ k, 0 < p n k := fun k =>
      lt_of_lt_of_le (hε n).1 ((hfeas n).floor k).1
    have hDbar : 0 ≤ Dbar := (hdep n).1.le
    have hK0 : 0 ≤ denominatorKernelBound ε0 dbar := denominatorKernelBound_nonneg hε0
    rcases Nat.eq_zero_or_pos (Fintype.card (Ox n)) with hcard | hcard
    · rw [hBern n, FiniteDesign.Var_const_mul]
      simp [hcard, mul_nonneg hDbar hK0]
    · have hcardR : 0 < (Fintype.card (Ox n) : ℝ) := by
        exact_mod_cast hcard
      have hvar := treatNumerator_var_le (E n) (ε n) (B n) dbar Dbar
        (hε n).1 (hε n).2 (hbdd n) (hdeg n) (hdep n) (p n) (hp0 n) (hp1 n) (hfeas n)
      have hK := denominatorKernelBound_le_of_floor (dbar := dbar) hε0 hε0le (hε n)
      rw [hBern n, FiniteDesign.Var_const_mul]
      calc
        (Real.sqrt (Fintype.card (Ox n)))⁻¹ ^ 2 *
            (bernoulliDesign (p n) (hp0 n) (hp1 n)).Var
              (fun z => treatNumerator (E n) (p n) z) =
            (Fintype.card (Ox n) : ℝ)⁻¹ *
              (bernoulliDesign (p n) (hp0 n) (hp1 n)).Var
                (fun z => treatNumerator (E n) (p n) z) := by
              congr 1
              rw [inv_pow, Real.sq_sqrt (by positivity)]
        _ ≤ (Fintype.card (Ox n) : ℝ)⁻¹ *
            ((Fintype.card (Ox n) : ℝ) *
              (4 * (Dbar * denominatorKernelBound (ε n) dbar))) :=
              mul_le_mul_of_nonneg_left hvar (inv_nonneg.mpr hcardR.le)
        _ = 4 * (Dbar * denominatorKernelBound (ε n) dbar) := by
              field_simp
        _ ≤ 4 * (Dbar * denominatorKernelBound ε0 dbar) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK hDbar) (by norm_num)
  · filter_upwards with n
    have hpos : ∀ k, 0 < p n k := fun k =>
      lt_of_lt_of_le (hε n).1 ((hfeas n).floor k).1
    rw [hBern n, FiniteDesign.E_const_mul]
    rw [treatNumerator_mean_zero (E n) (p n) (hp0 n) (hp1 n) hpos]
    simp

/-- A Bernoulli assignment design is unchanged when its treatment-probability schedule and the
corresponding conditions that all probabilities lie between zero and one are replaced by equal
ones. -/
add_decl_doc Causalean.Experimentation.UnknownInterference.bernoulliDesign.congr_simp

/-- The `√(card Ox)`-scaled control-arm numerator is bounded in probability (uniformly tight). -/
lemma ctrlNumerator_scaled_boundedInProb
    (E : ∀ n, BipartiteExperiment (Ix n) (Ox n))
    (D : ∀ n, FiniteDesign (Ix n → Bool)) (p : ∀ n, Ix n → ℝ)
    (hp0 : ∀ n k, 0 ≤ p n k) (hp1 : ∀ n k, p n k ≤ 1)
    (ε B : ℕ → ℝ) (dbar Dbar : ℝ)
    (hBern : ∀ n, IndepHeteroBernoulli (D n) (p n) (hp0 n) (hp1 n))
    (hbdd : ∀ n, BoundedOutcomes (E n))
    (hdeg : ∀ n, BoundedOutcomeDegree (E n) dbar)
    (hdep : ∀ n, BoundedOverlapDependency (E n) Dbar)
    (hfeas : ∀ n, FeasibleDesign (ε n) (B n) (p n))
    (hε : ∀ n, EpsilonAdmissible (ε n))
    (hεfloor : ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ᶠ n in atTop, ε0 ≤ ε n) :
    BoundedInProb D (fun n z =>
      (Real.sqrt (Fintype.card (Ox n)))⁻¹ * ctrlNumerator (E n) (p n) z) := by
  classical
  rcases hεfloor with ⟨ε0, hε0, hfloor⟩
  apply FiniteDesign.boundedInProb_of_var_bound D _
    (V := 4 * (Dbar * denominatorKernelBound ε0 dbar)) (c := 0)
  · filter_upwards [hfloor] with n hε0le
    have hlt : ∀ k, p n k < 1 := fun k => by
      linarith [(hfeas n).floor k |>.2, (hε n).1]
    have hDbar : 0 ≤ Dbar := (hdep n).1.le
    have hK0 : 0 ≤ denominatorKernelBound ε0 dbar := denominatorKernelBound_nonneg hε0
    rcases Nat.eq_zero_or_pos (Fintype.card (Ox n)) with hcard | hcard
    · rw [hBern n, FiniteDesign.Var_const_mul]
      simp [hcard, mul_nonneg hDbar hK0]
    · have hcardR : 0 < (Fintype.card (Ox n) : ℝ) := by
        exact_mod_cast hcard
      have hvar := ctrlNumerator_var_le (E n) (ε n) (B n) dbar Dbar
        (hε n).1 (hε n).2 (hbdd n) (hdeg n) (hdep n) (p n) (hp0 n) (hp1 n) (hfeas n)
      have hK := denominatorKernelBound_le_of_floor (dbar := dbar) hε0 hε0le (hε n)
      rw [hBern n, FiniteDesign.Var_const_mul]
      calc
        (Real.sqrt (Fintype.card (Ox n)))⁻¹ ^ 2 *
            (bernoulliDesign (p n) (hp0 n) (hp1 n)).Var
              (fun z => ctrlNumerator (E n) (p n) z) =
            (Fintype.card (Ox n) : ℝ)⁻¹ *
              (bernoulliDesign (p n) (hp0 n) (hp1 n)).Var
                (fun z => ctrlNumerator (E n) (p n) z) := by
              congr 1
              rw [inv_pow, Real.sq_sqrt (by positivity)]
        _ ≤ (Fintype.card (Ox n) : ℝ)⁻¹ *
            ((Fintype.card (Ox n) : ℝ) *
              (4 * (Dbar * denominatorKernelBound (ε n) dbar))) :=
              mul_le_mul_of_nonneg_left hvar (inv_nonneg.mpr hcardR.le)
        _ = 4 * (Dbar * denominatorKernelBound (ε n) dbar) := by
              field_simp
        _ ≤ 4 * (Dbar * denominatorKernelBound ε0 dbar) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK hDbar) (by norm_num)
  · filter_upwards with n
    have hlt : ∀ k, p n k < 1 := fun k => by
      linarith [(hfeas n).floor k |>.2, (hε n).1]
    rw [hBern n, FiniteDesign.E_const_mul]
    rw [ctrlNumerator_mean_zero (E n) (p n) (hp0 n) (hp1 n) hlt]
    simp

end CausalSmith.Experimentation.BipartiteMinimaxDesign
