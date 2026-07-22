/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Denominator moment bounds for the bipartite minimax design
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers.Kernel
import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers.Surrogate
import Causalean.Experimentation.DesignBased.InProb

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open scoped BigOperators
open Finset
open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.UnknownInterference

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]

-- @node: denominatorKernelBound
/-- Uniform reciprocal-product bound for one nonempty shared-neighborhood kernel. -/
noncomputable def denominatorKernelBound (ε dbar : ℝ) : ℝ :=
  ε⁻¹ * max 1 (ε ^ (-(dbar - 1)))

-- @node: denominatorKernelBound_nonneg
lemma denominatorKernelBound_nonneg {ε dbar : ℝ} (hε0 : 0 < ε) :
    0 ≤ denominatorKernelBound ε dbar := by
  unfold denominatorKernelBound
  exact mul_nonneg (inv_nonneg.mpr hε0.le) (le_trans zero_le_one (le_max_left _ _))

-- @node: denominatorKernelBound_le_of_floor
lemma denominatorKernelBound_le_of_floor {ε0 ε dbar : ℝ}
    (hε0 : 0 < ε0) (hε0le : ε0 ≤ ε) (hε : EpsilonAdmissible ε) :
    denominatorKernelBound ε dbar ≤ denominatorKernelBound ε0 dbar := by
  unfold denominatorKernelBound
  have hεpos : 0 < ε := hε.1
  have hεle1 : ε ≤ 1 := by linarith [hε.2]
  have hinv : ε⁻¹ ≤ ε0⁻¹ := (inv_le_inv₀ hεpos hε0).mpr hε0le
  have hpowMax :
      max 1 (ε ^ (-(dbar - 1))) ≤ max 1 (ε0 ^ (-(dbar - 1))) := by
    apply max_le
    · exact le_max_left _ _
    · by_cases hexp : 0 ≤ -(dbar - 1)
      · have hpow_le_one : ε ^ (-(dbar - 1)) ≤ 1 :=
          Real.rpow_le_one hεpos.le hεle1 hexp
        exact hpow_le_one.trans (le_max_left _ _)
      · have hexp_nonpos : -(dbar - 1) ≤ 0 := le_of_not_ge hexp
        have hpow_le : ε ^ (-(dbar - 1)) ≤ ε0 ^ (-(dbar - 1)) :=
          Real.rpow_le_rpow_of_nonpos hε0 hε0le hexp_nonpos
        exact hpow_le.trans (le_max_right _ _)
  have hmax_nonneg : 0 ≤ max 1 (ε ^ (-(dbar - 1))) :=
    le_trans zero_le_one (le_max_left _ _)
  exact mul_le_mul hinv hpowMax hmax_nonneg (inv_nonneg.mpr hε0.le)

-- @node: r1_le_denominatorKernelBound
/-- Under feasible floor-constrained propensities and bounded outcome degree, each treated-overlap kernel is bounded by the denominator-kernel bound. -/
lemma r1_le_denominatorKernelBound (E : BipartiteExperiment I O)
    (ε B dbar : ℝ) (hε0 : 0 < ε) (hε2 : ε < 1 / 2)
    (hdeg : BoundedOutcomeDegree E dbar) (q : I → ℝ) (hq : FeasibleDesign ε B q)
    (i j : O) :
    E.r1 q i j ≤ denominatorKernelBound ε dbar := by
  classical
  unfold BipartiteExperiment.r1
  by_cases hS : 0 < (E.shared i j).card
  · rw [if_pos hS]
    rcases Finset.card_pos.mp hS with ⟨k, hk⟩
    have hSle : ((E.shared i j).card : ℝ) ≤ dbar := by
      have hnat : (E.shared i j).card ≤ (E.N i).card :=
        Finset.card_le_card Finset.inter_subset_left
      have hreal : ((E.shared i j).card : ℝ) ≤ ((E.N i).card : ℝ) := by exact_mod_cast hnat
      exact hreal.trans (hdeg.2 i)
    have hcert := inv_pow_card_sub_one_le_certificate ε dbar (E.shared i j)
      hε0 hε2 hS hSle
    have ha0 : ∀ l ∈ E.shared i j, 0 ≤ (q l)⁻¹ := by
      intro l _
      exact inv_nonneg.mpr (hq.prob l).1
    have haε : ∀ l ∈ E.shared i j, (q l)⁻¹ ≤ ε⁻¹ := by
      intro l _
      have hqpos : 0 < q l := lt_of_lt_of_le hε0 (hq.floor l).1
      exact (inv_le_inv₀ hqpos hε0).mpr (hq.floor l).1
    have hsdiff :
        ∏ l ∈ E.shared i j \ {k}, (q l)⁻¹ ≤ max 1 (ε ^ (-(dbar - 1))) :=
      (prod_sdiff_le_inv_pow_card_sub_one (E.shared i j) (fun l => (q l)⁻¹)
        ε ha0 haε hk).trans hcert
    have hprod_nonneg : 0 ≤ ∏ l ∈ E.shared i j \ {k}, (q l)⁻¹ := by
      exact Finset.prod_nonneg (fun l hl => ha0 l (Finset.mem_sdiff.mp hl).1)
    have hprod :
        ∏ l ∈ E.shared i j, (q l)⁻¹ ≤ denominatorKernelBound ε dbar := by
      rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem hk]
      unfold denominatorKernelBound
      exact mul_le_mul (haε k hk) hsdiff hprod_nonneg (inv_nonneg.mpr hε0.le)
    linarith
  · rw [if_neg hS]
    exact denominatorKernelBound_nonneg hε0

-- @node: r0_le_denominatorKernelBound
/-- Under feasible floor-constrained propensities and bounded outcome degree, each control-overlap kernel is bounded by the denominator-kernel bound. -/
lemma r0_le_denominatorKernelBound (E : BipartiteExperiment I O)
    (ε B dbar : ℝ) (hε0 : 0 < ε) (hε2 : ε < 1 / 2)
    (hdeg : BoundedOutcomeDegree E dbar) (q : I → ℝ) (hq : FeasibleDesign ε B q)
    (i j : O) :
    E.r0 q i j ≤ denominatorKernelBound ε dbar := by
  classical
  unfold BipartiteExperiment.r0
  by_cases hS : 0 < (E.shared i j).card
  · rw [if_pos hS]
    rcases Finset.card_pos.mp hS with ⟨k, hk⟩
    have hSle : ((E.shared i j).card : ℝ) ≤ dbar := by
      have hnat : (E.shared i j).card ≤ (E.N i).card :=
        Finset.card_le_card Finset.inter_subset_left
      have hreal : ((E.shared i j).card : ℝ) ≤ ((E.N i).card : ℝ) := by exact_mod_cast hnat
      exact hreal.trans (hdeg.2 i)
    have hcert := inv_pow_card_sub_one_le_certificate ε dbar (E.shared i j)
      hε0 hε2 hS hSle
    have ha0 : ∀ l ∈ E.shared i j, 0 ≤ (1 - q l)⁻¹ := by
      intro l _
      have hnonneg : 0 ≤ 1 - q l := by linarith [(hq.prob l).2]
      exact inv_nonneg.mpr hnonneg
    have haε : ∀ l ∈ E.shared i j, (1 - q l)⁻¹ ≤ ε⁻¹ := by
      intro l _
      have hq_lt_one : q l < 1 := by linarith [(hq.floor l).2, hε0]
      have hpos : 0 < 1 - q l := sub_pos.mpr hq_lt_one
      have hfloor : ε ≤ 1 - q l := by linarith [(hq.floor l).2]
      exact (inv_le_inv₀ hpos hε0).mpr hfloor
    have hsdiff :
        ∏ l ∈ E.shared i j \ {k}, (1 - q l)⁻¹ ≤ max 1 (ε ^ (-(dbar - 1))) :=
      (prod_sdiff_le_inv_pow_card_sub_one (E.shared i j) (fun l => (1 - q l)⁻¹)
        ε ha0 haε hk).trans hcert
    have hprod_nonneg : 0 ≤ ∏ l ∈ E.shared i j \ {k}, (1 - q l)⁻¹ := by
      exact Finset.prod_nonneg (fun l hl => ha0 l (Finset.mem_sdiff.mp hl).1)
    have hprod :
        ∏ l ∈ E.shared i j, (1 - q l)⁻¹ ≤ denominatorKernelBound ε dbar := by
      rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem hk]
      unfold denominatorKernelBound
      exact mul_le_mul (haε k hk) hsdiff hprod_nonneg (inv_nonneg.mpr hε0.le)
    linarith
  · rw [if_neg hS]
    exact denominatorKernelBound_nonneg hε0

-- @node: treatDenominator_mean
/-- The expected treated Hájek denominator equals the number of outcomes. -/
lemma treatDenominator_mean (E : BipartiteExperiment I O) (q : I → ℝ)
    (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1) (hpos : ∀ k, 0 < q k) :
    (bernoulliDesign q hq0 hq1).E
        (fun z => ∑ i, E.expT z i / E.piT q i)
      = (Fintype.card O : ℝ) := by
  classical
  rw [(bernoulliDesign q hq0 hq1).E_sum Finset.univ
    (fun i z => E.expT z i / E.piT q i)]
  trans ∑ _i : O, (1 : ℝ)
  · apply Finset.sum_congr rfl
    intro i _
    have hpi_pos : 0 < E.piT q i := by
      unfold BipartiteExperiment.piT
      exact Finset.prod_pos (fun k _ => hpos k)
    have hE : (bernoulliDesign q hq0 hq1).E (fun z => E.expT z i) = E.piT q i := by
      unfold BipartiteExperiment.expT BipartiteExperiment.piT
      exact bernoulli_E_treat_prod q hq0 hq1 (E.N i)
    rw [show (fun z => E.expT z i / E.piT q i) =
        fun z => (E.piT q i)⁻¹ * E.expT z i by
          funext z; ring]
    rw [(bernoulliDesign q hq0 hq1).E_const_mul, hE]
    field_simp [(ne_of_gt hpi_pos)]
  · simp

-- @node: ctrlDenominator_mean
/-- The expected control Hájek denominator equals the number of outcomes. -/
lemma ctrlDenominator_mean (E : BipartiteExperiment I O) (q : I → ℝ)
    (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1) (hlt : ∀ k, q k < 1) :
    (bernoulliDesign q hq0 hq1).E
        (fun z => ∑ i, E.expC z i / E.piC q i)
      = (Fintype.card O : ℝ) := by
  classical
  rw [(bernoulliDesign q hq0 hq1).E_sum Finset.univ
    (fun i z => E.expC z i / E.piC q i)]
  trans ∑ _i : O, (1 : ℝ)
  · apply Finset.sum_congr rfl
    intro i _
    have hpi_pos : 0 < E.piC q i := by
      unfold BipartiteExperiment.piC
      exact Finset.prod_pos (fun k _ => sub_pos.mpr (hlt k))
    have hE : (bernoulliDesign q hq0 hq1).E (fun z => E.expC z i) = E.piC q i := by
      unfold BipartiteExperiment.expC BipartiteExperiment.piC
      exact bernoulli_E_ctrl_prod q hq0 hq1 (E.N i)
    rw [show (fun z => E.expC z i / E.piC q i) =
        fun z => (E.piC q i)⁻¹ * E.expC z i by
          funext z; ring]
    rw [(bernoulliDesign q hq0 hq1).E_const_mul, hE]
    field_simp [(ne_of_gt hpi_pos)]
  · simp

-- @node: treatDenominator_var_le
/-- The variance of the treated Hájek denominator is bounded by the number of outcomes times the overlap-dependency and denominator-kernel bounds. -/
lemma treatDenominator_var_le (E : BipartiteExperiment I O)
    (ε B dbar Dbar : ℝ) (hε0 : 0 < ε) (hε2 : ε < 1 / 2)
    (hdeg : BoundedOutcomeDegree E dbar) (hdep : BoundedOverlapDependency E Dbar)
    (q : I → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1)
    (hq : FeasibleDesign ε B q) :
    (bernoulliDesign q hq0 hq1).Var
        (fun z => ∑ i, E.expT z i / E.piT q i)
      ≤ (Fintype.card O : ℝ) * (Dbar * denominatorKernelBound ε dbar) := by
  classical
  let D := bernoulliDesign q hq0 hq1
  let X : O → (I → Bool) → ℝ := fun i z => E.expT z i / E.piT q i
  have hpos : ∀ k, 0 < q k := fun k => lt_of_lt_of_le hε0 (hq.floor k).1
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
      D.Var (fun z => ∑ i, X i z) = ∑ i : O, ∑ j : O, E.r1 q i j := by
    have hfun : (fun z => ∑ i, X i z) =
        fun z => ∑ i : O, (1 : ℝ) * X i z := by
      funext z
      simp
    rw [D.Var_congr (fun z => congrFun hfun z)]
    rw [D.Var_linear_comb Finset.univ (fun _ : O => (1 : ℝ)) X]
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
        have hz : E.r1 q i j = 0 := by simp [BipartiteExperiment.r1, hnot]
        simp [hj, hz]
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
  calc
    (bernoulliDesign q hq0 hq1).Var (fun z => ∑ i, E.expT z i / E.piT q i)
        = D.Var (fun z => ∑ i, X i z) := rfl
    _ = ∑ i : O, ∑ j : O, E.r1 q i j := hvar_eq
    _ ≤ ∑ _i : O, Dbar * denominatorKernelBound ε dbar :=
          Finset.sum_le_sum (fun i _ => hrow i)
    _ = (Fintype.card O : ℝ) * (Dbar * denominatorKernelBound ε dbar) := by simp

end CausalSmith.Experimentation.BipartiteMinimaxDesign
