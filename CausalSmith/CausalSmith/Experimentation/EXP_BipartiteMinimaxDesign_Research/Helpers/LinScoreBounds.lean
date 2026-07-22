/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Pointwise bounds for heterogeneous linear scores
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers.Denominator

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped BigOperators
open Finset
open Causalean.Experimentation.DesignBased

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]

-- @node: mu1_abs_le_one
/-- Under bounded potential outcomes, the treated potential-outcome mean is bounded by one in absolute value. -/
lemma mu1_abs_le_one (E : BipartiteExperiment I O) (hbdd : BoundedOutcomes E) :
    |E.mu1| ≤ 1 := by
  classical
  unfold BipartiteExperiment.mu1
  by_cases hcard : (Fintype.card O : ℝ) = 0
  · simp [hcard]
  have hcard_pos : 0 < (Fintype.card O : ℝ) := by
    have hn : 0 < Fintype.card O := Fintype.card_pos_iff.mpr (by
      by_contra hempty
      have : (Fintype.card O : ℝ) = 0 := by
        haveI : IsEmpty O := not_nonempty_iff.mp hempty
        simp
      exact hcard this)
    exact_mod_cast hn
  calc
    |(Fintype.card O : ℝ)⁻¹ * ∑ i, E.Y1 i|
        ≤ (Fintype.card O : ℝ)⁻¹ * ∑ _i : O, (1 : ℝ) := by
          rw [abs_mul, abs_of_pos (inv_pos.mpr hcard_pos)]
          exact mul_le_mul_of_nonneg_left
            ((Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun i _ => (hbdd i).1))
            (inv_nonneg.mpr hcard_pos.le)
    _ = 1 := by
      simp [hcard]

-- @node: mu0_abs_le_one
/-- Under bounded potential outcomes, the control potential-outcome mean is bounded by one in absolute value. -/
lemma mu0_abs_le_one (E : BipartiteExperiment I O) (hbdd : BoundedOutcomes E) :
    |E.mu0| ≤ 1 := by
  classical
  unfold BipartiteExperiment.mu0
  by_cases hcard : (Fintype.card O : ℝ) = 0
  · simp [hcard]
  have hcard_pos : 0 < (Fintype.card O : ℝ) := by
    have hn : 0 < Fintype.card O := Fintype.card_pos_iff.mpr (by
      by_contra hempty
      have : (Fintype.card O : ℝ) = 0 := by
        haveI : IsEmpty O := not_nonempty_iff.mp hempty
        simp
      exact hcard this)
    exact_mod_cast hn
  calc
    |(Fintype.card O : ℝ)⁻¹ * ∑ i, E.Y0 i|
        ≤ (Fintype.card O : ℝ)⁻¹ * ∑ _i : O, (1 : ℝ) := by
          rw [abs_mul, abs_of_pos (inv_pos.mpr hcard_pos)]
          exact mul_le_mul_of_nonneg_left
            ((Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun i _ => (hbdd i).2))
            (inv_nonneg.mpr hcard_pos.le)
    _ = 1 := by
      simp [hcard]

-- @node: piT_inv_le_denominatorKernelBound_add_one
/-- Each inverse treated exposure probability is bounded by one plus the denominator-kernel bound under the floor and degree conditions. -/
lemma piT_inv_le_denominatorKernelBound_add_one (E : BipartiteExperiment I O)
    (ε B dbar : ℝ) (hε : EpsilonAdmissible ε)
    (hdeg : BoundedOutcomeDegree E dbar) (p : I → ℝ) (hp : FeasibleDesign ε B p)
    (i : O) :
    (E.piT p i)⁻¹ ≤ denominatorKernelBound ε dbar + 1 := by
  classical
  have hε0 := hε.1
  have hε2 := hε.2
  have hr := r1_le_denominatorKernelBound E ε B dbar hε0 hε2 hdeg p hp i i
  unfold BipartiteExperiment.r1 BipartiteExperiment.shared at hr
  unfold BipartiteExperiment.piT
  by_cases hN : 0 < (E.N i ∩ E.N i).card
  · rw [if_pos hN] at hr
    have hprod_inv : (∏ k ∈ E.N i, p k)⁻¹ = ∏ k ∈ E.N i, (p k)⁻¹ := by
      rw [Finset.prod_inv_distrib]
    rw [hprod_inv]
    simpa [Finset.inter_self] using (sub_le_iff_le_add.mp hr)
  · have hzero : E.N i = ∅ := by
      rw [← Finset.inter_self (E.N i)]
      exact Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hN)
    simp [hzero]
    have hnonneg : 0 ≤ denominatorKernelBound ε dbar := denominatorKernelBound_nonneg hε0
    linarith

-- @node: piC_inv_le_denominatorKernelBound_add_one
/-- Each inverse control exposure probability is bounded by one plus the denominator-kernel bound under the floor and degree conditions. -/
lemma piC_inv_le_denominatorKernelBound_add_one (E : BipartiteExperiment I O)
    (ε B dbar : ℝ) (hε : EpsilonAdmissible ε)
    (hdeg : BoundedOutcomeDegree E dbar) (p : I → ℝ) (hp : FeasibleDesign ε B p)
    (i : O) :
    (E.piC p i)⁻¹ ≤ denominatorKernelBound ε dbar + 1 := by
  classical
  have hε0 := hε.1
  have hε2 := hε.2
  have hr := r0_le_denominatorKernelBound E ε B dbar hε0 hε2 hdeg p hp i i
  unfold BipartiteExperiment.r0 BipartiteExperiment.shared at hr
  unfold BipartiteExperiment.piC
  by_cases hN : 0 < (E.N i ∩ E.N i).card
  · rw [if_pos hN] at hr
    have hprod_inv : (∏ k ∈ E.N i, (1 - p k))⁻¹ = ∏ k ∈ E.N i, (1 - p k)⁻¹ := by
      rw [Finset.prod_inv_distrib]
    rw [hprod_inv]
    simpa [Finset.inter_self] using (sub_le_iff_le_add.mp hr)
  · have hzero : E.N i = ∅ := by
      rw [← Finset.inter_self (E.N i)]
      exact Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hN)
    simp [hzero]
    have hnonneg : 0 ≤ denominatorKernelBound ε dbar := denominatorKernelBound_nonneg hε0
    linarith

-- @node: linScore_abs_le_uniform
/-- Every linearization score is bounded in absolute value by the stated uniform denominator-kernel-based constant. -/
lemma linScore_abs_le_uniform (E : BipartiteExperiment I O)
    (ε B dbar : ℝ) (hε : EpsilonAdmissible ε)
    (hbdd : BoundedOutcomes E) (hdeg : BoundedOutcomeDegree E dbar)
    (p : I → ℝ) (hp : FeasibleDesign ε B p) (z : I → Bool) (i : O) :
    |E.linScore p z i| ≤ 4 * (denominatorKernelBound ε dbar + 2) := by
  classical
  let K : ℝ := denominatorKernelBound ε dbar + 1
  have hK_nonneg : 0 ≤ K := by
    have hnonneg : 0 ≤ denominatorKernelBound ε dbar := denominatorKernelBound_nonneg hε.1
    dsimp [K]
    linarith
  have hpiT_pos : 0 < E.piT p i := by
    unfold BipartiteExperiment.piT
    exact Finset.prod_pos (fun k _ => lt_of_lt_of_le hε.1 ((hp.floor k).1))
  have hpiC_pos : 0 < E.piC p i := by
    unfold BipartiteExperiment.piC
    exact Finset.prod_pos (fun k _ => sub_pos.mpr (by linarith [((hp.floor k).2), hε.1]))
  have hexpT_abs : |E.expT z i| ≤ 1 := by
    unfold BipartiteExperiment.expT
    have hterm : ∀ k ∈ E.N i, |(if z k then (1 : ℝ) else 0)| ≤ 1 := by
      intro k hk
      by_cases hz : z k <;> simp [hz]
    have hprod_nonneg : 0 ≤ ∏ k ∈ E.N i, |(if z k then (1 : ℝ) else 0)| :=
      Finset.prod_nonneg (fun k hk => abs_nonneg _)
    calc
      |∏ k ∈ E.N i, (if z k then (1 : ℝ) else 0)|
          = ∏ k ∈ E.N i, |(if z k then (1 : ℝ) else 0)| := Finset.abs_prod _ _
      _ ≤ ∏ _k ∈ E.N i, (1 : ℝ) := by
          exact Finset.prod_le_prod (fun k hk => abs_nonneg _) hterm
      _ = 1 := by simp
  have hexpC_abs : |E.expC z i| ≤ 1 := by
    unfold BipartiteExperiment.expC
    have hterm : ∀ k ∈ E.N i, |(if z k then (0 : ℝ) else 1)| ≤ 1 := by
      intro k hk
      by_cases hz : z k <;> simp [hz]
    calc
      |∏ k ∈ E.N i, (if z k then (0 : ℝ) else 1)|
          = ∏ k ∈ E.N i, |(if z k then (0 : ℝ) else 1)| := Finset.abs_prod _ _
      _ ≤ ∏ _k ∈ E.N i, (1 : ℝ) := by
          exact Finset.prod_le_prod (fun k hk => abs_nonneg _) hterm
      _ = 1 := by simp
  have hT_ratio : |E.expT z i / E.piT p i| ≤ K := by
    have hinv := piT_inv_le_denominatorKernelBound_add_one E ε B dbar hε hdeg p hp i
    have hinvK : (E.piT p i)⁻¹ ≤ K := by simpa [K] using hinv
    calc
      |E.expT z i / E.piT p i| = |E.expT z i| * (E.piT p i)⁻¹ := by
        rw [abs_div, abs_of_pos hpiT_pos, div_eq_mul_inv]
      _ ≤ 1 * K := mul_le_mul hexpT_abs hinvK (inv_nonneg.mpr hpiT_pos.le) zero_le_one
      _ = K := by ring
  have hC_ratio : |E.expC z i / E.piC p i| ≤ K := by
    have hinv := piC_inv_le_denominatorKernelBound_add_one E ε B dbar hε hdeg p hp i
    have hinvK : (E.piC p i)⁻¹ ≤ K := by simpa [K] using hinv
    calc
      |E.expC z i / E.piC p i| = |E.expC z i| * (E.piC p i)⁻¹ := by
        rw [abs_div, abs_of_pos hpiC_pos, div_eq_mul_inv]
      _ ≤ 1 * K := mul_le_mul hexpC_abs hinvK (inv_nonneg.mpr hpiC_pos.le) zero_le_one
      _ = K := by ring
  have hcenterT : |E.expT z i / E.piT p i - 1| ≤ K + 1 := by
    calc
      |E.expT z i / E.piT p i - 1| ≤ |E.expT z i / E.piT p i| + |(1 : ℝ)| :=
        by simpa using (abs_sub_le (E.expT z i / E.piT p i) 0 (1 : ℝ))
      _ ≤ K + 1 := by
        have h1 : |(1 : ℝ)| ≤ 1 := by norm_num
        exact add_le_add hT_ratio h1
  have hcenterC : |E.expC z i / E.piC p i - 1| ≤ K + 1 := by
    calc
      |E.expC z i / E.piC p i - 1| ≤ |E.expC z i / E.piC p i| + |(1 : ℝ)| :=
        by simpa using (abs_sub_le (E.expC z i / E.piC p i) 0 (1 : ℝ))
      _ ≤ K + 1 := by
        have h1 : |(1 : ℝ)| ≤ 1 := by norm_num
        exact add_le_add hC_ratio h1
  have hY1 : |E.Y1 i - E.mu1| ≤ 2 := by
    calc
      |E.Y1 i - E.mu1| ≤ |E.Y1 i| + |E.mu1| := by
        simpa using (abs_sub_le (E.Y1 i) 0 E.mu1)
      _ ≤ 1 + 1 := add_le_add (hbdd i).1 (mu1_abs_le_one E hbdd)
      _ = 2 := by norm_num
  have hY0 : |E.Y0 i - E.mu0| ≤ 2 := by
    calc
      |E.Y0 i - E.mu0| ≤ |E.Y0 i| + |E.mu0| := by
        simpa using (abs_sub_le (E.Y0 i) 0 E.mu0)
      _ ≤ 1 + 1 := add_le_add (hbdd i).2 (mu0_abs_le_one E hbdd)
      _ = 2 := by norm_num
  unfold BipartiteExperiment.linScore
  have hK1_nonneg : 0 ≤ K + 1 := by linarith
  have htermT :
      |(E.expT z i / E.piT p i - 1) * (E.Y1 i - E.mu1)| ≤ (K + 1) * 2 := by
    rw [abs_mul]
    exact mul_le_mul hcenterT hY1 (abs_nonneg _) hK1_nonneg
  have htermC :
      |(E.expC z i / E.piC p i - 1) * (E.Y0 i - E.mu0)| ≤ (K + 1) * 2 := by
    rw [abs_mul]
    exact mul_le_mul hcenterC hY0 (abs_nonneg _) hK1_nonneg
  calc
    |(E.expT z i / E.piT p i - 1) * (E.Y1 i - E.mu1) -
        (E.expC z i / E.piC p i - 1) * (E.Y0 i - E.mu0)|
        ≤ |(E.expT z i / E.piT p i - 1) * (E.Y1 i - E.mu1)|
          + |(E.expC z i / E.piC p i - 1) * (E.Y0 i - E.mu0)| := by
            simpa using (abs_sub_le
              ((E.expT z i / E.piT p i - 1) * (E.Y1 i - E.mu1)) 0
              ((E.expC z i / E.piC p i - 1) * (E.Y0 i - E.mu0)))
    _ ≤ (K + 1) * 2 + (K + 1) * 2 := add_le_add htermT htermC
    _ = 4 * (denominatorKernelBound ε dbar + 2) := by
      dsimp [K]
      ring

-- @node: linScore-abs-le-uniform-floor
/-- The linear-score bound only uses the probability-vector box, the positivity
floor, and the outcome degree. This variant lets a stronger uniform floor `ε0`
control a design originally certified feasible at a possibly larger floor. -/
lemma linScore_abs_le_uniform_floor (E : BipartiteExperiment I O)
    (ε0 dbar : ℝ) (hε0 : EpsilonAdmissible ε0)
    (hbdd : BoundedOutcomes E) (hdeg : BoundedOutcomeDegree E dbar)
    (p : I → ℝ) (hp_prob : ProbVector p) (hfloor : PositivityFloor ε0 p)
    (z : I → Bool) (i : O) :
    |E.linScore p z i| ≤ 4 * (denominatorKernelBound ε0 dbar + 2) := by
  classical
  let B0 : ℝ := ∑ k, p k
  have hp : FeasibleDesign ε0 B0 p := {
    prob := hp_prob
    admissible := hε0
    floor := hfloor
    budget := rfl }
  exact linScore_abs_le_uniform E ε0 B0 dbar hε0 hbdd hdeg p hp z i

end CausalSmith.Experimentation.BipartiteMinimaxDesign
