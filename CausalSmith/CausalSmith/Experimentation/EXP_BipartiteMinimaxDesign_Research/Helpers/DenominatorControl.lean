/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Control-arm denominator variance bound
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers.DenominatorMoment

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open scoped BigOperators
open Finset
open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.UnknownInterference

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]

-- @node: ctrlDenominator_var_le
/-- The variance of the control Hájek denominator is bounded by the number of outcomes times the overlap-dependency and denominator-kernel bounds. -/
lemma ctrlDenominator_var_le (E : BipartiteExperiment I O)
    (ε B dbar Dbar : ℝ) (hε0 : 0 < ε) (hε2 : ε < 1 / 2)
    (hdeg : BoundedOutcomeDegree E dbar) (hdep : BoundedOverlapDependency E Dbar)
    (q : I → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1)
    (hq : FeasibleDesign ε B q) :
    (bernoulliDesign q hq0 hq1).Var
        (fun z => ∑ i, E.expC z i / E.piC q i)
      ≤ (Fintype.card O : ℝ) * (Dbar * denominatorKernelBound ε dbar) := by
  classical
  let D := bernoulliDesign q hq0 hq1
  let X : O → (I → Bool) → ℝ := fun i z => E.expC z i / E.piC q i
  have hlt : ∀ k, q k < 1 := fun k => by linarith [(hq.floor k).2, hε0]
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
      D.Var (fun z => ∑ i, X i z) = ∑ i : O, ∑ j : O, E.r0 q i j := by
    have hfun : (fun z => ∑ i, X i z) =
        fun z => ∑ i : O, (1 : ℝ) * X i z := by
      funext z
      simp
    rw [D.Var_congr (fun z => congrFun hfun z)]
    rw [D.Var_linear_comb Finset.univ (fun _ : O => (1 : ℝ)) X]
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
        have hz : E.r0 q i j = 0 := by simp [BipartiteExperiment.r0, hnot]
        simp [hj, hz]
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
  calc
    (bernoulliDesign q hq0 hq1).Var (fun z => ∑ i, E.expC z i / E.piC q i)
        = D.Var (fun z => ∑ i, X i z) := rfl
    _ = ∑ i : O, ∑ j : O, E.r0 q i j := hvar_eq
    _ ≤ ∑ _i : O, Dbar * denominatorKernelBound ε dbar :=
          Finset.sum_le_sum (fun i _ => hrow i)
    _ = (Fintype.card O : ℝ) * (Dbar * denominatorKernelBound ε dbar) := by simp

end CausalSmith.Experimentation.BipartiteMinimaxDesign
