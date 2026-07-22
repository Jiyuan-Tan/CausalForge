/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.PO.ID.Partial.Lee.TrimMean
import Causalean.PO.ID.Partial.Basic

/-! # Lee Trimmed-Mean Bound

This file proves that the conditional mean of the treated potential outcome
among always-selected units is bounded by the lower and upper Lee trimmed
means. The result turns the constructed always-selected trim weight into the
scalar sandwich used by the final Lee bound.

The argument is an order-theoretic consequence of the trimmed-mean range and
the identity between the trim-weight mean and the always-selected conditional
mean. -/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POLeeSystem

variable {P : POSystem} (S : POLeeSystem P)


/-- The Lee trimmed-mean sandwich for the always-selected treated mean.

Given base Lee assumptions, monotone sample selection, and finite support for
the selected-treated outcome, the conditional mean `E[Y(1) | alwaysSelected]`
lies between the lower and upper trimmed means over all feasible Lee trim
weights on that support. -/
lemma trimmed_bounds_condExp_Y1_AS
    (hA : S.BaseAssumptions) (hMono : S.MonotoneSelection)
    (𝒴 : Finset ℝ)
    (hSupp : ∀ᵐ ω ∂(P.μ.restrict S.selectedTreated), S.factualY ω ∈ 𝒴) :
    S.lowerTrimMean 𝒴
      ≤ eventCondExp P.μ S.alwaysSelected (S.YofA true)
    ∧ eventCondExp P.μ S.alwaysSelected (S.YofA true) ≤ S.upperTrimMean 𝒴 := by
  classical
  have hMw := S.Mw_alwaysSelectedTrimWeight_eq_condExp_Y1_AS hA hMono 𝒴 hSupp
  have hmem :
      S.Mw (S.alwaysSelectedTrimWeight hA hMono 𝒴 hSupp)
        ∈ Set.range (fun wt : S.LeeTrimWeight 𝒴 => S.Mw wt) := by
    exact ⟨S.alwaysSelectedTrimWeight hA hMono 𝒴 hSupp, rfl⟩
  have hf1_nonneg : ∀ y, 0 ≤ S.f1 y := by
    intro y
    unfold f1 eventCondExp
    exact div_nonneg
      (MeasureTheory.setIntegral_nonneg
        S.measurableSet_selectedTreated
        (fun ω _ => by by_cases h : S.factualY ω = y <;> simp [h]))
      ENNReal.toReal_nonneg
  let K := |(S.rho)⁻¹| * ∑ y ∈ 𝒴, |y| * S.f1 y
  have hBddBelow :
      BddBelow (Set.range (fun wt : S.LeeTrimWeight 𝒴 => S.Mw wt)) := by
    refine ⟨-K, ?_⟩
    rintro z ⟨wt, rfl⟩
    unfold Mw
    have hsum_abs :
        |∑ y ∈ 𝒴, y * wt.w y * S.f1 y|
          ≤ ∑ y ∈ 𝒴, |y| * S.f1 y := by
      calc
        |∑ y ∈ 𝒴, y * wt.w y * S.f1 y|
            ≤ ∑ y ∈ 𝒴, |y * wt.w y * S.f1 y| := by
              exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ y ∈ 𝒴, |y| * S.f1 y := by
              refine Finset.sum_le_sum ?_
              intro y hy
              have hw0 := wt.nonneg y
              have hw1 := wt.le_one y
              have hf0 := hf1_nonneg y
              rw [abs_mul, abs_mul]
              have habsw : |wt.w y| = wt.w y := abs_of_nonneg hw0
              have habsf : |S.f1 y| = S.f1 y := abs_of_nonneg hf0
              rw [habsw, habsf]
              have hinner : wt.w y * S.f1 y ≤ S.f1 y := by
                nlinarith [mul_le_mul_of_nonneg_right hw1 hf0]
              simpa [mul_assoc] using
                mul_le_mul_of_nonneg_left hinner (abs_nonneg y)
    have habs :
        |(S.rho)⁻¹ * ∑ y ∈ 𝒴, y * wt.w y * S.f1 y| ≤ K := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hsum_abs (abs_nonneg _)
    nlinarith [neg_le_abs ((S.rho)⁻¹ *
      ∑ y ∈ 𝒴, y * wt.w y * S.f1 y)]
  have hBddAbove :
      BddAbove (Set.range (fun wt : S.LeeTrimWeight 𝒴 => S.Mw wt)) := by
    refine ⟨K, ?_⟩
    rintro z ⟨wt, rfl⟩
    unfold Mw
    have hsum_abs :
        |∑ y ∈ 𝒴, y * wt.w y * S.f1 y|
          ≤ ∑ y ∈ 𝒴, |y| * S.f1 y := by
      calc
        |∑ y ∈ 𝒴, y * wt.w y * S.f1 y|
            ≤ ∑ y ∈ 𝒴, |y * wt.w y * S.f1 y| := by
              exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ y ∈ 𝒴, |y| * S.f1 y := by
              refine Finset.sum_le_sum ?_
              intro y hy
              have hw0 := wt.nonneg y
              have hw1 := wt.le_one y
              have hf0 := hf1_nonneg y
              rw [abs_mul, abs_mul]
              have habsw : |wt.w y| = wt.w y := abs_of_nonneg hw0
              have habsf : |S.f1 y| = S.f1 y := abs_of_nonneg hf0
              rw [habsw, habsf]
              have hinner : wt.w y * S.f1 y ≤ S.f1 y := by
                nlinarith [mul_le_mul_of_nonneg_right hw1 hf0]
              simpa [mul_assoc] using
                mul_le_mul_of_nonneg_left hinner (abs_nonneg y)
    have habs :
        |(S.rho)⁻¹ * ∑ y ∈ 𝒴, y * wt.w y * S.f1 y| ≤ K := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hsum_abs (abs_nonneg _)
    exact le_trans (le_abs_self _) habs
  -- The trimmed-mean endpoints are the inf/sup of `Mw` over the unidentified
  -- trim-weight nuisance, and the always-selected witness is one feasible value;
  -- the sandwich is then the engine bridge `mem_Icc_csInf_csSup`.
  have hbridge :=
    Causalean.PartialID.mem_Icc_csInf_csSup hBddBelow hBddAbove hmem
  constructor
  · rw [← hMw, lowerTrimMean]
    exact hbridge.1
  · rw [← hMw, upperTrimMean]
    exact hbridge.2



end POLeeSystem

end PO
end Causalean
