/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.PO.ID.Partial.Lee.LatentSupport

/-! # Lee Trim Weights

This file constructs the outcome weights that represent the always-selected
treated subpopulation in Lee's sample-selection bounds. It defines the
always-selected conditional mass function `f1AS` and constructs
`alwaysSelectedTrimWeight`, the feasible Lee trim weight
`w(y) = rho * f1AS y / f1 y` on the finite selected-treated support.

The construction uses the selected-treated mixture identity and the finite
support transfer for the latent always-selected stratum. The mean identity and
trimmed-mean sandwich are proved in `TrimMean.lean` and `TrimBound.lean`. -/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POLeeSystem

variable {P : POSystem} (S : POLeeSystem P)

/-- Conditional density of `Y(1)` on `alwaysSelected` evaluated at `y`,
expressed as an `eventCondExp` of an indicator of `Y(1) = y`. -/
noncomputable def f1AS (y : ℝ) : ℝ :=
  eventCondExp P.μ S.alwaysSelected
    (fun ω => if S.YofA true ω = y then (1 : ℝ) else 0)

/-- The conditional sub-distribution of mass `ρ` of `Y(1) | AS`,
viewed as a Lee trim weight on `𝒴`. The construction yields a
`LeeTrimWeight` whose mean `Mw` equals `E[Y(1) | alwaysSelected]`.

Concretely, take `w(y) := ρ · f1AS y / f1 y` on the support of `f1` --
this satisfies the constraints of `LeeTrimWeight` precisely when the
selected-treated mixture identity (Step B) holds. -/
noncomputable def alwaysSelectedTrimWeight
    (hA : S.BaseAssumptions) (hMono : S.MonotoneSelection)
    (𝒴 : Finset ℝ)
    (hSupp : ∀ᵐ ω ∂(P.μ.restrict S.selectedTreated), S.factualY ω ∈ 𝒴) :
    S.LeeTrimWeight 𝒴 :=
by
  classical
  have h_f1_nonneg : ∀ y, 0 ≤ S.f1 y := by
    intro y
    unfold f1 eventCondExp
    exact div_nonneg
      (MeasureTheory.setIntegral_nonneg
        S.measurableSet_selectedTreated
        (fun ω _ => by by_cases h : S.factualY ω = y <;> simp [h]))
      ENNReal.toReal_nonneg
  have h_f1AS_nonneg : ∀ y, 0 ≤ S.f1AS y := by
    intro y
    unfold f1AS eventCondExp
    exact div_nonneg
      (MeasureTheory.setIntegral_nonneg
        S.measurableSet_alwaysSelected
        (fun ω _ => by by_cases h : S.YofA true ω = y <;> simp [h]))
      ENNReal.toReal_nonneg
  have h_rho_nonneg : 0 ≤ S.rho := by
    have hp0 : 0 ≤ S.p0 := by
      unfold p0 pSelGivenA eventCondExp
      refine div_nonneg ?_ ENNReal.toReal_nonneg
      exact MeasureTheory.setIntegral_nonneg (S.measurableSet_aEvent false) (fun ω _ => by
        unfold POVar.indicator
        by_cases h : ω ∈ S.selVar.event true <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, h])
    have hp1 : 0 ≤ S.p1 := by
      unfold p1 pSelGivenA eventCondExp
      refine div_nonneg ?_ ENNReal.toReal_nonneg
      exact MeasureTheory.setIntegral_nonneg (S.measurableSet_aEvent true) (fun ω _ => by
        unfold POVar.indicator
        by_cases h : ω ∈ S.selVar.event true <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, h])
    exact div_nonneg hp0 hp1
  have hSelectedControl :
      S.selectedControl = S.aEvent false ∩ S.selOfAFalseSet := by
    ext ω
    constructor
    · intro hω
      have hsel_cf : S.SelOfA false ω = S.factualSel ω :=
        POVar.cf_eq_factual_on_event hA.consistency
          S.selVar S.aVar false S.hASel.symm hω.1
      exact ⟨hω.1, by simpa [selOfAFalseSet, hsel_cf] using hω.2⟩
    · intro hω
      have hsel_cf : S.SelOfA false ω = S.factualSel ω :=
        POVar.cf_eq_factual_on_event hA.consistency
          S.selVar S.aVar false S.hASel.symm hω.1
      exact ⟨hω.1, by simpa [selOfAFalseSet, hsel_cf] using hω.2⟩
  have hSelFalseMass :
      (P.μ S.selectedControl).toReal
        = (P.μ (S.aEvent false)).toReal * (P.μ S.alwaysSelected).toReal := by
    have hselSet_pair : MeasurableSet {p : ℝ × Bool | p.2 = true} :=
      measurable_snd (measurableSet_singleton true)
    have hden_enn :
        P.μ (S.aEvent false ∩ S.selOfAFalseSet)
          = P.μ (S.aEvent false) * P.μ S.selOfAFalseSet := by
      have hraw :=
        (hA.randAssign false).measure_inter_preimage_eq_mul
          {false} {p : ℝ × Bool | p.2 = true}
          (measurableSet_singleton false) hselSet_pair
      simpa [aEvent, factualA, selOfAFalseSet, POVar.event] using hraw
    have hAS :
        (P.μ S.selOfAFalseSet).toReal = (P.μ S.alwaysSelected).toReal := by
      exact congrArg ENNReal.toReal
        (measure_congr (S.selOfAFalseSet_ae_eq_alwaysSelected hMono.monotone))
    rw [hSelectedControl, hden_enn, ENNReal.toReal_mul, hAS]
  have hIntControl :
      ∫ ω in S.aEvent false, S.selVar.indicator true ω ∂P.μ
        = (P.μ S.selectedControl).toReal := by
    rw [show S.selectedControl = S.aEvent false ∩ S.selEvent true by rfl]
    unfold POVar.indicator selEvent
    rw [MeasureTheory.setIntegral_indicator
      (show MeasurableSet (S.selVar.event true) from
        S.selVar.measurableSet_event true)]
    simp
    rfl
  have hAfalse_ne : (P.μ (S.aEvent false)).toReal ≠ 0 := by
    rw [ENNReal.toReal_ne_zero]
    exact ⟨hA.posAFalse, measure_ne_top _ _⟩
  have hAS_ne : (P.μ S.alwaysSelected).toReal ≠ 0 := by
    intro hzero
    have hsel_zero : (P.μ S.selectedControl).toReal = 0 := by
      rw [hSelFalseMass, hzero, mul_zero]
    have hsel_ne : (P.μ S.selectedControl).toReal ≠ 0 := by
      rw [ENNReal.toReal_ne_zero]
      exact ⟨hA.posSelectedControl, hA.posSelCtFinite⟩
    exact hsel_ne hsel_zero
  have hp0_eq : S.p0 = (P.μ S.alwaysSelected).toReal := by
    unfold p0 pSelGivenA eventCondExp
    rw [hIntControl, hSelFalseMass]
    field_simp [hAfalse_ne]
  have hp1_eq :
      S.p1 = (P.μ S.alwaysSelected).toReal
        + (P.μ S.helpedSelected).toReal := by
    have hInt :
        ∫ ω in S.aEvent true, S.selVar.indicator true ω ∂P.μ
          = (P.μ S.selectedTreated).toReal := by
      rw [show S.selectedTreated = S.aEvent true ∩ S.selEvent true by rfl]
      unfold POVar.indicator selEvent
      rw [MeasureTheory.setIntegral_indicator
        (show MeasurableSet (S.selVar.event true) from
          S.selVar.measurableSet_event true)]
      simp
      rfl
    have hsplit := S.selectedTreated_measure_split hA
    have hAtrue_ne : (P.μ (S.aEvent true)).toReal ≠ 0 := by
      rw [ENNReal.toReal_ne_zero]
      exact ⟨hA.posATrue, measure_ne_top _ _⟩
    unfold p1 pSelGivenA eventCondExp
    rw [hInt, hsplit]
    field_simp [hAtrue_ne]
  have hdom : ∀ y, S.rho * S.f1AS y ≤ S.f1 y := by
    intro y
    let a := (P.μ (S.aEvent true)).toReal
    let b := (P.μ S.alwaysSelected).toReal
    let c := (P.μ S.helpedSelected).toReal
    let iH :=
      ∫ ω in S.helpedSelected,
        (if S.YofA true ω = y then (1 : ℝ) else 0) ∂P.μ
    have hF1Split :
        S.f1 y * (P.μ S.selectedTreated).toReal
          = a * (S.f1AS y * b + iH) := by
      have hraw :
          S.f1 y * (P.μ S.selectedTreated).toReal
            = a *
              (∫ ω in S.alwaysSelected,
                  (if S.YofA true ω = y then (1 : ℝ) else 0) ∂P.μ
                + iH) := by
        have hden_ne : (P.μ S.selectedTreated).toReal ≠ 0 := by
          rw [ENNReal.toReal_ne_zero]
          exact ⟨hA.posSelectedTreated, hA.posSelTrFinite⟩
        unfold f1 eventCondExp
        rw [S.selectedTreated_integral_split_indicator hA y]
        field_simp [hden_ne]
        simp [a, iH]
      have hASrel :
          S.f1AS y * b =
            ∫ ω in S.alwaysSelected,
              (if S.YofA true ω = y then (1 : ℝ) else 0) ∂P.μ := by
        subst b
        unfold f1AS eventCondExp
        field_simp [hAS_ne]
      rw [← hASrel] at hraw
      exact hraw
    have hMeasureSplit :
        (P.μ S.selectedTreated).toReal = a * (b + c) := by
      simpa [a, b, c] using S.selectedTreated_measure_split hA
    have ha_ne : a ≠ 0 := by
      subst a
      rw [ENNReal.toReal_ne_zero]
      exact ⟨hA.posATrue, measure_ne_top _ _⟩
    have hbc_ne : b + c ≠ 0 := by
      intro hzero
      have hst_zero : (P.μ S.selectedTreated).toReal = 0 := by
        rw [hMeasureSplit, hzero, mul_zero]
      have hst_ne : (P.μ S.selectedTreated).toReal ≠ 0 := by
        rw [ENNReal.toReal_ne_zero]
        exact ⟨hA.posSelectedTreated, hA.posSelTrFinite⟩
      exact hst_ne hst_zero
    have hbc_pos : 0 < b + c := by
      have hb : 0 ≤ b := ENNReal.toReal_nonneg
      have hc : 0 ≤ c := ENNReal.toReal_nonneg
      exact lt_of_le_of_ne' (add_nonneg hb hc) hbc_ne
    have hiH_nonneg : 0 ≤ iH :=
      MeasureTheory.setIntegral_nonneg
        S.measurableSet_helpedSelected
        (fun ω _ => by by_cases h : S.YofA true ω = y <;> simp [h])
    have heq : S.f1 y * (b + c) = S.f1AS y * b + iH := by
      have h : a * (S.f1 y * (b + c)) = a * (S.f1AS y * b + iH) := by
        have h' := hF1Split
        rw [hMeasureSplit] at h'
        nlinarith [h']
      exact mul_left_cancel₀ ha_ne h
    have hrho_eq : S.rho = b / (b + c) := by
      unfold rho
      rw [hp0_eq, hp1_eq]
    rw [hrho_eq]
    have hmul_le : b * S.f1AS y ≤ S.f1 y * (b + c) := by
      rw [heq]
      nlinarith [hiH_nonneg]
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hbc_pos).mpr hmul_le
  have hsum_f1AS : ∑ y ∈ 𝒴, S.f1AS y = 1 := by
    have hASrel : ∀ y,
        S.f1AS y * (P.μ S.alwaysSelected).toReal =
          ∫ ω in S.alwaysSelected,
            (if S.YofA true ω = y then (1 : ℝ) else 0) ∂P.μ := by
      intro y
      unfold f1AS eventCondExp
      field_simp [hAS_ne]
    have hsum_mul :
        (∑ y ∈ 𝒴, S.f1AS y) * (P.μ S.alwaysSelected).toReal
          = ∫ ω in S.alwaysSelected,
              (∑ y ∈ 𝒴,
                (if S.YofA true ω = y then (1 : ℝ) else 0)) ∂P.μ := by
      have hInd_int : ∀ y,
          Integrable (fun ω =>
            if S.YofA true ω = y then (1 : ℝ) else 0)
            (P.μ.restrict S.alwaysSelected) := by
        intro y
        refine MeasureTheory.Integrable.of_bound
          ((Measurable.ite
            ((S.measurable_YofA true) (measurableSet_singleton y))
            measurable_const measurable_const).aestronglyMeasurable) 1
          (Filter.Eventually.of_forall ?_)
        intro ω
        by_cases hω : S.YofA true ω = y
        · simp [hω]
        · simp [hω]
      rw [Finset.sum_mul]
      rw [MeasureTheory.integral_finset_sum 𝒴 (fun y _ => hInd_int y)]
      refine Finset.sum_congr rfl ?_
      intro y hy
      exact hASrel y
    have hIntOne :
        ∫ ω in S.alwaysSelected,
            (∑ y ∈ 𝒴,
              (if S.YofA true ω = y then (1 : ℝ) else 0)) ∂P.μ
          = (P.μ S.alwaysSelected).toReal := by
      have hASsupp :=
        (S.YofA_true_in_finset_ae_alwaysSelected hA 𝒴 hSupp).1
      have hfun :
          (fun ω =>
            ∑ y ∈ 𝒴, (if S.YofA true ω = y then (1 : ℝ) else 0))
            =ᵐ[P.μ.restrict S.alwaysSelected] fun _ => (1 : ℝ) := by
        filter_upwards [hASsupp] with ω hω
        have hsingle :
            ∑ y ∈ 𝒴, (if S.YofA true ω = y then (1 : ℝ) else 0) = 1 := by
          rw [Finset.sum_eq_single (S.YofA true ω)]
          · simp
          · intro b hb hbne
            simp [hbne.symm]
          · intro hnot
            exact False.elim (hnot hω)
        exact hsingle
      have hIntCongr :
          ∫ ω,
              (∑ y ∈ 𝒴,
                (if S.YofA true ω = y then (1 : ℝ) else 0))
              ∂(P.μ.restrict S.alwaysSelected)
            = ∫ ω, (1 : ℝ) ∂(P.μ.restrict S.alwaysSelected) :=
        MeasureTheory.integral_congr_ae hfun
      change
          ∫ ω in S.alwaysSelected,
              (∑ y ∈ 𝒴,
                (if S.YofA true ω = y then (1 : ℝ) else 0)) ∂P.μ
            = ∫ ω in S.alwaysSelected, (1 : ℝ) ∂P.μ at hIntCongr
      rw [hIntCongr]
      simp
      rfl
    have h :
        (∑ y ∈ 𝒴, S.f1AS y) * (P.μ S.alwaysSelected).toReal
          = 1 * (P.μ S.alwaysSelected).toReal := by
      rw [hsum_mul, hIntOne]
      ring
    exact mul_right_cancel₀ hAS_ne h
  refine
    { w := fun y =>
        if y ∈ 𝒴 ∧ S.f1 y ≠ 0 then S.rho * S.f1AS y / S.f1 y else 0
      nonneg := ?_
      le_one := ?_
      zero_off := ?_
      sum_eq := ?_ }
  · intro y
    by_cases hy : y ∈ 𝒴 ∧ S.f1 y ≠ 0
    · simp only [hy, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
      exact div_nonneg (mul_nonneg h_rho_nonneg (h_f1AS_nonneg y))
        (h_f1_nonneg y)
    · simp [hy]
  · intro y
    by_cases hy : y ∈ 𝒴 ∧ S.f1 y ≠ 0
    · have hf_pos : 0 < S.f1 y :=
        lt_of_le_of_ne' (h_f1_nonneg y) hy.2
      simp only [hy, ne_eq, not_false_eq_true, and_self, ↓reduceIte, ge_iff_le]
      rw [div_le_iff₀ hf_pos]
      simpa [one_mul] using hdom y
    · simp [hy]
  · intro y hy
    simp [hy]
  · calc
      ∑ y ∈ 𝒴,
        (if y ∈ 𝒴 ∧ S.f1 y ≠ 0 then S.rho * S.f1AS y / S.f1 y else 0)
          * S.f1 y
          = ∑ y ∈ 𝒴, S.rho * S.f1AS y := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            by_cases hyf : S.f1 y = 0
            · have hprod_nonneg : 0 ≤ S.rho * S.f1AS y :=
                mul_nonneg h_rho_nonneg (h_f1AS_nonneg y)
              have hprod_zero : S.rho * S.f1AS y = 0 :=
                le_antisymm (by simpa [hyf] using hdom y) hprod_nonneg
              simp [hy, hyf, hprod_zero]
            · simp [hy, hyf]
      _ = S.rho * (∑ y ∈ 𝒴, S.f1AS y) := by
            rw [Finset.mul_sum]
      _ = S.rho := by rw [hsum_f1AS, mul_one]

end POLeeSystem

end PO
end Causalean
