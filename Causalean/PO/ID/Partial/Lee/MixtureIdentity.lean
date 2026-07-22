/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Lee bounds — selected-treated mixture identity

The doc's "mixture law" — three forms of the latent decomposition of the
observable selected-treated cell:

* `selectedTreated_integral_split` (Step B):
    `∫ in selectedTreated, factualY
       = (μ(A=true)).toReal · (∫ in alwaysSelected, Y(1) + ∫ in helpedSelected, Y(1))`.

* `selectedTreated_measure_split` (Step B'): the mass-level analogue
  with constant integrand `1`.

* `selectedTreated_integral_split_indicator`: the indicator-integrand
  version `1_{factualY = y}`, used by the trim-weight construction.

All three share the same proof shape: consistency on `{A=true, Sel=true}`
rewrites `factualY` to `YofA true` and `factualSel` to `SelOfA true`;
pair random assignment `A ⫫ (Y(1), Sel(1))` drops the `{A=true}`
conditioning; the pure set equality
`{Sel(1)=true} = alwaysSelected ∪ helpedSelected` (disjoint) splits the
result into the two latent strata.
-/

import Causalean.PO.ID.Partial.Lee.Assumptions
import Causalean.PO.ID.Partial.Lee.PrincipalStrata
import Causalean.PO.ID.Partial.Lee.Trim

/-! # Lee bounds selected-treated mixture identities

This file decomposes the observable selected-treated cell into always-selected
and helped-selected latent strata. The integral, mass, and indicator versions
combine consistency, random assignment, and monotone selection to prepare the
trim-weight construction.

The lemma `selectedTreated_integral_split` expresses the selected-treated
factual-outcome integral as the treatment-arm probability times the sum of
`Y(1)` integrals over `alwaysSelected` and `helpedSelected`. The lemma
`selectedTreated_measure_split` is the corresponding mass identity and feeds the
Lee trimming ratio. The lemma `selectedTreated_integral_split_indicator` repeats
the same decomposition for outcome indicators, which is needed to build and
normalize the always-selected trim-weight witness.
-/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POLeeSystem

variable {P : POSystem} (S : POLeeSystem P)

/-! ### Step B. Selected-treated mixture identity for `Y(1)`. -/

/-- Selected-treated integral split — the `f = factualY` analogue of
`selectedTreated_measure_split` (Step B'). Consistency on
`{A=true, Sel=true}` rewrites `factualY` to `YofA true`; pair random
assignment `A ⫫ (Y(1), Sel(1))` then drops the `{A=true}` conditioning
and introduces the scalar factor `(P.μ (S.aEvent true)).toReal`; the
latent `{Sel(1)=true}` set then splits as the disjoint union of
`alwaysSelected` and `helpedSelected`. -/
lemma selectedTreated_integral_split
    (hA : S.BaseAssumptions) :
    ∫ ω in S.selectedTreated, S.factualY ω ∂P.μ
    = (P.μ (S.aEvent true)).toReal *
        (∫ ω in S.alwaysSelected, S.YofA true ω ∂P.μ
         + ∫ ω in S.helpedSelected, S.YofA true ω ∂P.μ) := by
  have hSelectedTreated :
      S.selectedTreated = S.aEvent true ∩ S.selOfATrueSet := by
    ext ω
    constructor
    · intro hω
      have hsel_cf : S.SelOfA true ω = S.factualSel ω :=
        POVar.cf_eq_factual_on_event hA.consistency
          S.selVar S.aVar true S.hASel.symm hω.1
      exact ⟨hω.1, by simpa [selOfATrueSet, hsel_cf] using hω.2⟩
    · intro hω
      have hsel_cf : S.SelOfA true ω = S.factualSel ω :=
        POVar.cf_eq_factual_on_event hA.consistency
          S.selVar S.aVar true S.hASel.symm hω.1
      exact ⟨hω.1, by simpa [selOfATrueSet, hsel_cf] using hω.2⟩
  have hfac : ∀ ω ∈ S.selectedTreated, S.factualY ω = S.YofA true ω := by
    intro ω hω
    have hcf : S.YofA true ω = S.factualY ω :=
      POVar.cf_eq_factual_on_event hA.consistency
        S.yVar S.aVar true S.hAY.symm hω.1
    exact hcf.symm
  have hIntFac :
      ∫ ω in S.selectedTreated, S.factualY ω ∂P.μ
        = ∫ ω in S.selectedTreated, S.YofA true ω ∂P.μ := by
    apply MeasureTheory.setIntegral_congr_fun S.measurableSet_selectedTreated
    intro ω hω
    exact hfac ω hω
  have hpair_meas :
      Measurable (fun ω => (S.YofA true ω, S.SelOfA true ω)) :=
    Measurable.prodMk (S.measurable_YofA true) (S.measurable_SelOfA true)
  have hselSet_pair :
      MeasurableSet {p : ℝ × Bool | p.2 = true} :=
    measurable_snd (measurableSet_singleton true)
  have hφ_meas :
      Measurable (fun p : ℝ × Bool =>
        if p.2 = true then p.1 else (0 : ℝ)) := by
    exact Measurable.ite hselSet_pair measurable_fst measurable_const
  have hφ_indicator :
      (fun ω => if S.SelOfA true ω = true then S.YofA true ω else (0 : ℝ))
        = S.selOfATrueSet.indicator (S.YofA true) := by
    funext ω
    by_cases hω : S.SelOfA true ω = true
    · simp [selOfATrueSet, hω]
    · simp [selOfATrueSet, hω]
  have hdrop :
      ∫ ω in S.aEvent true ∩ S.selOfATrueSet, S.YofA true ω ∂P.μ
        = (P.μ (S.aEvent true)).toReal *
            ∫ ω in S.selOfATrueSet, S.YofA true ω ∂P.μ := by
    have hraw_num :
        ∫ ω in S.aEvent true,
            S.selOfATrueSet.indicator (S.YofA true) ω ∂P.μ
          = (P.μ (S.aEvent true)).toReal *
              ∫ ω, S.selOfATrueSet.indicator (S.YofA true) ω ∂P.μ := by
      have hraw :=
        (hA.randAssign true).integral_restrict_preimage_eq_mul
          S.measurable_factualA hpair_meas
          (measurableSet_singleton true) hφ_meas
      simpa [aEvent, factualA, POVar.event, hφ_indicator] using hraw
    rw [← MeasureTheory.setIntegral_indicator S.measurableSet_selOfATrueSet,
      ← MeasureTheory.integral_indicator S.measurableSet_selOfATrueSet]
    exact hraw_num
  have hsplit :
      ∫ ω in S.selOfATrueSet, S.YofA true ω ∂P.μ
        = ∫ ω in S.alwaysSelected, S.YofA true ω ∂P.μ
          + ∫ ω in S.helpedSelected, S.YofA true ω ∂P.μ := by
    rw [S.selOfATrueSet_eq_alwaysSelected_union_helpedSelected]
    exact MeasureTheory.setIntegral_union
      S.disjoint_alwaysSelected_helpedSelected S.measurableSet_helpedSelected
      hA.integrableY1.integrableOn hA.integrableY1.integrableOn
  calc
    ∫ ω in S.selectedTreated, S.factualY ω ∂P.μ
        = ∫ ω in S.selectedTreated, S.YofA true ω ∂P.μ := hIntFac
    _ = ∫ ω in S.aEvent true ∩ S.selOfATrueSet, S.YofA true ω ∂P.μ := by
          rw [hSelectedTreated]
    _ = (P.μ (S.aEvent true)).toReal *
          ∫ ω in S.selOfATrueSet, S.YofA true ω ∂P.μ := hdrop
    _ = (P.μ (S.aEvent true)).toReal *
        (∫ ω in S.alwaysSelected, S.YofA true ω ∂P.μ
         + ∫ ω in S.helpedSelected, S.YofA true ω ∂P.μ) := by
          rw [hsplit]

/-- Mass split: `μ(selectedTreated) = ?·μ(alwaysSelected) + ?·μ(helpedSelected)`.
This is the analog of `selectedTreated_integral_split` for the constant
function `1`, and it is what gives `ρ = μ(AS) / μ({Sel(1)=true})`. -/
lemma selectedTreated_measure_split
    (hA : S.BaseAssumptions) :
    (P.μ S.selectedTreated).toReal
    = (P.μ (S.aEvent true)).toReal *
        ((P.μ S.alwaysSelected).toReal + (P.μ S.helpedSelected).toReal) := by
  have hSelectedTreated :
      S.selectedTreated = S.aEvent true ∩ S.selOfATrueSet := by
    ext ω
    constructor
    · intro hω
      have hsel_cf : S.SelOfA true ω = S.factualSel ω :=
        POVar.cf_eq_factual_on_event hA.consistency
          S.selVar S.aVar true S.hASel.symm hω.1
      exact ⟨hω.1, by simpa [selOfATrueSet, hsel_cf] using hω.2⟩
    · intro hω
      have hsel_cf : S.SelOfA true ω = S.factualSel ω :=
        POVar.cf_eq_factual_on_event hA.consistency
          S.selVar S.aVar true S.hASel.symm hω.1
      exact ⟨hω.1, by simpa [selOfATrueSet, hsel_cf] using hω.2⟩
  have hpair_meas :
      Measurable (fun ω => (S.YofA true ω, S.SelOfA true ω)) :=
    Measurable.prodMk (S.measurable_YofA true) (S.measurable_SelOfA true)
  have hselSet_pair :
      MeasurableSet {p : ℝ × Bool | p.2 = true} :=
    measurable_snd (measurableSet_singleton true)
  have hden_enn :
      P.μ (S.aEvent true ∩ S.selOfATrueSet)
        = P.μ (S.aEvent true) * P.μ S.selOfATrueSet := by
    have hraw :=
      (hA.randAssign true).measure_inter_preimage_eq_mul
        {true} {p : ℝ × Bool | p.2 = true}
        (measurableSet_singleton true) hselSet_pair
    simpa [aEvent, factualA, selOfATrueSet, POVar.event] using hraw
  have hsplit_enn :
      P.μ S.selOfATrueSet = P.μ S.alwaysSelected + P.μ S.helpedSelected := by
    rw [S.selOfATrueSet_eq_alwaysSelected_union_helpedSelected]
    exact MeasureTheory.measure_union
      S.disjoint_alwaysSelected_helpedSelected S.measurableSet_helpedSelected
  calc
    (P.μ S.selectedTreated).toReal
        = (P.μ (S.aEvent true ∩ S.selOfATrueSet)).toReal := by
            rw [hSelectedTreated]
    _ = (P.μ (S.aEvent true)).toReal * (P.μ S.selOfATrueSet).toReal := by
            rw [hden_enn, ENNReal.toReal_mul]
    _ = (P.μ (S.aEvent true)).toReal *
          ((P.μ S.alwaysSelected).toReal + (P.μ S.helpedSelected).toReal) := by
            rw [hsplit_enn,
              ENNReal.toReal_add (measure_ne_top P.μ S.alwaysSelected)
                (measure_ne_top P.μ S.helpedSelected)]

/-! ### Step C. Trimming bound for the always-selected treated mean. -/

/-- **Step B for the indicator integrand `1_{factualY = y}`** — same
shape as `selectedTreated_integral_split` but with the indicator
integrand. Used by the `le_one` and `sum_eq` fields of
`alwaysSelectedTrimWeight`.  Proof mirrors Step B; the only change is
the integrand. -/
lemma selectedTreated_integral_split_indicator
    (hA : S.BaseAssumptions) (y : ℝ) :
    ∫ ω in S.selectedTreated, (if S.factualY ω = y then (1 : ℝ) else 0) ∂P.μ
    = (P.μ (S.aEvent true)).toReal *
        (∫ ω in S.alwaysSelected,
            (if S.YofA true ω = y then (1 : ℝ) else 0) ∂P.μ
         + ∫ ω in S.helpedSelected,
            (if S.YofA true ω = y then (1 : ℝ) else 0) ∂P.μ) := by
  have hSelectedTreated :
      S.selectedTreated = S.aEvent true ∩ S.selOfATrueSet := by
    ext ω
    constructor
    · intro hω
      have hsel_cf : S.SelOfA true ω = S.factualSel ω :=
        POVar.cf_eq_factual_on_event hA.consistency
          S.selVar S.aVar true S.hASel.symm hω.1
      exact ⟨hω.1, by simpa [selOfATrueSet, hsel_cf] using hω.2⟩
    · intro hω
      have hsel_cf : S.SelOfA true ω = S.factualSel ω :=
        POVar.cf_eq_factual_on_event hA.consistency
          S.selVar S.aVar true S.hASel.symm hω.1
      exact ⟨hω.1, by simpa [selOfATrueSet, hsel_cf] using hω.2⟩
  have hfac : ∀ ω ∈ S.selectedTreated, S.factualY ω = S.YofA true ω := by
    intro ω hω
    have hcf : S.YofA true ω = S.factualY ω :=
      POVar.cf_eq_factual_on_event hA.consistency
        S.yVar S.aVar true S.hAY.symm hω.1
    exact hcf.symm
  have hIntFac :
      ∫ ω in S.selectedTreated, (if S.factualY ω = y then (1 : ℝ) else 0) ∂P.μ
        = ∫ ω in S.selectedTreated,
            (if S.YofA true ω = y then (1 : ℝ) else 0) ∂P.μ := by
    apply MeasureTheory.setIntegral_congr_fun S.measurableSet_selectedTreated
    intro ω hω
    simp [hfac ω hω]
  have hInd_meas :
      Measurable (fun ω => if S.YofA true ω = y then (1 : ℝ) else 0) := by
    exact Measurable.ite
      ((S.measurable_YofA true) (measurableSet_singleton y))
      measurable_const measurable_const
  have hInd_int :
      Integrable (fun ω => if S.YofA true ω = y then (1 : ℝ) else 0) P.μ := by
    refine MeasureTheory.Integrable.of_bound hInd_meas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall ?_)
    intro ω
    by_cases hω : S.YofA true ω = y
    · simp [hω]
    · simp [hω]
  have hpair_meas :
      Measurable (fun ω => (S.YofA true ω, S.SelOfA true ω)) :=
    Measurable.prodMk (S.measurable_YofA true) (S.measurable_SelOfA true)
  have hselSet_pair :
      MeasurableSet {p : ℝ × Bool | p.2 = true} :=
    measurable_snd (measurableSet_singleton true)
  have hySet_pair :
      MeasurableSet {p : ℝ × Bool | p.1 = y} :=
    measurable_fst (measurableSet_singleton y)
  have hφ_meas :
      Measurable (fun p : ℝ × Bool =>
        if p.2 = true then (if p.1 = y then (1 : ℝ) else 0) else 0) := by
    exact Measurable.ite hselSet_pair
      (Measurable.ite hySet_pair measurable_const measurable_const)
      measurable_const
  have hφ_indicator :
      (fun ω =>
          if S.SelOfA true ω = true
          then (if S.YofA true ω = y then (1 : ℝ) else 0)
          else 0)
        = S.selOfATrueSet.indicator
            (fun ω => if S.YofA true ω = y then (1 : ℝ) else 0) := by
    funext ω
    by_cases hω : S.SelOfA true ω = true
    · simp [selOfATrueSet, hω]
    · simp [selOfATrueSet, hω]
  have hdrop :
      ∫ ω in S.aEvent true ∩ S.selOfATrueSet,
          (if S.YofA true ω = y then (1 : ℝ) else 0) ∂P.μ
        = (P.μ (S.aEvent true)).toReal *
            ∫ ω in S.selOfATrueSet,
              (if S.YofA true ω = y then (1 : ℝ) else 0) ∂P.μ := by
    have hraw_num :
        ∫ ω in S.aEvent true,
            S.selOfATrueSet.indicator
              (fun ω => if S.YofA true ω = y then (1 : ℝ) else 0) ω ∂P.μ
          = (P.μ (S.aEvent true)).toReal *
              ∫ ω,
                S.selOfATrueSet.indicator
                  (fun ω => if S.YofA true ω = y then (1 : ℝ) else 0) ω ∂P.μ := by
      have hraw :=
        (hA.randAssign true).integral_restrict_preimage_eq_mul
          S.measurable_factualA hpair_meas
          (measurableSet_singleton true) hφ_meas
      simpa [aEvent, factualA, POVar.event, hφ_indicator] using hraw
    rw [← MeasureTheory.setIntegral_indicator S.measurableSet_selOfATrueSet,
      ← MeasureTheory.integral_indicator S.measurableSet_selOfATrueSet]
    exact hraw_num
  have hsplit :
      ∫ ω in S.selOfATrueSet,
          (if S.YofA true ω = y then (1 : ℝ) else 0) ∂P.μ
        = ∫ ω in S.alwaysSelected,
            (if S.YofA true ω = y then (1 : ℝ) else 0) ∂P.μ
          + ∫ ω in S.helpedSelected,
            (if S.YofA true ω = y then (1 : ℝ) else 0) ∂P.μ := by
    rw [S.selOfATrueSet_eq_alwaysSelected_union_helpedSelected]
    exact MeasureTheory.setIntegral_union
      S.disjoint_alwaysSelected_helpedSelected S.measurableSet_helpedSelected
      hInd_int.integrableOn hInd_int.integrableOn
  calc
    ∫ ω in S.selectedTreated, (if S.factualY ω = y then (1 : ℝ) else 0) ∂P.μ
        = ∫ ω in S.selectedTreated,
            (if S.YofA true ω = y then (1 : ℝ) else 0) ∂P.μ := hIntFac
    _ = ∫ ω in S.aEvent true ∩ S.selOfATrueSet,
          (if S.YofA true ω = y then (1 : ℝ) else 0) ∂P.μ := by
          rw [hSelectedTreated]
    _ = (P.μ (S.aEvent true)).toReal *
          ∫ ω in S.selOfATrueSet,
            (if S.YofA true ω = y then (1 : ℝ) else 0) ∂P.μ := hdrop
    _ = (P.μ (S.aEvent true)).toReal *
        (∫ ω in S.alwaysSelected,
            (if S.YofA true ω = y then (1 : ℝ) else 0) ∂P.μ
         + ∫ ω in S.helpedSelected,
            (if S.YofA true ω = y then (1 : ℝ) else 0) ∂P.μ) := by
          rw [hsplit]

end POLeeSystem

end PO
end Causalean
