/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Lee bounds — support transfer to the latent strata

`YofA_true_in_finset_ae_alwaysSelected`: if the factual outcome lies in a
finite support `𝒴` almost surely on the
observable selected-treated cell, then the latent counterfactual `Y(1)`
lies in `𝒴` almost surely on each of the two latent strata
`alwaysSelected` and `helpedSelected`. Used by the trim-weight
construction to derive the normalisation `∑ y∈𝒴, f1AS y = 1`.
-/

import Causalean.PO.ID.Partial.Lee.MixtureIdentity

/-! # Lee Latent Support Transfer

This file proves that finite support observed among selected treated units
transfers to the treated potential outcome on the always-selected and
treatment-induced-selected latent strata. The support
transfer supplies the finite normalisation needed by the trim-weight
construction.

The public lemma `YofA_true_in_finset_ae_alwaysSelected` starts from an
almost-sure finite-support hypothesis for the factual outcome restricted to the
observable selected-treated cell. Using consistency and pair-level random
assignment, it proves that `YofA true` lies in the same finite support almost
surely on both `alwaysSelected` and `helpedSelected`. -/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POLeeSystem

variable {P : POSystem} (S : POLeeSystem P)

/-- **Support transfer**: if the factual outcome lies in the finite support 𝒴
a.e. on the selected-treated cell, then
the latent counterfactual `YofA true` lies in 𝒴 a.e. on the latent
`alwaysSelected` and `helpedSelected` strata. Used by the `sum_eq`
field of `alwaysSelectedTrimWeight` to derive `∑ y ∈ 𝒴, f1AS y = 1`.

The proof transfers `hSupp` from the observable cell to the latent
strata via consistency on `{A=true, Sel=true}` plus pair random
assignment on `(Y(1), Sel(1))`. -/
lemma YofA_true_in_finset_ae_alwaysSelected
    (hA : S.BaseAssumptions)
    (𝒴 : Finset ℝ)
    (hSupp : ∀ᵐ ω ∂(P.μ.restrict S.selectedTreated), S.factualY ω ∈ 𝒴) :
    (∀ᵐ ω ∂(P.μ.restrict S.alwaysSelected), S.YofA true ω ∈ 𝒴) ∧
    (∀ᵐ ω ∂(P.μ.restrict S.helpedSelected), S.YofA true ω ∈ 𝒴) := by
  classical
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
  have hFactBad_meas : MeasurableSet {ω | S.factualY ω ∉ 𝒴} :=
    ((S.measurable_factualY) ((𝒴.finite_toSet).measurableSet)).compl
  have hSupp_null_restrict :
      (P.μ.restrict S.selectedTreated) {ω | S.factualY ω ∉ 𝒴} = 0 := by
    simpa using (MeasureTheory.ae_iff.mp hSupp)
  have hFactBad_selected :
      P.μ ({ω | S.factualY ω ∉ 𝒴} ∩ S.selectedTreated) = 0 := by
    rw [← MeasureTheory.Measure.restrict_apply hFactBad_meas]
    exact hSupp_null_restrict
  have hBad_selected :
      P.μ ({ω | S.YofA true ω ∉ 𝒴} ∩ S.selectedTreated) = 0 := by
    refine MeasureTheory.measure_mono_null ?_ hFactBad_selected
    intro ω hω
    rcases hω with ⟨hbad, hst⟩
    have hcf : S.YofA true ω = S.factualY ω :=
      POVar.cf_eq_factual_on_event hA.consistency
        S.yVar S.aVar true S.hAY.symm hst.1
    exact ⟨by simpa [← hcf] using hbad, hst⟩
  have hBad_selected' :
      P.μ (S.aEvent true ∩ ({ω | S.YofA true ω ∉ 𝒴} ∩ S.selOfATrueSet)) = 0 := by
    rw [hSelectedTreated] at hBad_selected
    simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hBad_selected
  have hpair_meas :
      Measurable (fun ω => (S.YofA true ω, S.SelOfA true ω)) :=
    Measurable.prodMk (S.measurable_YofA true) (S.measurable_SelOfA true)
  have hbadPair_meas :
      MeasurableSet {p : ℝ × Bool | p.1 ∉ 𝒴 ∧ p.2 = true} :=
    (((measurable_fst) ((𝒴.finite_toSet).measurableSet)).compl).inter
      (measurable_snd (measurableSet_singleton true))
  have hprod :
      P.μ (S.aEvent true ∩ ({ω | S.YofA true ω ∉ 𝒴} ∩ S.selOfATrueSet))
        = P.μ (S.aEvent true) *
          P.μ ({ω | S.YofA true ω ∉ 𝒴} ∩ S.selOfATrueSet) := by
    have hraw :=
      (hA.randAssign true).measure_inter_preimage_eq_mul
        {true} {p : ℝ × Bool | p.1 ∉ 𝒴 ∧ p.2 = true}
        (measurableSet_singleton true) hbadPair_meas
    simpa [aEvent, factualA, POVar.event, selOfATrueSet] using hraw
  have hBad_selOfATrue :
      P.μ ({ω | S.YofA true ω ∉ 𝒴} ∩ S.selOfATrueSet) = 0 := by
    have hmul_zero :
        P.μ (S.aEvent true) *
          P.μ ({ω | S.YofA true ω ∉ 𝒴} ∩ S.selOfATrueSet) = 0 := by
      rw [← hprod]
      exact hBad_selected'
    rcases mul_eq_zero.mp hmul_zero with hA_zero | hbad_zero
    · exact False.elim (hA.posATrue hA_zero)
    · exact hbad_zero
  have hBad_alwaysSelected :
      P.μ ({ω | S.YofA true ω ∉ 𝒴} ∩ S.alwaysSelected) = 0 := by
    refine MeasureTheory.measure_mono_null ?_ hBad_selOfATrue
    intro ω hω
    exact ⟨hω.1, hω.2.2⟩
  have hBad_helpedSelected :
      P.μ ({ω | S.YofA true ω ∉ 𝒴} ∩ S.helpedSelected) = 0 := by
    refine MeasureTheory.measure_mono_null ?_ hBad_selOfATrue
    intro ω hω
    exact ⟨hω.1, hω.2.2⟩
  constructor
  · apply (MeasureTheory.ae_restrict_iff' S.measurableSet_alwaysSelected).mpr
    rw [MeasureTheory.ae_iff]
    simpa [Classical.not_imp, Set.inter_comm] using hBad_alwaysSelected
  · apply (MeasureTheory.ae_restrict_iff' S.measurableSet_helpedSelected).mpr
    rw [MeasureTheory.ae_iff]
    simpa [Classical.not_imp, Set.inter_comm] using hBad_helpedSelected

end POLeeSystem

end PO
end Causalean
