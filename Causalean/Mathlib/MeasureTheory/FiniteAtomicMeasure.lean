/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Measures carried by finitely many atoms

This file provides decomposition, pointwise recovery, and integrability facts for
finite measures concentrated on a finite family of measurable atoms.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace Causalean.Mathlib.MeasureTheory

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- Let `μ` be a finite measure and `cell` an injective family of finitely many points of the
sample space, indexed by a finite type `ι`. If [every singleton `{cell i}` is
measurable](hyp:hcell) and [`μ` assigns its full mass to the range of `cell`, i.e. `μ` puts no
mass outside these finitely many points](hyp:hrange), then [`μ` equals the sum, over the index
`i`, of the point mass `μ {cell i}` scaling the Dirac measure at `cell i`](goal). -/
lemma measure_eq_fin_sum_smul_dirac_of_range
    (μ : Measure 𝒳) [IsFiniteMeasure μ] {ι : Type*} [Fintype ι]
    (cell : ι ↪ 𝒳) (hcell : ∀ i, MeasurableSet {cell i})
    (hrange : μ (Set.range cell) = μ Set.univ) :
    μ = ∑ i, μ {cell i} • Measure.dirac (cell i) := by
  have hrangeMeas : MeasurableSet (Set.range cell) := by
    rw [show Set.range cell = ⋃ i, {cell i} by
      ext x
      simp]
    exact MeasurableSet.iUnion hcell
  have hae : ∀ᵐ x ∂μ, x ∈ Set.range cell := by
    change Set.range cell ∈ ae μ
    rw [mem_ae_iff, measure_compl hrangeMeas (measure_ne_top μ _), hrange]
    simp
  ext A hA
  rw [← Measure.measure_inter_eq_of_ae hae]
  rw [show Set.range cell ∩ A = ⋃ i, ({cell i} ∩ A) by
    ext x
    constructor
    · rintro ⟨⟨i, hix⟩, hxA⟩
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
      exact ⟨i, hix.symm, hxA⟩
    · intro hx
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff] at hx
      obtain ⟨i, hxi, hxA⟩ := hx
      exact ⟨⟨i, hxi.symm⟩, hxA⟩]
  rw [measure_iUnion]
  · simp only [Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hA, tsum_fintype]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hmem : cell i ∈ A
    · simp [hmem]
    · have hinter : {cell i} ∩ A = ∅ := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨rfl, hxA⟩
          exact (hmem hxA).elim
        · simp
      simp [hinter, hmem]
  · intro i j hij
    change Disjoint ({cell i} ∩ A) ({cell j} ∩ A)
    rw [Set.disjoint_left]
    intro x hxi hxj
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff] at hxi hxj
    exact hij ((cell.injective (hxi.1.symm.trans hxj.1)))
  · intro i
    exact (hcell i).inter hA

/-- An almost-sure property holds at every point to which the measure assigns nonzero mass. -/
lemma property_at_of_ae_of_singleton_pos
    (μ : Measure 𝒳) (p : 𝒳 → Prop) {x : 𝒳}
    (hp : ∀ᵐ y ∂μ, p y) (hx : μ {x} ≠ 0) :
    p x := by
  by_contra hpx
  have hnull : μ {y | ¬p y} = 0 := by
    change {y | p y} ∈ ae μ at hp
    rw [mem_ae_iff] at hp
    simpa only [Set.compl_setOf] using hp
  apply hx
  exact measure_mono_null (by simpa [Set.singleton_subset_iff]) hnull

/-- Every strongly measurable normed-vector-valued function is integrable under a finite measure
concentrated on finitely many measurable points. -/
lemma integrable_of_finite_atomic_support
    (μ : Measure 𝒳) [IsFiniteMeasure μ] {ι : Type*} [Finite ι]
    (cell : ι ↪ 𝒳) (hcell : ∀ i, MeasurableSet {cell i})
    (hrange : μ (Set.range cell) = μ Set.univ) {E : Type*} [NormedAddCommGroup E]
    (f : 𝒳 → E)
    (hf : StronglyMeasurable f) :
    Integrable f μ := by
  letI := Fintype.ofFinite ι
  rw [measure_eq_fin_sum_smul_dirac_of_range μ cell hcell hrange]
  apply integrable_finset_sum_measure.2
  intro i hi
  exact
    (integrable_dirac' hf (by simp)).smul_measure
      (measure_ne_top μ {cell i})

end Causalean.Mathlib.MeasureTheory
