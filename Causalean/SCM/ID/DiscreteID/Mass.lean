/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.ID.Density.FiniteReference
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Finite masses for discrete ID

This file provides the finite-measure primitives used by the discrete ID lane:
singleton masses, marginal singleton masses, and conditional masses as ratios.
The definitions are intentionally point-mass based, so later ID proofs can state
positivity on the actual denominators used by a formula.

The main API includes:

* `singletonMass`, `marginalMass`, `conditionalMass`, and
  `conditionalDenominator` for writing finite observational formulas.
* `measure_eq_of_singletonMass_eq` and `valuesOn_measure_eq_of_singletonMass_eq`,
  which reduce equality of finite/countable measures to equality of all singleton
  masses.
* `singletonMass_map_eq_sum_fiber`, `singletonMass_bind_eq_sum`, and the
  point-mass specializations for constant or degenerate mixtures.
* `conditionalMass_mul_denominator`, the algebraic cancellation lemma that
  recovers the joint point mass from a conditional-mass ratio once the actual
  denominator is nonzero and finite.
-/

namespace Causalean.SCM.ID.DiscreteID

open scoped MeasureTheory ProbabilityTheory ENNReal

/-- The mass that a measure assigns to a single point. -/
noncomputable def singletonMass {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (x : α) : ENNReal :=
  μ ({x} : Set α)

/-- The marginal mass of a selected coordinate value. -/
noncomputable def marginalMass {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : MeasureTheory.Measure α) (f : α → β) (_hf : Measurable f) (y : β) : ENNReal :=
  singletonMass (μ.map f) y

/-- A discrete conditional mass, written as a ratio of a joint point mass to a
marginal point mass.  A sound ID formula must separately carry positivity for
the denominator when it uses this value. -/
noncomputable def conditionalMass {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : MeasureTheory.Measure (α × β)) (a : α) (b : β) : ENNReal :=
  singletonMass μ (a, b) / singletonMass (μ.map Prod.snd) b

/-- The denominator used by `conditionalMass`. -/
noncomputable def conditionalDenominator {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : MeasureTheory.Measure (α × β)) (b : β) : ENNReal :=
  singletonMass (μ.map Prod.snd) b

@[simp] theorem singletonMass_apply {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (x : α) :
    singletonMass μ x = μ ({x} : Set α) :=
  rfl

/-- Measures on a countable space are equal when all singleton masses agree. -/
theorem measure_eq_of_singletonMass_eq {α : Type*} [MeasurableSpace α] [Countable α]
    {μ ν : MeasureTheory.Measure α}
    (h : ∀ x : α, singletonMass μ x = singletonMass ν x) :
    μ = ν :=
  MeasureTheory.Measure.ext_of_singleton h

/-- An almost-everywhere equality is pointwise when every singleton has nonzero
mass. -/
theorem eq_of_ae_eq_of_forall_singletonMass_ne_zero
    {α β : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {f g : α → β}
    (hμ : ∀ x : α, singletonMass μ x ≠ 0)
    (hfg : f =ᵐ[μ] g) :
    ∀ x : α, f x = g x := by
  intro x
  by_contra hx
  have hnull : μ {y | ¬ f y = g y} = 0 :=
    MeasureTheory.ae_iff.mp hfg
  have hsubset : ({x} : Set α) ⊆ {y | ¬ f y = g y} := by
    intro y hy
    have hyx : y = x := by simpa using hy
    simpa [hyx] using hx
  have hxzero : singletonMass μ x = 0 := by
    rw [singletonMass_apply]
    exact MeasureTheory.measure_mono_null hsubset hnull
  exact hμ x hxzero

/-- The singleton mass of a mapped measure is the mass of the corresponding
fibre. -/
theorem singletonMass_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β]
    (μ : MeasureTheory.Measure α) {f : α → β} (hf : Measurable f) (y : β) :
    singletonMass (μ.map f) y = μ (f ⁻¹' ({y} : Set β)) := by
  rw [singletonMass_apply, MeasureTheory.Measure.map_apply hf (MeasurableSet.singleton y)]

/-- If a measurable map is pointwise constant, the pushed-forward measure has
all mass at that constant value. -/
theorem singletonMass_map_const_eq_univ
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β]
    (μ : MeasureTheory.Measure α) {f : α → β} (hf : Measurable f)
    (y0 : β) (hconst : ∀ x : α, f x = y0) :
    singletonMass (μ.map f) y0 = μ Set.univ := by
  rw [singletonMass_map μ hf y0]
  congr
  ext x
  simp [hconst x]

/-- If a measurable map is pointwise constant at `y0`, the pushed-forward
measure has zero singleton mass at every different value. -/
theorem singletonMass_map_const_eq_zero_of_ne
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β]
    (μ : MeasureTheory.Measure α) {f : α → β} (hf : Measurable f)
    (y0 y : β) (hconst : ∀ x : α, f x = y0) (hy : y ≠ y0) :
    singletonMass (μ.map f) y = 0 := by
  rw [singletonMass_map μ hf y]
  have hpre : f ⁻¹' ({y} : Set β) = (∅ : Set α) := by
    ext x
    have hy' : y0 ≠ y := fun h => hy h.symm
    simp [hconst x, hy']
  rw [hpre, MeasureTheory.measure_empty]

/-- A pointwise constant measurable map from a probability measure gives unit
singleton mass at the constant value. -/
theorem singletonMass_map_const_eq_one
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β]
    (μ : MeasureTheory.Measure α) {f : α → β} (hf : Measurable f)
    (y0 : β) (hconst : ∀ x : α, f x = y0)
    (hμ : μ Set.univ = 1) :
    singletonMass (μ.map f) y0 = 1 := by
  rw [singletonMass_map_const_eq_univ μ hf y0 hconst, hμ]

/-- On a finite measurable-singleton space, the singleton mass of a pushed-forward
measure is the finite sum of singleton masses over the fiber. -/
theorem singletonMass_map_eq_sum_fiber
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype α] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DecidableEq β]
    (μ : MeasureTheory.Measure α) {f : α → β} (hf : Measurable f) (y : β) :
    singletonMass (μ.map f) y =
      ∑ x : α, if f x = y then singletonMass μ x else 0 := by
  classical
  let s : Finset α := Finset.univ.filter fun x => f x = y
  have hs : (s : Set α) = f ⁻¹' ({y} : Set β) := by
    ext x
    simp [s]
  calc
    singletonMass (μ.map f) y = μ (f ⁻¹' ({y} : Set β)) := by
      exact singletonMass_map μ hf y
    _ = μ (s : Set α) := by rw [← hs]
    _ = ∑ x ∈ s, μ ({x} : Set α) := by
      rw [← MeasureTheory.sum_measure_singleton (μ := μ) (s := s)]
    _ = ∑ x : α, if f x = y then singletonMass μ x else 0 := by
      have hsum :
          (∑ x : α, if f x = y then singletonMass μ x else 0) =
            ∑ x ∈ s, μ ({x} : Set α) := by
        simp [singletonMass, s, Finset.sum_filter]
      exact hsum.symm

/-- On a finite measurable-singleton space, the sum of all singleton masses is
the total mass of the measure. -/
theorem sum_singletonMass_eq_univ
    {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    (μ : MeasureTheory.Measure α) :
    (∑ x : α, singletonMass μ x) = μ Set.univ := by
  classical
  calc
    (∑ x : α, singletonMass μ x)
        = ∑ x ∈ (Finset.univ : Finset α), μ ({x} : Set α) := by
          simp [singletonMass]
    _ = μ ((Finset.univ : Finset α) : Set α) := by
          rw [MeasureTheory.sum_measure_singleton]
    _ = μ Set.univ := by
          simp

/-- On a finite measurable-singleton probability space, singleton masses sum to
one. -/
theorem sum_singletonMass_eq_one
    {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ] :
    (∑ x : α, singletonMass μ x) = 1 := by
  rw [sum_singletonMass_eq_univ]
  exact MeasureTheory.measure_univ

/-- On a finite source space, the singleton mass of a kernel mixture is the
finite weighted sum of the singleton masses of the kernel slices. -/
theorem singletonMass_comp_eq_sum
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype α] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : MeasureTheory.Measure α) (κ : ProbabilityTheory.Kernel α β) (y : β) :
    singletonMass (κ ∘ₘ μ) y =
      ∑ x : α, singletonMass μ x * singletonMass (κ x) y := by
  rw [singletonMass_apply,
    MeasureTheory.Measure.bind_apply (MeasurableSet.singleton y) κ.aemeasurable]
  rw [MeasureTheory.lintegral_fintype]
  simp [singletonMass, mul_comm]

/-- Alias for `singletonMass_comp_eq_sum` using the more descriptive "bind"
terminology common for measure mixtures. -/
theorem singletonMass_bind_eq_sum
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype α] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : MeasureTheory.Measure α) (κ : ProbabilityTheory.Kernel α β) (y : β) :
    singletonMass (κ ∘ₘ μ) y =
      ∑ x : α, singletonMass μ x * singletonMass (κ x) y :=
  singletonMass_comp_eq_sum μ κ y

/-- A finite kernel mixture has the common singleton mass of its slices when
the finite singleton masses of the mixing measure sum to one. -/
theorem singletonMass_comp_eq_of_const
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype α] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : MeasureTheory.Measure α) (κ : ProbabilityTheory.Kernel α β)
    (y : β) (c : ENNReal)
    (hμ : (∑ x : α, singletonMass μ x) = 1)
    (hconst : ∀ x : α, singletonMass (κ x) y = c) :
    singletonMass (κ ∘ₘ μ) y = c := by
  rw [singletonMass_comp_eq_sum]
  calc
    (∑ x : α, singletonMass μ x * singletonMass (κ x) y)
        = ∑ x : α, singletonMass μ x * c := by
          apply Finset.sum_congr rfl
          intro x _hx
          rw [hconst x]
    _ = (∑ x : α, singletonMass μ x) * c := by
          rw [Finset.sum_mul]
    _ = c := by
          rw [hμ, one_mul]

/-- A finite kernel mixture has the singleton mass of one slice when the mixing
measure is a point mass at that slice. -/
theorem singletonMass_comp_eq_of_pointMass
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Finite α] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : MeasureTheory.Measure α) (κ : ProbabilityTheory.Kernel α β)
    (x0 : α) (y : β)
    (hμ0 : singletonMass μ x0 = 1)
    (hμzero : ∀ x : α, x ≠ x0 → singletonMass μ x = 0) :
    singletonMass (κ ∘ₘ μ) y = singletonMass (κ x0) y := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  rw [singletonMass_comp_eq_sum]
  rw [Finset.sum_eq_single x0]
  · rw [hμ0, one_mul]
  · intro x _hx hx
    rw [hμzero x hx, zero_mul]
  · intro hx
    exact (hx (Finset.mem_univ x0)).elim

/-- Coordinate restriction is surjective when every omitted coordinate has at
least one default value. -/
theorem valuesProjection_surjective
    {M : Type*} [DecidableEq M] [Fintype M]
    {I J : Finset M} {Ω' : M → Type*}
    [∀ m, MeasurableSpace (Ω' m)] [∀ m, Nonempty (Ω' m)]
    (hJI : J ⊆ I) :
    Function.Surjective (valuesProjection (Ω := Ω') hJI) := by
  classical
  intro y
  refine ⟨fun i =>
    if h : i.val ∈ J then
      y ⟨i.val, h⟩
    else
      Classical.choice (inferInstance : Nonempty (Ω' i.val)), ?_⟩
  funext j
  simp [valuesProjection]

/-- Finite coordinate-product measures are determined by their point masses. -/
theorem valuesOn_measure_eq_of_singletonMass_eq
    {M : Type*} [DecidableEq M] [Fintype M]
    {Ω' : M → Type*} [∀ m, MeasurableSpace (Ω' m)] [∀ m, Countable (Ω' m)]
    (I : Finset M)
    {μ ν : MeasureTheory.Measure (ValuesOn I Ω')}
    (h : ∀ x : ValuesOn I Ω', singletonMass μ x = singletonMass ν x) :
    μ = ν :=
  measure_eq_of_singletonMass_eq h

@[simp] theorem conditionalDenominator_apply {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : MeasureTheory.Measure (α × β)) (b : β) :
    conditionalDenominator μ b = singletonMass (μ.map Prod.snd) b :=
  rfl

/-- Multiplying a discrete conditional mass by its actual denominator recovers
the joint point mass, provided that denominator is nonzero and finite. -/
theorem conditionalMass_mul_denominator {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : MeasureTheory.Measure (α × β)) (a : α) (b : β)
    (h0 : conditionalDenominator μ b ≠ 0)
    (htop : conditionalDenominator μ b ≠ ∞) :
    conditionalMass μ a b * conditionalDenominator μ b =
      singletonMass μ (a, b) := by
  rw [conditionalMass, conditionalDenominator]
  exact ENNReal.div_mul_cancel h0 htop

end Causalean.SCM.ID.DiscreteID
