/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.ID.DiscreteID.Mass
import Causalean.SCM.ID.Identifiable

/-!
# Positivity assumptions for discrete ID formulas

The discrete ID lane uses ratio-based conditional masses.  This file records the
nonzero point-mass assumptions needed to make those ratios meaningful.  The
default model-level predicate is full observational support on every observed
assignment at every fixed slice; later formula-level soundness lemmas can weaken
it to only the denominators actually used by a concrete formula.

Important declarations are `PositiveMass`, `DiscretePositive`, and
`StandardDiscretePositive`, together with transport lemmas showing that positive
point mass is preserved by measurable surjections and coordinate projections.
These lemmas turn full observational support into the denominator positivity
needed by `conditionalMass`.
-/

namespace Causalean.SCM.ID.DiscreteID

open scoped MeasureTheory ENNReal

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- A measure has full point-mass support when every singleton has nonzero mass. -/
def PositiveMass {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) : Prop :=
  ∀ x : α, singletonMass μ x ≠ 0

/-- Under positive point mass at every point, almost-everywhere equality is
pointwise equality. -/
theorem PositiveMass.eq_of_ae_eq
    {α β : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (hμ : PositiveMass μ) {f g : α → β} (hfg : f =ᵐ[μ] g) :
    ∀ x : α, f x = g x :=
  eq_of_ae_eq_of_forall_singletonMass_ne_zero hμ hfg

/-- A discrete SCM has full observational support on every observed assignment,
at every fixed-value slice.  This is strong but non-vacuous, and it is the
safe default assumption for first-pass discrete ID soundness. -/
def DiscretePositive (M : Causalean.SCM N Ω) : Prop :=
  ∀ s : M.FixedValues, PositiveMass (M.obsKernel s)

/-- Positive point mass is preserved by a measurable surjection. -/
theorem PositiveMass.map_of_surjective
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β]
    {μ : MeasureTheory.Measure α} {f : α → β}
    (hf : Measurable f) (hμ : PositiveMass μ) (hsurj : Function.Surjective f) :
    PositiveMass (μ.map f) := by
  intro y
  rcases hsurj y with ⟨x, hx⟩
  rw [singletonMass_map μ hf y]
  intro hzero
  have hsubset : ({x} : Set α) ⊆ f ⁻¹' ({y} : Set β) := by
    intro z hz
    change f z = y
    rw [show z = x by simpa using hz, hx]
  have hle : μ ({x} : Set α) ≤ μ (f ⁻¹' ({y} : Set β)) :=
    MeasureTheory.measure_mono hsubset
  have hxzero : singletonMass μ x = 0 := by
    rw [singletonMass_apply]
    exact le_antisymm (by simpa [hzero] using hle) (zero_le _)
  exact hμ x hxzero

/-- Positive point mass is preserved by coordinate projection. -/
theorem PositiveMass.map_valuesProjection
    {M : Type*} [DecidableEq M] [Fintype M]
    {I J : Finset M} {Ω' : M → Type*}
    [∀ m, MeasurableSpace (Ω' m)] [∀ m, Nonempty (Ω' m)]
    [∀ m, MeasurableSingletonClass (Ω' m)]
    {μ : MeasureTheory.Measure (ValuesOn I Ω')}
    (hμ : PositiveMass μ) (hJI : J ⊆ I) :
    PositiveMass (μ.map (valuesProjection (Ω := Ω') hJI)) :=
  PositiveMass.map_of_surjective (measurable_valuesProjection hJI) hμ
    (valuesProjection_surjective hJI)

/-- Positive point mass can be pulled back across an injective measurable map
when the pushed-forward measure is positive at every image value. -/
theorem PositiveMass.of_map_injective
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β]
    {μ : MeasureTheory.Measure α} {f : α → β}
    (hf : Measurable f) (hinj : Function.Injective f)
    (hmap : PositiveMass (μ.map f)) :
    PositiveMass μ := by
  intro x
  have hxmap : singletonMass (μ.map f) (f x) ≠ 0 := hmap (f x)
  rw [singletonMass_map μ hf (f x)] at hxmap
  have hpre : f ⁻¹' ({f x} : Set β) = ({x} : Set α) := by
    ext y
    constructor
    · intro hy
      have hfy : f y = f x := by simpa using hy
      exact hinj hfy
    · intro hy
      have hyx : y = x := by simpa using hy
      simp [hyx]
  rw [hpre] at hxmap
  exact hxmap

/-- A positive marginal point mass is exactly the nonzero denominator needed by
the finite conditional-mass ratio. -/
theorem conditionalDenominator_ne_zero_of_positive_marginal
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)}
    (hμ : PositiveMass (μ.map Prod.snd)) (b : β) :
    conditionalDenominator μ b ≠ 0 :=
  hμ b

/-- The structural assumptions for the first discrete ID soundness target. -/
def StandardDiscretePositive (M : Causalean.SCM N Ω) : Prop :=
  M.isStandard ∧ DiscretePositive M

end Causalean.SCM.ID.DiscreteID
