/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.ID.Density.ReferenceMeasure
import Mathlib.Probability.Kernel.RadonNikodym

/-! # Finite reference measures for discrete ID densities

When every node value space is finite with measurable singletons, the per-node
reference measures in a σ-finite reference family are finite.  Consequently the
finite products `jointRef ref I` are finite as well.  This file packages those
instances and the simple measurability fact used by the finite/discrete
chain-rule density proof.
-/

namespace Causalean.SCM

open scoped MeasureTheory ProbabilityTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- Every random or fixed SWIG-node value space is finite when every base-node value space is finite. -/
instance instFintypeSwigΩ [∀ n, Fintype (Ω n)] :
    ∀ sn : SWIGNode N, Fintype (swigΩ Ω sn)
  | .random _ => inferInstance
  | .fixed _ => inferInstance

/-- Every random or fixed SWIG-node value space has measurable singletons when every base-node value space has measurable singletons. -/
instance instMeasurableSingletonClassSwigΩ [∀ n, MeasurableSingletonClass (Ω n)] :
    ∀ sn : SWIGNode N, MeasurableSingletonClass (swigΩ Ω sn)
  | .random _ => inferInstance
  | .fixed _ => inferInstance

/-- A σ-finite measure on a finite measurable-singleton space is finite. -/
lemma isFiniteMeasure_of_finite_measurableSingleton
    {α : Type*} [MeasurableSpace α] [Finite α] [MeasurableSingletonClass α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ] :
    MeasureTheory.IsFiniteMeasure μ := by
  refine ⟨?_⟩
  have hcover :
      (Set.univ : Set α) = ⋃ x ∈ (Set.univ : Set α), ({x} : Set α) := by
    ext x
    simp
  rw [hcover]
  exact MeasureTheory.measure_biUnion_lt_top Set.finite_univ
    (fun x _ => MeasureTheory.measure_singleton_lt_top (μ := μ) (a := x))

/-- Each coordinate reference measure is finite on finite measurable-singleton node spaces. -/
instance instIsFiniteMeasure_refMu [∀ n, Fintype (Ω n)]
    [∀ n, MeasurableSingletonClass (Ω n)]
    (ref : ReferenceMeasures Ω) (v : SWIGNode N) :
    MeasureTheory.IsFiniteMeasure (ref.μ v) := by
  haveI : MeasureTheory.SigmaFinite (ref.μ v) := ref.sigmaFinite v
  exact isFiniteMeasure_of_finite_measurableSingleton (ref.μ v)

/-- The finite product reference measure is finite on finite measurable-singleton node spaces. -/
instance instIsFiniteMeasure_jointRef [∀ n, Fintype (Ω n)]
    [∀ n, MeasurableSingletonClass (Ω n)]
    (ref : ReferenceMeasures Ω) (I : Finset (SWIGNode N)) :
    MeasureTheory.IsFiniteMeasure (jointRef ref I) := by
  unfold jointRef
  infer_instance

/-- A reference family is faithful when every single coordinate value has nonzero reference mass.

Counting reference measures on finite spaces satisfy this full-support condition. -/
def ReferenceFaithful (ref : ReferenceMeasures Ω) : Prop :=
  ∀ (v : SWIGNode N) (x : swigΩ Ω v), ref.μ v {x} ≠ 0

/-- Any measure is absolutely continuous with respect to a measure that gives every singleton nonzero mass.

A null set for such a reference measure cannot contain any point. -/
lemma absolutelyContinuous_of_singleton_ne_zero {α : Type*} [MeasurableSpace α]
    (μ ν : MeasureTheory.Measure α) (hν : ∀ x : α, ν ({x} : Set α) ≠ 0) :
    μ ≪ ν := by
  refine MeasureTheory.Measure.AbsolutelyContinuous.mk ?_
  intro s _hs hνs
  have hs_empty : s = ∅ := by
    ext x
    constructor
    · intro hx
      exfalso
      have hsingle_subset : ({x} : Set α) ⊆ s := by
        intro y hy
        have hyx : y = x := by simpa using hy
        simpa [hyx] using hx
      have hle : ν ({x} : Set α) ≤ ν s := MeasureTheory.measure_mono hsingle_subset
      have hzero : ν ({x} : Set α) = 0 :=
        le_antisymm (by simpa [hνs] using hle) (zero_le _)
      exact hν x hzero
    · intro hx
      cases hx
  simp [hs_empty]

/-- A faithful reference family gives every point in a finite coordinate product nonzero joint reference mass. -/
lemma jointRef_singleton_ne_zero [∀ n, MeasurableSingletonClass (Ω n)]
    (ref : ReferenceMeasures Ω) (href : ReferenceFaithful ref)
    (I : Finset (SWIGNode N)) (x : ValuesOn I (swigΩ Ω)) :
    jointRef ref I ({x} : Set (ValuesOn I (swigΩ Ω))) ≠ 0 := by
  classical
  unfold jointRef
  rw [MeasureTheory.Measure.pi_singleton]
  exact Finset.prod_ne_zero_iff.mpr (by
    intro i _hi
    exact href i.val (x i))

/-- Every measure on a finite coordinate product is dominated by a faithful product reference measure. -/
lemma absolutelyContinuous_jointRef_of_faithful [∀ n, MeasurableSingletonClass (Ω n)]
    (ref : ReferenceMeasures Ω) (href : ReferenceFaithful ref)
    (I : Finset (SWIGNode N)) (μ : MeasureTheory.Measure (ValuesOn I (swigΩ Ω))) :
    μ ≪ jointRef ref I := by
  exact absolutelyContinuous_of_singleton_ne_zero μ (jointRef ref I)
    (jointRef_singleton_ne_zero ref href I)

/-- Every fibre Radon-Nikodym derivative selector is almost-everywhere measurable on a finite measurable-singleton product. -/
lemma aemeasurable_fiber_rnDeriv_of_finite
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Finite α] [Finite β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (ν : MeasureTheory.Measure α) (ρ : MeasureTheory.Measure β)
    (κ : ProbabilityTheory.Kernel α β) :
    AEMeasurable (fun p : α × β => (κ p.1).rnDeriv ρ p.2) (ν.prod ρ) :=
  (measurable_of_finite (fun p : α × β => (κ p.1).rnDeriv ρ p.2)).aemeasurable

end Causalean.SCM
