/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.ID.Density.ChainRuleDensity

/-! # c-component regrouping of the chain-rule density

The joint observational density is a *scalar* product of one-node conditional
densities (`qFactorDensityProduct`).  Because scalar multiplication is
commutative, that product can be regrouped by c-component: collect the factors
whose node lies in each c-component of the graph.  This regrouping is exactly the
step that has no kernel-composition analogue — composed kernels cannot be
permuted to bring a non-contiguous c-component's factors together, but scalar
density factors can.

This file performs the regrouping (`qFactorDensityProduct_eq_prod_cComponentFactor`)
and isolates the per-component scalar factor `cComponentDensityFactor`, which the
next layer identifies with Tian's `Q[C]` density.
-/

namespace Causalean.SCM

open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- The **per-c-component density factor**: the product of the one-node
conditional density factors over exactly the observed nodes lying in the
c-component `C`.  This is the density-side analogue of Tian's c-factor `Q[C]`. -/
noncomputable def cComponentDensityFactor
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    (C : Finset (SWIGNode N))
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))] :
    ValuesOn M.observed (swigΩ Ω) → ENNReal :=
  fun x =>
    ∏ i ∈ Finset.univ.filter
        (fun i : Fin M.observed.card =>
          M.toSWIGGraph.cComponentOf (M.observedAt i).val = C),
      M.obsStepCondDensity ref s i x

/-- **c-component regrouping of the chain-rule density product.**

The product of all one-node conditional density factors equals the product, over
the c-components of the graph, of the per-component factors.  Pure commutative
`Finset` regrouping: each observed index is sent to the (unique) c-component
containing its node, and the fibers of that map partition the index set. -/
theorem qFactorDensityProduct_eq_prod_cComponentFactor
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.qFactorDensityProduct ref s x =
      ∏ C ∈ M.toSWIGGraph.cComponentSet, M.cComponentDensityFactor ref s C x := by
  classical
  have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin M.observed.card)),
      M.toSWIGGraph.cComponentOf (M.observedAt i).val ∈ M.toSWIGGraph.cComponentSet := by
    intro i _
    exact Finset.mem_image.mpr ⟨(M.observedAt i).val, (M.observedAt i).property, rfl⟩
  unfold qFactorDensityProduct cComponentDensityFactor
  exact (Finset.prod_fiberwise_of_maps_to hmaps
    (fun i => M.obsStepCondDensity ref s i x)).symm

/-- **Cross-model c-component density-factor transport.** If two structural
causal models share the same SWIG graph and have heterogeneously-equal
observational kernels, then every c-component density factor recovered from the
observational chain-rule density is heterogeneously equal across the two models.

The factor is a product of `obsStepCondDensity` terms, and each such term is a
Radon--Nikodym derivative of `obsStepCondKernel`, which is built functorially
from `obsKernel` and the shared graph. -/
lemma cComponentDensityFactor_heq_of_obsKernel_heq
    (M₁ M₂ : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    (C : Finset (SWIGNode N))
    (hsg : M₁.toSWIGGraph = M₂.toSWIGGraph)
    (hobs : HEq M₁.obsKernel M₂.obsKernel)
    [∀ s' : M₁.FixedValues, MeasureTheory.IsFiniteMeasure (M₁.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M₁.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M₁.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M₁.observed.card),
      Nonempty
        (ValuesOn ({(M₁.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M₁.FixedValues (ValuesOn (M₁.prefixNodes k) (swigΩ Ω))]
    [∀ s' : M₂.FixedValues, MeasureTheory.IsFiniteMeasure (M₂.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M₂.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M₂.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M₂.observed.card),
      Nonempty
        (ValuesOn ({(M₂.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M₂.FixedValues (ValuesOn (M₂.prefixNodes k) (swigΩ Ω))] :
    HEq (fun s => M₁.cComponentDensityFactor ref s C)
      (fun s => M₂.cComponentDensityFactor ref s C) := by
  obtain ⟨⟨dag₁, fixed₁, observed₁, unobserved₁,
           fio₁, oi₁, od₁, oou₁, foi₁, fou₁, aic₁, dc₁, foff₁, aco₁⟩,
         eT₁, iota₁, sf₁, mf₁, lD₁, pL₁⟩ := M₁
  obtain ⟨⟨dag₂, fixed₂, observed₂, unobserved₂,
           fio₂, oi₂, od₂, oou₂, foi₂, fou₂, aic₂, dc₂, foff₂, aco₂⟩,
         eT₂, iota₂, sf₂, mf₂, lD₂, pL₂⟩ := M₂
  cases hsg
  have hfio : fio₂ = fio₁ := Subsingleton.elim _ _
  subst fio₂
  have hoi : oi₂ = oi₁ := Subsingleton.elim _ _
  subst oi₂
  have hod : od₂ = od₁ := Subsingleton.elim _ _
  subst od₂
  have hoou : oou₂ = oou₁ := Subsingleton.elim _ _
  subst oou₂
  have hfoi : foi₂ = foi₁ := Subsingleton.elim _ _
  subst foi₂
  have hfou : fou₂ = fou₁ := Subsingleton.elim _ _
  subst fou₂
  have haic : aic₂ = aic₁ := Subsingleton.elim _ _
  subst aic₂
  have hdc : dc₂ = dc₁ := Subsingleton.elim _ _
  subst dc₂
  have hfoff : foff₂ = foff₁ := Subsingleton.elim _ _
  subst foff₂
  have haco : aco₂ = aco₁ := Subsingleton.elim _ _
  subst aco₂
  have hk : _ = _ := eq_of_heq hobs
  apply heq_of_eq
  funext s x
  unfold cComponentDensityFactor
  congr 1
  funext i
  unfold obsStepCondDensity obsStepCondKernel SCM.obsCondKernel SCM.obsCondPairKernel
  repeat' congr

end Causalean.SCM
