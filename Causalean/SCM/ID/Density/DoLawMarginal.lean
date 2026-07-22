/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.ID.Density.ReferenceMeasure

/-! # Foundational helpers for the do-law Y-marginal

This file collects foundational facts used to identify the `Y`-marginal of the
do-law from observational densities.  It currently provides cross-model density
transport: two structural causal models sharing the same SWIG graph and the same
observational kernel also share the same observational density, so densities
transport across models that agree on those data.  This is the step that turns the
hypothesis "the two models have the same observational law" into "the two models
have the same observational density", from which the recovered c-factors — and
hence the identifiable do-law `Y`-marginal — are read off.
-/

namespace Causalean.SCM

open scoped MeasureTheory ProbabilityTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- **Cross-model density transport.** If two structural causal models `M₁` and
`M₂` share the same SWIG graph and have heterogeneously-equal observational
kernels, then their observational densities are heterogeneously equal.  After
unifying the SWIG-graph data the observed-value types coincide, the observational
kernels become literally equal, and the density is the Radon–Nikodym derivative of
that kernel against a fixed reference measure. -/
lemma obsDensity_heq_of_obsKernel_heq
    (M₁ M₂ : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    (hsg : M₁.toSWIGGraph = M₂.toSWIGGraph)
    (hobs : HEq M₁.obsKernel M₂.obsKernel) :
    HEq (M₁.obsDensity ref) (M₂.obsDensity ref) := by
  obtain ⟨⟨dag₁, fixed₁, observed₁, unobserved₁,
           fio₁, oi₁, od₁, oou₁, foi₁, fou₁, aic₁, dc₁, foff₁, aco₁⟩,
         eT₁, iota₁, sf₁, mf₁, lD₁, pL₁⟩ := M₁
  obtain ⟨⟨dag₂, fixed₂, observed₂, unobserved₂,
           fio₂, oi₂, od₂, oou₂, foi₂, fou₂, aic₂, dc₂, foff₂, aco₂⟩,
         eT₂, iota₂, sf₂, mf₂, lD₂, pL₂⟩ := M₂
  cases hsg
  -- The observed-value types now coincide, so `hobs` is a homogeneous equality.
  have hk : _ = _ := eq_of_heq hobs
  -- `obsDensity ref = fun s => (obsKernel s).rnDeriv (jointRef ref observed)`.
  apply heq_of_eq
  unfold obsDensity
  rw [hk]

/-- **Cross-model law transport (converse).** If two dominated structural causal
models `M₁` and `M₂` share the same SWIG graph and have heterogeneously-equal
observational densities, then their observational kernels are heterogeneously
equal.  After unifying the SWIG-graph data the observed-value types coincide and
the densities become literally equal; weighting the common joint reference by that
density recovers each observational law (`withDensity_obsDensity_eq`), so the two
laws agree.  This is the converse of `obsDensity_heq_of_obsKernel_heq`: under
dominance, equal density and equal law are interchangeable, letting the
kernel-level identification tools be driven from a density hypothesis. -/
lemma obsKernel_heq_of_obsDensity_heq
    (M₁ M₂ : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    (hsg : M₁.toSWIGGraph = M₂.toSWIGGraph)
    (hdom₁ : DominatedObs M₁ ref) (hdom₂ : DominatedObs M₂ ref)
    (hden : HEq (M₁.obsDensity ref) (M₂.obsDensity ref)) :
    HEq M₁.obsKernel M₂.obsKernel := by
  obtain ⟨⟨dag₁, fixed₁, observed₁, unobserved₁,
           fio₁, oi₁, od₁, oou₁, foi₁, fou₁, aic₁, dc₁, foff₁, aco₁⟩,
         eT₁, iota₁, sf₁, mf₁, lD₁, pL₁⟩ := M₁
  obtain ⟨⟨dag₂, fixed₂, observed₂, unobserved₂,
           fio₂, oi₂, od₂, oou₂, foi₂, fou₂, aic₂, dc₂, foff₂, aco₂⟩,
         eT₂, iota₂, sf₂, mf₂, lD₂, pL₂⟩ := M₂
  cases hsg
  -- The observed-value types now coincide, so `hden` is a homogeneous equality.
  have hd : _ = _ := eq_of_heq hden
  apply heq_of_eq
  refine ProbabilityTheory.Kernel.ext (fun s => ?_)
  rw [← withDensity_obsDensity_eq _ ref hdom₁ s,
    ← withDensity_obsDensity_eq _ ref hdom₂ s, hd]

end Causalean.SCM
