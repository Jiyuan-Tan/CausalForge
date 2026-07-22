/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.Model.Kernel
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! # Reference measure and joint observational density

A *reference measure family* assigns one σ-finite measure to every SWIG-node value
space: the counting measure for a discrete node, Lebesgue measure for a continuous
node, or any σ-finite choice.  Its finite product over a node set is the joint
reference measure, and a gSCM is *dominated* when its observational kernel is
absolutely continuous with respect to that joint reference.  In the dominated case
the observational law has a joint density (Radon–Nikodym derivative), and the law
is recovered from the density.

This is the foundation for the density-assisted c-component factorization: Tian's
assembly step `P(v) = ∏_C Q[C]` is a commutative regrouping of scalar density
factors, which has no kernel-composition analogue.  The downstream ID theorems in
this slice specialize these reference-measure definitions to finite node value
spaces with measurable singleton sets and faithful finite-product references.
-/

namespace Causalean.SCM

open scoped MeasureTheory ProbabilityTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- A reference measure family assigns a sigma-finite reference measure to every random or fixed node value space.

Take the counting measure on discrete nodes and Lebesgue measure on continuous
nodes; any sigma-finite choice is allowed. This is the dominating measure
against which observational densities are formed. -/
structure ReferenceMeasures (Ω : N → Type*) [∀ n, MeasurableSpace (Ω n)] where
  /-- The reference measure on the value space of node `v`. -/
  μ : ∀ v : SWIGNode N, MeasureTheory.Measure (swigΩ Ω v)
  /-- Each reference measure is σ-finite. -/
  sigmaFinite : ∀ v, MeasureTheory.SigmaFinite (μ v)

attribute [instance] ReferenceMeasures.sigmaFinite

/-- The joint reference measure is the finite product of the per-node reference measures over a node set.

For counting references this is counting measure on the discrete product; for
Lebesgue references it is Lebesgue measure on the continuous product. -/
noncomputable def jointRef (ref : ReferenceMeasures Ω) (I : Finset (SWIGNode N)) :
    MeasureTheory.Measure (ValuesOn I (swigΩ Ω)) :=
  MeasureTheory.Measure.pi (fun i : {i // i ∈ I} => ref.μ i.val)

/-- Finite products of sigma-finite coordinate reference measures are sigma-finite. -/
instance instSigmaFiniteJointRef (ref : ReferenceMeasures Ω) (I : Finset (SWIGNode N)) :
    MeasureTheory.SigmaFinite (jointRef ref I) := by
  unfold jointRef
  infer_instance

/-- A structural causal model is dominated when each observational law is absolutely continuous with respect to the joint reference measure.

Equivalently, the observational law admits a joint density at every fixed-value
slice. -/
def DominatedObs (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) : Prop :=
  ∀ s : M.FixedValues, M.obsKernel s ≪ jointRef ref M.observed

/-- The joint observational density is the Radon-Nikodym derivative of the observational law with respect to the observed-node reference product. -/
noncomputable def obsDensity (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    (s : M.FixedValues) : ValuesOn M.observed (swigΩ Ω) → ENNReal :=
  (M.obsKernel s).rnDeriv (jointRef ref M.observed)

/-- In a dominated model, weighting the joint reference measure by the observational density recovers the observational law. -/
theorem withDensity_obsDensity_eq (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    (hdom : DominatedObs M ref) (s : M.FixedValues) :
    (jointRef ref M.observed).withDensity (M.obsDensity ref s) = M.obsKernel s := by
  unfold obsDensity
  exact MeasureTheory.Measure.withDensity_rnDeriv_eq _ _ (hdom s)

/-- Within one model, two fixed-value slices with almost-everywhere equal joint densities have the same observational law.

The cross-model determination used for soundness is assembled downstream, where
the shared graph equality lets the two laws be compared in one type. -/
theorem obsKernel_eq_of_obsDensity_ae_eq
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    (hdom : DominatedObs M ref) (s₁ s₂ : M.FixedValues)
    (hdens : (M.obsDensity ref s₁)
        =ᵐ[jointRef ref M.observed] (M.obsDensity ref s₂)) :
    M.obsKernel s₁ = M.obsKernel s₂ := by
  rw [← withDensity_obsDensity_eq M ref hdom s₁,
    ← withDensity_obsDensity_eq M ref hdom s₂,
    MeasureTheory.withDensity_congr_ae hdens]

end Causalean.SCM
