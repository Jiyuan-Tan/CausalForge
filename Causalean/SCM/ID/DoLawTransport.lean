/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.SCM.ID.Backdoor

/-! # Structural transport of the do-observational law to `doKernelY`

The post-intervention `Y`-marginal kernel `doKernelY` is built from the
do-observational law `(M.fixSet X).obsKernel` by a `comap` (extend the fixed
slice by the treatment value) followed by a `map` (project to the outcomes `Y`):

`doKernelY M X … Y … s₀ = ((M.fixSet X).obsKernel.comap (fixSetExtend s₀)).map π_Y`.

The `comap`/`map` data (`fixSetExtend`, the `Y`-projection) and the
intermediate value-space types depend on `M` **only through its SWIG graph**
(`observed`, `fixed`, which `fixSet` preserves/enlarges structurally) and the base
slice `s₀`.  Therefore two models sharing a SWIG graph whose do-observational laws
agree produce the *same* `doKernelY`.

This isolates the genuine identification content — that the do-observational laws
agree — from the purely structural transport performed here.  The identification
content is discharged elsewhere (the Tian g-formula in
`GraphicalThms/DoGFormula` and its recursive/discrete soundness layers); this file
is graph/measure bookkeeping only and makes no appeal to `idSucceeds` or any
reference measure.
-/

namespace Causalean.SCM.ID

open scoped MeasureTheory ProbabilityTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- The **`Y`-marginal of the do-observational law**: push `(M.fixSet X).obsKernel`
forward along the projection to the outcome coordinates `Y`.  This is the only
part of the do-law that the post-intervention `Y`-marginal kernel `doKernelY`
depends on — `doKernelY` is this marginal, reindexed in the treatment value by the
`comap` extension.  Crucially this is the *identifiable* object: the full do-law
over all observed nodes is not a functional of the observational law, but its
`Y`-marginal (more precisely its `An_{G_X}(Y)`-marginal, of which this is a further
projection) is. -/
noncomputable def doObsKernelYMarginal
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N)) (hY : Y ⊆ M.observed) :
    ProbabilityTheory.Kernel (M.fixSet X hObs hFix).FixedValues
      (ValuesOn Y (swigΩ Ω)) :=
  (M.fixSet X hObs hFix).obsKernel.map
    (valuesProjection ((SCM.fixSet_observed M X hObs hFix).symm ▸ hY))

/-- **Structural transport.**  For two models sharing a SWIG graph, equal (heterogeneous)
`Y`-marginals of the do-observational law give equal post-intervention `Y`-marginal
kernels.

`doKernelY` is the `Y`-marginal `doObsKernelYMarginal` reindexed in the treatment
value by the structural `comap` extension; the shared SWIG graph
(through `observed`/`fixed`) and the base slice `s₀` are the only other data.  So
two models sharing a SWIG graph whose do-law `Y`-marginals agree produce the same
`doKernelY`.  The hypothesis is the `Y`-marginal (not the full do-law) because that
is exactly what `doKernelY` consumes — and the only part the identification content
delivers.  The `HEq` hypotheses are needed because the intermediate value spaces
`(M.fixSet X).observed`/`.fixed` are only propositionally — not definitionally —
equal across the two models. -/
theorem doKernelY_eq_of_doObsKernel_heq
    (X : Finset N) (Y : Finset (SWIGNode N))
    (M₁ M₂ : Causalean.SCM N Ω)
    (hsg : M₁.toSWIGGraph = M₂.toSWIGGraph)
    (hObs₁ : ∀ D ∈ X, SWIGNode.random D ∈ M₁.observed)
    (hFix₁ : ∀ D ∈ X, SWIGNode.fixed D ∉ M₁.fixed)
    (hObs₂ : ∀ D ∈ X, SWIGNode.random D ∈ M₂.observed)
    (hFix₂ : ∀ D ∈ X, SWIGNode.fixed D ∉ M₂.fixed)
    (hY₁ : Y ⊆ M₁.observed) (hY₂ : Y ⊆ M₂.observed)
    (s0₁ : M₁.FixedValues) (s0₂ : M₂.FixedValues) (hs0 : HEq s0₁ s0₂)
    (hdoobsY :
      HEq (doObsKernelYMarginal M₁ X hObs₁ hFix₁ Y hY₁)
          (doObsKernelYMarginal M₂ X hObs₂ hFix₂ Y hY₂)) :
    M₁.doKernelY X hObs₁ hFix₁ Y hY₁ s0₁
      = M₂.doKernelY X hObs₂ hFix₂ Y hY₂ s0₂ := by
  obtain ⟨⟨dag₁, fixed₁, observed₁, unobserved₁,
           fio₁, oi₁, od₁, oou₁, foi₁, fou₁, aic₁, dc₁, foff₁, aco₁⟩,
         eT₁, iota₁, sf₁, mf₁, lD₁, pL₁⟩ := M₁
  obtain ⟨⟨dag₂, fixed₂, observed₂, unobserved₂,
           fio₂, oi₂, od₂, oou₂, foi₂, fou₂, aic₂, dc₂, foff₂, aco₂⟩,
         eT₂, iota₂, sf₂, mf₂, lD₂, pL₂⟩ := M₂
  cases hsg
  have hs0_eq : s0₁ = s0₂ := eq_of_heq hs0
  subst hs0_eq
  have hmapY_eq : _ = _ := eq_of_heq hdoobsY
  unfold SCM.doKernelY doObsKernelYMarginal at *
  ext t A hA
  -- Peel `map`/`comap` to the fibre, then fold the fibre back into `obsKernel.map π_Y`
  -- so the marginal hypothesis `hmapY_eq` rewrites both sides to the same kernel.
  rw [ProbabilityTheory.Kernel.map_apply _ (measurable_valuesProjection _),
      ProbabilityTheory.Kernel.comap_apply,
      ProbabilityTheory.Kernel.map_apply _ (measurable_valuesProjection _),
      ProbabilityTheory.Kernel.comap_apply,
      ← ProbabilityTheory.Kernel.map_apply _ (measurable_valuesProjection _),
      ← ProbabilityTheory.Kernel.map_apply _ (measurable_valuesProjection _),
      hmapY_eq]
  -- Both sides are now the same `Y`-marginal kernel; the residual fibre arguments
  -- differ only in proof-irrelevant SWIG-graph proof fields.
  congr 1

end Causalean.SCM.ID
