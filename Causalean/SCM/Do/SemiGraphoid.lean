/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.Model.SCM
import Causalean.SCM.Model.Kernel
import Causalean.SCM.Do.ValuesProjectionCI
import Mathlib.Probability.Independence.Conditional

/-! # Observational Conditional Independence

This file defines `ObsCondIndep`, conditional independence for projections of
the observed state of a structural causal model under an arbitrary finite
observational measure. It also proves the semi-graphoid rules used by the Markov
and do-calculus layers: `obsCondIndep_symm`, `obsCondIndep_subset_right`,
`obsCondIndep_decomposition`, `obsCondIndep_weak_union`, and
`obsCondIndep_contraction`. The corresponding `condIndep_valuesProjection_*`
theorems expose the same coordinate-projection facts directly for finite product
spaces.
-/

namespace Causalean

open scoped MeasureTheory ProbabilityTheory

namespace SCM

universe uN uΩ

variable {N : Type uN} [DecidableEq N] [Fintype N]
variable {Ω : N → Type uΩ} [∀ n, MeasurableSpace (Ω n)]

-- ============================================================
-- § 1. ObsCondIndep: conditional independence under a measure
--      on ObservedValues
-- ============================================================

/-- **Observational conditional independence.**

    `ObsCondIndep M X Y Z hX hY hZ μ` says that the `X`-projection and
    `Y`-projection of `M.ObservedValues` are conditionally independent given
    the `Z`-projection under the measure `μ`.

    Wraps Mathlib's `ProbabilityTheory.CondIndepFun` with the sub-σ-algebra
    `MeasurableSpace.comap (valuesProjection hZ) inferInstance`.

    In the SCM world the canonical `μ` is `Causalean.SCM.obsKernel M s` at some
    `s : M.FixedValues`, but the definition only needs the underlying measure
    so it is stated at that generality. -/
def ObsCondIndep (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.ObservedValues]
    (X Y Z : Finset (SWIGNode N))
    (hX : X ⊆ M.observed) (hY : Y ⊆ M.observed) (hZ : Z ⊆ M.observed)
    (μ : MeasureTheory.Measure M.ObservedValues)
    [MeasureTheory.IsFiniteMeasure μ] : Prop :=
  ProbabilityTheory.CondIndepFun
    (MeasurableSpace.comap (valuesProjection hZ) inferInstance)
    (comap_valuesProjection_le hZ)
    (valuesProjection hX)
    (valuesProjection hY)
    μ

-- ============================================================
-- § 2. Semi-graphoid axioms
-- ============================================================

/-- **Symmetry.** Conditional independence is symmetric in X and Y. -/
theorem obsCondIndep_symm (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.ObservedValues]
    {X Y W : Finset (SWIGNode N)}
    (hX : X ⊆ M.observed) (hY : Y ⊆ M.observed) (hW : W ⊆ M.observed)
    {μ : MeasureTheory.Measure M.ObservedValues} [MeasureTheory.IsFiniteMeasure μ]
    (h : ObsCondIndep M X Y W hX hY hW μ) :
    ObsCondIndep M Y X W hY hX hW μ :=
  h.symm

omit [DecidableEq N] [Fintype N] in
/-- Symmetry for `CondIndepFun` when coordinates are given by `valuesProjection`. -/
theorem condIndep_valuesProjection_symm
    {I X Y Z : Finset (SWIGNode N)}
    (hX : X ⊆ I) (hY : Y ⊆ I) (hZ : Z ⊆ I)
    [StandardBorelSpace (ValuesOn I (swigΩ Ω))]
    {μ : MeasureTheory.Measure (ValuesOn I (swigΩ Ω))}
    [MeasureTheory.IsFiniteMeasure μ]
    (h : ProbabilityTheory.CondIndepFun
      (MeasurableSpace.comap (valuesProjection (Ω := swigΩ Ω) hZ) inferInstance)
      (comap_valuesProjection_le (Ω' := swigΩ Ω) hZ)
      (valuesProjection (Ω := swigΩ Ω) hX)
      (valuesProjection (Ω := swigΩ Ω) hY)
      μ) :
    ProbabilityTheory.CondIndepFun
      (MeasurableSpace.comap (valuesProjection (Ω := swigΩ Ω) hZ) inferInstance)
      (comap_valuesProjection_le (Ω' := swigΩ Ω) hZ)
      (valuesProjection (Ω := swigΩ Ω) hY)
      (valuesProjection (Ω := swigΩ Ω) hX)
      μ :=
  h.symm

omit [DecidableEq N] [Fintype N] in
/-- Subset-right for `CondIndepFun` when coordinates are given by `valuesProjection`. -/
theorem condIndep_valuesProjection_subset_right
    {I X Y Y' Z : Finset (SWIGNode N)}
    (hX : X ⊆ I) (hY : Y ⊆ I) (hY' : Y' ⊆ I) (hZ : Z ⊆ I)
    (hY'Y : Y' ⊆ Y)
    [StandardBorelSpace (ValuesOn I (swigΩ Ω))]
    {μ : MeasureTheory.Measure (ValuesOn I (swigΩ Ω))}
    [MeasureTheory.IsFiniteMeasure μ]
    (h : ProbabilityTheory.CondIndepFun
      (MeasurableSpace.comap (valuesProjection (Ω := swigΩ Ω) hZ) inferInstance)
      (comap_valuesProjection_le (Ω' := swigΩ Ω) hZ)
      (valuesProjection (Ω := swigΩ Ω) hX)
      (valuesProjection (Ω := swigΩ Ω) hY)
      μ) :
    ProbabilityTheory.CondIndepFun
      (MeasurableSpace.comap (valuesProjection (Ω := swigΩ Ω) hZ) inferInstance)
      (comap_valuesProjection_le (Ω' := swigΩ Ω) hZ)
      (valuesProjection (Ω := swigΩ Ω) hX)
      (valuesProjection (Ω := swigΩ Ω) hY')
      μ := by
  have h' := h.comp measurable_id (measurable_valuesProjection (Ω' := swigΩ Ω) hY'Y)
  simpa [Function.id_comp, valuesProjection_comp (Ω' := swigΩ Ω) hY'Y hY] using h'

omit [Fintype N] in
/-- Decomposition for `CondIndepFun` when coordinates are given by `valuesProjection`. -/
theorem condIndep_valuesProjection_decomposition
    {I X Y W Z : Finset (SWIGNode N)}
    (hX : X ⊆ I) (hYW : (Y ∪ W) ⊆ I) (hZ : Z ⊆ I)
    [StandardBorelSpace (ValuesOn I (swigΩ Ω))]
    {μ : MeasureTheory.Measure (ValuesOn I (swigΩ Ω))}
    [MeasureTheory.IsFiniteMeasure μ]
    (h : ProbabilityTheory.CondIndepFun
      (MeasurableSpace.comap (valuesProjection (Ω := swigΩ Ω) hZ) inferInstance)
      (comap_valuesProjection_le (Ω' := swigΩ Ω) hZ)
      (valuesProjection (Ω := swigΩ Ω) hX)
      (valuesProjection (Ω := swigΩ Ω) hYW)
      μ) :
    ProbabilityTheory.CondIndepFun
      (MeasurableSpace.comap (valuesProjection (Ω := swigΩ Ω) hZ) inferInstance)
      (comap_valuesProjection_le (Ω' := swigΩ Ω) hZ)
      (valuesProjection (Ω := swigΩ Ω) hX)
      (valuesProjection (Ω := swigΩ Ω) (Finset.subset_union_left.trans hYW))
      μ :=
  condIndep_valuesProjection_subset_right hX hYW (Finset.subset_union_left.trans hYW) hZ
    Finset.subset_union_left h

omit [Fintype N] in
/-- Weak union for `CondIndepFun` when coordinates are given by `valuesProjection`. -/
theorem condIndep_valuesProjection_weak_union_axiom
    {I X Y W Z : Finset (SWIGNode N)}
    (hX : X ⊆ I) (hYW : (Y ∪ W) ⊆ I) (hZ : Z ⊆ I)
    [StandardBorelSpace (ValuesOn I (swigΩ Ω))]
    {μ : MeasureTheory.Measure (ValuesOn I (swigΩ Ω))}
    [MeasureTheory.IsFiniteMeasure μ]
    (h : ProbabilityTheory.CondIndepFun
      (MeasurableSpace.comap (valuesProjection (Ω := swigΩ Ω) hZ) inferInstance)
      (comap_valuesProjection_le (Ω' := swigΩ Ω) hZ)
      (valuesProjection (Ω := swigΩ Ω) hX)
      (valuesProjection (Ω := swigΩ Ω) hYW)
      μ) :
    ProbabilityTheory.CondIndepFun
      (MeasurableSpace.comap (valuesProjection (Ω := swigΩ Ω)
        (Finset.union_subset hZ (Finset.subset_union_right.trans hYW))) inferInstance)
      (comap_valuesProjection_le (Ω' := swigΩ Ω)
        (Finset.union_subset hZ (Finset.subset_union_right.trans hYW)))
      (valuesProjection (Ω := swigΩ Ω) hX)
      (valuesProjection (Ω := swigΩ Ω) (Finset.subset_union_left.trans hYW))
      μ :=
  condIndep_valuesProjection_weak_union
    (M := SWIGNode N) (I := I) (X := X) (Y := Y) (W := W) (Z := Z) (Ω := swigΩ Ω)
    hX hYW (Finset.union_subset hZ (Finset.subset_union_right.trans hYW)) h

omit [Fintype N] in
/-- Contraction for `CondIndepFun` when coordinates are given by `valuesProjection`. -/
theorem condIndep_valuesProjection_contraction_axiom
    {I X Y W Z : Finset (SWIGNode N)}
    (hX : X ⊆ I) (hY : Y ⊆ I) (hW : W ⊆ I) (hZ : Z ⊆ I)
    [StandardBorelSpace (ValuesOn I (swigΩ Ω))]
    {μ : MeasureTheory.Measure (ValuesOn I (swigΩ Ω))}
    [MeasureTheory.IsFiniteMeasure μ]
    (h1 : ProbabilityTheory.CondIndepFun
      (MeasurableSpace.comap
        (valuesProjection (Ω := swigΩ Ω) (Finset.union_subset hZ hW)) inferInstance)
      (comap_valuesProjection_le (Ω' := swigΩ Ω) (Finset.union_subset hZ hW))
      (valuesProjection (Ω := swigΩ Ω) hX)
      (valuesProjection (Ω := swigΩ Ω) hY)
      μ)
    (h2 : ProbabilityTheory.CondIndepFun
      (MeasurableSpace.comap (valuesProjection (Ω := swigΩ Ω) hZ) inferInstance)
      (comap_valuesProjection_le (Ω' := swigΩ Ω) hZ)
      (valuesProjection (Ω := swigΩ Ω) hX)
      (valuesProjection (Ω := swigΩ Ω) hW)
      μ) :
    ProbabilityTheory.CondIndepFun
      (MeasurableSpace.comap (valuesProjection (Ω := swigΩ Ω) hZ) inferInstance)
      (comap_valuesProjection_le (Ω' := swigΩ Ω) hZ)
      (valuesProjection (Ω := swigΩ Ω) hX)
      (valuesProjection (Ω := swigΩ Ω) (Finset.union_subset hY hW))
      μ :=
  condIndep_valuesProjection_contraction
    (M := SWIGNode N) (I := I) (X := X) (Y := Y) (W := W) (Z := Z) (Ω := swigΩ Ω)
    hX hY hW hZ h1 h2

/-- **Subset right.** If X ⊥ Y | Z and Y' ⊆ Y, then X ⊥ Y' | Z. -/
theorem obsCondIndep_subset_right (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.ObservedValues]
    {X Y Y' Z : Finset (SWIGNode N)}
    (hX : X ⊆ M.observed) (hY : Y ⊆ M.observed) (hY' : Y' ⊆ M.observed)
    (hZ : Z ⊆ M.observed)
    (hY'Y : Y' ⊆ Y)
    {μ : MeasureTheory.Measure M.ObservedValues} [MeasureTheory.IsFiniteMeasure μ]
    (h : ObsCondIndep M X Y Z hX hY hZ μ) :
    ObsCondIndep M X Y' Z hX hY' hZ μ := by
  unfold ObsCondIndep at h ⊢
  exact condIndep_valuesProjection_subset_right (μ := μ) hX hY hY' hZ hY'Y h

/-- **Decomposition.** X ⊥ (Y ∪ W) | Z → X ⊥ Y | Z. -/
theorem obsCondIndep_decomposition (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.ObservedValues]
    {X Y W Z : Finset (SWIGNode N)}
    (hX : X ⊆ M.observed) (hYW : (Y ∪ W) ⊆ M.observed)
    (hZ : Z ⊆ M.observed)
    {μ : MeasureTheory.Measure M.ObservedValues} [MeasureTheory.IsFiniteMeasure μ]
    (h : ObsCondIndep M X (Y ∪ W) Z hX hYW hZ μ) :
    ObsCondIndep M X Y Z hX (Finset.subset_union_left.trans hYW) hZ μ := by
  unfold ObsCondIndep at h ⊢
  exact condIndep_valuesProjection_decomposition (μ := μ) hX hYW
    hZ h

/-- **Weak union.** X ⊥ (Y ∪ W) | Z → X ⊥ Y | (Z ∪ W). -/
theorem obsCondIndep_weak_union (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.ObservedValues]
    {X Y W Z : Finset (SWIGNode N)}
    (hX : X ⊆ M.observed) (hYW : (Y ∪ W) ⊆ M.observed)
    (hZ : Z ⊆ M.observed)
    {μ : MeasureTheory.Measure M.ObservedValues} [MeasureTheory.IsFiniteMeasure μ]
    (h : ObsCondIndep M X (Y ∪ W) Z hX hYW hZ μ) :
    ObsCondIndep M X Y (Z ∪ W) hX (Finset.subset_union_left.trans hYW)
      (Finset.union_subset hZ (Finset.subset_union_right.trans hYW)) μ := by
  unfold ObsCondIndep at h ⊢
  exact condIndep_valuesProjection_weak_union_axiom hX hYW hZ h

/-- **Contraction.** X ⊥ Y | (Z ∪ W) ∧ X ⊥ W | Z → X ⊥ (Y ∪ W) | Z. -/
theorem obsCondIndep_contraction (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.ObservedValues]
    {X Y W Z : Finset (SWIGNode N)}
    (hX : X ⊆ M.observed) (hY : Y ⊆ M.observed)
    (hW : W ⊆ M.observed) (hZ : Z ⊆ M.observed)
    {μ : MeasureTheory.Measure M.ObservedValues} [MeasureTheory.IsFiniteMeasure μ]
    (h1 : ObsCondIndep M X Y (Z ∪ W) hX hY (Finset.union_subset hZ hW) μ)
    (h2 : ObsCondIndep M X W Z hX hW hZ μ) :
    ObsCondIndep M X (Y ∪ W) Z hX (Finset.union_subset hY hW) hZ μ := by
  unfold ObsCondIndep at h1 h2 ⊢
  exact condIndep_valuesProjection_contraction_axiom hX hY hW hZ h1 h2

end SCM

end Causalean
