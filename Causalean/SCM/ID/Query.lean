/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.ID.Backdoor

/-!
# Total interventional query API

This file contains the lightweight query-level API shared by ID soundness
theorems.  It deliberately avoids importing the Tian/c-factor ID skeleton, so
modules can state and prove base cases for `interventionalQuery` without
depending on the full density recovery stack.
-/

namespace Causalean.SCM.ID

open scoped MeasureTheory ProbabilityTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- Every random or fixed SWIG-node value space is nonempty when every base-node
value space is nonempty. -/
noncomputable def swigValueNonempty [∀ n, Nonempty (Ω n)]
    (w : SWIGNode N) : Nonempty (swigΩ Ω w) := by
  cases w <;> infer_instance

/-- A finite coordinate product of SWIG-node value spaces is nonempty when all
base-node value spaces are nonempty. -/
noncomputable def valuesOnNonempty [∀ n, Nonempty (Ω n)]
    (Y : Finset (SWIGNode N)) :
    Nonempty (ValuesOn Y (swigΩ Ω)) :=
  ⟨fun y => Classical.choice (swigValueNonempty (Ω := Ω) y.val)⟩

/-- This fixed fallback kernel is used only outside the standard identification
query domain. -/
noncomputable def defaultInterventionalKernel [∀ n, Nonempty (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) :
    ProbabilityTheory.Kernel
      (ValuesOn (X.image SWIGNode.random) (swigΩ Ω))
      (ValuesOn Y (swigΩ Ω)) := by
  classical
  letI : Nonempty (ValuesOn Y (swigΩ Ω)) :=
    valuesOnNonempty (Ω := Ω) Y
  exact ProbabilityTheory.Kernel.const _
    (MeasureTheory.Measure.dirac (Classical.choice inferInstance))

/-- A standard structural causal model has a canonical fixed-value assignment.

When `M.fixed = ∅`, the fixed-value product has no coordinates, so it has a
unique canonical inhabitant. -/
noncomputable def standardFixedValues (M : Causalean.SCM N Ω)
    (hM : M.isStandard) : M.FixedValues :=
  fun d => False.elim (by
    have hempty : M.fixed = ∅ := hM
    have hd : d.val ∈ (∅ : Finset (SWIGNode N)) := by
      simpa [hempty] using d.property
    exact Finset.notMem_empty d.val hd)

/-- This predicate states when the interventional query is in its meaningful
standard-model branch. -/
def interventionalQueryValid
    (X : Finset N) (Y : Finset (SWIGNode N))
    (M : Causalean.SCM N Ω) : Prop :=
  (∀ D ∈ X, SWIGNode.random D ∈ M.observed) ∧
    (∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed) ∧
    (Y ⊆ M.observed) ∧ M.isStandard

/-- The interventional query returns the post-intervention outcome law as a
kernel indexed by treatment values.

For standard SCMs in which the treatment random nodes and outcome nodes are
observed, this is exactly `M.doKernelY X ... Y ... s0`.  Outside that
well-formed setting it returns a fixed dummy kernel so the query is a total
functional with model-independent codomain. -/
noncomputable def interventionalQuery [∀ n, Nonempty (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) :
    CausalQuery N Ω
      (ProbabilityTheory.Kernel
        (ValuesOn (X.image SWIGNode.random) (swigΩ Ω))
        (ValuesOn Y (swigΩ Ω))) := by
  classical
  exact fun M =>
    if h : (∀ D ∈ X, SWIGNode.random D ∈ M.observed) ∧
        (∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed) ∧
        (Y ⊆ M.observed) ∧ M.isStandard then
      M.doKernelY X h.1 h.2.1 Y h.2.2.1
        (standardFixedValues M h.2.2.2)
    else
      defaultInterventionalKernel X Y

/-- On the well-formed branch, the total interventional query is the
post-intervention outcome-marginal kernel. -/
lemma interventionalQuery_eq_doKernelY_of_valid [∀ n, Nonempty (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) (M : Causalean.SCM N Ω)
    (h : interventionalQueryValid X Y M) :
    interventionalQuery (Ω := Ω) X Y M =
      M.doKernelY X h.1 h.2.1 Y h.2.2.1
        (standardFixedValues M h.2.2.2) := by
  classical
  rw [interventionalQuery]
  exact dif_pos (by simpa [interventionalQueryValid] using h)

/-- Outside the well-formed branch, the total interventional query is the fixed
fallback kernel. -/
lemma interventionalQuery_eq_default_of_not_valid [∀ n, Nonempty (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) (M : Causalean.SCM N Ω)
    (h : ¬ interventionalQueryValid X Y M) :
    interventionalQuery (Ω := Ω) X Y M =
      defaultInterventionalKernel (Ω := Ω) X Y := by
  classical
  rw [interventionalQuery]
  exact dif_neg (by simpa [interventionalQueryValid] using h)

/-- Two models with the same SWIG graph agree on whether the total query is
well formed. -/
theorem interventionalQueryValid_iff_of_obsKernel_heq [∀ n, Nonempty (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) (G : SWIGGraph N)
    (M₁ M₂ : Causalean.SCM N Ω)
    (hsg₁ : M₁.toSWIGGraph = G) (hsg₂ : M₂.toSWIGGraph = G)
    (_hobs : HEq M₁.obsKernel M₂.obsKernel) :
    interventionalQueryValid X Y M₁ ↔ interventionalQueryValid X Y M₂ := by
  have hsg : M₁.toSWIGGraph = M₂.toSWIGGraph := hsg₁.trans hsg₂.symm
  have ho : M₁.observed = M₂.observed := congrArg SWIGGraph.observed hsg
  have hf : M₁.fixed = M₂.fixed := congrArg SWIGGraph.fixed hsg
  unfold interventionalQueryValid Causalean.SCM.isStandard
  rw [ho, hf]

end Causalean.SCM.ID
