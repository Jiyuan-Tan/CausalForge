/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.PO.Core.System
import Causalean.PO.Core.Regime
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! # Potential-Outcome Variables

This file packages a variable of a potential-outcome system together with a
common measurable value space, so that factual and counterfactual realizations
can be handled uniformly.  It also provides event indicators and variables
paired with intervention regimes for counterfactual independence statements.

The main public objects are `POVar`, its factual and counterfactual value maps
`factual`, `cf`, and `cfUnder`, the factual-event indicator API, and
`RegimedVar` for bundling a variable with the regime under which it is evaluated. -/

namespace Causalean
namespace PO

open MeasureTheory

/-- A potential-outcome variable records a system variable together with a
measurable relabeling of its native values into a chosen analysis scale.

A PO system variable whose value space is identified with a fixed measurable
type `α` via a measurable equivalence.  Bundles the underlying node `v : P.V`
together with the equivalence, so that factual and counterfactual realisations
land in `α` rather than `P.X v`. -/
structure POVar (P : POSystem) (α : Type*) [MeasurableSpace α] where
  v : P.V
  equiv : P.X v ≃ᵐ α

namespace POVar

variable {P : POSystem} {α : Type*} [MeasurableSpace α]

/-- A counterfactual value function assigns each unit the value that a selected
variable would have under a selected intervention regime, reported on its
chosen analysis scale.

Counterfactual value of the variable under regime `r`. -/
def cf (a : POVar P α) (r : Regime P.V P.X) : P.Ω → α :=
  fun ω => a.equiv (P.eval r ω a.v)

/-- A factual value function assigns each unit the observed no-intervention
value of a selected variable, reported on its chosen analysis scale.

Factual (empty-regime) value of the variable. -/
def factual (a : POVar P α) : P.Ω → α := a.cf Regime.empty

/-- The counterfactual-value function of a potential-outcome variable under any
intervention regime is measurable. -/
lemma measurable_cf (a : POVar P α) (r : Regime P.V P.X) : Measurable (a.cf r) :=
  a.equiv.measurable.comp
    ((measurable_pi_apply _).comp (P.measurable_eval r))

/-- The factual-value function of a potential-outcome variable is measurable. -/
lemma measurable_factual (a : POVar P α) : Measurable a.factual :=
  a.measurable_cf _

/-- A factual-value event is the set of units whose observed value of a selected
variable equals a selected analysis-scale value.

The event `{factual a = x}` as a measurable set. -/
def event (a : POVar P α) (x : α) : Set P.Ω := a.factual ⁻¹' {x}

/-- The event that a potential-outcome variable's factual value equals a given
singleton-measurable value is measurable. -/
lemma measurableSet_event [MeasurableSingletonClass α] (a : POVar P α) (x : α) :
    MeasurableSet (a.event x) :=
  a.measurable_factual (measurableSet_singleton x)

/-- The potential outcome of variable `y` when the intervention variable `w` is
set to the value `d`: the single-variable counterfactual `y(w := d)`. (Binders
follow the usual econometric convention — `y` is the outcome variable and `d` is
the treatment/intervention value; `w` is the variable being intervened on.)

This is the common single-intervention specialization used by identification
files to write objects such as `Y(d)` without manually constructing a
singleton `Regime`. -/
def cfUnder {β : Type*} [MeasurableSpace β]
    (y : POVar P α) (w : POVar P β) (d : β) : P.Ω → α :=
  y.cf (Regime.single w.v (w.equiv.symm d))

/-- The single-intervention counterfactual-value function is measurable. -/
lemma measurable_cfUnder {β : Type*} [MeasurableSpace β]
    (y : POVar P α) (w : POVar P β) (d : β) : Measurable (y.cfUnder w d) :=
  y.measurable_cf _

/-! ### Real-valued factual indicator `1_{A = x}`

Packages the `fun ω => if a.factual ω = x then 1 else 0` pattern used by every
identification theorem, together with the boilerplate measurability /
integrability / set-indicator lemmas. -/

/-- A factual-value indicator is the zero-one function that marks units whose
observed value of a selected variable equals a selected analysis-scale value.

The real-valued indicator of the factual event `{a = x}`, defined as
`(a.event x).indicator 1`. -/
noncomputable def indicator (a : POVar P α) [MeasurableSingletonClass α] (x : α) :
    P.Ω → ℝ :=
  (a.event x).indicator (fun _ => (1 : ℝ))

variable [MeasurableSingletonClass α]

/-- `a.indicator x` equals the set-indicator of the event `{a = x}`. -/
lemma indicator_eq_event_indicator (a : POVar P α) (x : α) :
    a.indicator x = (a.event x).indicator (fun _ => (1 : ℝ)) := rfl

/-- Pointwise: `a.indicator x ω = 1` on `{a = x}`. -/
lemma indicator_apply_eq_one (a : POVar P α) {x : α} {ω : P.Ω}
    (hω : a.factual ω = x) : a.indicator x ω = 1 := by
  unfold POVar.indicator
  exact Set.indicator_of_mem (show ω ∈ a.event x from hω) _

/-- Pointwise: `a.indicator x ω = 0` off `{a = x}`. -/
lemma indicator_apply_eq_zero (a : POVar P α) {x : α} {ω : P.Ω}
    (hω : a.factual ω ≠ x) : a.indicator x ω = 0 := by
  unfold POVar.indicator
  exact Set.indicator_of_notMem (show ω ∉ a.event x from hω) _

/-- `a.indicator x` is measurable. -/
lemma measurable_indicator (a : POVar P α) (x : α) :
    Measurable (a.indicator x) := by
  unfold POVar.indicator
  exact ((measurable_const : Measurable (fun _ : P.Ω => (1 : ℝ)))).indicator
    (a.measurableSet_event x)

/-- `a.indicator x` is strongly measurable w.r.t. the σ-algebra generated by
`a.factual`. -/
lemma stronglyMeasurable_indicator_comap (a : POVar P α) (x : α) :
    StronglyMeasurable[MeasurableSpace.comap a.factual inferInstance]
      (a.indicator x) := by
  letI : MeasurableSpace P.Ω := MeasurableSpace.comap a.factual inferInstance
  have hev : MeasurableSet[MeasurableSpace.comap a.factual inferInstance]
      (a.event x) :=
    ⟨{x}, MeasurableSet.singleton x, rfl⟩
  have hmeas : Measurable[MeasurableSpace.comap a.factual inferInstance]
      (a.indicator x) := by
    unfold POVar.indicator
    exact (measurable_const).indicator hev
  exact hmeas.stronglyMeasurable

/-- `a.indicator x` is integrable under any finite measure (bounded by `1`). -/
lemma integrable_indicator [IsFiniteMeasure P.μ] (a : POVar P α) (x : α) :
    MeasureTheory.Integrable (a.indicator x) P.μ := by
  refine MeasureTheory.Integrable.of_bound
    (a.measurable_indicator x).aestronglyMeasurable 1
    (Filter.Eventually.of_forall ?_)
  intro ω
  unfold POVar.indicator
  by_cases hω : ω ∈ a.event x
  · simp [Set.indicator_of_mem hω]
  · simp [Set.indicator_of_notMem hω]

/-- `a.indicator x ω` is always `0` or `1`. -/
lemma indicator_eq_one_or_zero (a : POVar P α) (x : α) (ω : P.Ω) :
    a.indicator x ω = 1 ∨ a.indicator x ω = 0 := by
  unfold POVar.indicator
  by_cases hω : ω ∈ a.event x
  · exact Or.inl (by simp [Set.indicator_of_mem hω])
  · exact Or.inr (by simp [Set.indicator_of_notMem hω])

/-- Binary case: `a.indicator true ω + a.indicator false ω = 1`. -/
lemma indicator_add_indicator_not (a : POVar P Bool) (ω : P.Ω) :
    a.indicator true ω + a.indicator false ω = 1 := by
  unfold POVar.indicator
  by_cases hT : a.factual ω = true
  · have hT_t : ω ∈ a.event true := hT
    have hT_f : ω ∉ a.event false := by
      change a.factual ω ≠ false; rw [hT]; decide
    simp [Set.indicator_of_mem hT_t, Set.indicator_of_notMem hT_f]
  · have hF : a.factual ω = false := by
      cases h : a.factual ω <;> simp_all
    have hT_t : ω ∉ a.event true := hT
    have hT_f : ω ∈ a.event false := hF
    simp [Set.indicator_of_notMem hT_t, Set.indicator_of_mem hT_f]

end POVar

/-- A regimed variable pairs a potential-outcome variable with the intervention
regime under which it should be evaluated.

A PO variable equipped with an intervention regime.  Used to state
independence hypotheses uniformly via `jointValue` / `IndepCF` (see
`IndepCF.lean`). -/
structure RegimedVar (P : POSystem) (α : Type*) [MeasurableSpace α] where
  var : POVar P α
  regime : Regime P.V P.X

namespace RegimedVar

variable {P : POSystem} {α : Type*} [MeasurableSpace α]

/-- A regimed variable's value function assigns each unit the counterfactual
value implied by the variable-regime pair.

Evaluate the regimed variable as a `P.Ω → α` map. -/
def value (rv : RegimedVar P α) : P.Ω → α := rv.var.cf rv.regime

/-- The value function of a regimed variable is measurable. -/
lemma measurable_value (rv : RegimedVar P α) : Measurable rv.value :=
  rv.var.measurable_cf _

/-- Factual bundling views a potential-outcome variable as evaluated under the
no-intervention regime.

Factual bundling: the empty regime. -/
def ofFactual (a : POVar P α) : RegimedVar P α := ⟨a, Regime.empty⟩

/-- Single-intervention bundling views a potential-outcome variable as evaluated
after fixing one system variable to a chosen native value.

Bundling under a single-node intervention. -/
def ofSingle (a : POVar P α) (w : P.V) (x : P.X w) : RegimedVar P α :=
  ⟨a, Regime.single w x⟩

end RegimedVar

end PO
end Causalean
