/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Tactic.Attr
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

/-- A potential-outcome variable records [a system variable](hyp:v) together with
[a measurable relabeling of its native value space into a chosen analysis scale
`α`](hyp:equiv).

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

/-- At a given unit, the counterfactual value of a variable under a regime is
the system's world evaluation of that variable at that unit under that regime,
carried over to the analysis scale by the variable's measurable equivalence.

This is the simp-shaped form of the definition of the counterfactual value
function: rewriting with it replaces the project constant by the system's own
evaluation map. -/
@[causal_defs_simps]
lemma cf_apply (a : POVar P α) (r : Regime P.V P.X) (ω : P.Ω) :
    a.cf r ω = a.equiv (P.eval r ω a.v) :=
  rfl

/-- A factual value function assigns each unit the observed no-intervention
value of a selected variable, reported on its chosen analysis scale.

Factual (empty-regime) value of the variable. -/
def factual (a : POVar P α) : P.Ω → α := a.cf Regime.empty

/-- The factual value function of a variable is its counterfactual value
function under the empty intervention regime.

This is the simp-shaped form of the definition of the factual value function;
it feeds the counterfactual-value normal form. -/
@[causal_defs_simps]
lemma factual_eq (a : POVar P α) : a.factual = a.cf Regime.empty :=
  rfl

/-- The counterfactual-value function of a potential-outcome variable under any
intervention regime is measurable. -/
@[fun_prop]
lemma measurable_cf (a : POVar P α) (r : Regime P.V P.X) : Measurable (a.cf r) :=
  a.equiv.measurable.comp
    ((measurable_pi_apply _).comp (P.measurable_eval r))

/-- The factual-value function of a potential-outcome variable is measurable. -/
@[fun_prop]
lemma measurable_factual (a : POVar P α) : Measurable a.factual :=
  a.measurable_cf _

/-- A factual-value event is the set of units whose observed value of a selected
variable equals a selected analysis-scale value.

The event `{factual a = x}` as a measurable set. -/
def event (a : POVar P α) (x : α) : Set P.Ω := a.factual ⁻¹' {x}

/-- The factual-value event of a variable at a value is the preimage, under the
variable's factual value function, of the one-point set at that value.

This is the simp-shaped form of the definition of the factual-value event:
rewriting with it replaces the project constant by an explicit preimage, after
which the set API applies. -/
@[causal_defs_simps]
lemma event_eq (a : POVar P α) (x : α) : a.event x = a.factual ⁻¹' {x} :=
  rfl

/-- The event that a potential-outcome variable's factual value equals a given
singleton-measurable value is measurable. -/
@[measurability]
lemma measurableSet_event (a : POVar P α) (x : α) (hx : MeasurableSet ({x} : Set α)) :
    MeasurableSet (a.event x) :=
  a.measurable_factual hx

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

/-- The single-intervention counterfactual value function of an outcome
variable at a treatment value is its counterfactual value function under the
singleton regime that fixes the treatment variable to that value, read back
through the treatment variable's measurable equivalence.

This is the simp-shaped form of the definition of the single-intervention
counterfactual; it feeds the counterfactual-value normal form. -/
@[causal_defs_simps]
lemma cfUnder_eq {β : Type*} [MeasurableSpace β]
    (y : POVar P α) (w : POVar P β) (d : β) :
    y.cfUnder w d = y.cf (Regime.single w.v (w.equiv.symm d)) :=
  rfl

/-- The single-intervention counterfactual-value function is measurable. -/
@[fun_prop]
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
noncomputable def indicator (a : POVar P α) (x : α) :
    P.Ω → ℝ :=
  (a.event x).indicator (fun _ => (1 : ℝ))

/-- For [a potential-outcome variable `a`](hyp:a) and [a value `x` in its
range](hyp:x), [the real-valued factual indicator `a.indicator x` equals the
set-indicator of the factual event `{a = x}`](goal). -/
@[indicator_simps, causal_defs_simps]
lemma indicator_eq_event_indicator (a : POVar P α) (x : α) :
    a.indicator x = (a.event x).indicator (fun _ => (1 : ℝ)) := rfl

/-- Pointwise: `a.indicator x ω = 1` on `{a = x}`. -/
@[indicator_simps]
lemma indicator_apply_eq_one (a : POVar P α) {x : α} {ω : P.Ω}
    (hω : a.factual ω = x) : a.indicator x ω = 1 := by
  simp only [causal_defs_simps]
  exact Set.indicator_of_mem (show ω ∈ a.event x from hω) _

/-- Pointwise: `a.indicator x ω = 0` off `{a = x}`. -/
@[indicator_simps]
lemma indicator_apply_eq_zero (a : POVar P α) {x : α} {ω : P.Ω}
    (hω : a.factual ω ≠ x) : a.indicator x ω = 0 := by
  simp only [causal_defs_simps]
  exact Set.indicator_of_notMem (show ω ∉ a.event x from hω) _

/-- `a.indicator x` is measurable. -/
@[fun_prop]
lemma measurable_indicator (a : POVar P α) (x : α) (hx : MeasurableSet ({x} : Set α)) :
    Measurable (a.indicator x) := by
  simp only [causal_defs_simps]
  exact ((measurable_const : Measurable (fun _ : P.Ω => (1 : ℝ)))).indicator
    (a.measurableSet_event x hx)

/-- `a.indicator x` is strongly measurable w.r.t. the σ-algebra generated by
`a.factual`. -/
@[fun_prop]
lemma stronglyMeasurable_indicator_comap (a : POVar P α) (x : α)
    (hx : MeasurableSet ({x} : Set α)) :
    StronglyMeasurable[MeasurableSpace.comap a.factual inferInstance]
      (a.indicator x) := by
  letI : MeasurableSpace P.Ω := MeasurableSpace.comap a.factual inferInstance
  have hev : MeasurableSet[MeasurableSpace.comap a.factual inferInstance]
      (a.event x) :=
    ⟨{x}, hx, rfl⟩
  have hmeas : Measurable[MeasurableSpace.comap a.factual inferInstance]
      (a.indicator x) := by
    simp only [causal_defs_simps]
    exact (measurable_const).indicator hev
  exact hmeas.stronglyMeasurable

/-- `a.indicator x` is integrable under any finite measure (bounded by `1`). -/
@[fun_prop]
lemma integrable_indicator {μ : Measure P.Ω} [IsFiniteMeasure μ]
    (a : POVar P α) (x : α) (hx : MeasurableSet ({x} : Set α)) :
    MeasureTheory.Integrable (a.indicator x) μ := by
  refine MeasureTheory.Integrable.of_bound
    (a.measurable_indicator x hx).aestronglyMeasurable 1
    (Filter.Eventually.of_forall ?_)
  intro ω
  unfold POVar.indicator
  by_cases hω : ω ∈ a.event x
  · simp [Set.indicator_of_mem hω]
  · simp [Set.indicator_of_notMem hω]

/-! #### Ambient and singleton-class indicator corollaries

The three indicator lemmas above are stated for a `MeasurableSet {x}` side
condition and, in the strongly-measurable case, for the σ-algebra generated by
the variable's factual value.  The corollaries below restate them in the two
shapes the standard function-property tactics look for: strong measurability
against the ambient σ-algebra, and the side-condition-free form available when
the value space has measurable one-point sets. -/

/-- The real-valued factual indicator of a potential-outcome variable at a
singleton-measurable value is strongly measurable on the sample space. -/
@[fun_prop]
lemma stronglyMeasurable_indicator (a : POVar P α) (x : α)
    (hx : MeasurableSet ({x} : Set α)) :
    StronglyMeasurable (a.indicator x) :=
  (a.measurable_indicator x hx).stronglyMeasurable

/-- On a value space whose one-point sets are measurable, the factual indicator of
a potential-outcome variable at any value is a measurable function of the unit. -/
@[fun_prop]
lemma measurable_indicator_of_singleton [MeasurableSingletonClass α]
    (a : POVar P α) (x : α) : Measurable (a.indicator x) :=
  a.measurable_indicator x (MeasurableSet.singleton x)

/-- On a value space whose one-point sets are measurable, the factual indicator of
a potential-outcome variable at any value is strongly measurable on the sample
space. -/
@[fun_prop]
lemma stronglyMeasurable_indicator_of_singleton [MeasurableSingletonClass α]
    (a : POVar P α) (x : α) : StronglyMeasurable (a.indicator x) :=
  (a.measurable_indicator x (MeasurableSet.singleton x)).stronglyMeasurable

/-- On a value space whose one-point sets are measurable, the factual indicator of
a potential-outcome variable at any value is strongly measurable with respect to
the information carried by that variable's factual value. -/
@[fun_prop]
lemma stronglyMeasurable_indicator_comap_of_singleton [MeasurableSingletonClass α]
    (a : POVar P α) (x : α) :
    StronglyMeasurable[MeasurableSpace.comap a.factual inferInstance]
      (a.indicator x) :=
  a.stronglyMeasurable_indicator_comap x (MeasurableSet.singleton x)

/-- On a value space whose one-point sets are measurable, the factual indicator of
a potential-outcome variable at any value is integrable under every finite measure
on the sample space. -/
@[fun_prop]
lemma integrable_indicator_of_singleton [MeasurableSingletonClass α]
    {μ : Measure P.Ω} [IsFiniteMeasure μ] (a : POVar P α) (x : α) :
    MeasureTheory.Integrable (a.indicator x) μ :=
  a.integrable_indicator x (MeasurableSet.singleton x)

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

/-- A regimed variable pairs [a potential-outcome variable](hyp:var) with [the intervention
regime under which it should be evaluated](hyp:regime).

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

/-- The value function of a regimed variable is the counterfactual value
function of its underlying variable under its bundled regime.

This is the simp-shaped form of the definition of the regimed-variable value
function; it feeds the counterfactual-value normal form. -/
@[causal_defs_simps]
lemma value_eq (rv : RegimedVar P α) : rv.value = rv.var.cf rv.regime :=
  rfl

/-- The value function of a regimed variable is measurable. -/
@[fun_prop]
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
