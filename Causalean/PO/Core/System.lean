/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Potential Outcome System

Implements def:po-system and def:po-operator from Basic Concepts.tex:
a graph-free tuple `(V, {X_v}, Ω, μ, {v(r)})` together with the derived
world-eval map and the PO operator (pushforward).
-/

import Causalean.PO.Core.Regime

/-! # Potential Outcome Systems

This file defines a graph-free potential-outcome system, its coordinate-level
potential outcomes, subset-valued potential outcomes, and the induced
pushforward law of a subset under a regime. These are the base objects used by
the counterfactual and identification layers of the library. -/

namespace Causalean
namespace PO

open MeasureTheory

/-- A potential-outcome system consists of a finite set of variables with
decidable equality, a measurable value space for each variable, a measurable
sample space with a probability measure, and, for every intervention regime
and sample point, a measurable joint assignment of potential outcomes to all
variables.

Implements def:po-system. -/
structure POSystem where
  V : Type*
  [decEqV : DecidableEq V]
  [fintypeV : Fintype V]
  X : V → Type*
  [measX : ∀ v, MeasurableSpace (X v)]
  Ω : Type*
  [measΩ : MeasurableSpace Ω]
  μ : Measure Ω
  [isProb : IsProbabilityMeasure μ]
  /-- Derived world-evaluation map `Eval^P_r` -- def:po-operator. -/
  eval : Regime V X → Ω → ∀ v, X v
  measurable_eval : ∀ r, Measurable (eval r)

namespace POSystem

attribute [instance] POSystem.decEqV POSystem.fintypeV
  POSystem.measX POSystem.measΩ POSystem.isProb

variable (P : POSystem)

/-- A coordinate potential outcome maps each unit to the value a selected
variable would take under a selected intervention regime.

Implements the per-coordinate part of def:po-operator. -/
def component (r : Regime P.V P.X) (v : P.V) : P.Ω → P.X v :=
  fun ω => P.eval r ω v

/-- The coordinate potential outcome of any variable under any intervention regime is measurable. -/
lemma measurable_component (r : Regime P.V P.X) (v : P.V) :
    Measurable (P.component r v) :=
  (measurable_pi_apply v).comp (P.measurable_eval r)

/-- A joint potential outcome maps each unit to the vector of values a selected
finite set of variables would take under a selected intervention regime.

Implements the subset-valued variable in def:po-operator. -/
def poVariable (r : Regime P.V P.X) (Y : Finset P.V) :
    P.Ω → ValuesOn Y P.X :=
  fun ω v => P.eval r ω v.val

/-- The joint potential outcome for any finite set of variables under any
intervention regime is measurable. -/
lemma measurable_poVariable (r : Regime P.V P.X) (Y : Finset P.V) :
    Measurable (P.poVariable r Y) := by
  refine measurable_pi_lambda _ ?_
  intro v
  exact (measurable_pi_apply v.val).comp (P.measurable_eval r)

/-- A potential-outcome law is the distribution of a selected finite set of
variables under a selected intervention regime.

Implements def:po-operator. -/
noncomputable def poOperator (r : Regime P.V P.X) (Y : Finset P.V) :
    Measure (ValuesOn Y P.X) :=
  (P.μ).map (P.poVariable r Y)

/-- The potential-outcome law of a finite set of variables under a regime is a
probability measure. -/
instance (r : Regime P.V P.X) (Y : Finset P.V) :
    IsProbabilityMeasure (P.poOperator r Y) := by
  unfold poOperator
  exact MeasureTheory.Measure.isProbabilityMeasure_map
    (P.measurable_poVariable r Y).aemeasurable

end POSystem

end PO
end Causalean
