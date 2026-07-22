/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.PO.Core.System

/-! # Consistency for Potential Outcomes

This file defines the pathwise agreement predicates and the two-clause consistency
assumption for potential-outcome systems.  These notions connect factual agreement,
sequential interventions, and equality of potential outcomes outside the intervened
coordinates.  The public API consists of `POSystem.FactualAgrees`,
`POSystem.IntermediateAgrees`, and the `POSystem.Consistency` structure with its
factual-consistency and composition-consistency fields. -/

namespace Causalean
namespace PO

namespace POSystem

variable (P : POSystem)

/-- For a potential-outcome system, an intervention regime, and a unit in the
sample space, factual agreement means that for every variable targeted by the
regime, the factual value of that variable for the unit equals the value assigned
by the regime.

Pathwise predicate: factual value of `r.target` equals `r.assign` at `ω`. -/
def FactualAgrees (r : Regime P.V P.X) (ω : P.Ω) : Prop :=
  ∀ v (hv : v ∈ r.target), P.eval Regime.empty ω v = r.assign v hv

/-- For a potential-outcome system, two intervention regimes, and a unit in the
sample space, intermediate agreement means that after applying the first regime,
every variable targeted by the second regime has the value assigned to it by the
second regime.

Pathwise predicate: post-`r₁` value of `r₂.target` equals `r₂.assign` at `ω`. -/
def IntermediateAgrees (r₁ r₂ : Regime P.V P.X) (ω : P.Ω) : Prop :=
  ∀ v (hv : v ∈ r₂.target), P.eval r₁ ω v = r₂.assign v hv

/-- A potential-outcome system is consistent when two conditions hold.  First,
for every intervention regime and every finite set of variables disjoint from
the regime target, if a unit factually agrees with the regime, then the
potential outcomes for that finite set under the regime equal the factual
potential outcomes for that unit.  Second, for every pair of disjoint regimes
and every finite set of variables disjoint from the union of their targets, if a
unit agrees with the second regime after the first regime has been applied, then
the potential outcomes for that finite set under the combined regime equal the
potential outcomes under the first regime alone.

Consistency assumption -- def:po-consistency. -/
structure Consistency (P : POSystem) : Prop where
  /-- Factual consistency. -/
  factual :
    ∀ (r : Regime P.V P.X) (Y : Finset P.V),
      _root_.Disjoint Y r.target →
      ∀ ω : P.Ω, P.FactualAgrees r ω →
        P.poVariable r Y ω = P.poVariable Regime.empty Y ω
  /-- Composition / nested consistency. -/
  composition :
    ∀ (r₁ r₂ : Regime P.V P.X) (h : r₁.Disjoint r₂) (Y : Finset P.V),
      _root_.Disjoint Y (r₁.target ∪ r₂.target) →
      ∀ ω : P.Ω, P.IntermediateAgrees r₁ r₂ ω →
        P.poVariable (r₁.sqcup r₂ h) Y ω = P.poVariable r₁ Y ω

end POSystem

end PO
end Causalean
