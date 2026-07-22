/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Lee bounds: data layer

The `POLeeSystem` structure (def:po-lee-system) plus the basic accessors,
factual / counterfactual variables, factual events
(`aEvent`, `selEvent`, `selectedTreated`, `selectedControl`),
and measurability lemmas.

No assumption bundles and no principal-stratum events live here — see
`Assumptions.lean` and `PrincipalStrata.lean`.
-/

import Causalean.PO.Assumptions.ConsistencyLemmas
import Causalean.PO.Conditioning.EventCondExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Lee Bounds Setup

This file defines the potential-outcome data layer for Lee sample-selection
bounds. It provides the treatment, selection, and outcome variables, their
factual and counterfactual versions, the observed selected cells, and basic
measurability facts. -/

namespace Causalean
namespace PO

open MeasureTheory

/-- The data layer for Lee (2009) bounds: a treatment-selection model in which a
binary treatment `A` affects whether an outcome `Y` is observed at all, through a
binary sample-selection indicator `Sel`.  The outcome `Y` is only meaningful when
`Sel = true` (e.g. a wage observed only for the employed), so the treatment
effect on `Y` among the always-selected subpopulation is only partially
identified — the object the Lee bounds bracket.  Formally this packages, inside
an ambient PO system `P`, the three nodes `A`, `Sel`, `Y`, the measurable
identifications of their value spaces with `Bool`/`Bool`/`ℝ`, and the fact that
the three nodes are distinct (def:po-lee-system).

* `A` is the binary treatment.
* `Sel` is the binary sample-selection indicator
  (denoted `S` in the doc; renamed to `Sel` so that the conventional
  bound variable `S : POLeeSystem P` does not shadow it).
* `Y` is the real-valued outcome (only meaningful on `{Sel = true}`). -/
structure POLeeSystem (P : POSystem) where
  /-- The binary treatment node (an index into the ambient system's variables). -/
  A : P.V
  /-- The binary sample-selection / observability indicator node: `Y` is observed
  iff `Sel = true`. -/
  Sel : P.V
  /-- The real-valued outcome node (only meaningful where `Sel = true`). -/
  Y : P.V
  /-- The treatment's value space is measurably equivalent to `Bool`. -/
  hAbool : P.X A ≃ᵐ Bool
  /-- The selection indicator's value space is measurably equivalent to `Bool`. -/
  hSelbool : P.X Sel ≃ᵐ Bool
  /-- The outcome's value space is measurably equivalent to `ℝ`. -/
  hYreal : P.X Y ≃ᵐ ℝ
  /-- Treatment and selection are distinct nodes. -/
  hASel : A ≠ Sel
  /-- Treatment and outcome are distinct nodes. -/
  hAY : A ≠ Y
  /-- Selection and outcome are distinct nodes. -/
  hSelY : Sel ≠ Y

namespace POLeeSystem

variable {P : POSystem} (S : POLeeSystem P)

/-- Treatment packaged as a `POVar` valued in `Bool`. -/
def aVar : POVar P Bool := ⟨S.A, S.hAbool⟩

/-- Selection indicator packaged as a `POVar` valued in `Bool`. -/
def selVar : POVar P Bool := ⟨S.Sel, S.hSelbool⟩

/-- Outcome packaged as a `POVar` valued in `ℝ`. -/
def yVar : POVar P ℝ := ⟨S.Y, S.hYreal⟩

/-- Counterfactual selection under treatment arm `a`.

This is the function `Sel(a) : P.Ω → Bool`. -/
noncomputable def SelOfA (a : Bool) : P.Ω → Bool := S.selVar.cfUnder S.aVar a

/-- Counterfactual outcome under treatment arm `a`.

This is the function `Y(a) : P.Ω → ℝ`. -/
noncomputable def YofA (a : Bool) : P.Ω → ℝ := S.yVar.cfUnder S.aVar a

/-- Factual treatment. -/
noncomputable def factualA : P.Ω → Bool := S.aVar.factual

/-- Factual selection indicator. -/
noncomputable def factualSel : P.Ω → Bool := S.selVar.factual

/-- Factual outcome. -/
noncomputable def factualY : P.Ω → ℝ := S.yVar.factual

/-- The event `{A = a}`. -/
def aEvent (a : Bool) : Set P.Ω := S.aVar.event a

/-- The event `{Sel = s}`. -/
def selEvent (s : Bool) : Set P.Ω := S.selVar.event s

/-- The selected-treated cell `{A = true, Sel = true}`. -/
def selectedTreated : Set P.Ω := S.aEvent true ∩ S.selEvent true

/-- The selected-control cell `{A = false, Sel = true}`. -/
def selectedControl : Set P.Ω := S.aEvent false ∩ S.selEvent true

/-! ### Measurability -/

/-- Counterfactual selection under any fixed arm is measurable. -/
lemma measurable_SelOfA (a : Bool) : Measurable (S.SelOfA a) :=
  S.selVar.measurable_cfUnder S.aVar a

/-- Counterfactual outcome under any fixed arm is measurable. -/
lemma measurable_YofA (a : Bool) : Measurable (S.YofA a) :=
  S.yVar.measurable_cfUnder S.aVar a

/-- Factual treatment is measurable. -/
lemma measurable_factualA : Measurable S.factualA := S.aVar.measurable_factual
/-- Factual selection is measurable. -/
lemma measurable_factualSel : Measurable S.factualSel := S.selVar.measurable_factual
/-- Factual outcome is measurable. -/
lemma measurable_factualY : Measurable S.factualY := S.yVar.measurable_factual

/-- Each factual treatment arm event is measurable. -/
lemma measurableSet_aEvent (a : Bool) : MeasurableSet (S.aEvent a) :=
  S.aVar.measurableSet_event _

/-- Each factual selection event is measurable. -/
lemma measurableSet_selEvent (s : Bool) : MeasurableSet (S.selEvent s) :=
  S.selVar.measurableSet_event _

/-- The selected-treated observed cell is measurable. -/
lemma measurableSet_selectedTreated : MeasurableSet S.selectedTreated :=
  (S.measurableSet_aEvent true).inter (S.measurableSet_selEvent true)

/-- The selected-control observed cell is measurable. -/
lemma measurableSet_selectedControl : MeasurableSet S.selectedControl :=
  (S.measurableSet_aEvent false).inter (S.measurableSet_selEvent true)

end POLeeSystem

end PO
end Causalean
