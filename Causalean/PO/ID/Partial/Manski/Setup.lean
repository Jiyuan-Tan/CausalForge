/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.PO.Assumptions.ConsistencyLemmas
import Causalean.PO.Conditioning.EventCondExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Manski IV Setup

This file defines the data layer for Manski bounds with a discrete instrument,
a binary treatment, and a real-valued outcome. It provides the potential
outcomes, factual variables, instrument support, target average treatment
effect, and the four observable bound functionals used by the Manski
identification arguments.

Assumption bundles are kept in the companion assumptions file. -/

namespace Causalean
namespace PO

open MeasureTheory

/-- The Manski IV data layer records a discrete instrument, a binary treatment,
and a real outcome inside a potential-outcome system.

This is the discrete-IV system for Manski average-treatment-effect bounds,
corresponding to `def:po-iv-manski-system`.

`α` is the value space of the instrument; discreteness enters via
`MeasurableSingletonClass α`, which makes the events `{Z = z}` measurable. -/
structure POManskiIVSystem (P : POSystem) (α : Type*)
    [MeasurableSpace α] [MeasurableSingletonClass α] where
  Z : P.V
  D : P.V
  Y : P.V
  hZ : P.X Z ≃ᵐ α
  hDbool : P.X D ≃ᵐ Bool
  hYreal : P.X Y ≃ᵐ ℝ
  hZD : Z ≠ D
  hZY : Z ≠ Y
  hDY : D ≠ Y

namespace POManskiIVSystem

variable {P : POSystem} {α : Type*}
  [MeasurableSpace α] [MeasurableSingletonClass α]
  (S : POManskiIVSystem P α)

/-- Instrument packaged as a `POVar` valued in `α`. -/
def zVar : POVar P α := ⟨S.Z, S.hZ⟩

/-- Treatment packaged as a `POVar` valued in `Bool`. -/
def dVar : POVar P Bool := ⟨S.D, S.hDbool⟩

/-- Outcome packaged as a `POVar` valued in `ℝ`. -/
def yVar : POVar P ℝ := ⟨S.Y, S.hYreal⟩

/-- Counterfactual outcome under treatment arm `d`.

This is the function `Y(d) : P.Ω → ℝ`. -/
noncomputable def YofD (d : Bool) : P.Ω → ℝ := S.yVar.cfUnder S.dVar d

/-- Factual instrument. -/
noncomputable def factualZ : P.Ω → α := S.zVar.factual

/-- Factual treatment. -/
noncomputable def factualD : P.Ω → Bool := S.dVar.factual

/-- Factual outcome. -/
noncomputable def factualY : P.Ω → ℝ := S.yVar.factual

/-- The event `{Z = z}`. -/
def zEvent (z : α) : Set P.Ω := S.zVar.event z

/-- The event `{D = d}`. -/
def dEvent (d : Bool) : Set P.Ω := S.dVar.event d

/-! ### Measurability -/

/-- Counterfactual outcomes under each treatment arm are measurable. -/
lemma measurable_YofD (d : Bool) : Measurable (S.YofD d) :=
  S.yVar.measurable_cfUnder S.dVar d

/-- Factual instrument is measurable. -/
lemma measurable_factualZ : Measurable S.factualZ := S.zVar.measurable_factual
/-- Factual treatment is measurable. -/
lemma measurable_factualD : Measurable S.factualD := S.dVar.measurable_factual
/-- Factual outcome is measurable. -/
lemma measurable_factualY : Measurable S.factualY := S.yVar.measurable_factual

/-- Each instrument stratum event is measurable. -/
lemma measurableSet_zEvent (z : α) : MeasurableSet (S.zEvent z) :=
  S.zVar.measurableSet_event _

/-- Each treatment arm event is measurable. -/
lemma measurableSet_dEvent (d : Bool) : MeasurableSet (S.dEvent d) :=
  S.dVar.measurableSet_event _

/-! ### Target parameter, support, and bound functionals -/

/-- Average treatment effect `E[Y(1) - Y(0)]`. -/
noncomputable def ATE : ℝ := ∫ ω, S.YofD true ω - S.YofD false ω ∂P.μ

/-- Support of the instrument: `{z | μ(Z = z) ≠ 0}`. -/
def support : Set α := {z | P.μ (S.zEvent z) ≠ 0}

/-- The unified arm-bound functional averages the observed outcome on arm `d`
and the supplied outcome floor or ceiling on the opposite arm within instrument
stratum `z`.

The outcome-bound parameter `c` is applied on the counterfactual arm `!d`.
Specialising `d` to `true`/`false` and `c` to `lo`/`hi` recovers the four
named functionals `lowerBound1`, `upperBound1`, `lowerBound0`, `upperBound0`. -/
noncomputable def boundArm (d : Bool) (c : ℝ) (z : α) : ℝ :=
  eventCondExp P.μ (S.zEvent z)
    (fun ω => S.factualY ω * S.dVar.indicator d ω
               + c * S.dVar.indicator (!d) ω)

/-- The lower observable bound for the treated potential-outcome mean in instrument
stratum `z` uses the outcome floor on untreated units. -/
noncomputable def lowerBound1 (lo : ℝ) (z : α) : ℝ := S.boundArm true lo z

/-- The upper observable bound for the treated potential-outcome mean in instrument
stratum `z` uses the outcome ceiling on untreated units. -/
noncomputable def upperBound1 (hi : ℝ) (z : α) : ℝ := S.boundArm true hi z

/-- The lower observable bound for the control potential-outcome mean in instrument
stratum `z` uses the outcome floor on treated units. -/
noncomputable def lowerBound0 (lo : ℝ) (z : α) : ℝ := S.boundArm false lo z

/-- The upper observable bound for the control potential-outcome mean in instrument
stratum `z` uses the outcome ceiling on treated units. -/
noncomputable def upperBound0 (hi : ℝ) (z : α) : ℝ := S.boundArm false hi z

end POManskiIVSystem

end PO
end Causalean
