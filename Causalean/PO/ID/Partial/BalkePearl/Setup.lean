/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Balke-Pearl IV bounds: data layer

The `POBalkePearlSystem` structure (def:po-iv-balke-pearl-system) plus all
basic accessors, measurability lemmas, the target parameter `ATE`, and the
cell probability `cellProb`.

All three variables Z, D, Y are binary (Bool).  No assumption bundles live
here — see `Assumptions.lean`.
-/

import Causalean.PO.Assumptions.ConsistencyLemmas
import Causalean.PO.Conditioning.EventCondExp
import Causalean.PO.Assumptions.IndepCF
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Balke-Pearl Setup

This file defines the data layer for Balke-Pearl partial identification of the
average treatment effect with a binary instrument, binary treatment, and binary
outcome. The structure `POBalkePearlSystem` records the three binary system
variables and their distinctness; its namespace supplies the factual variables
`factualZ`, `factualD`, `factualY`, the counterfactuals `DofZ`, `YofD`, and
`YofZD`, the real-valued Boolean embedding used for integration, the target
estimand `ATE`, and the observable conditional cell probability `cellProb`. -/

namespace Causalean
namespace PO

open MeasureTheory

/-- Binary-IV system for Balke-Pearl ATE bounds — def:po-iv-balke-pearl-system.

The system consists of a binary instrument `Z`, binary treatment `D`, and binary
outcome `Y`, each represented as a variable of the ambient potential-outcome
system. The fields `hZD`, `hZY`, and `hDY` state that these are distinct system
variables. -/
structure POBalkePearlSystem (P : POSystem) where
  Z : P.V
  D : P.V
  Y : P.V
  hZbool : P.X Z ≃ᵐ Bool
  hDbool : P.X D ≃ᵐ Bool
  hYbool : P.X Y ≃ᵐ Bool
  hZD : Z ≠ D
  hZY : Z ≠ Y
  hDY : D ≠ Y

namespace POBalkePearlSystem

variable {P : POSystem} (S : POBalkePearlSystem P)

/-! ### POVar wrappers -/

/-- Instrument packaged as a `POVar` valued in `Bool`. -/
def zVar : POVar P Bool := ⟨S.Z, S.hZbool⟩

/-- Treatment packaged as a `POVar` valued in `Bool`. -/
def dVar : POVar P Bool := ⟨S.D, S.hDbool⟩

/-- Outcome packaged as a `POVar` valued in `Bool`. -/
def yVar : POVar P Bool := ⟨S.Y, S.hYbool⟩

/-! ### Single-target counterfactuals -/

/-- The treatment value that would be observed for a unit if the instrument were set to `z`. -/
noncomputable def DofZ (z : Bool) : P.Ω → Bool := S.dVar.cfUnder S.zVar z

/-- `Y(d) : P.Ω → Bool`. -/
noncomputable def YofD (d : Bool) : P.Ω → Bool := S.yVar.cfUnder S.dVar d

/-! ### Two-target counterfactual Y(z,d) -/

/-- Two-variable intervention regime `r_{z,d} = ({Z,D}, (z,d))`.

Built as a disjoint union of the singleton regimes `{Z ← z}` and `{D ← d}`;
disjointness uses `S.hZD : Z ≠ D`. -/
noncomputable def regimeZD (z d : Bool) : Regime P.V P.X :=
  (Regime.single S.Z (S.hZbool.symm z)).sqcup
    (Regime.single S.D (S.hDbool.symm d))
    (Regime.single_disjoint_single S.hZD _ _)

/-- Two-variable counterfactual `Y(z,d) := yVar.cf (r_{z,d})`. -/
noncomputable def YofZD (z d : Bool) : P.Ω → Bool := S.yVar.cf (S.regimeZD z d)

/-! ### Factuals -/

/-- Factual instrument. -/
noncomputable def factualZ : P.Ω → Bool := S.zVar.factual

/-- Factual treatment. -/
noncomputable def factualD : P.Ω → Bool := S.dVar.factual

/-- Factual outcome. -/
noncomputable def factualY : P.Ω → Bool := S.yVar.factual

/-! ### Real cast for integration -/

/-- Canonical embedding of `Bool` into `ℝ`: `true ↦ 1`, `false ↦ 0`. -/
@[simp] noncomputable def boolToReal : Bool → ℝ
  | true  => 1
  | false => 0

/-- `Y(d)` lifted to `ℝ` for integration. -/
noncomputable def YofD_real (d : Bool) : P.Ω → ℝ := boolToReal ∘ S.YofD d

/-! ### Events -/

/-- The event `{Z = z}`. -/
def zEvent (z : Bool) : Set P.Ω := S.zVar.event z

/-- The event `{D = d}`. -/
def dEvent (d : Bool) : Set P.Ω := S.dVar.event d

/-- The event `{Y = y}`. -/
def yEvent (y : Bool) : Set P.Ω := S.yVar.event y

/-! ### Measurability -/

/-- The treatment under a fixed instrument value is measurable. -/
lemma measurable_DofZ (z : Bool) : Measurable (S.DofZ z) :=
  S.dVar.measurable_cfUnder S.zVar z

/-- The outcome under a fixed treatment value is measurable. -/
lemma measurable_YofD (d : Bool) : Measurable (S.YofD d) :=
  S.yVar.measurable_cfUnder S.dVar d

/-- The outcome under fixed instrument and treatment values is measurable. -/
lemma measurable_YofZD (z d : Bool) : Measurable (S.YofZD z d) :=
  S.yVar.measurable_cf _

/-- The factual instrument is measurable. -/
lemma measurable_factualZ : Measurable S.factualZ := S.zVar.measurable_factual
/-- The factual treatment is measurable. -/
lemma measurable_factualD : Measurable S.factualD := S.dVar.measurable_factual
/-- The factual outcome is measurable. -/
lemma measurable_factualY : Measurable S.factualY := S.yVar.measurable_factual

/-- The factual instrument event is measurable. -/
lemma measurableSet_zEvent (z : Bool) : MeasurableSet (S.zEvent z) :=
  S.zVar.measurableSet_event _

/-- The factual treatment event is measurable. -/
lemma measurableSet_dEvent (d : Bool) : MeasurableSet (S.dEvent d) :=
  S.dVar.measurableSet_event _

/-- The factual outcome event is measurable. -/
lemma measurableSet_yEvent (y : Bool) : MeasurableSet (S.yEvent y) :=
  S.yVar.measurableSet_event _

/-- The Boolean-to-real embedding is measurable. -/
lemma measurable_boolToReal : Measurable (boolToReal) := by
  apply measurable_of_finite

/-- The real-valued potential outcome under a fixed treatment is measurable. -/
lemma measurable_YofD_real (d : Bool) : Measurable (S.YofD_real d) :=
  measurable_boolToReal.comp (S.measurable_YofD d)

/-! ### Target parameter and cell probability -/

/-- Average treatment effect `E[Y(1) - Y(0)]` (as a difference of Bool-in-ℝ integrals). -/
noncomputable def ATE : ℝ :=
  ∫ ω, S.YofD_real true ω - S.YofD_real false ω ∂P.μ

/-- Conditional cell probability `P(Y = y, D = d | Z = z)`.

Defined as `μ(Z = z ∩ Y = y ∩ D = d) / μ(Z = z)`. -/
noncomputable def cellProb (y d z : Bool) : ℝ :=
  (P.μ (S.zEvent z ∩ S.yEvent y ∩ S.dEvent d)).toReal
    / (P.μ (S.zEvent z)).toReal

end POBalkePearlSystem

end PO
end Causalean
