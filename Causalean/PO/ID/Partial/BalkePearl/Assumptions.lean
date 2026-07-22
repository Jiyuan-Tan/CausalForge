/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Balke-Pearl IV bounds: assumption bundle

`BaseAssumptions` collects the Balke-Pearl IV conditions (def:po-iv-balke-pearl-assumptions):
IV-specific consistency for treatment and outcome cells, exclusion restriction,
instrument exogeneity (Z ⊥ (D(0),D(1),Y(0),Y(1))), and positive instrument
probability.
-/

import Causalean.PO.ID.Partial.BalkePearl.Setup

/-! # Balke-Pearl Assumptions

This file collects the structural assumptions for Balke-Pearl partial
identification with a binary instrument, including the IV-specific consistency
equalities, exclusion, instrument exogeneity, and positive instrument probabilities.
It also packages the counterfactual variables used by the exogeneity condition. -/

namespace Causalean
namespace PO

open MeasureTheory

namespace POBalkePearlSystem

variable {P : POSystem} (S : POBalkePearlSystem P)

/-! ### RegimedVar components -/

/-- `D(z)` as a `RegimedVar`. -/
def dUnderZ (z : Bool) : RegimedVar P Bool :=
  ⟨S.dVar, Regime.single S.Z (S.hZbool.symm z)⟩

/-- `Y(d)` as a `RegimedVar`. -/
def yUnderD (d : Bool) : RegimedVar P Bool :=
  ⟨S.yVar, Regime.single S.D (S.hDbool.symm d)⟩

/-! ### Counterfactual bundle (for the exogeneity assumption) -/

/-- Bundle `(D(0), D(1), Y(0), Y(1))` for the exogeneity assumption
`Z ⊥ (D(0), D(1), Y(0), Y(1))`. -/
def cfBundle : POCFBundle P :=
  .cons (S.dUnderZ false) <|
  .cons (S.dUnderZ true) <|
  .cons (S.yUnderD false) <|
  .cons (S.yUnderD true) <|
  .nil P

/-! ### Assumption structure -/

/-- Balke-Pearl IV assumptions — def:po-iv-balke-pearl-assumptions.

The consistency component is deliberately IV-specific: on the instrument cell
`{Z=z}`, factual treatment equals `D(z)`, and on the treatment cell `{D=d}`,
factual outcome equals `Y(d)`.  The bundle does not assume the library-wide
potential-outcome consistency axiom for arbitrary regimes. -/
structure BaseAssumptions (S : POBalkePearlSystem P) : Prop where
  /-- Treatment consistency on instrument cells: on `{Z=z}`, factual `D` equals `D(z)`. -/
  consistency_D : ∀ (z : Bool) {ω : P.Ω}, ω ∈ S.zEvent z → S.DofZ z ω = S.factualD ω
  /-- Outcome consistency on treatment cells: on `{D=d}`, factual `Y` equals `Y(d)`. -/
  consistency_Y : ∀ (d : Bool) {ω : P.Ω}, ω ∈ S.dEvent d → S.YofD d ω = S.factualY ω
  /-- Exclusion: Y(z,d) = Y(d) a.s. for all z d. -/
  exclusion   : ∀ (z d : Bool), S.YofZD z d =ᵐ[P.μ] S.YofD d
  /-- Instrument exogeneity: Z ⊥ (D(0),D(1),Y(0),Y(1)). -/
  exogeneity  : P.IndepCF (.ofFactual S.zVar) S.cfBundle P.μ
  /-- Both arms of Z have positive probability. -/
  posZ        : ∀ z : Bool, 0 < P.μ (S.zVar.event z)

namespace BaseAssumptions

variable {S : POBalkePearlSystem P}

/-- Positive instrument probabilities are nonzero. -/
lemma posZ_ne_zero (hA : S.BaseAssumptions) (z : Bool) :
    P.μ (S.zVar.event z) ≠ 0 := ne_of_gt (hA.posZ z)

/-- Instrument-cell probabilities are finite. -/
lemma posZ_ne_top (_ : S.BaseAssumptions) (z : Bool) :
    P.μ (S.zVar.event z) ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt prob_le_one (by norm_num))

/-- Positive instrument probabilities remain positive after conversion to real numbers. -/
lemma posZ_toReal_pos (hA : S.BaseAssumptions) (z : Bool) :
    0 < (P.μ (S.zVar.event z)).toReal :=
  ENNReal.toReal_pos (hA.posZ_ne_zero z) (hA.posZ_ne_top z)

end BaseAssumptions

end POBalkePearlSystem

end PO
end Causalean
