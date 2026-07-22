/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.PO.ID.Partial.Manski.Setup
import Causalean.PO.Conditioning.CondExpTooling

/-! # Manski Assumptions

This file states the assumption bundles for Manski bounds with a discrete
instrument. The baseline assumptions impose consistency, bounded potential
outcomes, and integrability, while separate shape restrictions encode mean
independence, monotone treatment response, monotone treatment selection, and
monotone instrumental variables.

The assumptions are separated from the data layer so later bound theorems can
combine them independently. -/

namespace Causalean
namespace PO

open MeasureTheory

namespace POManskiIVSystem

variable {P : POSystem} {α : Type*}
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Discrete-IV ATE-bound baseline assumptions -- common part of
def:po-iv-manski-assumptions.

`lo, hi` are the almost-sure outcome bounds (`a, b` in the tex).  Shape
restrictions live in the `MeanIndep`, `MTR`, `MTS`, `MIV` structures. -/
structure BaseAssumptions (S : POManskiIVSystem P α) where
  consistency : P.Consistency
  lo : ℝ
  hi : ℝ
  hle : lo ≤ hi
  bounded_one : ∀ᵐ ω ∂P.μ, lo ≤ S.YofD true ω ∧ S.YofD true ω ≤ hi
  bounded_zero : ∀ᵐ ω ∂P.μ, lo ≤ S.YofD false ω ∧ S.YofD false ω ≤ hi
  integrable_Y1 : Integrable (S.YofD true) P.μ
  integrable_Y0 : Integrable (S.YofD false) P.μ

namespace BaseAssumptions

variable {S : POManskiIVSystem P α}

/-- Binary-folded form of `bounded_one` / `bounded_zero`: `Y(d)` is a.s. in
`[lo, hi]` uniformly in `d : Bool`. -/
lemma bounded (hA : S.BaseAssumptions) (d : Bool) :
    ∀ᵐ ω ∂P.μ, hA.lo ≤ S.YofD d ω ∧ S.YofD d ω ≤ hA.hi := by
  cases d
  · exact hA.bounded_zero
  · exact hA.bounded_one

/-- Binary-folded form of `integrable_Y1` / `integrable_Y0`. -/
lemma integrable_YofD (hA : S.BaseAssumptions) (d : Bool) :
    Integrable (S.YofD d) P.μ := by
  cases d
  · exact hA.integrable_Y0
  · exact hA.integrable_Y1

/-- The factual outcome `Y` is integrable.  Derived from arm integrability via
consistency (`factualY = Σ_d Y(d)·1{D=d}` a.e.), so it need not be assumed
separately. -/
lemma integrable_factualY (hA : S.BaseAssumptions) :
    Integrable S.factualY P.μ := by
  have hY1_ind :
      Integrable (fun ω => S.YofD true ω * S.dVar.indicator true ω) P.μ :=
    S.dVar.integrable_mul_indicator true hA.integrable_Y1 (S.measurable_YofD true)
  have hY0_ind :
      Integrable (fun ω => S.YofD false ω * S.dVar.indicator false ω) P.μ :=
    S.dVar.integrable_mul_indicator false hA.integrable_Y0 (S.measurable_YofD false)
  refine (hY1_ind.add hY0_ind).congr ?_
  filter_upwards with ω
  have htrue := congr_fun
    (POVar.factual_mul_indicator_eq_cfUnder_mul_indicator_fn
      hA.consistency S.yVar S.dVar true (Ne.symm S.hDY)) ω
  have hfalse := congr_fun
    (POVar.factual_mul_indicator_eq_cfUnder_mul_indicator_fn
      hA.consistency S.yVar S.dVar false (Ne.symm S.hDY)) ω
  have htrue' : S.YofD true ω * S.dVar.indicator true ω =
      S.factualY ω * S.dVar.indicator true ω := by
    simpa [POManskiIVSystem.YofD, POManskiIVSystem.factualY] using htrue.symm
  have hfalse' : S.YofD false ω * S.dVar.indicator false ω =
      S.factualY ω * S.dVar.indicator false ω := by
    simpa [POManskiIVSystem.YofD, POManskiIVSystem.factualY] using hfalse.symm
  have hsum := S.dVar.indicator_add_indicator_not ω
  calc
    S.YofD true ω * S.dVar.indicator true ω
        + S.YofD false ω * S.dVar.indicator false ω
        = S.factualY ω * S.dVar.indicator true ω
          + S.factualY ω * S.dVar.indicator false ω := by rw [htrue', hfalse']
    _ = S.factualY ω * (S.dVar.indicator true ω + S.dVar.indicator false ω) := by ring
    _ = S.factualY ω := by rw [hsum, mul_one]

end BaseAssumptions

/-- Mean independence of the potential outcomes from the instrument.  Stated
directly on `eventCondExp` — matches def:po-iv-manski-assumptions
letter-for-letter and avoids the stronger joint independence used in LATE. -/
structure MeanIndep (S : POManskiIVSystem P α) : Prop where
  meanIndep_one : ∀ z ∈ S.support,
    eventCondExp P.μ (S.zEvent z) (S.YofD true) = ∫ ω, S.YofD true ω ∂P.μ
  meanIndep_zero : ∀ z ∈ S.support,
    eventCondExp P.μ (S.zEvent z) (S.YofD false) = ∫ ω, S.YofD false ω ∂P.μ

/-- Monotone treatment response -- prop:po-iv-mtr, item 1.
`Y(0) ≤ Y(1)` almost surely. -/
structure MTR (S : POManskiIVSystem P α) : Prop where
  monotone : ∀ᵐ ω ∂P.μ, S.YofD false ω ≤ S.YofD true ω

/-- Monotone treatment selection -- prop:po-iv-mts.

`mts_one` asserts `E[Y(d) | D=0] ≤ E[Y(d) | D=1]` for each `d`. -/
structure MTS (S : POManskiIVSystem P α) : Prop where
  mts_one : ∀ (d : Bool),
    eventCondExp P.μ (S.dEvent false) (S.YofD d)
      ≤ eventCondExp P.μ (S.dEvent true) (S.YofD d)

/-- Monotone instrumental variable -- prop:po-iv-miv.

Bundles the linear order on the instrument value space `α` so that
`Setup.lean` stays generic.  Downstream files recover the order via
`letI := hMIV.inst`. -/
structure MIV (S : POManskiIVSystem P α) where
  inst : LinearOrder α
  monotone : ∀ (d : Bool) (z z' : α),
    z ∈ S.support → z' ∈ S.support → @LE.le α inst.toLE z z' →
      eventCondExp P.μ (S.zEvent z) (S.YofD d)
        ≤ eventCondExp P.μ (S.zEvent z') (S.YofD d)

end POManskiIVSystem

end PO
end Causalean
