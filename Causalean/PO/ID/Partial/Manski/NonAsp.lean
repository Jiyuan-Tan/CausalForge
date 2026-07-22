/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Manski bounds: baseline (no additional shape restrictions)

Integral-level stratum bounds and the ATE sandwich (prop:po-iv-manski),
obtained by combining the conditional stratum bounds from `Helpers.lean`
with mean-independence (`MeanIndep`).
-/

import Causalean.PO.ID.Partial.Manski.Helpers

/-! # Baseline non-asymptotic Manski bounds

This file proves the baseline integral-level Manski bounds without additional
shape restrictions. Conditional stratum bounds from the shared helper file are
combined with mean independence to place the ATE between the worst-case lower
and upper endpoints.

The file exposes per-stratum integral bounds for `Y(1)` and `Y(0)`, the
two-stratum ATE sandwich `manski_bounds_ATE`, and the support-aggregated
supremum/infimum statement `manski_bounds_ATE_ciSup`.
-/

namespace Causalean
namespace PO

open MeasureTheory

namespace POManskiIVSystem

variable {P : POSystem} {α : Type*}
  [MeasurableSpace α] [MeasurableSingletonClass α]
  (S : POManskiIVSystem P α)

/-! ### Integral-level stratum bounds

Under the full assumptions (base + mean independence), the conditional
stratum bounds collapse to bounds on the unconditional integral. -/

/-- Stratum-level lower bound on `E[Y(1)]`. -/
theorem lowerBound1_le_integral_Y1 [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) (hMI : S.MeanIndep) {z : α} (hz : z ∈ S.support) :
    S.lowerBound1 hA.lo z ≤ ∫ ω, S.YofD true ω ∂P.μ :=
  (S.lowerBound1_le_cond_Y1 hA hz).trans_eq (hMI.meanIndep_one z hz)

/-- Stratum-level upper bound on `E[Y(1)]`. -/
theorem integral_Y1_le_upperBound1 [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) (hMI : S.MeanIndep) {z : α} (hz : z ∈ S.support) :
    ∫ ω, S.YofD true ω ∂P.μ ≤ S.upperBound1 hA.hi z :=
  (hMI.meanIndep_one z hz).symm.trans_le (S.cond_Y1_le_upperBound1 hA hz)

/-- Stratum-level lower bound on `E[Y(0)]`. -/
theorem lowerBound0_le_integral_Y0 [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) (hMI : S.MeanIndep) {z : α} (hz : z ∈ S.support) :
    S.lowerBound0 hA.lo z ≤ ∫ ω, S.YofD false ω ∂P.μ :=
  (S.lowerBound0_le_cond_Y0 hA hz).trans_eq (hMI.meanIndep_zero z hz)

/-- Stratum-level upper bound on `E[Y(0)]`. -/
theorem integral_Y0_le_upperBound0 [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) (hMI : S.MeanIndep) {z : α} (hz : z ∈ S.support) :
    ∫ ω, S.YofD false ω ∂P.μ ≤ S.upperBound0 hA.hi z :=
  (hMI.meanIndep_zero z hz).symm.trans_le (S.cond_Y0_le_upperBound0 hA hz)

/-! ### Per-stratum-pair ATE sandwich

For any two strata `z₁, z₀ ∈ support(Z)`, the ATE is sandwiched between
the `z₁`-lower / `z₀`-upper pair on one side and the `z₁`-upper / `z₀`-lower
pair on the other. -/
/-- **Manski bounds for the ATE under an imperfect instrument.** For any two
instrument strata `z₁` and `z₀` in the support of the instrument, the average
treatment effect is sandwiched between the worst-case lower bound formed from
the `z₁`-stratum lower envelope and `z₀`-stratum upper envelope, and the
corresponding upper bound with the roles reversed — using only bounded outcomes
and mean independence of the instrument, with no selection assumptions. -/
theorem manski_bounds_ATE [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) (hMI : S.MeanIndep)
    {z₁ z₀ : α} (hz₁ : z₁ ∈ S.support) (hz₀ : z₀ ∈ S.support) :
    S.lowerBound1 hA.lo z₁ - S.upperBound0 hA.hi z₀ ≤ S.ATE
    ∧ S.ATE ≤ S.upperBound1 hA.hi z₁ - S.lowerBound0 hA.lo z₀ := by
  have hL1 : S.lowerBound1 hA.lo z₁ ≤ ∫ ω, S.YofD true ω ∂P.μ :=
    S.lowerBound1_le_integral_Y1 hA hMI hz₁
  have hU1 : ∫ ω, S.YofD true ω ∂P.μ ≤ S.upperBound1 hA.hi z₁ :=
    S.integral_Y1_le_upperBound1 hA hMI hz₁
  have hL0 : S.lowerBound0 hA.lo z₀ ≤ ∫ ω, S.YofD false ω ∂P.μ :=
    S.lowerBound0_le_integral_Y0 hA hMI hz₀
  have hU0 : ∫ ω, S.YofD false ω ∂P.μ ≤ S.upperBound0 hA.hi z₀ :=
    S.integral_Y0_le_upperBound0 hA hMI hz₀
  have hATE_eq :
      S.ATE = ∫ ω, S.YofD true ω ∂P.μ - ∫ ω, S.YofD false ω ∂P.μ := by
    unfold ATE
    exact integral_sub hA.integrable_Y1 hA.integrable_Y0
  refine ⟨?_, ?_⟩
  · rw [hATE_eq]; linarith
  · rw [hATE_eq]; linarith

/-! ### Sup / inf aggregation over the support -/

/-- Sup-over-support form of `lowerBound1_le_integral_Y1`. -/
theorem ciSup_lowerBound1_le_integral_Y1 [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) (hMI : S.MeanIndep) (hne : S.support.Nonempty) :
    ⨆ z : ↑S.support, S.lowerBound1 hA.lo z.val ≤ ∫ ω, S.YofD true ω ∂P.μ := by
  haveI : Nonempty ↑S.support := hne.to_subtype
  exact ciSup_le (fun z => S.lowerBound1_le_integral_Y1 hA hMI z.property)

/-- Inf-over-support form of `integral_Y1_le_upperBound1`. -/
theorem integral_Y1_le_ciInf_upperBound1 [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) (hMI : S.MeanIndep) (hne : S.support.Nonempty) :
    ∫ ω, S.YofD true ω ∂P.μ ≤ ⨅ z : ↑S.support, S.upperBound1 hA.hi z.val := by
  haveI : Nonempty ↑S.support := hne.to_subtype
  exact le_ciInf (fun z => S.integral_Y1_le_upperBound1 hA hMI z.property)

/-- Sup-over-support form of `lowerBound0_le_integral_Y0`. -/
theorem ciSup_lowerBound0_le_integral_Y0 [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) (hMI : S.MeanIndep) (hne : S.support.Nonempty) :
    ⨆ z : ↑S.support, S.lowerBound0 hA.lo z.val ≤ ∫ ω, S.YofD false ω ∂P.μ := by
  haveI : Nonempty ↑S.support := hne.to_subtype
  exact ciSup_le (fun z => S.lowerBound0_le_integral_Y0 hA hMI z.property)

/-- Inf-over-support form of `integral_Y0_le_upperBound0`. -/
theorem integral_Y0_le_ciInf_upperBound0 [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) (hMI : S.MeanIndep) (hne : S.support.Nonempty) :
    ∫ ω, S.YofD false ω ∂P.μ ≤ ⨅ z : ↑S.support, S.upperBound0 hA.hi z.val := by
  haveI : Nonempty ↑S.support := hne.to_subtype
  exact le_ciInf (fun z => S.integral_Y0_le_upperBound0 hA hMI z.property)

/-- **Manski bounds for the ATE** in sup/inf form: sup of lowers minus inf
of uppers on one side, inf of uppers minus sup of lowers on the other. -/
theorem manski_bounds_ATE_ciSup [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) (hMI : S.MeanIndep) (hne : S.support.Nonempty) :
    (⨆ z : ↑S.support, S.lowerBound1 hA.lo z.val)
        - (⨅ z : ↑S.support, S.upperBound0 hA.hi z.val) ≤ S.ATE
    ∧ S.ATE ≤ (⨅ z : ↑S.support, S.upperBound1 hA.hi z.val)
                - (⨆ z : ↑S.support, S.lowerBound0 hA.lo z.val) := by
  have hL1 := S.ciSup_lowerBound1_le_integral_Y1 hA hMI hne
  have hU1 := S.integral_Y1_le_ciInf_upperBound1 hA hMI hne
  have hL0 := S.ciSup_lowerBound0_le_integral_Y0 hA hMI hne
  have hU0 := S.integral_Y0_le_ciInf_upperBound0 hA hMI hne
  have hATE_eq :
      S.ATE = ∫ ω, S.YofD true ω ∂P.μ - ∫ ω, S.YofD false ω ∂P.μ := by
    unfold ATE
    exact integral_sub hA.integrable_Y1 hA.integrable_Y0
  refine ⟨?_, ?_⟩
  · rw [hATE_eq]; linarith
  · rw [hATE_eq]; linarith

end POManskiIVSystem

end PO
end Causalean
