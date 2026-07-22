/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.PO.ID.Partial.Manski.NonAsp
import Causalean.PO.ID.Partial.Manski.Combined
import Causalean.PO.ID.Partial.Basic

/-! # Manski Interval Forms

This file restates Manski scalar lower-and-upper bounds as closed interval
membership statements for the average treatment effect. It covers the
no-assumption, monotone treatment response with monotone treatment selection,
and monotone treatment response with monotone instrumental variable bounds.

These results add no new identification content; they translate existing
sandwich inequalities into the interval vocabulary used by the partial
identification engine. -/

set_option linter.unusedFintypeInType false

namespace Causalean
namespace PO

open MeasureTheory

namespace POManskiIVSystem

variable {P : POSystem} {α : Type*}
  [MeasurableSpace α] [MeasurableSingletonClass α]
  (S : POManskiIVSystem P α)

/-- **`Set.Icc` form of `manski_bounds_ATE`.**  The per-stratum-pair Manski
no-assumption sandwich, restated as membership in the reported interval. -/
theorem manski_ATE_mem_Icc [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) (hMI : S.MeanIndep)
    {z₁ z₀ : α} (hz₁ : z₁ ∈ S.support) (hz₀ : z₀ ∈ S.support) :
    S.ATE ∈ Set.Icc (S.lowerBound1 hA.lo z₁ - S.upperBound0 hA.hi z₀)
      (S.upperBound1 hA.hi z₁ - S.lowerBound0 hA.lo z₀) := by
  have h := S.manski_bounds_ATE hA hMI hz₁ hz₀
  exact Causalean.PartialID.mem_Icc_of_sandwich h.1 h.2

/-- **`Set.Icc` form of `manski_bounds_ATE_ciSup`.**  The sup/inf-aggregated
Manski no-assumption sandwich, restated as membership in the reported
interval. -/
theorem manski_ATE_mem_Icc_ciSup [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) (hMI : S.MeanIndep) (hne : S.support.Nonempty) :
    S.ATE ∈ Set.Icc
      ((⨆ z : ↑S.support, S.lowerBound1 hA.lo z.val)
        - (⨅ z : ↑S.support, S.upperBound0 hA.hi z.val))
      ((⨅ z : ↑S.support, S.upperBound1 hA.hi z.val)
        - (⨆ z : ↑S.support, S.lowerBound0 hA.lo z.val)) := by
  have h := S.manski_bounds_ATE_ciSup hA hMI hne
  exact Causalean.PartialID.mem_Icc_of_sandwich h.1 h.2

/-- **`Set.Icc` form of `mtr_mts_bounds_ATE`.**  The MTR + MTS sandwich,
restated as membership in `[0, E[Y|D=1] - E[Y|D=0]]`. -/
theorem mtr_mts_ATE_mem_Icc (hA : S.BaseAssumptions)
    (hMTR : S.MTR) (hMTS : S.MTS) :
    S.ATE ∈ Set.Icc 0
      (eventCondExp P.μ (S.dEvent true) S.factualY
        - eventCondExp P.μ (S.dEvent false) S.factualY) := by
  have h := S.mtr_mts_bounds_ATE hA hMTR hMTS
  exact Causalean.PartialID.mem_Icc_of_sandwich h.1 h.2

/-- **`Set.Icc` form of `mtr_miv_bounds_ATE`.**  The MTR + MIV sandwich,
restated as membership in `[0, ∫ (mUpper1(Z) - mLower0(Z))]`. -/
theorem mtr_miv_ATE_mem_Icc [IsFiniteMeasure P.μ] [Fintype α]
    (hA : S.BaseAssumptions) (hMTR : S.MTR) (hMIV : S.MIV) :
    letI := hMIV.inst
    S.ATE ∈ Set.Icc 0
      (∫ ω, S.mUpper1 hA (S.factualZ ω) - S.mLower0 hA (S.factualZ ω) ∂P.μ) := by
  letI := hMIV.inst
  have h := S.mtr_miv_bounds_ATE hA hMTR hMIV
  exact Causalean.PartialID.mem_Icc_of_sandwich h.1 h.2

end POManskiIVSystem

end PO
end Causalean
