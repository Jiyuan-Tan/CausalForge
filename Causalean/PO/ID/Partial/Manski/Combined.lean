/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.PO.ID.Partial.Manski.MTR
import Causalean.PO.ID.Partial.Manski.MTS
import Causalean.PO.ID.Partial.Manski.MIV

/-! # Manski Combined Bounds

This file proves Manski corollaries that combine shape restrictions. Monotone
treatment response with monotone treatment selection gives a nonnegative
average treatment effect bounded above by the observed treated-control mean
contrast, while monotone treatment response with a monotone instrument gives a
nonnegative effect bounded above by the integrated monotone-instrument
envelope.

The arguments reuse the separate monotonicity, selection, and instrument
bounds proved in the preceding Manski modules. -/

set_option linter.unusedFintypeInType false

namespace Causalean
namespace PO

open MeasureTheory

namespace POManskiIVSystem

variable {P : POSystem} {α : Type*}
  [MeasurableSpace α] [MeasurableSingletonClass α]
  (S : POManskiIVSystem P α)

/-- **cor:po-iv-mtr-mts.** Under [the baseline Manski assumptions](hyp:hA), [monotone treatment
response, `Y(0) ≤ Y(1)` almost surely](hyp:hMTR), and [monotone treatment selection — each
potential outcome's mean given control is no larger than its mean given
treatment](hyp:hMTS), [the average treatment effect is nonnegative and is upper-bounded by the
naive observed contrast `E[Y | D=1] − E[Y | D=0]`](goal). -/
theorem mtr_mts_bounds_ATE (hA : S.BaseAssumptions)
    (hMTR : S.MTR) (hMTS : S.MTS) :
    0 ≤ S.ATE ∧
    S.ATE ≤ eventCondExp P.μ (S.dEvent true) S.factualY
              - eventCondExp P.μ (S.dEvent false) S.factualY := by
  refine ⟨S.mtr_nonneg_ATE hA hMTR, ?_⟩
  -- MTS gives E[Y(1)] ≤ E[Y|D=1] and E[Y|D=0] ≤ E[Y(0)].
  have hU := S.mts_E_Y1_le_condY1 hA hMTS
  have hL := S.mts_condY0_le_E_Y0 hA hMTS
  have hATE_eq :
      S.ATE = ∫ ω, S.YofD true ω ∂P.μ - ∫ ω, S.YofD false ω ∂P.μ := by
    unfold ATE
    exact integral_sub hA.integrable_Y1 hA.integrable_Y0
  rw [hATE_eq]; linarith

/-- **cor:po-iv-mtr-miv.** Under [the baseline Manski assumptions](hyp:hA),
[monotone treatment response, `Y(0) ≤ Y(1)` almost surely](hyp:hMTR), and [a monotone
instrumental variable — the conditional mean of each potential outcome is nondecreasing in the
instrument value across its support](hyp:hMIV), [the average treatment effect is nonnegative and
is upper-bounded by the integrated monotone-instrument envelope contrast
`∫ (mUpper1(Z) − mLower0(Z))`](goal). -/
theorem mtr_miv_bounds_ATE [IsFiniteMeasure P.μ] [Fintype α]
    (hA : S.BaseAssumptions) (hMTR : S.MTR) (hMIV : S.MIV) :
    letI := hMIV.inst
    0 ≤ S.ATE ∧
    S.ATE ≤
      ∫ ω, S.mUpper1 hA (S.factualZ ω) - S.mLower0 hA (S.factualZ ω) ∂P.μ := by
  letI := hMIV.inst
  refine ⟨S.mtr_nonneg_ATE hA hMTR, ?_⟩
  exact (S.miv_bounds_ATE hA hMIV).2

end POManskiIVSystem

end PO
end Causalean
