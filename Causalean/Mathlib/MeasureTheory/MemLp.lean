/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# MemLp from square-integrability

This file proves `MemLp.of_measurable_of_integral_sq_le`, which turns an explicit
integrability witness for the square of a real measurable function into membership of
that function in L².
-/

open MeasureTheory

namespace Causalean.Mathlib.MeasureTheory

/-- Square-integrability upgrades measurability to `MemLp f 2`.

The explicit `Integrable (fun x => f x ^ 2) Q` hypothesis is essential:
Mathlib's Bochner integral convention makes a bare upper bound on
`∫ x, f x ^ 2 ∂Q` vacuous for non-integrable squares. -/
theorem MemLp.of_measurable_of_integral_sq_le
    {X : Type*} [MeasurableSpace X] {Q : Measure X}
    {f : X → ℝ}
    (hf_meas : Measurable f)
    (h_sq_int : Integrable (fun x => f x ^ 2) Q) :
    MemLp f 2 Q :=
  (MeasureTheory.memLp_two_iff_integrable_sq hf_meas.aestronglyMeasurable).2 h_sq_int

end Causalean.Mathlib.MeasureTheory
