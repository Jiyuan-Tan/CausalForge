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
integrability witness for the squared norm of an almost-everywhere strongly measurable
function into membership of that function in L².
-/

open MeasureTheory

namespace Causalean.Mathlib.MeasureTheory

/-- Almost-everywhere strong measurability together with integrability of the squared norm puts a
normed-vector-valued function in L².

The explicit integrability hypothesis is essential:
Mathlib's Bochner integral convention makes a bare upper bound on
`∫ x, f x ^ 2 ∂Q` vacuous for non-integrable squares. -/
theorem MemLp.of_measurable_of_integral_sq_le
    {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F] {Q : Measure X}
    {f : X → F}
    (hf_meas : AEStronglyMeasurable f Q)
    (h_sq_int : Integrable (fun x => ‖f x‖ ^ 2) Q) :
    MemLp f 2 Q :=
  (MeasureTheory.memLp_two_iff_integrable_sq_norm hf_meas).2 h_sq_int

end Causalean.Mathlib.MeasureTheory
