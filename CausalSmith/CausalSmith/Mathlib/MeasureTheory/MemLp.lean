/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# MemLp from square-integrability

If `f : X → ℝ` is measurable and `f ^ 2` is Bochner-integrable, then `f`
belongs to `Lᵖ` for `p = 2`.

This statement is purely a Mathlib-level regularity bridge between an
explicit square-integrability witness and `MemLp f 2 Q`, and depends only on
standard measure theory. The real Bochner bound `∫ f ^ 2 ≤ A` alone is not
enough in Mathlib, because `∫` is defined as `0` for non-integrable functions.
-/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

namespace CausalSmith.Mathlib.MeasureTheory

/-- Square-integrability upgrades measurability to `MemLp f 2`.

The explicit `Integrable (fun x => f x ^ 2) Q` hypothesis is essential:
Mathlib's Bochner integral convention makes a bare upper bound on
`∫ x, f x ^ 2 ∂Q` vacuous for non-integrable squares. -/
theorem MemLp.of_measurable_of_integral_sq_le
    {X : Type*} [MeasurableSpace X] {Q : Measure X}
    {f : X → ℝ} {A : ℝ}
    (hf_meas : Measurable f)
    (h_sq_int : Integrable (fun x => f x ^ 2) Q)
    (_hA_nn : 0 ≤ A)
    (_h_sq_le : ∫ x, f x ^ 2 ∂Q ≤ A) :
    MemLp f 2 Q :=
  (MeasureTheory.memLp_two_iff_integrable_sq hf_meas.aestronglyMeasurable).2 h_sq_int

end CausalSmith.Mathlib.MeasureTheory
