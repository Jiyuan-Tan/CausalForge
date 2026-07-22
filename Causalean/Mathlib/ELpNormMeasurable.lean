/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Measurability of the L²-norm functional `ω ↦ ‖g ω‖_{L²(P)}`

For a parameter-dependent function `g : Ω → X → ℝ`, the map
`ω ↦ (eLpNorm (g ω) 2 P).toReal` is measurable provided `g` is jointly
measurable in `(ω, x)`.

This file provides two flavours, both consequences of Tonelli for the
parametric integral `ω ↦ ∫⁻ x, ‖g ω x‖₊^2 ∂P` followed by the post-processing
`(·)^(1/2)` and `.toReal`:

* `measurable_eLpNorm_two_toReal_of_uncurry`  — top-σ-algebra version: from
  joint measurability of `Function.uncurry g`.
* `measurable_eLpNorm_two_toReal_of_uncurry_of_factor`  — sub-σ-algebra
  version: from joint measurability wrt the sub-σ-algebra product.

These are causal-agnostic measurability facts and are candidates for
upstream contribution to Mathlib once stable.
-/

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Integral.Prod

/-! # Measurability of Parametric L2 Norms

This file proves that the parameter map sending a jointly measurable integrand to
its $L^2$ norm under a fixed measure is measurable. It supplies a causal-agnostic
Tonelli-based measurability tool for empirical-process and sample-splitting
arguments.

The top-σ-algebra lemma is `measurable_eLpNorm_two_toReal_of_uncurry`; the
sub-σ-algebra version, where joint measurability factors through
`mΩ × MeasurableSpace X`, is
`measurable_eLpNorm_two_toReal_of_uncurry_of_factor`. -/

namespace Causalean.Mathlib

open MeasureTheory ENNReal

variable {Ω X : Type*} [MeasurableSpace X]

/-- **L²-norm measurable from joint measurability (top σ-algebra).**
If `(ω, x) ↦ g ω x` is jointly measurable on `Ω × X` and `P` is `SFinite`,
then `ω ↦ (eLpNorm (g ω) 2 P).toReal` is measurable.

**Proof sketch.** `(eLpNorm (g ω) 2 P).toReal =
  ((∫⁻ x, ‖g ω x‖₊^2 ∂P)^(1/2 : ℝ)).toReal`.  Use:
* `Measurable.lintegral_prod_right` (Tonelli) on `(ω, x) ↦ ‖g ω x‖₊^2` —
  joint measurable from `hg` via `Measurable.pow_const`/`enorm`/`sq`.
* `Measurable.pow_const` (or `Measurable.rpow_const`) for the `(1/2)` power.
* `ENNReal.measurable_toReal` for the final `.toReal`. -/
lemma measurable_eLpNorm_two_toReal_of_uncurry
    [MeasurableSpace Ω] {P : Measure X} [SFinite P]
    {g : Ω → X → ℝ}
    (hg : Measurable (Function.uncurry g)) :
    Measurable (fun ω => (eLpNorm (g ω) 2 P).toReal) := by
  have h_int :
      Measurable (fun ω => ∫⁻ x, ‖g ω x‖ₑ ^ ((2 : ENNReal).toReal) ∂P) := by
    exact Measurable.lintegral_prod_right' ((hg.enorm).pow_const ((2 : ENNReal).toReal))
  have h_norm : Measurable (fun ω => eLpNorm (g ω) 2 P) := by
    simpa [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)] using
      (h_int.pow_const (1 / (2 : ENNReal).toReal))
  exact ENNReal.measurable_toReal.comp h_norm

/-- **L²-norm measurable wrt a sub-σ-algebra.**
If `(ω, x) ↦ g ω x` is jointly measurable wrt
`mΩ × MeasurableSpace X`, then `ω ↦ (eLpNorm (g ω) 2 P).toReal` is
`mΩ`-measurable.

**Proof sketch.** Apply `Measurable.lintegral_prod_right'` at the
sub-σ-algebra product level to `‖g ω x‖₊^2`, then post-process by
`(·)^(1/2)` and `.toReal`. -/
lemma measurable_eLpNorm_two_toReal_of_uncurry_of_factor
    {mΩ : MeasurableSpace Ω}
    {P : Measure X} [SFinite P]
    {g : Ω → X → ℝ}
    (hg_uncurry :
      @Measurable (Ω × X) ℝ
        (@Prod.instMeasurableSpace Ω X mΩ inferInstance) inferInstance
        (Function.uncurry g)) :
    Measurable[mΩ] (fun ω => (eLpNorm (g ω) 2 P).toReal) := by
  have h_int :
      Measurable[mΩ] (fun ω => ∫⁻ x, ‖g ω x‖ₑ ^ ((2 : ENNReal).toReal) ∂P) := by
    exact Measurable.lintegral_prod_right' ((hg_uncurry.enorm).pow_const ((2 : ENNReal).toReal))
  have h_norm : Measurable[mΩ] (fun ω => eLpNorm (g ω) 2 P) := by
    simpa [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)] using
      (h_int.pow_const (1 / (2 : ENNReal).toReal))
  exact ENNReal.measurable_toReal.comp h_norm

end Causalean.Mathlib
