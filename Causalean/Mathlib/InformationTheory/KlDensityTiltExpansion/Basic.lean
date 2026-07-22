/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib

/-!
# The linear density tilt and its probability-measure property

For a probability measure `μ` on a measurable space `Z` and a bounded, mean-zero
"score" `s : Z → ℝ`, the **linear density tilt** at strength `h : ℝ` is the
measure

    tiltMeasure μ s h  :=  μ.withDensity (fun y => ENNReal.ofReal (1 + h · s y)).

This file sets up that construction and proves the elementary facts needed for
the second-order Kullback–Leibler expansion in `KLExpansion.lean`:

* `tiltMeasure_absolutelyContinuous` — the tilt is absolutely continuous wrt `μ`;
* `tiltDensity_nonneg` — for `|h| · C ≤ 1` the density `1 + h · s` is `≥ 0`
  everywhere (bounded score `|s| ≤ C`);
* `integrable_of_bounded` — a bounded measurable score is `μ`-integrable
  (finite measure);
* `integral_tiltDensity` — the density integrates to `1` (mean-zero score);
* `isProbabilityMeasure_tiltMeasure` — hence for small `|h|` the tilt is a
  probability measure.

Reference: van der Vaart, *Asymptotic Statistics*, Ch. 5 (differentiability in
quadratic mean / local asymptotic normality).
-/

open MeasureTheory Real Filter Topology
open scoped ENNReal

namespace Causalean.Mathlib.InformationTheory.KlDensityTiltExpansion

variable {Z : Type*} [MeasurableSpace Z]

/-- The **linear density tilt** of `μ` by the score `s` at strength `h`:
`tiltMeasure μ s h = μ.withDensity (y ↦ ENNReal.ofReal (1 + h · s y))`.  When
`1 + h · s ≥ 0` a.e. and `s` is mean-zero this is again a probability measure
(see `isProbabilityMeasure_tiltMeasure`). -/
noncomputable def tiltMeasure (μ : Measure Z) (s : Z → ℝ) (h : ℝ) : Measure Z :=
  μ.withDensity (fun y => ENNReal.ofReal (1 + h * s y))

/-- The tilt is absolutely continuous with respect to the base measure `μ`
(any `withDensity` measure is). -/
lemma tiltMeasure_absolutelyContinuous (μ : Measure Z) (s : Z → ℝ) (h : ℝ) :
    tiltMeasure μ s h ≪ μ :=
  withDensity_absolutelyContinuous _ _

/-- For a bounded score `|s y| ≤ C` and tilt strength with `|h| · C ≤ 1`, the tilt
density `1 + h · s y` is nonnegative: `|h · s y| ≤ |h| · C ≤ 1`.

Proof sketch: `|h * s y| = |h| * |s y| ≤ |h| * C ≤ 1`, hence `h * s y ≥ -1`, i.e.
`1 + h * s y ≥ 0`. -/
lemma tiltDensity_nonneg {s : Z → ℝ} {C h : ℝ} (hsC : ∀ y, |s y| ≤ C)
    (hh : |h| * C ≤ 1) (y : Z) : 0 ≤ 1 + h * s y := by
  have h_abs : |h * s y| ≤ |h| * C := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hsC y) (abs_nonneg h)
  have h_lower : -1 ≤ h * s y := by
    have h_bound : -(|h| * C) ≤ h * s y := by
      have h_neg : -(|h| * C) ≤ -|h * s y| := by
        rw [neg_le_neg_iff]
        exact h_abs
      exact le_trans h_neg (neg_abs_le _)
    linarith
  linarith

/-- A bounded measurable function is integrable with respect to a finite measure:
`|s| ≤ C` is dominated by the integrable constant `C`.

Proof sketch: `Integrable.of_bound`/`memℒp` route — `s` is a.e.-strongly-measurable
and `‖s‖ ≤ C` a.e. with `C` integrable on the finite measure `μ`. -/
lemma integrable_of_bounded {μ : Measure Z} [IsFiniteMeasure μ] {s : Z → ℝ} {C : ℝ}
    (hs_meas : Measurable s) (hsC : ∀ y, |s y| ≤ C) : Integrable s μ := by
  exact Integrable.of_bound hs_meas.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hsC y)

/-- The tilt density integrates to `1`: `∫ (1 + h · s) dμ = 1 + h · ∫ s = 1` for a
probability measure `μ` and a mean-zero score `s`.

Proof sketch: split `∫ (1 + h · s) = ∫ 1 + h · ∫ s` via `integral_add`
(`s` integrable by `integrable_of_bounded`), then `∫ 1 = 1` (probability measure)
and `∫ s = 0`. -/
lemma integral_tiltDensity {μ : Measure Z} [IsProbabilityMeasure μ] {s : Z → ℝ} {C h : ℝ}
    (hs_meas : Measurable s) (hsC : ∀ y, |s y| ≤ C) (hs_mean : ∫ y, s y ∂μ = 0) :
    ∫ y, (1 + h * s y) ∂μ = 1 := by
  have hs_int : Integrable s μ := integrable_of_bounded hs_meas hsC
  calc
    ∫ y, (1 + h * s y) ∂μ
        = ∫ y, (1 : ℝ) + h * s y ∂μ := rfl
    _ = ∫ y, (1 : ℝ) ∂μ + ∫ y, h * s y ∂μ := by
        rw [integral_add (integrable_const 1) (hs_int.const_mul h)]
    _ = 1 + h * ∫ y, s y ∂μ := by
        rw [integral_const, probReal_univ, one_smul, integral_const_mul]
    _ = 1 := by
        simp [hs_mean]

/-- **The linear tilt is a probability measure for small `|h|`.**  For a probability
measure `μ`, a bounded mean-zero score `|s| ≤ C` with `∫ s = 0`, and tilt strength
`|h| · C ≤ 1`, the measure `tiltMeasure μ s h` is a probability measure.

Proof sketch: its total mass is `withDensity f univ = ∫⁻ f dμ`; since the density
`f = ofReal (1 + h · s)` is nonnegative (`tiltDensity_nonneg`) and integrable, this
equals `ENNReal.ofReal (∫ (1 + h · s) dμ) = ENNReal.ofReal 1 = 1`
(`integral_tiltDensity`). -/
lemma isProbabilityMeasure_tiltMeasure {μ : Measure Z} [IsProbabilityMeasure μ]
    {s : Z → ℝ} {C h : ℝ} (hs_meas : Measurable s) (hsC : ∀ y, |s y| ≤ C)
    (hs_mean : ∫ y, s y ∂μ = 0) (hh : |h| * C ≤ 1) :
    IsProbabilityMeasure (tiltMeasure μ s h) := by
  constructor
  have h_int : Integrable (fun y => (1 : ℝ) + h * s y) μ :=
    (integrable_const 1).add ((integrable_of_bounded hs_meas hsC).const_mul h)
  have h_nonneg : 0 ≤ᵐ[μ] fun y => (1 : ℝ) + h * s y :=
    Filter.Eventually.of_forall fun y => tiltDensity_nonneg hsC hh y
  have hmass :
      (μ.withDensity (fun y => ENNReal.ofReal (1 + h * s y))) Set.univ
        = ENNReal.ofReal (∫ y, (1 + h * s y) ∂μ) := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal h_int h_nonneg]
  rw [tiltMeasure, hmass, integral_tiltDensity hs_meas hsC hs_mean]
  norm_num

end Causalean.Mathlib.InformationTheory.KlDensityTiltExpansion
