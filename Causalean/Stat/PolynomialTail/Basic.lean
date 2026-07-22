/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Polynomial lower-tail moments: setup, integrands, and basic facts

Real-analysis infrastructure for the small-value (lower-tail) asymptotics of a
bounded positive random variable.  Fix a probability measure `P` and a measurable
`U : Ω → ℝ` with `0 < U ≤ 1` almost surely.  The polynomial lower-tail hypothesis
`PolyTail P U κ t₀ cm cp` pins the lower CDF to a power law near zero:

    ∀ t ∈ (0, t₀],  cm · tᵏ ≤ P{U ≤ t} ≤ cp · tᵏ.

The two truncated inverse moments studied downstream are

    I P U λ  =  ∫ U / (max U λ)²            ( = 1/U on {U ≥ λ}, = U/λ² on {U < λ} )
    J P U λ  =  ∫ (max U λ)⁻¹               ( = 1/U on {U ≥ λ}, = 1/λ  on {U < λ} )

together with the leftover trimming weight `wλ = 1 − U/(max U λ) ∈ [0,1]`, supported
on `{U < λ}`.

This file provides the foundation: the `PolyTail` structure, the three definitions,
measurability of the integrands, the elementary mass bound `P{U < λ} ≤ cp λᵏ`, and
integrability of the bounded integrands.  The three-regime downstream bounds live in
`Stat/PolynomialTail/TailIntegralBounds.lean`,
`Stat/PolynomialTail/MomentJBounds.lean`, and `Stat/PolynomialTail/MomentIBounds.lean`.
-/

import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Polynomial lower-tail setup

This module defines the reusable setup for polynomial lower-tail calculations.  The structure
`PolyTail P U kappa t0 cm cp` states that the lower CDF of a positive `[0,1]`-valued variable
`U` is squeezed between `cm * t ^ kappa` and `cp * t ^ kappa` on `(0, t0]`; `TailSetup P U`
records the measurability and almost-sure bounds `0 < U <= 1`.

The main integrands are the truncated denominator `truncDen U lam`, the inverse second moment
`invMomentI P U lam = int U / (max U lam)^2`, the inverse first moment
`invMomentJ P U lam = int (max U lam)^(-1)`, and the trimming weight
`trimWeight U lam = 1 - U / (max U lam)`.  The file proves their measurability, elementary
pointwise bounds, the open lower-level-set mass bound `measureReal_lt_le`, and bounded
integrability lemmas used by the layer-cake and regime-bound modules.
-/

namespace Causalean.Stat.PolynomialTail

open MeasureTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ## The polynomial-tail hypothesis -/

/-- **Polynomial lower tail.**  For a measurable `[0,1]`-valued function `U`, says
that the lower CDF `t ↦ P{U ≤ t}` is squeezed between `cm tᵏ` and `cp tᵏ` on the
window `(0, t₀]`, with exponent `κ > 0`, a window `t₀ ∈ (0,1)`, and constants
`0 < cm < cp`.  This is the sole distributional input to the inverse-moment
asymptotics. -/
structure PolyTail (P : Measure Ω) (U : Ω → ℝ) (κ t₀ cm cp : ℝ) : Prop where
  /-- The tail exponent is positive. -/
  kappa_pos : 0 < κ
  /-- The window upper endpoint is positive. -/
  t0_pos : 0 < t₀
  /-- The window endpoint is `< 1`. -/
  t0_lt_one : t₀ < 1
  /-- The lower constant is positive. -/
  cm_pos : 0 < cm
  /-- The lower constant is strictly below the upper constant. -/
  cm_lt_cp : cm < cp
  /-- Lower polynomial bound on the CDF over the window. -/
  tail_lower : ∀ t, 0 < t → t ≤ t₀ → cm * t ^ κ ≤ P.real {ω | U ω ≤ t}
  /-- Upper polynomial bound on the CDF over the window. -/
  tail_upper : ∀ t, 0 < t → t ≤ t₀ → P.real {ω | U ω ≤ t} ≤ cp * t ^ κ

namespace PolyTail

variable {U : Ω → ℝ} {κ t₀ cm cp : ℝ}

/-- The upper constant is positive. -/
theorem cp_pos (h : PolyTail P U κ t₀ cm cp) : 0 < cp := lt_trans h.cm_pos h.cm_lt_cp

/-- The window endpoint is positive and `< 1` packaged together. -/
theorem t0_mem : PolyTail P U κ t₀ cm cp → 0 < t₀ ∧ t₀ < 1 :=
  fun h => ⟨h.t0_pos, h.t0_lt_one⟩

end PolyTail

/-! ## The tail setup -/

/-- **Tail setup.**  Bundles the structural hypotheses on `U`: measurability and
`0 < U ≤ 1` almost surely.  `IsProbabilityMeasure P` is required separately as a
typeclass on the theorems that need it. -/
structure TailSetup (P : Measure Ω) (U : Ω → ℝ) : Prop where
  /-- `U` is measurable. -/
  measurable : Measurable U
  /-- `U` is a.s. positive. -/
  pos : ∀ᵐ ω ∂P, 0 < U ω
  /-- `U` is a.s. bounded by `1`. -/
  le_one : ∀ᵐ ω ∂P, U ω ≤ 1

/-! ## The three definitions -/

/-- The truncated denominator `max U λ` shared by the inverse-moment integrands. -/
noncomputable def truncDen (U : Ω → ℝ) (lam : ℝ) (ω : Ω) : ℝ := max (U ω) lam

/-- `I P U λ = ∫ U / (max U λ)²`.  Equals `1/U` on `{U ≥ λ}` and `U/λ²` on
`{U < λ}`; the truncated inverse *second moment*. -/
noncomputable def invMomentI (P : Measure Ω) (U : Ω → ℝ) (lam : ℝ) : ℝ :=
  ∫ ω, U ω / (max (U ω) lam) ^ 2 ∂P

/-- `J P U λ = ∫ (max U λ)⁻¹`.  Equals `1/U` on `{U ≥ λ}` and `1/λ` on `{U < λ}`;
the truncated inverse *first moment*. -/
noncomputable def invMomentJ (P : Measure Ω) (U : Ω → ℝ) (lam : ℝ) : ℝ :=
  ∫ ω, (max (U ω) lam)⁻¹ ∂P

/-- The leftover trimming weight `wλ ω = 1 − U/(max U λ) ∈ [0,1]`, supported on `{U < λ}`. -/
noncomputable def trimWeight (U : Ω → ℝ) (lam : ℝ) (ω : Ω) : ℝ :=
  1 - U ω / (max (U ω) lam)

/-! ## Measurability of the integrands -/

variable {U : Ω → ℝ} {lam : ℝ}

/-- The truncated denominator is measurable when `U` is measurable. -/
theorem measurable_truncDen (hU : Measurable U) :
    Measurable (truncDen U lam) :=
  hU.max measurable_const

/-- The inverse second-moment integrand is measurable when `U` is measurable. -/
theorem measurable_invMomentI_integrand (hU : Measurable U) :
    Measurable (fun ω => U ω / (max (U ω) lam) ^ 2) :=
  hU.div ((hU.max measurable_const).pow_const 2)

/-- The inverse first-moment integrand is measurable when `U` is measurable. -/
theorem measurable_invMomentJ_integrand (hU : Measurable U) :
    Measurable (fun ω => (max (U ω) lam)⁻¹) :=
  (hU.max measurable_const).inv

/-- The leftover trimming weight is measurable when `U` is measurable. -/
theorem measurable_trimWeight (hU : Measurable U) :
    Measurable (trimWeight U lam) :=
  measurable_const.sub (hU.div (hU.max measurable_const))

/-! ## Positivity and pointwise bounds on the denominator -/

omit [MeasurableSpace Ω] in
/-- `max U λ ≥ λ` (pointwise, no hypotheses). -/
theorem le_truncDen (ω : Ω) : lam ≤ truncDen U lam ω := le_max_right _ _

omit [MeasurableSpace Ω] in
/-- For `0 < λ`, the denominator is positive. -/
theorem truncDen_pos (hlam : 0 < lam) (ω : Ω) : 0 < truncDen U lam ω :=
  lt_of_lt_of_le hlam (le_max_right _ _)

/-! ## Elementary mass bound -/

variable {κ t₀ cm cp : ℝ}

/-- **Mass below `λ`.**  The open lower level set `{U < λ}` has mass at most
`cp · λᵏ`.  (Immediate from monotonicity and the upper tail at `t = λ`.) -/
theorem measureReal_lt_le [IsFiniteMeasure P] (h : PolyTail P U κ t₀ cm cp)
    (hlam_pos : 0 < lam) (hlam_le : lam ≤ t₀) :
    P.real {ω | U ω < lam} ≤ cp * lam ^ κ := by
  have hsub : {ω | U ω < lam} ⊆ {ω | U ω ≤ lam} := fun ω (hω : U ω < lam) => hω.le
  exact le_trans (measureReal_mono hsub (measure_ne_top P _))
    (h.tail_upper lam hlam_pos hlam_le)

/-! ## Pointwise bounds and integrability of the integrands -/

/-- On `{0 < U ≤ 1}` the `I`-integrand is squeezed in `[0, 1/λ²]`. -/
theorem invMomentI_integrand_mem (hlam : 0 < lam) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    0 ≤ x / (max x lam) ^ 2 ∧ x / (max x lam) ^ 2 ≤ (lam ^ 2)⁻¹ := by
  have hden : 0 < max x lam := lt_of_lt_of_le hlam (le_max_right _ _)
  have hden2 : 0 < (max x lam) ^ 2 := by positivity
  refine ⟨div_nonneg hx0.le hden2.le, ?_⟩
  rw [div_le_iff₀ hden2, inv_mul_eq_div, le_div_iff₀ (by positivity : (0:ℝ) < lam ^ 2)]
  have hlx : lam ≤ max x lam := le_max_right _ _
  nlinarith [hx1, hlx, hlam, sq_nonneg lam, mul_le_mul hlx hlx hlam.le hden.le]

/-- The `J`-integrand is squeezed in `[0, 1/λ]`. -/
theorem invMomentJ_integrand_mem (hlam : 0 < lam) (x : ℝ) :
    0 ≤ (max x lam)⁻¹ ∧ (max x lam)⁻¹ ≤ lam⁻¹ := by
  have hden : 0 < max x lam := lt_of_lt_of_le hlam (le_max_right _ _)
  exact ⟨inv_nonneg.mpr hden.le, by
    rw [inv_le_inv₀ hden hlam]; exact le_max_right _ _⟩

omit [MeasurableSpace Ω] in
/-- The leftover weight lies in `[0,1]` whenever `U > 0`. -/
theorem trimWeight_mem (hlam : 0 < lam) {x : ℝ} (hx0 : 0 < x) :
    0 ≤ 1 - x / (max x lam) ∧ 1 - x / (max x lam) ≤ 1 := by
  have hden : 0 < max x lam := lt_of_lt_of_le hlam (le_max_right _ _)
  have hxle : x ≤ max x lam := le_max_left _ _
  refine ⟨by rw [sub_nonneg, div_le_one hden]; exact hxle, ?_⟩
  have : 0 ≤ x / max x lam := div_nonneg hx0.le hden.le
  linarith

/-- The `I`-integrand is integrable (bounded a.e. on a probability space). -/
theorem integrable_invMomentI_integrand [IsProbabilityMeasure P]
    (hsetup : TailSetup P U) (hlam : 0 < lam) :
    Integrable (fun ω => U ω / (max (U ω) lam) ^ 2) P := by
  refine Integrable.mono' (integrable_const (lam ^ 2)⁻¹)
    (measurable_invMomentI_integrand hsetup.measurable).aestronglyMeasurable ?_
  filter_upwards [hsetup.pos, hsetup.le_one] with ω hpos hle
  rw [Real.norm_eq_abs, abs_of_nonneg (invMomentI_integrand_mem hlam hpos hle).1]
  exact (invMomentI_integrand_mem hlam hpos hle).2

/-- The `J`-integrand is integrable. -/
theorem integrable_invMomentJ_integrand [IsProbabilityMeasure P]
    (hsetup : TailSetup P U) (hlam : 0 < lam) :
    Integrable (fun ω => (max (U ω) lam)⁻¹) P := by
  refine Integrable.mono' (integrable_const lam⁻¹)
    (measurable_invMomentJ_integrand hsetup.measurable).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (invMomentJ_integrand_mem hlam (U ω)).1]
  exact (invMomentJ_integrand_mem hlam (U ω)).2

/-- The leftover weight is integrable. -/
theorem integrable_trimWeight [IsProbabilityMeasure P]
    (hsetup : TailSetup P U) (hlam : 0 < lam) :
    Integrable (trimWeight U lam) P := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_trimWeight hsetup.measurable).aestronglyMeasurable ?_
  filter_upwards [hsetup.pos] with ω hpos
  rw [Real.norm_eq_abs, trimWeight, abs_of_nonneg (trimWeight_mem hlam hpos).1]
  exact (trimWeight_mem hlam hpos).2

end Causalean.Stat.PolynomialTail
