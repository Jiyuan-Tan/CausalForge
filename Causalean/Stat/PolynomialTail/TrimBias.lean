/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# General bias bound for the leftover trimming weight

The trimming weight `wλ = 1 − U/(max U λ) ∈ [0,1]` vanishes on `{U ≥ λ}` and is
therefore supported on the small set `{U < λ}` (mass `≤ cp · λᵏ` under `PolyTail`).
Coupling this with a Hölder envelope `|g| ≤ Cβ · λ^β` on `{U < λ}` gives the general
*bias* bound

    | ∫ wλ · g ∂P |  ≤  Cβ · cp · λ^{κ+β},

for any measurable `g` obeying that envelope.  It is a product of "tail mass ×
envelope", proved elementarily (no layer cake).
-/

import Causalean.Stat.PolynomialTail.Basic

/-!
# Bias from trimming the lower tail

This module bounds the contribution left by the trimming weight
`trimWeight U lam = 1 - U / (max U lam)`.  Since this weight is between `0` and `1` and vanishes
off `{omega | U omega < lam}`, any integrand `g` whose absolute value is bounded by
`Cbeta * lam^beta` on the trimmed set has integrated bias controlled by the lower-tail mass.

The main theorem `trimWeight_bias_bound` proves
`|int trimWeight U lam * g dP| <= Cbeta * cp * lam^(kappa + beta)` under `PolyTail`, `TailSetup`,
and `0 < lam <= t0`.  It is the elementary "tail mass times local envelope" companion to the
layer-cake inverse-moment bounds.
-/

namespace Causalean.Stat.PolynomialTail

open MeasureTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : Ω → ℝ}
  {κ t₀ cm cp lam β : ℝ}

/-- **General trimming-bias bound.**  If `g` is measurable with
`|g| ≤ Cβ · λ^β` on `{U < λ}` (the Hölder envelope, `Cβ ≥ 0`), then under `PolyTail`
and the tail setup,

    `| ∫ wλ · g ∂P | ≤ Cβ · cp · λ^{κ+β}`.

The proof bounds `|wλ · g|` a.e. by `Cβ·λ^β · 𝟙{U<λ}` (using `wλ ∈ [0,1]` and `wλ = 0`
off `{U < λ}`) and integrates, picking up the tail mass `P{U < λ} ≤ cp·λᵏ`. -/
theorem trimWeight_bias_bound [IsProbabilityMeasure P]
    (h : PolyTail P U κ t₀ cm cp) (hsetup : TailSetup P U)
    (hlam_pos : 0 < lam) (hlam_le : lam ≤ t₀)
    {g : Ω → ℝ} {Cβ : ℝ} (hCβ : 0 ≤ Cβ) (hg_meas : Measurable g)
    (hg_bd : ∀ ω, U ω < lam → |g ω| ≤ Cβ * lam ^ β) :
    |∫ ω, trimWeight U lam ω * g ω ∂P| ≤ Cβ * cp * lam ^ (κ + β) := by
  have hmsβ : (0 : ℝ) ≤ Cβ * lam ^ β := mul_nonneg hCβ (Real.rpow_nonneg hlam_pos.le _)
  have hsmeas : MeasurableSet {ω | U ω < lam} := hsetup.measurable measurableSet_Iio
  -- a.e. pointwise bound by the envelope times the indicator of `{U < λ}`
  have hpt : ∀ᵐ ω ∂P, |trimWeight U lam ω * g ω|
      ≤ (Cβ * lam ^ β) * Set.indicator {ω | U ω < lam} (fun _ => (1 : ℝ)) ω := by
    filter_upwards [hsetup.pos] with ω hUpos
    by_cases hω : U ω < lam
    · have hw := trimWeight_mem hlam_pos hUpos
      have hwle1 : trimWeight U lam ω ≤ 1 := hw.2
      have hw0 : 0 ≤ trimWeight U lam ω := hw.1
      rw [abs_mul, Set.indicator_of_mem (show ω ∈ {ω | U ω < lam} from hω), mul_one]
      calc |trimWeight U lam ω| * |g ω|
          ≤ 1 * (Cβ * lam ^ β) :=
            mul_le_mul (by rw [abs_of_nonneg hw0]; exact hwle1) (hg_bd ω hω)
              (abs_nonneg _) (by norm_num)
        _ = Cβ * lam ^ β := one_mul _
    · have hzero : trimWeight U lam ω = 0 := by
        simp only [trimWeight, max_eq_left (not_lt.mp hω), div_self (ne_of_gt hUpos), sub_self]
      rw [hzero, zero_mul, abs_zero]
      exact mul_nonneg hmsβ (Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
  -- integrability of `wλ · g` (bounded a.e. by the integrable RHS)
  have hRHS_int : Integrable
      (fun ω => (Cβ * lam ^ β) * Set.indicator {ω | U ω < lam} (fun _ => (1 : ℝ)) ω) P :=
    (integrable_const (1 : ℝ)).indicator hsmeas |>.const_mul _
  have hint : Integrable (fun ω => trimWeight U lam ω * g ω) P := by
    refine Integrable.mono' hRHS_int
      ((measurable_trimWeight hsetup.measurable).mul hg_meas).aestronglyMeasurable ?_
    filter_upwards [hpt] with ω hω; rwa [Real.norm_eq_abs]
  -- chain: |∫| ≤ ∫|·| ≤ ∫ envelope·𝟙 = Cβλ^β · P{U<λ} ≤ Cβ cp λ^{κ+β}
  calc |∫ ω, trimWeight U lam ω * g ω ∂P|
      ≤ ∫ ω, |trimWeight U lam ω * g ω| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (Cβ * lam ^ β) *
          Set.indicator {ω | U ω < lam} (fun _ => (1 : ℝ)) ω ∂P :=
        integral_mono_ae hint.abs hRHS_int hpt
    _ = (Cβ * lam ^ β) * P.real {ω | U ω < lam} := by
        rw [integral_const_mul, integral_indicator hsmeas, setIntegral_const,
          smul_eq_mul, mul_one]
    _ ≤ (Cβ * lam ^ β) * (cp * lam ^ κ) := by
        gcongr
        exact measureReal_lt_le h hlam_pos hlam_le
    _ = Cβ * cp * lam ^ (κ + β) := by
        rw [Real.rpow_add hlam_pos]; ring

end Causalean.Stat.PolynomialTail
