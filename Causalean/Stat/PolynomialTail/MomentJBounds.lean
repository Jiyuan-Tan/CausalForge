/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Three-regime two-sided bounds for the inverse first moment `J`

Combining the layer-cake reduction `J = 1 + tailIntegral`, the tail-integral
sandwich `cm·PowInt ≤ tailIntegral ≤ (t₀⁻¹−1) + cp·PowInt`, and the power-integral
evaluation, gives uniform two-sided bounds on `J P U λ` for all `λ ∈ (0, t₀]`, with
constants depending only on `(κ, cm, cp, t₀)`:

* `invMomentJ_bounds_lt`  (0 < κ < 1):  `a·λ^{κ-1} ≤ J ≤ A·λ^{κ-1}`.
* `invMomentJ_bounds_eq`  (κ = 1):      `a·log(1/λ) ≤ J ≤ A·log(1/λ) + A`.
* `invMomentJ_bounds_gt`  (κ > 1):      `a ≤ J ≤ A`  (bounded inverse moment).

These `J`-bounds anchor the `I`-bounds too, since `I ≤ J` (file `MomentIBounds`).
-/

import Causalean.Stat.PolynomialTail.TailIntegralBounds

/-!
# Three-regime bounds for the inverse first moment

This module combines the exact identity `invMomentJ_eq_one_add_tailIntegral`, the tail-integral
sandwich from `TailIntegralBounds`, and the power-integral evaluations to prove uniform bounds for
`J P U lam = invMomentJ P U lam` on `lam in (0, t0]`.

The helper theorems `powInt_ne_one` and `powInt_eq_one` rewrite the comparison integral over
`(t0^(-1), lam^(-1)]` into either a power expression or a logarithm.  The main public bounds are
`invMomentJ_bounds_lt` for `0 < kappa < 1`, `invMomentJ_bounds_eq` for `kappa = 1`, and
`invMomentJ_bounds_gt` for `1 < kappa`, giving respectively power blow-up, logarithmic growth,
and bounded inverse-moment behavior with constants depending only on the polynomial-tail
parameters.
-/

namespace Causalean.Stat.PolynomialTail

open MeasureTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : Ω → ℝ}
  {κ t₀ cm cp lam : ℝ}

/-! ## Power-integral evaluation per regime -/

/-- `PowInt = (λ^{κ-1} − t₀^{κ-1})/(1−κ)` when `κ ≠ 1`. -/
theorem powInt_ne_one (h : PolyTail P U κ t₀ cm cp) (hκ : κ ≠ 1)
    (hlam_pos : 0 < lam) (hlam_le : lam ≤ t₀) :
    ∫ t in Ioc t₀⁻¹ lam⁻¹, t ^ (-κ) = (lam ^ (κ - 1) - t₀ ^ (κ - 1)) / (1 - κ) := by
  rw [integral_rpow_neg_Ioc hκ (inv_pos.mpr h.t0_pos)
      ((inv_le_inv₀ h.t0_pos hlam_pos).mpr hlam_le),
    inv_rpow_eq_rpow_neg hlam_pos (1 - κ), inv_rpow_eq_rpow_neg h.t0_pos (1 - κ)]
  simp only [neg_sub]

/-- `PowInt = log(1/λ) − log(1/t₀)` when `κ = 1`. -/
theorem powInt_eq_one (h : PolyTail P U κ t₀ cm cp) (hκ : κ = 1)
    (hlam_pos : 0 < lam) (hlam_le : lam ≤ t₀) :
    ∫ t in Ioc t₀⁻¹ lam⁻¹, t ^ (-κ) = Real.log (1 / lam) - Real.log (1 / t₀) := by
  subst hκ
  rw [integral_inv_neg_Ioc (inv_pos.mpr h.t0_pos)
    ((inv_le_inv₀ h.t0_pos hlam_pos).mpr hlam_le), one_div, one_div]

/-! ## Regime κ < 1 -/

/-- **Regime `0 < κ < 1`.** Under [the polynomial lower-tail hypothesis `PolyTail P U κ t₀ cm
cp`](hyp:h) with [`U` measurable and almost surely in `(0,1]`](hyp:hsetup) and [tail exponent
strictly between `0` and `1`](hyp:hκ1), [there exist constants `0 < a ≤ A`, depending only on
`κ, cm, cp, t₀`, such that the truncated inverse first moment `J P U λ` is squeezed between
`a·λ^{κ-1}` and `A·λ^{κ-1}`, uniformly for every `λ ∈ (0, t₀]`](goal). -/
theorem invMomentJ_bounds_lt [IsProbabilityMeasure P] (h : PolyTail P U κ t₀ cm cp)
    (hsetup : TailSetup P U) (hκ1 : κ < 1) :
    ∃ a A : ℝ, 0 < a ∧ a ≤ A ∧ ∀ lam : ℝ, 0 < lam → lam ≤ t₀ →
      a * lam ^ (κ - 1) ≤ invMomentJ P U lam ∧ invMomentJ P U lam ≤ A * lam ^ (κ - 1) := by
  have hone_sub : 0 < 1 - κ := by linarith
  set A1 : ℝ := cm / (1 - κ) with hA1
  have hA1_pos : 0 < A1 := div_pos h.cm_pos hone_sub
  set a : ℝ := min A1 (t₀ ^ (1 - κ)) with ha_def
  set A : ℝ := t₀⁻¹ + cp / (1 - κ) with hA_def
  have ht0_pos := h.t0_pos
  have hBcoef_pos : 0 < cp / (1 - κ) := div_pos h.cp_pos hone_sub
  have ha_pos : 0 < a := lt_min hA1_pos (Real.rpow_pos_of_pos ht0_pos _)
  have hA_pos : 0 < A := by positivity
  have hcm_cp : cm / (1 - κ) ≤ cp / (1 - κ) := by gcongr; exact h.cm_lt_cp.le
  have ha_le_A : a ≤ A := le_trans (min_le_left _ _) (by
    simp only [hA1, hA_def]; linarith [inv_pos.mpr ht0_pos, hcm_cp])
  refine ⟨a, A, ha_pos, ha_le_A, fun lam hlam_pos hlam_le => ?_⟩
  set M : ℝ := lam ^ (κ - 1) with hM
  set M0 : ℝ := t₀ ^ (κ - 1) with hM0
  have hM0_nonneg : 0 ≤ M0 := Real.rpow_nonneg ht0_pos.le _
  have hlam_lt_one : lam < 1 := lt_of_le_of_lt hlam_le h.t0_lt_one
  have hM_ge_one : 1 ≤ M :=
    le_of_eq_of_le (Real.one_rpow _).symm
      (Real.rpow_le_rpow_of_nonpos hlam_pos hlam_lt_one.le (by linarith))
  have hM0_le_M : M0 ≤ M := Real.rpow_le_rpow_of_nonpos hlam_pos hlam_le (by linarith)
  have hPow := powInt_ne_one h (ne_of_lt hκ1) hlam_pos hlam_le
  have hJ : invMomentJ P U lam = 1 + tailIntegral P U lam :=
    invMomentJ_eq_one_add_tailIntegral hsetup hlam_pos hlam_lt_one
  have hTle := tailIntegral_le h hlam_pos hlam_le
  have hTge := tailIntegral_ge h hlam_pos hlam_le
  rw [hPow] at hTle hTge
  -- cm·PowInt = A1·(M − M0),  cp·PowInt = (cp/(1−κ))·(M − M0)
  have hcmPow : cm * ((M - M0) / (1 - κ)) = A1 * (M - M0) := by rw [hA1]; ring
  have hcpPow : cp * ((M - M0) / (1 - κ)) = (cp / (1 - κ)) * (M - M0) := by ring
  rw [hcmPow] at hTge
  rw [hcpPow] at hTle
  constructor
  · -- lower: a·M ≤ J
    have h_aM0_le_1 : a * M0 ≤ 1 := by
      have hmul : t₀ ^ (1 - κ) * M0 = 1 := by
        rw [hM0, ← Real.rpow_add ht0_pos, show (1 - κ) + (κ - 1) = 0 from by ring,
          Real.rpow_zero]
      calc a * M0 ≤ t₀ ^ (1 - κ) * M0 :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hM0_nonneg
        _ = 1 := hmul
    have hprod : 0 ≤ (A1 - a) * (M - M0) :=
      mul_nonneg (by linarith [min_le_left A1 (t₀ ^ (1 - κ))]) (by linarith)
    nlinarith [hJ, hTge, hprod, h_aM0_le_1]
  · -- upper: J ≤ A·M
    have h1 : 0 ≤ t₀⁻¹ * (M - 1) :=
      mul_nonneg (inv_pos.mpr ht0_pos).le (by linarith)
    have h2 : 0 ≤ (cp / (1 - κ)) * M0 := mul_nonneg hBcoef_pos.le hM0_nonneg
    nlinarith [hJ, hTle, h1, h2]

/-! ## Regime κ = 1 -/

/-- **Regime `κ = 1`.** Under [the polynomial lower-tail hypothesis `PolyTail P U κ t₀ cm
cp`](hyp:h) with [`U` measurable and almost surely in `(0,1]`](hyp:hsetup) and [tail exponent
exactly `1`](hyp:hκ), [there exist constants `0 < a ≤ A` such that the truncated inverse first
moment `J P U λ` is squeezed between `a·log(1/λ)` and `A·log(1/λ) + A`, uniformly for every
`λ ∈ (0, t₀]`](goal). -/
theorem invMomentJ_bounds_eq [IsProbabilityMeasure P] (h : PolyTail P U κ t₀ cm cp)
    (hsetup : TailSetup P U) (hκ : κ = 1) :
    ∃ a A : ℝ, 0 < a ∧ a ≤ A ∧ ∀ lam : ℝ, 0 < lam → lam ≤ t₀ →
      a * Real.log (1 / lam) ≤ invMomentJ P U lam ∧
        invMomentJ P U lam ≤ A * Real.log (1 / lam) + A := by
  have ht0_pos := h.t0_pos
  set L0 : ℝ := Real.log (1 / t₀) with hL0
  have hL0_pos : 0 < L0 := by
    rw [hL0]; apply Real.log_pos; rw [one_div]; exact (one_lt_inv₀ ht0_pos).mpr h.t0_lt_one
  set a : ℝ := min cm (1 / L0) with ha_def
  set A : ℝ := t₀⁻¹ + cp with hA_def
  have ha_pos : 0 < a := lt_min h.cm_pos (by positivity)
  have ha_le_A : a ≤ A := le_trans (min_le_left _ _) (by
    simp only [hA_def]; linarith [inv_pos.mpr ht0_pos, h.cm_lt_cp])
  refine ⟨a, A, ha_pos, ha_le_A, fun lam hlam_pos hlam_le => ?_⟩
  have hlam_lt_one : lam < 1 := lt_of_le_of_lt hlam_le h.t0_lt_one
  have hL_ge_L0 : L0 ≤ Real.log (1 / lam) := by
    rw [hL0]
    exact Real.log_le_log (by positivity) (one_div_le_one_div_of_le hlam_pos hlam_le)
  have hL_pos : 0 < Real.log (1 / lam) := lt_of_lt_of_le hL0_pos hL_ge_L0
  have hPow := powInt_eq_one h hκ hlam_pos hlam_le
  rw [← hL0] at hPow
  have hJ := invMomentJ_eq_one_add_tailIntegral hsetup hlam_pos hlam_lt_one
  have hTle := tailIntegral_le h hlam_pos hlam_le
  have hTge := tailIntegral_ge h hlam_pos hlam_le
  rw [hPow] at hTle hTge
  have h_aL0 : a * L0 ≤ 1 := by
    calc a * L0 ≤ (1 / L0) * L0 := mul_le_mul_of_nonneg_right (min_le_right _ _) hL0_pos.le
      _ = 1 := one_div_mul_cancel (ne_of_gt hL0_pos)
  constructor
  · -- lower
    have hprod : 0 ≤ (cm - a) * (Real.log (1 / lam) - L0) :=
      mul_nonneg (by linarith [min_le_left cm (1 / L0)]) (by linarith)
    nlinarith [hJ, hTge, hprod, h_aL0]
  · -- upper
    have h1 : 0 ≤ t₀⁻¹ * Real.log (1 / lam) :=
      mul_nonneg (inv_pos.mpr ht0_pos).le hL_pos.le
    have h2 : 0 ≤ cp * L0 := mul_nonneg h.cp_pos.le hL0_pos.le
    nlinarith [hJ, hTle, h1, h2]

/-! ## Regime κ > 1 -/

/-- **Regime `κ > 1`.** Under [the polynomial lower-tail hypothesis `PolyTail P U κ t₀ cm
cp`](hyp:h) with [`U` measurable and almost surely in `(0,1]`](hyp:hsetup) and [tail exponent
strictly above `1`](hyp:hκ1), [there exist constants `0 < a ≤ A` such that the truncated inverse
first moment `J P U λ` is bounded between `a` and `A`, uniformly for every `λ ∈ (0,
t₀]`](goal): the inverse first moment does not blow up. -/
theorem invMomentJ_bounds_gt [IsProbabilityMeasure P] (h : PolyTail P U κ t₀ cm cp)
    (hsetup : TailSetup P U) (hκ1 : 1 < κ) :
    ∃ a A : ℝ, 0 < a ∧ a ≤ A ∧ ∀ lam : ℝ, 0 < lam → lam ≤ t₀ →
      a ≤ invMomentJ P U lam ∧ invMomentJ P U lam ≤ A := by
  have ht0_pos := h.t0_pos
  have hκm1_pos : 0 < κ - 1 := by linarith
  set A : ℝ := t₀⁻¹ + cp * t₀ ^ (κ - 1) / (κ - 1) with hA_def
  have hA_one : (1 : ℝ) ≤ A := by
    rw [hA_def]
    have h1 : (1 : ℝ) ≤ t₀⁻¹ := (one_le_inv₀ ht0_pos).mpr h.t0_lt_one.le
    have h2 : 0 ≤ cp * t₀ ^ (κ - 1) / (κ - 1) :=
      div_nonneg (mul_nonneg h.cp_pos.le (Real.rpow_nonneg ht0_pos.le _)) hκm1_pos.le
    linarith
  refine ⟨1, A, one_pos, hA_one, fun lam hlam_pos hlam_le => ?_⟩
  have hlam_lt_one : lam < 1 := lt_of_le_of_lt hlam_le h.t0_lt_one
  have hPow := powInt_ne_one h (by linarith : κ ≠ 1) hlam_pos hlam_le
  have hJ := invMomentJ_eq_one_add_tailIntegral hsetup hlam_pos hlam_lt_one
  have hTle := tailIntegral_le h hlam_pos hlam_le
  have hTnn : (0 : ℝ) ≤ tailIntegral P U lam := tailIntegral_nonneg
  rw [hPow] at hTle
  set M : ℝ := lam ^ (κ - 1) with hM
  set M0 : ℝ := t₀ ^ (κ - 1) with hM0
  have hM_nonneg : 0 ≤ M := Real.rpow_nonneg hlam_pos.le _
  have hM0_nonneg : 0 ≤ M0 := Real.rpow_nonneg ht0_pos.le _
  have hM_le_M0 : M ≤ M0 := Real.rpow_le_rpow hlam_pos.le hlam_le hκm1_pos.le
  constructor
  · rw [hJ]; linarith [hTnn]
  · -- upper: rewrite PowInt = (M0 - M)/(κ-1) ≤ M0/(κ-1)
    have heq : (M - M0) / (1 - κ) = (M0 - M) / (κ - 1) := by
      rw [div_eq_div_iff (ne_of_lt (show (1 : ℝ) - κ < 0 by linarith)) (ne_of_gt hκm1_pos)]
      ring
    have hPI_bd : cp * ((M0 - M) / (κ - 1)) ≤ cp * (M0 / (κ - 1)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (by linarith [hM_nonneg]) hκm1_pos.le) h.cp_pos.le
    have hassoc : cp * (M0 / (κ - 1)) = cp * M0 / (κ - 1) := by rw [mul_div_assoc]
    rw [heq] at hTle
    rw [hJ, hA_def]
    linarith [hTle, hPI_bd, hassoc]

end Causalean.Stat.PolynomialTail
