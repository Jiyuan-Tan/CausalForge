/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Layer-cake reduction of the inverse moments to a threshold integral

The analytic engine for the polynomial lower-tail asymptotics.  Using Mathlib's
layer-cake theorem (`MeasureTheory.Integrable.integral_eq_integral_Ioc_meas_le`), the
truncated inverse first moment `J P U λ = ∫ (max U λ)⁻¹` is rewritten as

    J P U λ = 1 + ∫ t in Ioc 1 λ⁻¹, P{U ≤ t⁻¹} dt.

The `1` is the contribution of the levels `t ≤ 1` (where `(max U λ)⁻¹ ≥ 1` a.s.); the
remaining "tail integral" `tailIntegral P U λ` is what carries the `λ^{κ-1}` /
`log(1/λ)` / bounded trichotomy once the polynomial-tail bounds are applied to the
integrand `P{U ≤ t⁻¹}`.

This file proves only the *exact identity* and basic facts about `tailIntegral`
(nonnegativity, an integrand sandwich on the window).  The power-integral evaluation
and the three-regime bounds live in `Stat/PolynomialTail/TailIntegralBounds.lean`,
`Stat/PolynomialTail/MomentJBounds.lean`, and `Stat/PolynomialTail/MomentIBounds.lean`.
-/

import Causalean.Stat.PolynomialTail.Basic

/-!
# Layer-cake reduction to the tail integral

This module isolates the one-dimensional threshold integral that controls the truncated inverse
first moment.  The definition
`tailIntegral P U lam = int t in Ioc 1 lam^(-1), P.real {omega | U omega <= t^(-1)}`
captures the nonconstant part of the layer-cake formula for `invMomentJ`.

The central theorem `invMomentJ_eq_one_add_tailIntegral` proves the exact identity
`invMomentJ P U lam = 1 + tailIntegral P U lam` for `0 < lam < 1` under `TailSetup`.
Auxiliary results establish monotonicity and measurability of the lower CDF, bounded
integrability of the tail integrand, and nonnegativity of `tailIntegral`.  The polynomial-tail
assumption is not used here; it enters later through the sandwich bounds in
`TailIntegralBounds`.
-/

namespace Causalean.Stat.PolynomialTail

open MeasureTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : Ω → ℝ} {lam : ℝ}

/-- The threshold ("tail") integral `∫ t in (1, λ⁻¹], P{U ≤ t⁻¹} dt`. -/
noncomputable def tailIntegral (P : Measure Ω) (U : Ω → ℝ) (lam : ℝ) : ℝ :=
  ∫ t in Ioc 1 lam⁻¹, P.real {ω | U ω ≤ t⁻¹}

/-- The lower CDF `s ↦ P{U ≤ s}` is monotone. -/
theorem monotone_cdf [IsFiniteMeasure P] :
    Monotone (fun s : ℝ => P.real {ω | U ω ≤ s}) :=
  fun _ _ hs => measureReal_mono (fun ω (hω : U ω ≤ _) => le_trans hω hs) (measure_ne_top P _)

/-- The integrand `t ↦ P{U ≤ t⁻¹}` is measurable (monotone CDF ∘ inversion). -/
theorem measurable_tailIntegrand [IsFiniteMeasure P] :
    Measurable (fun t : ℝ => P.real {ω | U ω ≤ t⁻¹}) :=
  (monotone_cdf.measurable).comp measurable_inv

/-- The integrand is nonnegative. -/
theorem tailIntegrand_nonneg (t : ℝ) : 0 ≤ P.real {ω | U ω ≤ t⁻¹} :=
  measureReal_nonneg

/-- The integrand is bounded by `1`. -/
theorem tailIntegrand_le_one [IsProbabilityMeasure P] (t : ℝ) :
    P.real {ω | U ω ≤ t⁻¹} ≤ 1 := by
  calc P.real {ω | U ω ≤ t⁻¹}
      ≤ P.real (univ : Set Ω) := measureReal_mono (subset_univ _) (measure_ne_top P _)
    _ = 1 := by rw [measureReal_def, measure_univ, ENNReal.toReal_one]

/-- The tail integrand is integrable on `Ioc a b`. -/
theorem integrableOn_tailIntegrand [IsProbabilityMeasure P] (a b : ℝ) :
    IntegrableOn (fun t : ℝ => P.real {ω | U ω ≤ t⁻¹}) (Ioc a b) volume := by
  haveI : IsFiniteMeasure (volume.restrict (Ioc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_tailIntegrand.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (tailIntegrand_nonneg t)]
  exact tailIntegrand_le_one t

/-- **Master layer-cake reduction.**  For `0 < λ < 1`,

    `J P U λ = 1 + tailIntegral P U λ`.

The level `t ≤ 1` part of the layer-cake integral contributes exactly `1` (since the
integrand `(max U λ)⁻¹ ≥ 1` a.s.), and the levels `t ∈ (1, λ⁻¹]` reproduce
`P{U ≤ t⁻¹}`. -/
theorem invMomentJ_eq_one_add_tailIntegral [IsProbabilityMeasure P]
    (hsetup : TailSetup P U) (hlam_pos : 0 < lam) (hlam_lt : lam < 1) :
    invMomentJ P U lam = 1 + tailIntegral P U lam := by
  have hU := hsetup.measurable
  -- Layer-cake on the J-integrand `f = (max U λ)⁻¹`, bounded by `M = λ⁻¹`.
  have hint : Integrable (fun ω => (max (U ω) lam)⁻¹) P :=
    integrable_invMomentJ_integrand hsetup hlam_pos
  have hnn : 0 ≤ᵐ[P] fun ω => (max (U ω) lam)⁻¹ :=
    Filter.Eventually.of_forall fun ω => (invMomentJ_integrand_mem hlam_pos (U ω)).1
  have hbd : (fun ω => (max (U ω) lam)⁻¹) ≤ᵐ[P] fun _ => lam⁻¹ :=
    Filter.Eventually.of_forall fun ω => (invMomentJ_integrand_mem hlam_pos (U ω)).2
  rw [invMomentJ, hint.integral_eq_integral_Ioc_meas_le hnn hbd]
  have h1le : (1 : ℝ) ≤ lam⁻¹ := (one_le_inv₀ hlam_pos).mpr hlam_lt.le
  -- On the whole window `t ∈ (0, λ⁻¹]` the level set `{t ≤ (max U λ)⁻¹}` equals `{U ≤ t⁻¹}`.
  have hset : ∀ t : ℝ, 0 < t → t ≤ lam⁻¹ →
      {a | t ≤ (max (U a) lam)⁻¹} = {a | U a ≤ t⁻¹} := by
    intro t htpos htle
    have hlamt : lam ≤ t⁻¹ := (le_inv_comm₀ hlam_pos htpos).mpr htle
    ext a
    simp only [mem_setOf_eq]
    rw [le_inv_comm₀ htpos (lt_of_lt_of_le hlam_pos (le_max_right _ _)), max_le_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, hlamt⟩⟩
  have hcongr : EqOn (fun t => P.real {a | t ≤ (max (U a) lam)⁻¹})
      (fun t => P.real {a | U a ≤ t⁻¹}) (Ioc 0 lam⁻¹) := by
    intro t ht
    simp only [hset t ht.1 ht.2]
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr]
  -- Split `Ioc 0 λ⁻¹ = Ioc 0 1 ∪ Ioc 1 λ⁻¹`.
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioc 1 lam⁻¹) := by
    rw [Set.disjoint_left]
    rintro x ⟨_, hx1⟩ ⟨hx2, _⟩
    exact absurd hx2 (not_lt.mpr hx1)
  rw [← Set.Ioc_union_Ioc_eq_Ioc (by norm_num : (0 : ℝ) ≤ 1) h1le,
      setIntegral_union hdisj measurableSet_Ioc
        (integrableOn_tailIntegrand 0 1) (integrableOn_tailIntegrand 1 lam⁻¹)]
  rw [tailIntegral]
  congr 1
  -- The `Ioc 0 1` part is the constant `1`.
  have hone : EqOn (fun t : ℝ => P.real {a | U a ≤ t⁻¹}) (fun _ => (1 : ℝ)) (Ioc 0 1) := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t⁻¹ := (one_le_inv₀ ht.1).mpr ht.2
    have hfull : {a | U a ≤ t⁻¹} =ᵐ[P] (univ : Set Ω) := by
      filter_upwards [hsetup.le_one] with a ha
      exact eq_true (le_trans ha ht1)
    change P.real {a | U a ≤ t⁻¹} = 1
    rw [measureReal_congr hfull, measureReal_def, measure_univ, ENNReal.toReal_one]
  rw [setIntegral_congr_fun measurableSet_Ioc hone]
  simp

/-- `tailIntegral` is nonnegative. -/
theorem tailIntegral_nonneg [IsProbabilityMeasure P] :
    0 ≤ tailIntegral P U lam :=
  setIntegral_nonneg measurableSet_Ioc (fun t _ => tailIntegrand_nonneg t)

end Causalean.Stat.PolynomialTail
