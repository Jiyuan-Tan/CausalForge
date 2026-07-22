/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Two-sided bounds on the tail integral

Bridges the layer-cake reduction (`tailIntegral = ∫_{(1,λ⁻¹]} P{U ≤ t⁻¹}`) to the
power integral `∫_{(t₀⁻¹,λ⁻¹]} t^{-κ}`.  Splitting at `t₀⁻¹`:

* on `(1, t₀⁻¹]` the integrand is `≤ 1` (mass bound) — a bounded constant `t₀⁻¹ − 1`;
* on `(t₀⁻¹, λ⁻¹]` the polynomial tail gives `cm·t^{-κ} ≤ P{U ≤ t⁻¹} ≤ cp·t^{-κ}`.

Hence

    cm · PowInt  ≤  tailIntegral  ≤  (t₀⁻¹ − 1) + cp · PowInt,
        PowInt := ∫_{(t₀⁻¹,λ⁻¹]} t^{-κ}.

The regime trichotomy then follows by evaluating `PowInt` (file `PowerIntegral`).
-/

import Causalean.Stat.PolynomialTail.LayerCakeReduction
import Causalean.Stat.PolynomialTail.PowerIntegral

/-!
# Bounds on the polynomial-tail integral

This module applies `PolyTail` to the layer-cake integrand from `LayerCakeReduction`.  On the
window `(t0^(-1), lam^(-1)]`, the substitution `s = t^(-1)` puts `s` in `(0, t0]`, so the
polynomial lower-tail bounds give
`cm * t^(-kappa) <= P.real {omega | U omega <= t^(-1)} <= cp * t^(-kappa)`.

The pointwise sandwich is recorded in `tailIntegrand_lower_window` and
`tailIntegrand_upper_window`, with `integrableOn_rpow_neg_window` supplying the integrability of
the power comparison function.  The main results `tailIntegral_ge` and `tailIntegral_le` bound
`tailIntegral P U lam` between `cm` times the power integral and an upper expression with the
bounded pre-window contribution `(t0^(-1) - 1)` plus `cp` times the same power integral.  These
are the inputs for the three-regime `J` and `I` moment bounds.
-/

namespace Causalean.Stat.PolynomialTail

open MeasureTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : Ω → ℝ}
  {κ t₀ cm cp lam : ℝ}

/-- `(t⁻¹)^κ = t^{-κ}` for `t > 0`. -/
theorem inv_rpow_eq_rpow_neg {t : ℝ} (ht : 0 < t) (κ : ℝ) : (t⁻¹) ^ κ = t ^ (-κ) := by
  rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]

/-- Upper sandwich of the tail integrand on the polynomial window. -/
theorem tailIntegrand_upper_window [IsFiniteMeasure P] (h : PolyTail P U κ t₀ cm cp)
    {t : ℝ} (ht : t ∈ Ioc t₀⁻¹ lam⁻¹) :
    P.real {ω | U ω ≤ t⁻¹} ≤ cp * t ^ (-κ) := by
  have htpos : 0 < t := lt_trans (inv_pos.mpr h.t0_pos) ht.1
  have htinv_le : t⁻¹ ≤ t₀ := le_of_lt ((inv_lt_comm₀ htpos h.t0_pos).mpr ht.1)
  calc P.real {ω | U ω ≤ t⁻¹} ≤ cp * (t⁻¹) ^ κ := h.tail_upper t⁻¹ (inv_pos.mpr htpos) htinv_le
    _ = cp * t ^ (-κ) := by rw [inv_rpow_eq_rpow_neg htpos]

/-- Lower sandwich of the tail integrand on the polynomial window. -/
theorem tailIntegrand_lower_window [IsFiniteMeasure P] (h : PolyTail P U κ t₀ cm cp)
    {t : ℝ} (ht : t ∈ Ioc t₀⁻¹ lam⁻¹) :
    cm * t ^ (-κ) ≤ P.real {ω | U ω ≤ t⁻¹} := by
  have htpos : 0 < t := lt_trans (inv_pos.mpr h.t0_pos) ht.1
  have htinv_le : t⁻¹ ≤ t₀ := le_of_lt ((inv_lt_comm₀ htpos h.t0_pos).mpr ht.1)
  calc cm * t ^ (-κ) = cm * (t⁻¹) ^ κ := by rw [inv_rpow_eq_rpow_neg htpos]
    _ ≤ P.real {ω | U ω ≤ t⁻¹} := h.tail_lower t⁻¹ (inv_pos.mpr htpos) htinv_le

/-- `t^{-κ}` is integrable on the window `(t₀⁻¹, λ⁻¹]`. -/
theorem integrableOn_rpow_neg_window (h : PolyTail P U κ t₀ cm cp) (hlam_pos : 0 < lam)
    (hlam_le : lam ≤ t₀) :
    IntegrableOn (fun t : ℝ => t ^ (-κ)) (Ioc t₀⁻¹ lam⁻¹) volume := by
  have ht0lam : t₀⁻¹ ≤ lam⁻¹ := (inv_le_inv₀ h.t0_pos hlam_pos).mpr hlam_le
  exact (intervalIntegral.intervalIntegrable_rpow
    (Or.inr (zero_notMem_uIcc (inv_pos.mpr h.t0_pos) ht0lam))).1

/-- Endpoints of the split satisfy `1 ≤ t₀⁻¹ ≤ λ⁻¹`. -/
private theorem split_endpoints (h : PolyTail P U κ t₀ cm cp) (hlam_pos : 0 < lam)
    (hlam_le : lam ≤ t₀) : (1 : ℝ) ≤ t₀⁻¹ ∧ t₀⁻¹ ≤ lam⁻¹ :=
  ⟨(one_le_inv₀ h.t0_pos).mpr h.t0_lt_one.le, (inv_le_inv₀ h.t0_pos hlam_pos).mpr hlam_le⟩

/-- **Upper bound on the tail integral.**  Under the polynomial lower-tail hypothesis and
`0 < λ ≤ t₀`, the layer-cake tail integral is bounded by a constant pre-window contribution plus
the upper polynomial comparison:

`tailIntegral P U λ ≤ (t₀⁻¹ - 1) + cp * ∫ t in Ioc t₀⁻¹ λ⁻¹, t ^ (-κ)`.

The split at `t₀⁻¹` keeps the part where the polynomial tail assumption is unavailable bounded by
`1`, and uses `tailIntegrand_upper_window` on the polynomial window. -/
theorem tailIntegral_le [IsProbabilityMeasure P] (h : PolyTail P U κ t₀ cm cp)
    (hlam_pos : 0 < lam) (hlam_le : lam ≤ t₀) :
    tailIntegral P U lam ≤ (t₀⁻¹ - 1) + cp * ∫ t in Ioc t₀⁻¹ lam⁻¹, t ^ (-κ) := by
  obtain ⟨h1t0, ht0lam⟩ := split_endpoints h hlam_pos hlam_le
  have hdisj : Disjoint (Ioc (1 : ℝ) t₀⁻¹) (Ioc t₀⁻¹ lam⁻¹) := by
    rw [Set.disjoint_left]; rintro x ⟨_, hx1⟩ ⟨hx2, _⟩; exact absurd hx2 (not_lt.mpr hx1)
  have hpow_int := integrableOn_rpow_neg_window h hlam_pos hlam_le
  have hconst_int : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 1 t₀⁻¹) volume := by
    haveI : IsFiniteMeasure (volume.restrict (Ioc (1 : ℝ) t₀⁻¹)) :=
      ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
    exact integrable_const 1
  rw [tailIntegral, ← Set.Ioc_union_Ioc_eq_Ioc h1t0 ht0lam,
    setIntegral_union hdisj measurableSet_Ioc
      (integrableOn_tailIntegrand 1 t₀⁻¹) (integrableOn_tailIntegrand t₀⁻¹ lam⁻¹)]
  refine add_le_add ?_ ?_
  · -- left piece: `≤ t₀⁻¹ - 1`
    calc ∫ t in Ioc (1 : ℝ) t₀⁻¹, P.real {ω | U ω ≤ t⁻¹}
        ≤ ∫ _t in Ioc (1 : ℝ) t₀⁻¹, (1 : ℝ) :=
          setIntegral_mono_on (integrableOn_tailIntegrand 1 t₀⁻¹) hconst_int
            measurableSet_Ioc (fun t _ => tailIntegrand_le_one t)
      _ = t₀⁻¹ - 1 := by
          rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, Real.volume_Ioc,
            ENNReal.toReal_ofReal (by linarith)]
  · -- right piece: `≤ cp * PowInt`
    rw [← integral_const_mul]
    exact setIntegral_mono_on (integrableOn_tailIntegrand t₀⁻¹ lam⁻¹)
      (hpow_int.const_mul cp) measurableSet_Ioc
      (fun t ht => tailIntegrand_upper_window h ht)

/-- **Lower bound on the tail integral.**  Under the polynomial lower-tail hypothesis and
`0 < λ ≤ t₀`, the polynomial window alone gives

`cm * ∫ t in Ioc t₀⁻¹ λ⁻¹, t ^ (-κ) ≤ tailIntegral P U λ`.

The proof discards the nonnegative pre-window contribution and applies
`tailIntegrand_lower_window` on `(t₀⁻¹, λ⁻¹]`. -/
theorem tailIntegral_ge [IsProbabilityMeasure P] (h : PolyTail P U κ t₀ cm cp)
    (hlam_pos : 0 < lam) (hlam_le : lam ≤ t₀) :
    cm * ∫ t in Ioc t₀⁻¹ lam⁻¹, t ^ (-κ) ≤ tailIntegral P U lam := by
  obtain ⟨h1t0, ht0lam⟩ := split_endpoints h hlam_pos hlam_le
  have hdisj : Disjoint (Ioc (1 : ℝ) t₀⁻¹) (Ioc t₀⁻¹ lam⁻¹) := by
    rw [Set.disjoint_left]; rintro x ⟨_, hx1⟩ ⟨hx2, _⟩; exact absurd hx2 (not_lt.mpr hx1)
  have hpow_int := integrableOn_rpow_neg_window h hlam_pos hlam_le
  rw [tailIntegral, ← Set.Ioc_union_Ioc_eq_Ioc h1t0 ht0lam,
    setIntegral_union hdisj measurableSet_Ioc
      (integrableOn_tailIntegrand 1 t₀⁻¹) (integrableOn_tailIntegrand t₀⁻¹ lam⁻¹)]
  have hleft : (0 : ℝ) ≤ ∫ t in Ioc (1 : ℝ) t₀⁻¹, P.real {ω | U ω ≤ t⁻¹} :=
    setIntegral_nonneg measurableSet_Ioc (fun t _ => tailIntegrand_nonneg t)
  have hright : cm * ∫ t in Ioc t₀⁻¹ lam⁻¹, t ^ (-κ)
      ≤ ∫ t in Ioc t₀⁻¹ lam⁻¹, P.real {ω | U ω ≤ t⁻¹} := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hpow_int.const_mul cm)
      (integrableOn_tailIntegrand t₀⁻¹ lam⁻¹) measurableSet_Ioc
      (fun t ht => tailIntegrand_lower_window h ht)
  linarith

end Causalean.Stat.PolynomialTail
