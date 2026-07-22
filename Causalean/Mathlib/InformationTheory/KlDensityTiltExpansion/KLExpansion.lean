/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.InformationTheory.KlDensityTiltExpansion.Basic
import Causalean.Mathlib.InformationTheory.KlDensityTiltExpansion.CubicRemainder

/-!
# Second-order Kullback–Leibler expansion of the linear density tilt

For a probability measure `μ` and a bounded mean-zero score `s : Z → ℝ`
(`|s| ≤ C`, `∫ s = 0`), the linear tilt `tiltMeasure μ s h` (see `Basic.lean`)
satisfies the **local asymptotic normality / Fisher-information expansion**

    KL(tiltMeasure μ s h ‖ μ)  =  (h² / 2) · ∫ s² dμ  +  o(h²)   as `h → 0`.

## Main results

* `klDiv_tiltMeasure_toReal_eq` — the KL divergence is the `μ`-integral of the
  `x log x` density functional:
  `(klDiv (tiltMeasure μ s h) μ).toReal = ∫ (1 + h·s) · log (1 + h·s) dμ`.
* `abs_klRemainder_le` — the dominated cubic remainder bound: for `|h|·C ≤ 1/2`,
  `|KL.toReal - (h²/2)·∫ s²| ≤ C³ · |h|³`.
* `klDiv_tilt_expansion` — the headline `o(h²)` expansion, as an
  `Asymptotics.IsLittleO` statement.

## Proof outline

1. `klDiv_tiltMeasure_toReal_eq`: `tiltMeasure μ s h ≪ μ` and both are probability
   measures, so `toReal_klDiv_of_measure_eq` gives `KL.toReal = ∫ llr (tilt) μ ∂(tilt)`.
   The log-likelihood ratio `llr (tilt) μ =ᵐ log (rnDeriv) =ᵐ log (1 + h·s)`
   (`rnDeriv_withDensity`), and change of measure
   (`integral_withDensity_eq_integral_toReal_smul`) rewrites the `tilt`-integral of
   `log (1 + h·s)` as the `μ`-integral of `(1 + h·s) · log (1 + h·s)`.
2. `abs_klRemainder_le`: write the integrand as
   `(1 + h·s)·log(1 + h·s) = h·s + (h·s)²/2 + R(h·s)` with
   `R(x) = (1+x)log(1+x) - x - x²/2`.  Integrating, `∫ h·s = 0` and
   `∫ (h·s)²/2 = (h²/2)∫ s²`, so the difference equals `∫ R(h·s) dμ`, bounded
   pointwise by `abs_tiltRemainder_le` (valid since `|h·s| ≤ |h|·C ≤ 1/2`):
   `|∫ R(h·s)| ≤ ∫ |h·s|³ ≤ |h|³·C³` (probability measure, `|s| ≤ C`).
3. `klDiv_tilt_expansion`: from `abs_klRemainder_le`, `|remainder h| ≤ C³·|h|³
   = (C³·|h|)·h²` eventually, and `C³·|h| → 0`, so `Asymptotics.isLittleO_iff`
   closes it.
-/

open MeasureTheory InformationTheory Real Filter Topology Asymptotics
open scoped ENNReal

namespace Causalean.Mathlib.InformationTheory.KlDensityTiltExpansion

variable {Z : Type*} [MeasurableSpace Z]

/-- **KL of the linear tilt as an `x log x` density integral.**  For a probability
measure `μ`, bounded mean-zero score `|s| ≤ C` with `∫ s = 0`, and `|h|·C ≤ 1`,

    (klDiv (tiltMeasure μ s h) μ).toReal = ∫ (1 + h · s y) · log (1 + h · s y) dμ.

Proof sketch: the tilt is a probability measure (`isProbabilityMeasure_tiltMeasure`)
absolutely continuous wrt `μ` (`tiltMeasure_absolutelyContinuous`), so
`toReal_klDiv_of_measure_eq` gives `KL.toReal = ∫ llr (tilt) μ ∂(tilt)`.  Then
`llr (tilt) μ =ᵐ[tilt] log (1 + h·s)` via `rnDeriv_withDensity`, and
`integral_withDensity_eq_integral_toReal_smul` converts the `tilt`-integral to the
`μ`-integral weighted by the density `1 + h·s`. -/
lemma klDiv_tiltMeasure_toReal_eq {μ : Measure Z} [IsProbabilityMeasure μ] {s : Z → ℝ}
    {C h : ℝ} (hs_meas : Measurable s) (hsC : ∀ y, |s y| ≤ C) (hs_mean : ∫ y, s y ∂μ = 0)
    (hh : |h| * C ≤ 1) :
    (InformationTheory.klDiv (tiltMeasure μ s h) μ).toReal
      = ∫ y, (1 + h * s y) * Real.log (1 + h * s y) ∂μ := by
  let ν : Measure Z := tiltMeasure μ s h
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_tiltMeasure hs_meas hsC hs_mean hh
  have hac : ν ≪ μ := tiltMeasure_absolutelyContinuous μ s h
  have hf_meas : Measurable (fun y : Z => ENNReal.ofReal (1 + h * s y)) := by
    fun_prop
  have hf_lt_top : ∀ᵐ y ∂μ, ENNReal.ofReal (1 + h * s y) < ∞ := by
    simp
  have hllr : llr ν μ =ᵐ[ν] fun y => Real.log (1 + h * s y) := by
    have hrnμ :
        ν.rnDeriv μ =ᵐ[μ] fun y => ENNReal.ofReal (1 + h * s y) := by
      simpa [ν, tiltMeasure] using
        (Measure.rnDeriv_withDensity μ hf_meas)
    filter_upwards [hrnμ.filter_mono hac.ae_le] with y hy
    simp [MeasureTheory.llr_def, hy, ENNReal.toReal_ofReal (tiltDensity_nonneg hsC hh y)]
  calc
    (InformationTheory.klDiv (tiltMeasure μ s h) μ).toReal
        = (InformationTheory.klDiv ν μ).toReal := rfl
    _ = ∫ y, llr ν μ y ∂ν := by
        exact InformationTheory.toReal_klDiv_of_measure_eq hac (by simp [ν])
    _ = ∫ y, Real.log (1 + h * s y) ∂ν := integral_congr_ae hllr
    _ = ∫ y, (ENNReal.ofReal (1 + h * s y)).toReal •
          Real.log (1 + h * s y) ∂μ := by
        simpa [ν, tiltMeasure] using
          (integral_withDensity_eq_integral_toReal_smul hf_meas hf_lt_top
            (fun y : Z => Real.log (1 + h * s y)))
    _ = ∫ y, (1 + h * s y) * Real.log (1 + h * s y) ∂μ := by
        apply integral_congr_ae
        filter_upwards with y
        simp [ENNReal.toReal_ofReal (tiltDensity_nonneg hsC hh y), smul_eq_mul]

/-- **Dominated cubic remainder bound.**  For `|h|·C ≤ 1/2`,

    |(klDiv (tiltMeasure μ s h) μ).toReal - (h²/2) · ∫ s² dμ|  ≤  C³ · |h|³.

Proof sketch: rewrite `KL.toReal` via `klDiv_tiltMeasure_toReal_eq`.  Decompose the
integrand `(1 + h·s)·log(1 + h·s) = h·s + h²·s²/2 + R(h·s)`; integrate termwise
(all summands bounded, hence integrable): `∫ h·s = h·∫ s = 0` and
`∫ h²·s²/2 = (h²/2)·∫ s²`.  The difference is `∫ R(h·s) dμ`; bound
`|∫ R(h·s)| ≤ ∫ |R(h·s)| ≤ ∫ |h·s|³ dμ` by `abs_tiltRemainder_le` (its hypothesis
`|h·s y| ≤ |h|·C ≤ 1/2` holds), and `∫ |h·s|³ = |h|³ ∫ |s|³ ≤ |h|³·C³` since
`|s| ≤ C` and `μ` is a probability measure. -/
lemma abs_klRemainder_le {μ : Measure Z} [IsProbabilityMeasure μ] {s : Z → ℝ}
    {C h : ℝ} (hC : 0 ≤ C) (hs_meas : Measurable s) (hsC : ∀ y, |s y| ≤ C)
    (hs_mean : ∫ y, s y ∂μ = 0) (hh : |h| * C ≤ 1 / 2) :
    |(InformationTheory.klDiv (tiltMeasure μ s h) μ).toReal
        - (h ^ 2 / 2) * ∫ y, s y ^ 2 ∂μ| ≤ C ^ 3 * |h| ^ 3 := by
  have hh_one : |h| * C ≤ 1 := by linarith
  rw [klDiv_tiltMeasure_toReal_eq hs_meas hsC hs_mean hh_one]
  let R : Z → ℝ := fun y =>
    (1 + h * s y) * Real.log (1 + h * s y) - h * s y - (h * s y) ^ 2 / 2
  have hR_bound : ∀ y, |R y| ≤ C ^ 3 * |h| ^ 3 := by
    intro y
    have hxs : |h * s y| ≤ |h| * C := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hsC y) (abs_nonneg h)
    have hsmall : |h * s y| ≤ 1 / 2 := le_trans hxs hh
    have hrem := abs_tiltRemainder_le (x := h * s y) hsmall
    have hpow : |h * s y| ^ 3 ≤ (|h| * C) ^ 3 := by
      exact pow_le_pow_left₀ (abs_nonneg _) hxs 3
    have hprod_nonneg : 0 ≤ |h| * C := mul_nonneg (abs_nonneg h) hC
    have hconst_nonneg : 0 ≤ C ^ 3 * |h| ^ 3 := by positivity
    dsimp [R]
    calc
      |(1 + h * s y) * Real.log (1 + h * s y) - h * s y - (h * s y) ^ 2 / 2|
          ≤ |h * s y| ^ 3 := hrem
      _ ≤ C ^ 3 * |h| ^ 3 := by
        nlinarith [hpow, hprod_nonneg, hconst_nonneg]
  have hs_int : Integrable s μ := integrable_of_bounded hs_meas hsC
  have hs2_int : Integrable (fun y => s y ^ 2) μ := by
    refine integrable_of_bounded (μ := μ) (s := fun y => s y ^ 2) (C := C ^ 2) ?_ ?_
    · fun_prop
    · intro y
      have hsq : |s y| ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hsC y) 2
      simpa [abs_pow] using hsq
  have hlin_int : Integrable (fun y => h * s y) μ := hs_int.const_mul h
  have hquad_int : Integrable (fun y => (h ^ 2 / 2) * s y ^ 2) μ :=
    hs2_int.const_mul (h ^ 2 / 2)
  have hR_meas : Measurable R := by
    dsimp [R]
    fun_prop
  have hR_int : Integrable R μ := by
    refine Integrable.of_bound hR_meas.aestronglyMeasurable (C ^ 3 * |h| ^ 3) ?_
    exact Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hR_bound y
  have hmain_eq :
      ∫ y, (1 + h * s y) * Real.log (1 + h * s y) ∂μ
        = ∫ y, h * s y ∂μ
          + ∫ y, (h ^ 2 / 2) * s y ^ 2 ∂μ
          + ∫ y, R y ∂μ := by
    calc
      ∫ y, (1 + h * s y) * Real.log (1 + h * s y) ∂μ
          = ∫ y, (h * s y + (h ^ 2 / 2) * s y ^ 2) + R y ∂μ := by
            apply integral_congr_ae
            filter_upwards with y
            dsimp [R]
            ring
      _ = ∫ y, h * s y + (h ^ 2 / 2) * s y ^ 2 ∂μ + ∫ y, R y ∂μ := by
            simpa [Pi.add_apply, add_assoc] using
              (integral_add (hlin_int.add hquad_int) hR_int)
      _ = (∫ y, h * s y ∂μ) + (∫ y, (h ^ 2 / 2) * s y ^ 2 ∂μ)
            + ∫ y, R y ∂μ := by
            simpa [Pi.add_apply, add_assoc] using
              congrArg (fun t => t + ∫ y, R y ∂μ) (integral_add hlin_int hquad_int)
  have hlin_eq : ∫ y, h * s y ∂μ = 0 := by
    rw [integral_const_mul, hs_mean, mul_zero]
  have hquad_eq :
      ∫ y, (h ^ 2 / 2) * s y ^ 2 ∂μ = (h ^ 2 / 2) * ∫ y, s y ^ 2 ∂μ := by
    rw [integral_const_mul]
  have hrem_eq :
      ∫ y, (1 + h * s y) * Real.log (1 + h * s y) ∂μ
          - (h ^ 2 / 2) * ∫ y, s y ^ 2 ∂μ
        = ∫ y, R y ∂μ := by
    rw [hmain_eq, hlin_eq, hquad_eq]
    ring
  calc
    |∫ y, (1 + h * s y) * Real.log (1 + h * s y) ∂μ
          - (h ^ 2 / 2) * ∫ y, s y ^ 2 ∂μ|
        = |∫ y, R y ∂μ| := by rw [hrem_eq]
    _ = ‖∫ y, R y ∂μ‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ _y, C ^ 3 * |h| ^ 3 ∂μ := by
        refine norm_integral_le_of_norm_le (integrable_const (C ^ 3 * |h| ^ 3)) ?_
        exact Eventually.of_forall fun y => by
          simpa [Real.norm_eq_abs] using hR_bound y
    _ = C ^ 3 * |h| ^ 3 := by
        rw [integral_const, probReal_univ, smul_eq_mul, one_mul]

/-- **Second-order KL expansion of the linear density tilt (headline result).**
For a probability measure `μ` and a bounded mean-zero score `s` (`|s| ≤ C`,
`∫ s = 0`),

    (fun h => (klDiv (tiltMeasure μ s h) μ).toReal - (h²/2) · ∫ s² dμ)
      =o[𝓝 0] (fun h => h²).

Equivalently `KL(tiltMeasure μ s h ‖ μ) = (h²/2)·∫ s² dμ + o(h²)` as `h → 0`,
the local-asymptotic-normality / Fisher-information expansion.

Proof sketch: by `Asymptotics.isLittleO_iff`, fix `c > 0`.  Eventually as `h → 0`
we have both `|h|·C ≤ 1/2` and `C³·|h| ≤ c` (continuity at `0`).  Then
`abs_klRemainder_le` gives `|remainder h| ≤ C³·|h|³ = (C³·|h|)·|h|² ≤ c·|h²|`,
which is `≤ c · ‖h²‖`. -/
theorem klDiv_tilt_expansion {μ : Measure Z} [IsProbabilityMeasure μ] {s : Z → ℝ}
    {C : ℝ} (hs_meas : Measurable s) (hsC : ∀ y, |s y| ≤ C) (hs_mean : ∫ y, s y ∂μ = 0) :
    (fun h => (InformationTheory.klDiv (tiltMeasure μ s h) μ).toReal
        - (h ^ 2 / 2) * ∫ y, s y ^ 2 ∂μ)
      =o[𝓝 0] (fun h => h ^ 2) := by
  have hC : 0 ≤ C := by
    rcases (nonempty_of_isProbabilityMeasure μ : Nonempty Z) with ⟨z⟩
    exact le_trans (abs_nonneg (s z)) (hsC z)
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hsmall : ∀ᶠ h in 𝓝 (0 : ℝ), |h| * C ≤ 1 / 2 := by
    by_cases hC0 : C = 0
    · filter_upwards with h
      simp [hC0]
    · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
      refine Metric.eventually_nhds_iff.2 ⟨(1 / 2) / C, by positivity, ?_⟩
      intro h hdist
      have habs : |h| < (1 / 2) / C := by
        simpa [Real.dist_eq, abs_sub_comm] using hdist
      have hmul : |h| * C < ((1 / 2) / C) * C :=
        mul_lt_mul_of_pos_right habs hCpos
      have hdiv : ((1 / 2) / C) * C = 1 / 2 := by field_simp [hCpos.ne']
      linarith
  have hcoef : ∀ᶠ h in 𝓝 (0 : ℝ), C ^ 3 * |h| ≤ c := by
    by_cases hC0 : C = 0
    · filter_upwards with h
      simp [hC0, le_of_lt hc]
    · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
      have hC3pos : 0 < C ^ 3 := by positivity
      refine Metric.eventually_nhds_iff.2 ⟨c / (C ^ 3), by positivity, ?_⟩
      intro h hdist
      have habs : |h| < c / (C ^ 3) := by
        simpa [Real.dist_eq, abs_sub_comm] using hdist
      have hmul : |h| * C ^ 3 < (c / (C ^ 3)) * C ^ 3 :=
        mul_lt_mul_of_pos_right habs hC3pos
      have hdiv : (c / (C ^ 3)) * C ^ 3 = c := by field_simp [hC3pos.ne']
      have : C ^ 3 * |h| < c := by
        nlinarith
      exact le_of_lt this
  filter_upwards [hsmall, hcoef] with h hh_small hh_coef
  have hrem :=
    abs_klRemainder_le (μ := μ) (s := s) (C := C) (h := h)
      hC hs_meas hsC hs_mean hh_small
  calc
    ‖(InformationTheory.klDiv (tiltMeasure μ s h) μ).toReal
        - (h ^ 2 / 2) * ∫ y, s y ^ 2 ∂μ‖
        = |(InformationTheory.klDiv (tiltMeasure μ s h) μ).toReal
            - (h ^ 2 / 2) * ∫ y, s y ^ 2 ∂μ| := Real.norm_eq_abs _
    _ ≤ C ^ 3 * |h| ^ 3 := hrem
    _ = (C ^ 3 * |h|) * |h| ^ 2 := by ring
    _ ≤ c * |h| ^ 2 :=
        mul_le_mul_of_nonneg_right hh_coef (sq_nonneg |h|)
    _ = c * ‖h ^ 2‖ := by
        simp [Real.norm_eq_abs]

end Causalean.Mathlib.InformationTheory.KlDensityTiltExpansion
