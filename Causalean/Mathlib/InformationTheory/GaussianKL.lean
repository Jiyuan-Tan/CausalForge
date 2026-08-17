/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Kullback–Leibler divergence between real Gaussian measures

Mathlib provides the real Gaussian measure `ProbabilityTheory.gaussianReal m v`
(mean `m : ℝ`, variance `v : ℝ≥0`) and the Kullback–Leibler divergence
`MeasureTheory.klDiv` (an `ℝ≥0∞`), but not the closed form of the KL divergence
between two Gaussians.  This file derives the **equal-variance** closed form

  `klDiv (gaussianReal m₀ v) (gaussianReal m₁ v)
      = ENNReal.ofReal ((m₀ - m₁)^2 / (2 * v))`   (`0 < v`),

which is the canonical KL input for Gaussian-location minimax (Le Cam / two-point)
lower bounds.

## Proof outline

For `0 < v` both measures are `volume.withDensity (gaussianPDF · v)` with a strictly
positive density, hence mutually absolutely continuous with `volume`.  The derivation
follows the standard four steps:

1. `gaussianReal_ac_gaussianReal` — absolute continuity
   `gaussianReal m₀ v ≪ gaussianReal m₁ v`, via `volume` as an intermediary.
2. `llr_gaussianReal_ae` — the log-likelihood ratio is a.e. the difference of the two
   Gaussian log-densities; at equal variance the normalising constants cancel, leaving
   the affine function `x ↦ (m₀ - m₁) * (2*x - m₀ - m₁) / (2*v)`.
3. `integrable_llr_gaussianReal` — that affine ratio is integrable under
   `gaussianReal m₀ v` (the Gaussian has a finite first moment).
4. `gaussianKL_eq` — `klDiv = ENNReal.ofReal (∫ llr ∂gaussianReal m₀ v)`, evaluated with
   `∫ x ∂gaussianReal m₀ v = m₀`.

## Main result

* `gaussianKL_eq` — the equal-variance Gaussian KL closed form (the reusable workhorse).

## References

Standard information-theory identity
`KL(N(m₀,σ²) ∥ N(m₁,σ²)) = (m₀ − m₁)² / (2σ²)` (e.g. Cover & Thomas).
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace Causalean.Mathlib.InformationTheory

variable {m₀ m₁ : ℝ} {v : ℝ≥0}

/-- **Absolute continuity of nondegenerate Gaussians.** For `v₀ ≠ 0` and `v₁ ≠ 0`,
`gaussianReal m₀ v₀` is absolutely continuous with respect to `gaussianReal m₁ v₁`:
both are `volume.withDensity` of a strictly positive density, so each is mutually
absolutely continuous with Lebesgue measure, and absolute continuity is transitive. -/
lemma gaussianReal_ac_gaussianReal (m₀ m₁ : ℝ) {v₀ v₁ : ℝ≥0}
    (hv₀ : v₀ ≠ 0) (hv₁ : v₁ ≠ 0) :
    gaussianReal m₀ v₀ ≪ gaussianReal m₁ v₁ :=
  (gaussianReal_absolutelyContinuous m₀ hv₀).trans
    (gaussianReal_absolutelyContinuous' m₁ hv₁)

/-- **Radon–Nikodym ratio of equal-variance Gaussians, as a real number.** For `v ≠ 0`,
the real part of the Radon–Nikodym derivative `∂(gaussianReal m₀ v)/∂(gaussianReal m₁ v)`
is a.e. (with respect to `gaussianReal m₀ v`) the pointwise ratio of the two Gaussian
densities `gaussianPDFReal m₀ v x / gaussianPDFReal m₁ v x`. -/
lemma rnDeriv_toReal_gaussianReal_ae (m₀ m₁ : ℝ) (hv : v ≠ 0) :
    (fun x ↦ ((gaussianReal m₀ v).rnDeriv (gaussianReal m₁ v) x).toReal)
      =ᵐ[gaussianReal m₀ v]
      fun x ↦ gaussianPDFReal m₀ v x / gaussianPDFReal m₁ v x := by
  let μ : Measure ℝ := gaussianReal m₀ v
  let ν : Measure ℝ := gaussianReal m₁ v
  have hμvol : μ ≪ volume := gaussianReal_absolutelyContinuous m₀ hv
  have hμν : μ ≪ ν := gaussianReal_ac_gaussianReal m₀ m₁ hv hv
  have hvolν : volume ≪ ν := gaussianReal_absolutelyContinuous' m₁ hv
  have hchain : μ.rnDeriv volume * volume.rnDeriv ν =ᵐ[μ] μ.rnDeriv ν := by
    exact hμν (Measure.rnDeriv_mul_rnDeriv (μ := μ) (ν := volume) (κ := ν) hμvol)
  have hμpdf : μ.rnDeriv volume =ᵐ[μ] gaussianPDF m₀ v :=
    hμvol (rnDeriv_gaussianReal m₀ v)
  have hνpdf_vol : (ν.rnDeriv volume)⁻¹ =ᵐ[volume] volume.rnDeriv ν := by
    exact Measure.inv_rnDeriv' (μ := volume) (ν := ν) hvolν
  have hνpdf : (gaussianPDF m₁ v)⁻¹ =ᵐ[μ] volume.rnDeriv ν := by
    exact hμvol (((rnDeriv_gaussianReal m₁ v).symm.inv).trans hνpdf_vol)
  filter_upwards [hchain, hμpdf, hνpdf] with x hchain hx0 hx1
  rw [← hchain]
  simp only [Pi.mul_apply]
  rw [hx0, ← hx1]
  simp [div_eq_mul_inv]

/-- **Log-likelihood ratio of equal-variance Gaussians.** For `v ≠ 0`, the
log-likelihood ratio `llr (gaussianReal m₀ v) (gaussianReal m₁ v)` is a.e. (with respect
to `gaussianReal m₀ v`) equal to the affine function
`x ↦ (m₀ - m₁) * (2*x - m₀ - m₁) / (2*v)`.  At equal variance the `(√(2πv))⁻¹`
normalising constants cancel in the density ratio, so the log-ratio reduces to
`((x - m₁)^2 - (x - m₀)^2) / (2*v) = (m₀ - m₁)*(2*x - m₀ - m₁)/(2*v)`. -/
lemma llr_gaussianReal_ae (m₀ m₁ : ℝ) (hv : v ≠ 0) :
    llr (gaussianReal m₀ v) (gaussianReal m₁ v)
      =ᵐ[gaussianReal m₀ v]
      fun x ↦ (m₀ - m₁) * (2 * x - m₀ - m₁) / (2 * (v : ℝ)) := by
  filter_upwards [rnDeriv_toReal_gaussianReal_ae m₀ m₁ hv] with x hx
  have hvposNN : 0 < v := by exact zero_lt_iff.mpr hv
  have hvpos : 0 < (v : ℝ) := by exact_mod_cast hvposNN
  have hc : (√(2 * π * (v : ℝ)))⁻¹ ≠ 0 := by positivity
  simp only [llr_def, hx]
  calc
    log (gaussianPDFReal m₀ v x / gaussianPDFReal m₁ v x)
        = log (rexp (-(x - m₀) ^ 2 / (2 * (v : ℝ))) /
            rexp (-(x - m₁) ^ 2 / (2 * (v : ℝ)))) := by
          congr 1
          simp [gaussianPDFReal]
          field_simp [hc]
    _ = (-(x - m₀) ^ 2 / (2 * (v : ℝ))) -
          (-(x - m₁) ^ 2 / (2 * (v : ℝ))) := by
          rw [Real.log_div (Real.exp_ne_zero _) (Real.exp_ne_zero _)]
          simp
    _ = (m₀ - m₁) * (2 * x - m₀ - m₁) / (2 * (v : ℝ)) := by
          field_simp [(show (2 : ℝ) * (v : ℝ) ≠ 0 by positivity)]
          ring

/-- **Integrability of the Gaussian log-likelihood ratio.** For `v ≠ 0`, the affine
log-likelihood ratio `x ↦ (m₀ - m₁) * (2*x - m₀ - m₁) / (2*v)` is integrable with respect
to `gaussianReal m₀ v`, because the Gaussian has a finite first moment. -/
lemma integrable_llr_gaussianReal (m₀ m₁ : ℝ) (hv : v ≠ 0) :
    Integrable (llr (gaussianReal m₀ v) (gaussianReal m₁ v)) (gaussianReal m₀ v) := by
  have hid : Integrable (fun x : ℝ ↦ x) (gaussianReal m₀ v) := by
    simpa [Function.id_def] using (memLp_id_gaussianReal (μ := m₀) (v := v) (p := 1)).integrable
      (by norm_num)
  have haffine : Integrable
      (fun x : ℝ ↦ ((m₀ - m₁) / (2 * (v : ℝ))) * (2 * x - (m₀ + m₁)))
      (gaussianReal m₀ v) := by
    exact (((hid.const_mul 2).sub (integrable_const (m₀ + m₁))).const_mul
      ((m₀ - m₁) / (2 * (v : ℝ))))
  have htarget : Integrable
      (fun x : ℝ ↦ (m₀ - m₁) * (2 * x - m₀ - m₁) / (2 * (v : ℝ)))
      (gaussianReal m₀ v) := by
    convert haffine using 1
    funext x
    ring
  exact htarget.congr (llr_gaussianReal_ae m₀ m₁ hv).symm

/-- **Integral of the Gaussian log-likelihood ratio.** For `v ≠ 0`,
`∫ llr (gaussianReal m₀ v) (gaussianReal m₁ v) ∂(gaussianReal m₀ v) = (m₀ - m₁)^2 / (2*v)`,
obtained by integrating the affine a.e. form against `∫ x ∂gaussianReal m₀ v = m₀`. -/
lemma integral_llr_gaussianReal (m₀ m₁ : ℝ) (hv : v ≠ 0) :
    ∫ x, llr (gaussianReal m₀ v) (gaussianReal m₁ v) x ∂(gaussianReal m₀ v)
      = (m₀ - m₁) ^ 2 / (2 * (v : ℝ)) := by
  have hid : Integrable (fun x : ℝ ↦ x) (gaussianReal m₀ v) := by
    simpa [Function.id_def] using (memLp_id_gaussianReal (μ := m₀) (v := v) (p := 1)).integrable
      (by norm_num)
  have hden : (2 : ℝ) * (v : ℝ) ≠ 0 := by
    have hvposNN : 0 < v := by exact zero_lt_iff.mpr hv
    have hvpos : 0 < (v : ℝ) := by exact_mod_cast hvposNN
    positivity
  rw [integral_congr_ae (llr_gaussianReal_ae m₀ m₁ hv)]
  calc
    ∫ x, (m₀ - m₁) * (2 * x - m₀ - m₁) / (2 * (v : ℝ)) ∂(gaussianReal m₀ v)
        = ∫ x, ((m₀ - m₁) / (2 * (v : ℝ))) * (2 * x - (m₀ + m₁))
            ∂(gaussianReal m₀ v) := by
          apply integral_congr_ae
          exact ae_of_all _ (fun x ↦ by ring)
    _ = ((m₀ - m₁) / (2 * (v : ℝ))) *
          ∫ x, (2 * x - (m₀ + m₁)) ∂(gaussianReal m₀ v) := by
          rw [integral_const_mul]
    _ = ((m₀ - m₁) / (2 * (v : ℝ))) * (2 * m₀ - (m₀ + m₁)) := by
          rw [integral_sub (hid.const_mul 2) (integrable_const (m₀ + m₁))]
          rw [integral_const_mul, integral_id_gaussianReal]
          simp [integral_const]
    _ = (m₀ - m₁) ^ 2 / (2 * (v : ℝ)) := by
          field_simp [hden]
          ring

/-- **Equal-variance Gaussian KL divergence (closed form).** For means `m₀`, `m₁` and
[a strictly positive common variance `v`](hyp:hv), [the Kullback–Leibler divergence between two
real Gaussians of equal variance `v` and respective means `m₀` and `m₁` equals `(m₀ - m₁)² /
(2v)`](goal):

  `klDiv (gaussianReal m₀ v) (gaussianReal m₁ v) = ENNReal.ofReal ((m₀ - m₁)^2 / (2*v))`.

This is the canonical KL input for Gaussian-location minimax (Le Cam / two-point)
lower bounds. -/
theorem gaussianKL_eq (m₀ m₁ : ℝ) (hv : 0 < v) :
    InformationTheory.klDiv (gaussianReal m₀ v) (gaussianReal m₁ v)
      = ENNReal.ofReal ((m₀ - m₁) ^ 2 / (2 * (v : ℝ))) := by
  have hv0 : v ≠ 0 := hv.ne'
  rw [InformationTheory.klDiv_of_ac_of_integrable (gaussianReal_ac_gaussianReal m₀ m₁ hv0 hv0)
    (integrable_llr_gaussianReal m₀ m₁ hv0)]
  rw [integral_llr_gaussianReal m₀ m₁ hv0]
  simp

end Causalean.Mathlib.InformationTheory
