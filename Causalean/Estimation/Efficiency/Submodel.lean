/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Regular parametric submodels via exponential tilting

A *regular parametric submodel* through a base law `P` is a smooth one-parameter
family of probability measures `P_t` passing through `P` at `t = 0`, with a
*score* `s = ∂ₜ log p_t |₀`.  For semiparametric efficiency we only ever need to
differentiate functionals along such paths, and the exponential tilt

    P_t  :=  (e^{t·s} / c(t)) · P,        c(t) = ∫ e^{t·s} dP

realizes every bounded mean-zero score `s` as a genuine regular submodel.  This
file builds that construction and proves the **tilt-derivative lemma**: for a
fixed (integrable) `φ`,

    d/dt  E_{P_t}[φ] |_{t=0}  =  ∫ φ·s dP  =  Cov_P(φ, s)

(the last equality because `∫ s dP = 0`).  This is the analytic core of every
pathwise-derivative computation — in particular of the proof that the AIPW
influence function is Hahn's (1998) efficient influence function
(`Causalean/Estimation/Efficiency/ATETangent.lean`).

Reference: van der Vaart, *Asymptotic Statistics*, §25.3 (scores and tangent
spaces); Bickel–Klaassen–Ritov–Wellner, *Efficient and Adaptive Estimation*.
-/

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
Defines exponential-tilt submodels and score paths used in semiparametric
efficiency arguments. The module provides the differentiable perturbation
interface for tangent-space calculations.
-/

namespace Causalean
namespace Estimation
namespace Efficiency

open MeasureTheory Real Filter Topology

variable {Z : Type*} [MeasurableSpace Z]

/-! ## The exponential tilt -/

/-- Normalizing constant `c(t) = ∫ e^{t·s} dP` of the exponential tilt. -/
noncomputable def tiltNorm (P : Measure Z) (s : Z → ℝ) (t : ℝ) : ℝ :=
  ∫ z, Real.exp (t * s z) ∂P

/-- Tilted expectation `E_{P_t}[φ] = (∫ φ·e^{t·s} dP)/(∫ e^{t·s} dP)`.  This is
the expectation of `φ` under the exponentially tilted law `P_t`. -/
noncomputable def tiltExp (P : Measure Z) (s φ : Z → ℝ) (t : ℝ) : ℝ :=
  (∫ z, φ z * Real.exp (t * s z) ∂P) / tiltNorm P s t

/-- The exponentially tilted measure `P_t = (e^{t·s}/c(t)) · P`. -/
noncomputable def tiltMeasure (P : Measure Z) (s : Z → ℝ) (t : ℝ) : Measure Z :=
  (ENNReal.ofReal (tiltNorm P s t))⁻¹ •
    P.withDensity (fun z => ENNReal.ofReal (Real.exp (t * s z)))

/-- At `t = 0` the normalizing constant is the total mass `= 1`. -/
@[simp] lemma tiltNorm_zero {P : Measure Z} [IsProbabilityMeasure P] {s : Z → ℝ} :
    tiltNorm P s 0 = 1 := by
  simp [tiltNorm]

/-! ## The tilt-derivative lemma

The single analytic workhorse: differentiation under the integral sign for the
exponential family, specialised to give `d/dt E_{P_t}[φ]|₀ = ∫ φ·s dP`. -/

section Derivative

variable {P : Measure Z} [IsProbabilityMeasure P] {s φ : Z → ℝ} {M : ℝ}

/-- `IsProbabilityMeasure` forces the sample space to be nonempty. -/
private lemma nonempty_of_isProbabilityMeasure
    (P : Measure Z) [IsProbabilityMeasure P] : Nonempty Z := by
  by_contra h
  rw [not_nonempty_iff] at h
  have h1 : P (Set.univ : Set Z) = 1 := measure_univ
  rw [Set.univ_eq_empty_iff.2 h] at h1
  simp at h1

/-- **Numerator derivative.** `d/dt ∫ φ·e^{t·s} dP |₀ = ∫ φ·s dP`, for bounded
measurable score `s` and integrable `φ`. -/
lemma hasDerivAt_tilt_numerator
    (hs_meas : Measurable s) (hsM : ∀ z, |s z| ≤ M)
    (hφ_meas : AEStronglyMeasurable φ P) (hφ_int : Integrable φ P) :
    HasDerivAt (fun t => ∫ z, φ z * Real.exp (t * s z) ∂P)
      (∫ z, φ z * s z ∂P) 0 := by
  have hZ : Nonempty Z := nonempty_of_isProbabilityMeasure P
  set F : ℝ → Z → ℝ := fun t z => φ z * Real.exp (t * s z) with hF
  set F' : ℝ → Z → ℝ := fun t z => φ z * s z * Real.exp (t * s z) with hF'
  set bound : Z → ℝ := fun z => |φ z| * (M * Real.exp M) with hbound
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (s hZ.some)) (hsM hZ.some)
  have hset : Metric.ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 one_pos
  have hF_meas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) P := by
    filter_upwards with t
    exact hφ_meas.mul ((hs_meas.const_mul t).exp.aestronglyMeasurable)
  have hF0_int : Integrable (F 0) P := by simpa [hF] using hφ_int
  have hF'_meas : AEStronglyMeasurable (F' 0) P := by
    have : AEStronglyMeasurable (fun z => φ z * s z) P :=
      hφ_meas.mul hs_meas.aestronglyMeasurable
    simpa [hF'] using this
  have h_bound : ∀ᵐ z ∂P, ∀ t ∈ Metric.ball (0 : ℝ) 1, ‖F' t z‖ ≤ bound z := by
    filter_upwards with z t ht
    have htlt : |t| < 1 := by simpa [Real.dist_eq] using ht
    have hexp_le : Real.exp (t * s z) ≤ Real.exp M := by
      apply Real.exp_le_exp.2
      calc t * s z ≤ |t * s z| := le_abs_self _
        _ = |t| * |s z| := abs_mul _ _
        _ ≤ 1 * M := by
              apply mul_le_mul (le_of_lt htlt) (hsM z) (abs_nonneg _) (by norm_num)
        _ = M := one_mul _
    calc ‖F' t z‖ = |φ z| * |s z| * Real.exp (t * s z) := by
            rw [hF']
            rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ |φ z| * M * Real.exp M := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left (hsM z) (abs_nonneg _)
            · exact hexp_le
            · exact (Real.exp_pos _).le
            · exact mul_nonneg (abs_nonneg _) hM0
      _ = bound z := by rw [hbound]; ring
  have hbound_int : Integrable bound P := by
    rw [hbound]; exact hφ_int.abs.mul_const _
  have h_diff : ∀ᵐ z ∂P, ∀ t ∈ Metric.ball (0 : ℝ) 1,
      HasDerivAt (fun t => F t z) (F' t z) t := by
    filter_upwards with z t _
    have h1 : HasDerivAt (fun t : ℝ => t * s z) (s z) t := by
      simpa using (hasDerivAt_id t).mul_const (s z)
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (t * s z))
        (Real.exp (t * s z) * s z) t := h1.exp
    have h3 := h2.const_mul (φ z)
    simpa [hF, hF', mul_comm, mul_left_comm, mul_assoc] using h3
  have hmain :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := bound)
      (F := F) (F' := F') (x₀ := (0 : ℝ)) (s := Metric.ball (0 : ℝ) 1)
      hset hF_meas hF0_int hF'_meas h_bound hbound_int h_diff
  have hconc := hmain.2
  have heq : (∫ z, F' 0 z ∂P) = ∫ z, φ z * s z ∂P := by
    apply integral_congr_ae
    filter_upwards with z
    simp [hF']
  rw [heq] at hconc
  exact hconc

/-- **The tilt-derivative lemma.**  Along the exponential tilt with bounded
mean-zero score `s`, the tilted expectation of a fixed integrable `φ` is
differentiable at `t = 0` with derivative `∫ φ·s dP`.  (Mean-zero `s` makes the
normalizing-constant contribution vanish, so the derivative is the raw
covariance `∫ φ·s dP`.) -/
theorem hasDerivAt_tiltExp
    (hs_meas : Measurable s) (hsM : ∀ z, |s z| ≤ M)
    (hs_mean : ∫ z, s z ∂P = 0)
    (hφ_meas : AEStronglyMeasurable φ P) (hφ_int : Integrable φ P) :
    HasDerivAt (tiltExp P s φ) (∫ z, φ z * s z ∂P) 0 := by
  have hN : HasDerivAt (fun t => ∫ z, φ z * Real.exp (t * s z) ∂P)
      (∫ z, φ z * s z ∂P) 0 := hasDerivAt_tilt_numerator hs_meas hsM hφ_meas hφ_int
  have hc : HasDerivAt (fun t => tiltNorm P s t) (∫ z, s z ∂P) 0 := by
    have := hasDerivAt_tilt_numerator (P := P) (φ := fun _ => (1 : ℝ)) hs_meas hsM
      aestronglyMeasurable_const (integrable_const (1 : ℝ))
    simpa [tiltNorm, one_mul] using this
  have hc0_ne : tiltNorm P s 0 ≠ 0 := by rw [tiltNorm_zero]; norm_num
  have hquot := hN.div hc hc0_ne
  rw [tiltNorm_zero, hs_mean] at hquot
  simpa [tiltExp, mul_zero, sub_zero, one_pow, div_one, mul_one] using hquot

end Derivative

/-! ## Measure-level properties of the tilt

The derivative lemmas above work entirely with the explicit integral formulas
`tiltNorm`/`tiltExp`.  This section relates those formulas to the genuine tilted
*measure* `tiltMeasure`: it is a probability measure, and its expectation
operator is exactly `tiltExp`.  This is the bridge that lets a downstream file
write `E_{P_t}[φ] = tiltExp P s φ t` and feed `hasDerivAt_tiltExp`. -/

section Measure

variable {P : Measure Z} [IsProbabilityMeasure P] {s : Z → ℝ} {M : ℝ} {t : ℝ}

/-- For a bounded measurable score, `e^{t·s}` is `P`-integrable (it is bounded by
the constant `e^{|t|·M}` on the finite measure `P`). -/
lemma tilt_exp_integrable (hs_meas : Measurable s) (hsM : ∀ z, |s z| ≤ M) :
    Integrable (fun z => Real.exp (t * s z)) P := by
  apply Integrable.mono' (integrable_const (Real.exp (|t| * M)))
    (hs_meas.const_mul t).exp.aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  calc t * s z ≤ |t * s z| := le_abs_self _
    _ = |t| * |s z| := abs_mul _ _
    _ ≤ |t| * M := mul_le_mul_of_nonneg_left (hsM z) (abs_nonneg _)

/-- The normalizing constant `c(t) = ∫ e^{t·s} dP` is strictly positive. -/
lemma tiltNorm_pos (hs_meas : Measurable s) (hsM : ∀ z, |s z| ≤ M) :
    0 < tiltNorm P s t := by
  have hlow : ∀ z, Real.exp (-(|t| * M)) ≤ Real.exp (t * s z) := by
    intro z
    apply Real.exp_le_exp.2
    have : -(|t| * M) ≤ t * s z := by
      have h1 : -(|t| * M) ≤ -|t * s z| := by
        rw [neg_le_neg_iff, abs_mul]
        exact mul_le_mul_of_nonneg_left (hsM z) (abs_nonneg _)
      exact le_trans h1 (neg_abs_le _)
    exact this
  calc (0 : ℝ) < Real.exp (-(|t| * M)) := Real.exp_pos _
    _ = ∫ _z, Real.exp (-(|t| * M)) ∂P := by
        rw [integral_const, probReal_univ, one_smul]
    _ ≤ tiltNorm P s t :=
        integral_mono (integrable_const _) (tilt_exp_integrable hs_meas hsM) hlow

/-- The tilted law `tiltMeasure P s t` is a probability measure. -/
lemma isProbabilityMeasure_tiltMeasure
    (hs_meas : Measurable s) (hsM : ∀ z, |s z| ≤ M) :
    IsProbabilityMeasure (tiltMeasure P s t) := by
  constructor
  have hnn : 0 ≤ᵐ[P] fun z => Real.exp (t * s z) :=
    Filter.Eventually.of_forall fun z => (Real.exp_pos _).le
  have hmass :
      (P.withDensity (fun z => ENNReal.ofReal (Real.exp (t * s z)))) Set.univ
        = ENNReal.ofReal (tiltNorm P s t) := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (tilt_exp_integrable hs_meas hsM) hnn]
    rfl
  rw [tiltMeasure, Measure.smul_apply, hmass, smul_eq_mul]
  have hne0 : ENNReal.ofReal (tiltNorm P s t) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact tiltNorm_pos hs_meas hsM
  exact ENNReal.inv_mul_cancel hne0 ENNReal.ofReal_ne_top

/-- The expectation of `h_fn` under the tilted law equals `tiltExp P s h_fn t`.
(No integrability hypothesis is needed: both sides reduce to the same `P`-integral
of `h_fn · e^{t·s}` scaled by `1/c(t)`, and a non-integrable `h_fn` makes both
the integral and `tiltExp`'s numerator the same junk default.) -/
lemma integral_tiltMeasure (hs_meas : Measurable s) (hsM : ∀ z, |s z| ≤ M)
    {h_fn : Z → ℝ} :
    ∫ z, h_fn z ∂(tiltMeasure P s t) = tiltExp P s h_fn t := by
  rw [tiltMeasure, integral_smul_measure]
  have hdens : (fun z => ENNReal.ofReal (Real.exp (t * s z)))
      = (fun z => (((Real.exp (t * s z)).toNNReal : NNReal) : ENNReal)) := rfl
  have hwd :
      ∫ z, h_fn z ∂(P.withDensity (fun z => ENNReal.ofReal (Real.exp (t * s z))))
        = ∫ z, Real.exp (t * s z) * h_fn z ∂P := by
    rw [hdens, integral_withDensity_eq_integral_smul₀
      ((hs_meas.const_mul t).exp.real_toNNReal.aemeasurable) h_fn]
    apply integral_congr_ae
    filter_upwards with z
    rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Real.exp_pos _).le]
  rw [hwd]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (tiltNorm_pos hs_meas hsM).le,
    smul_eq_mul]
  rw [tiltExp, div_eq_inv_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  ring

end Measure

end Efficiency
end Estimation
end Causalean
