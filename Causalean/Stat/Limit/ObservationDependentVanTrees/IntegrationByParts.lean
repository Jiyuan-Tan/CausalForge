/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Limit.ObservationDependentVanTrees.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Absolute-continuity integration by parts

This module supplies integration-by-parts identities from absolute continuity
and almost-everywhere derivative representatives, including the weighted-error
identity used for observation-dependent targets.
-/

open MeasureTheory intervalIntegral Set

namespace Causalean.Stat.Limit.ObservationDependentVanTrees

/-- Two functions on an ordered interval with [absolute continuity, almost-everywhere derivative representatives, and an integrable product-rule field](hyp:hab,hf,hg,hdf,hdg,hint) satisfy [the product-rule integral equals the endpoint change in their product](goal). -/
theorem ac_product_integral_eq_boundary {a b : ℝ} {f g df dg : ℝ → ℝ}
    (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hdf : ∀ᵐ θ ∂parameterMeasure a b, HasDerivAt f (df θ) θ)
    (hdg : ∀ᵐ θ ∂parameterMeasure a b, HasDerivAt g (dg θ) θ)
    (hint : IntervalIntegrable (fun θ => df θ * g θ + f θ * dg θ) volume a b) :
    (∫ θ in a..b, df θ * g θ + f θ * dg θ) = f b * g b - f a * g a := by
  let q : ℝ → ℝ := fun θ => f θ * g θ
  have hq : AbsolutelyContinuousOnInterval q a b := hf.fun_mul hg
  have hqderiv : ∀ᵐ θ ∂parameterMeasure a b,
      HasDerivAt q (df θ * g θ + f θ * dg θ) θ := by
    filter_upwards [hdf, hdg] with θ hdfθ hdgθ
    exact hdfθ.mul hdgθ
  calc
    ∫ θ in a..b, df θ * g θ + f θ * dg θ =
        ∫ θ, df θ * g θ + f θ * dg θ ∂parameterMeasure a b := by
      rw [intervalIntegral.integral_of_le hab, parameterMeasure,
        restrict_Ioc_eq_restrict_Icc]
    _ = ∫ θ, deriv q θ ∂parameterMeasure a b := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hqderiv] with θ hθ
      exact hθ.deriv.symm
    _ = ∫ θ in a..b, deriv q θ := by
      rw [intervalIntegral.integral_of_le hab, parameterMeasure,
        restrict_Ioc_eq_restrict_Icc]
    _ = q b - q a := hq.integral_deriv_eq_sub
    _ = f b * g b - f a * g a := rfl

/-- A prior weight, likelihood section, and observation-dependent target with [absolute continuity, almost-everywhere derivative representatives, and an integrable weighted-error derivative field](hyp:hab,hw,hp,hg,hdw,hdp,hdg,hint) satisfy [the weighted-error derivative integral equals the weighted endpoint difference](goal). -/
theorem ac_weighted_error_integral_eq_boundary {a b c : ℝ}
    {w p g dw dp dg : ℝ → ℝ}
    (hab : a ≤ b)
    (hw : AbsolutelyContinuousOnInterval w a b)
    (hp : AbsolutelyContinuousOnInterval p a b)
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hdw : ∀ᵐ θ ∂parameterMeasure a b, HasDerivAt w (dw θ) θ)
    (hdp : ∀ᵐ θ ∂parameterMeasure a b, HasDerivAt p (dp θ) θ)
    (hdg : ∀ᵐ θ ∂parameterMeasure a b, HasDerivAt g (dg θ) θ)
    (hint : IntervalIntegrable
      (fun θ => (dw θ * p θ + w θ * dp θ) * (c - g θ) - w θ * p θ * dg θ)
      volume a b) :
    (∫ θ in a..b,
        (dw θ * p θ + w θ * dp θ) * (c - g θ) - w θ * p θ * dg θ) =
      w b * p b * (c - g b) - w a * p a * (c - g a) := by
  let q : ℝ → ℝ := fun θ => w θ * p θ * (c - g θ)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b := by
    rw [absolutelyContinuousOnInterval_iff]
    intro ε hε
    exact ⟨1, zero_lt_one, by intros; simpa using hε⟩
  have hq : AbsolutelyContinuousOnInterval q a b :=
    (hw.fun_mul hp).fun_mul (hconst.sub hg)
  have hqderiv : ∀ᵐ θ ∂parameterMeasure a b,
      HasDerivAt q
        ((dw θ * p θ + w θ * dp θ) * (c - g θ) - w θ * p θ * dg θ) θ := by
    filter_upwards [hdw, hdp, hdg] with θ hdwθ hdpθ hdgθ
    have hmul := (hdwθ.mul hdpθ).mul (hdgθ.const_sub c)
    have hder :
        (dw θ * p θ + w θ * dp θ) * (c - g θ) + (w * p) θ * -dg θ =
          (dw θ * p θ + w θ * dp θ) * (c - g θ) - w θ * p θ * dg θ := by
      simp only [Pi.mul_apply]
      ring
    rw [hder] at hmul
    exact hmul
  calc
    ∫ θ in a..b,
        (dw θ * p θ + w θ * dp θ) * (c - g θ) - w θ * p θ * dg θ =
        ∫ θ, (dw θ * p θ + w θ * dp θ) * (c - g θ) - w θ * p θ * dg θ
          ∂parameterMeasure a b := by
      rw [intervalIntegral.integral_of_le hab, parameterMeasure,
        restrict_Ioc_eq_restrict_Icc]
    _ = ∫ θ, deriv q θ ∂parameterMeasure a b := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hqderiv] with θ hθ
      exact hθ.deriv.symm
    _ = ∫ θ in a..b, deriv q θ := by
      rw [intervalIntegral.integral_of_le hab, parameterMeasure,
        restrict_Ioc_eq_restrict_Icc]
    _ = q b - q a := hq.integral_deriv_eq_sub
    _ = w b * p b * (c - g b) - w a * p a * (c - g a) := rfl

/-- In a σ-finite observation model, if the [prior weight and almost every likelihood and target section are absolutely continuous with the stated derivative representatives, endpoint error products vanish, and the derivative-balance field is measurable and integrable](hyp:hab,hw,hp,hg,hdw,hdp,hdg,hboundary,hsm,hint), [the joint integral of the derivative-balance field is zero](goal). -/
theorem product_integral_derivativeBalance_eq_zero
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]
    {a b : ℝ} (hab : a ≤ b) {w dw : ℝ → ℝ} {p dp g dg : ℝ → X → ℝ} {T : X → ℝ}
    (hw : AbsolutelyContinuousOnInterval w a b)
    (hp : ∀ᵐ x ∂μ, AbsolutelyContinuousOnInterval (fun θ => p θ x) a b)
    (hg : ∀ᵐ x ∂μ, AbsolutelyContinuousOnInterval (fun θ => g θ x) a b)
    (hdw : ∀ᵐ θ ∂parameterMeasure a b, HasDerivAt w (dw θ) θ)
    (hdp : ∀ᵐ x ∂μ, ∀ᵐ θ ∂parameterMeasure a b, HasDerivAt (fun t => p t x) (dp θ x) θ)
    (hdg : ∀ᵐ x ∂μ, ∀ᵐ θ ∂parameterMeasure a b, HasDerivAt (fun t => g t x) (dg θ x) θ)
    (hboundary : ∀ᵐ x ∂μ,
      w b * p b x * (T x - g b x) = 0 ∧ w a * p a x * (T x - g a x) = 0)
    (hsm : AEStronglyMeasurable (derivativeBalanceField w dw p dp g dg T)
      ((parameterMeasure a b).prod μ))
    (hint : Integrable (derivativeBalanceField w dw p dp g dg T)
      ((parameterMeasure a b).prod μ)) :
    ∫ z, derivativeBalanceField w dw p dp g dg T z ∂((parameterMeasure a b).prod μ) = 0 := by
  letI : IsFiniteMeasure (parameterMeasure a b) := by
    unfold parameterMeasure
    infer_instance
  rw [integral_prod_symm _ hint]
  apply integral_eq_zero_of_ae
  filter_upwards [hp, hg, hdp, hdg, hboundary, hint.prod_left_ae] with
      x hpx hgx hdpx hdgx hboundaryx hintx
  let q : ℝ → ℝ := fun θ => w θ * p θ x * (T x - g θ x)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => T x) a b := by
    rw [absolutelyContinuousOnInterval_iff]
    intro ε hε
    exact ⟨1, zero_lt_one, by intros; simpa using hε⟩
  have hq : AbsolutelyContinuousOnInterval q a b :=
    (hw.fun_mul hpx).fun_mul (hconst.sub hgx)
  have hqderiv : ∀ᵐ θ ∂parameterMeasure a b,
      HasDerivAt q (derivativeBalanceField w dw p dp g dg T (θ, x)) θ := by
    filter_upwards [hdw, hdpx, hdgx] with θ hdwθ hdpθ hdgθ
    have hmul := (hdwθ.mul hdpθ).mul (hdgθ.const_sub (T x))
    simp only [Pi.mul_apply] at hmul
    have hder :
        (dw θ * p θ x + w θ * dp θ x) * (T x - g θ x) +
            w θ * p θ x * -dg θ x =
          derivativeBalanceField w dw p dp g dg T (θ, x) := by
      simp only [derivativeBalanceField, jointDensity]
      ring
    rw [hder] at hmul
    exact hmul
  calc
    ∫ θ, derivativeBalanceField w dw p dp g dg T (θ, x) ∂parameterMeasure a b =
        ∫ θ, deriv q θ ∂parameterMeasure a b := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hqderiv] with θ hθ
      exact hθ.deriv.symm
    _ = ∫ θ in a..b, deriv q θ := by
      rw [intervalIntegral.integral_of_le hab, parameterMeasure,
        restrict_Ioc_eq_restrict_Icc]
    _ = q b - q a := hq.integral_deriv_eq_sub
    _ = 0 := by simp [q, hboundaryx.1, hboundaryx.2]

end Causalean.Stat.Limit.ObservationDependentVanTrees
