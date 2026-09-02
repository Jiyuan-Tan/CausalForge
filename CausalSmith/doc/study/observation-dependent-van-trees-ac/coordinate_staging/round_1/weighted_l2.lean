/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Limit.ObservationDependentVanTrees.Basic
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Product-measure weighted L2 Cauchy--Schwarz

This module packages Fubini for explicitly integrable product fields and proves
the squared weighted Cauchy--Schwarz inequality used in van Trees arguments.
-/

open MeasureTheory

namespace Causalean.Stat.Limit.ObservationDependentVanTrees

/-- A real-valued product field that is [almost-everywhere strongly measurable and integrable under two σ-finite measures](hyp:hsm,hint) has [both iterated integrals equal to its product-measure integral](goal). -/
theorem product_integral_eq_iterated
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]
    {F : A × B → ℝ}
    (hsm : AEStronglyMeasurable F (μ.prod ν)) (hint : Integrable F (μ.prod ν)) :
    (∫ z, F z ∂(μ.prod ν)) = ∫ a, (∫ b, F (a, b) ∂ν) ∂μ ∧
      (∫ z, F z ∂(μ.prod ν)) = ∫ b, (∫ a, F (a, b) ∂μ) ∂ν := by
  have hint' : Integrable F (μ.prod ν) := ⟨hsm, hint.hasFiniteIntegral⟩
  exact ⟨integral_prod F hint', integral_prod_symm F hint'⟩

/-- Under a [nonnegative weight and measurable, integrable weighted square and cross-product fields](hyp:hq,hfsm,hssm,hfssm,hfint,hsint,hfsint), [the squared weighted pairing is bounded by the product of the two weighted second moments](goal). -/
theorem weighted_integral_mul_sq_le
    {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {q f s : A → ℝ}
    (hq : ∀ᵐ a ∂μ, 0 ≤ q a)
    (hfsm : AEStronglyMeasurable (fun a => f a ^ 2 * q a) μ)
    (hssm : AEStronglyMeasurable (fun a => s a ^ 2 * q a) μ)
    (hfssm : AEStronglyMeasurable (fun a => f a * s a * q a) μ)
    (hfint : Integrable (fun a => f a ^ 2 * q a) μ)
    (hsint : Integrable (fun a => s a ^ 2 * q a) μ)
    (hfsint : Integrable (fun a => f a * s a * q a) μ) :
    (∫ a, f a * s a * q a ∂μ) ^ 2 ≤
      (∫ a, f a ^ 2 * q a ∂μ) * (∫ a, s a ^ 2 * q a ∂μ) := by
  have hfint' : Integrable (fun a => f a ^ 2 * q a) μ :=
    ⟨hfsm, hfint.hasFiniteIntegral⟩
  have hsint' : Integrable (fun a => s a ^ 2 * q a) μ :=
    ⟨hssm, hsint.hasFiniteIntegral⟩
  have hfsint' : Integrable (fun a => f a * s a * q a) μ :=
    ⟨hfssm, hfsint.hasFiniteIntegral⟩
  have hquad : ∀ t : ℝ,
      0 ≤ (∫ a, s a ^ 2 * q a ∂μ) * (t * t) +
        (-2 * (∫ a, f a * s a * q a ∂μ)) * t +
        (∫ a, f a ^ 2 * q a ∂μ) := by
    intro t
    have hnonneg : 0 ≤ ∫ a, (f a - t * s a) ^ 2 * q a ∂μ := by
      apply integral_nonneg_of_ae
      filter_upwards [hq] with a hqa
      exact mul_nonneg (sq_nonneg _) hqa
    have hcross : Integrable (fun a => (2 * t) * (f a * s a * q a)) μ :=
      hfsint'.const_mul (2 * t)
    have hsquare : Integrable (fun a => t ^ 2 * (s a ^ 2 * q a)) μ :=
      hsint'.const_mul (t ^ 2)
    have hexpand :
        (∫ a, (f a - t * s a) ^ 2 * q a ∂μ) =
          (∫ a, f a ^ 2 * q a ∂μ) -
            (2 * t) * (∫ a, f a * s a * q a ∂μ) +
            t ^ 2 * (∫ a, s a ^ 2 * q a ∂μ) := by
      calc
        (∫ a, (f a - t * s a) ^ 2 * q a ∂μ) =
            ∫ a, (f a ^ 2 * q a) -
              (2 * t) * (f a * s a * q a) +
              t ^ 2 * (s a ^ 2 * q a) ∂μ := by
                apply integral_congr_ae
                filter_upwards with a
                ring
        _ = (∫ a, (f a ^ 2 * q a) -
              (2 * t) * (f a * s a * q a) ∂μ) +
              (∫ a, t ^ 2 * (s a ^ 2 * q a) ∂μ) :=
                integral_add (hfint'.sub hcross) hsquare
        _ = ((∫ a, f a ^ 2 * q a ∂μ) -
              (∫ a, (2 * t) * (f a * s a * q a) ∂μ)) +
              (∫ a, t ^ 2 * (s a ^ 2 * q a) ∂μ) := by
                rw [integral_sub hfint' hcross]
        _ = (∫ a, f a ^ 2 * q a ∂μ) -
              (2 * t) * (∫ a, f a * s a * q a ∂μ) +
              t ^ 2 * (∫ a, s a ^ 2 * q a ∂μ) := by
                rw [integral_const_mul, integral_const_mul]
    rw [hexpand] at hnonneg
    nlinarith [hnonneg]
  have hdisc :
      discrim (∫ a, s a ^ 2 * q a ∂μ)
        (-2 * (∫ a, f a * s a * q a ∂μ))
        (∫ a, f a ^ 2 * q a ∂μ) ≤ 0 := by
    apply discrim_le_zero
    intro t
    exact hquad t
  unfold discrim at hdisc
  nlinarith [hdisc]

end Causalean.Stat.Limit.ObservationDependentVanTrees
