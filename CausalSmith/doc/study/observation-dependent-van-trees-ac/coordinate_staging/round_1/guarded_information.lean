/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Limit.ObservationDependentVanTrees.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Guarded scores, centering, and information decomposition

This module proves the density-zero algebra for guarded scores, derives score
centering from likelihood normalization and differentiation under the integral,
and decomposes the joint score information into prior and Fisher terms.
-/

open MeasureTheory Set

namespace Causalean.Stat.Limit.ObservationDependentVanTrees

/-- A differentiable nonnegative function has zero derivative at any point where [it attains value zero](hyp:hnonneg,hderiv,hzero), so [the supplied derivative is zero](goal). -/
theorem derivative_eq_zero_of_nonnegative_of_eq_zero {f : ℝ → ℝ} {df θ : ℝ}
    (hnonneg : ∀ t, 0 ≤ f t) (hderiv : HasDerivAt f df θ) (hzero : f θ = 0) :
    df = 0 := by
  have hmin : IsLocalMin f θ := by
    filter_upwards with t
    rw [hzero]
    exact hnonneg t
  exact IsLocalMin.hasDerivAt_eq_zero hmin hderiv

/-- A nonnegative density with [a derivative numerator that vanishes whenever the density vanishes](hyp:hq,hzero) has [its guarded score times its density equal to that derivative numerator](goal). -/
theorem guarded_score_mul_density {q dq : ℝ} (hq : 0 ≤ q)
    (hzero : q = 0 → dq = 0) :
    (if 0 < q then dq / q else 0) * q = dq := by
  by_cases hqpos : 0 < q
  · simp [hqpos, ne_of_gt hqpos]
  · have hqzero : q = 0 := le_antisymm (le_of_not_gt hqpos) hq
    simp [hqzero, hzero hqzero]

/-- At a point where [both the prior and likelihood densities are positive](hyp:hw,hp), [the guarded joint score equals the sum of their guarded scores](goal). -/
theorem jointScore_eq_add {X : Type*} {w dw : ℝ → ℝ} {p dp : ℝ → X → ℝ}
    {θ : ℝ} {x : X} (hw : 0 < w θ) (hp : 0 < p θ x) :
    jointScore w dw p dp (θ, x) = priorScore w dw θ + likelihoodScore p dp θ x := by
  simp only [jointScore, jointDensity, priorScore, likelihoodScore,
    hw, hp, mul_pos hw hp, if_true]
  field_simp

/-- For nonnegative prior and likelihood densities whose [derivative numerators vanish on their respective zero-density sets](hyp:hw,hp,hwzero,hpzero), [joint density times guarded joint score equals the product-rule derivative numerator](goal). -/
theorem jointScore_mul_jointDensity {X : Type*} {w dw : ℝ → ℝ}
    {p dp : ℝ → X → ℝ} {θ : ℝ} {x : X}
    (hw : 0 ≤ w θ) (hp : 0 ≤ p θ x)
    (hwzero : w θ = 0 → dw θ = 0) (hpzero : p θ x = 0 → dp θ x = 0) :
    jointScore w dw p dp (θ, x) * jointDensity w p (θ, x) =
      dw θ * p θ x + w θ * dp θ x := by
  apply guarded_score_mul_density (mul_nonneg hw hp)
  intro hzero
  rcases mul_eq_zero.mp hzero with hwz | hpz
  · rw [hwzero hwz, hwz]
    ring
  · rw [hpzero hpz, hpz]
    ring

/-- For nonnegative prior and likelihood densities whose [derivative numerators vanish wherever the corresponding density is zero](hyp:hw,hp,hwzero,hpzero), [the weighted error--score field equals estimation error times the unguarded product-rule numerator](goal). -/
theorem errorScoreField_eq_numerator {X : Type*} {w dw : ℝ → ℝ}
    {p dp g : ℝ → X → ℝ} {T : X → ℝ} {θ : ℝ} {x : X}
    (hw : 0 ≤ w θ) (hp : 0 ≤ p θ x)
    (hwzero : w θ = 0 → dw θ = 0) (hpzero : p θ x = 0 → dp θ x = 0) :
    errorScoreField w dw p dp g T (θ, x) =
      (T x - g θ x) * (dw θ * p θ x + w θ * dp θ x) := by
  have hjoint := jointScore_mul_jointDensity (w := w) (dw := dw) (p := p) (dp := dp)
    (θ := θ) (x := x) hw hp hwzero hpzero
  rw [errorScoreField, mul_assoc, hjoint]

/-- At an interior parameter value, a [normalized likelihood whose integral may be differentiated using the supplied derivative, with nonnegative density, zero-set derivative control, and both fields integrable](hyp:hθ,hnorm,hdiff,hp,hpzero,hpint,hdpint) has [conditional mean-zero guarded likelihood score](goal). -/
theorem likelihoodScore_integral_eq_zero_of_normalization
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {a b θ : ℝ} {p dp : ℝ → X → ℝ}
    (hθ : θ ∈ Ioo a b)
    (hnorm : ∀ t ∈ Icc a b, ∫ x, p t x ∂μ = 1)
    (hdiff : HasDerivAt (fun t => ∫ x, p t x ∂μ) (∫ x, dp θ x ∂μ) θ)
    (hp : ∀ x, 0 ≤ p θ x)
    (hpzero : ∀ᵐ x ∂μ, p θ x = 0 → dp θ x = 0)
    (hpint : Integrable (fun x => p θ x) μ)
    (hdpint : Integrable (fun x => dp θ x) μ) :
    ∫ x, likelihoodScore p dp θ x * p θ x ∂μ = 0 := by
  have hnorm_nhds : (fun t => ∫ x, p t x ∂μ) =ᶠ[nhds θ] fun _ => 1 := by
    filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with t ht
    exact hnorm t ⟨ht.1.le, ht.2.le⟩
  have hderiv_zero : (∫ x, dp θ x ∂μ) = 0 := by
    apply hdiff.unique
    exact (hasDerivAt_const θ 1).congr_of_eventuallyEq hnorm_nhds
  have hscore_mul :
      (fun x => likelihoodScore p dp θ x * p θ x) =ᵐ[μ] fun x => dp θ x := by
    filter_upwards [hpzero] with x hx
    exact guarded_score_mul_density (hp x) hx
  rw [integral_congr_ae hscore_mul, hderiv_zero]

/-- For nonnegative prior and likelihood densities with [zero-set derivative control, likelihood normalization, centered conditional scores, and the stated measurable integrability of all square and cross fields](hyp:hw,hp,hwzero,hpzero,hnorm,hcenter,hscoreSm,hscoreInt,hpriorSm,hpriorInt,hpriorJointSm,hpriorJointInt,hfisherSm,hfisherInt,hcrossSm,hcrossInt), [joint-score information equals prior information plus average conditional Fisher information](goal). -/
theorem joint_score_information_decomposition
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]
    {a b : ℝ} {w dw : ℝ → ℝ} {p dp : ℝ → X → ℝ}
    (hw : ∀ θ, 0 ≤ w θ) (hp : ∀ θ x, 0 ≤ p θ x)
    (hwzero : ∀ᵐ θ ∂parameterMeasure a b, w θ = 0 → dw θ = 0)
    (hpzero : ∀ᵐ z ∂((parameterMeasure a b).prod μ), p z.1 z.2 = 0 → dp z.1 z.2 = 0)
    (hnorm : ∀ᵐ θ ∂parameterMeasure a b, ∫ x, p θ x ∂μ = 1)
    (hcenter : ∀ᵐ θ ∂parameterMeasure a b,
      ∫ x, likelihoodScore p dp θ x * p θ x ∂μ = 0)
    (hscoreSm : AEStronglyMeasurable (scoreSqField w dw p dp)
      ((parameterMeasure a b).prod μ))
    (hscoreInt : Integrable (scoreSqField w dw p dp)
      ((parameterMeasure a b).prod μ))
    (hpriorSm : AEStronglyMeasurable (fun θ => w θ * (priorScore w dw θ) ^ 2)
      (parameterMeasure a b))
    (hpriorInt : Integrable (fun θ => w θ * (priorScore w dw θ) ^ 2)
      (parameterMeasure a b))
    (hpriorJointSm : AEStronglyMeasurable
      (fun z : ℝ × X => w z.1 * p z.1 z.2 * (priorScore w dw z.1) ^ 2)
      ((parameterMeasure a b).prod μ))
    (hpriorJointInt : Integrable
      (fun z : ℝ × X => w z.1 * p z.1 z.2 * (priorScore w dw z.1) ^ 2)
      ((parameterMeasure a b).prod μ))
    (hfisherSm : AEStronglyMeasurable
      (fun z : ℝ × X => w z.1 * p z.1 z.2 * (likelihoodScore p dp z.1 z.2) ^ 2)
      ((parameterMeasure a b).prod μ))
    (hfisherInt : Integrable
      (fun z : ℝ × X => w z.1 * p z.1 z.2 * (likelihoodScore p dp z.1 z.2) ^ 2)
      ((parameterMeasure a b).prod μ))
    (hcrossSm : AEStronglyMeasurable
      (fun z : ℝ × X =>
        w z.1 * p z.1 z.2 * (priorScore w dw z.1 * likelihoodScore p dp z.1 z.2))
      ((parameterMeasure a b).prod μ))
    (hcrossInt : Integrable
      (fun z : ℝ × X =>
        w z.1 * p z.1 z.2 * (priorScore w dw z.1 * likelihoodScore p dp z.1 z.2))
      ((parameterMeasure a b).prod μ)) :
    ∫ z, scoreSqField w dw p dp z ∂((parameterMeasure a b).prod μ) =
      priorInformation a b w dw +
        ∫ θ, w θ * fisherInformation μ p dp θ ∂parameterMeasure a b := by
  letI : IsFiniteMeasure (parameterMeasure a b) := by
    unfold parameterMeasure
    infer_instance
  have hscore_expand (θ : ℝ) (x : X) :
      scoreSqField w dw p dp (θ, x) =
        w θ * p θ x * (priorScore w dw θ) ^ 2 +
          (w θ * p θ x * (likelihoodScore p dp θ x) ^ 2 +
            2 * (w θ * p θ x *
              (priorScore w dw θ * likelihoodScore p dp θ x))) := by
    by_cases hwpos : 0 < w θ
    · by_cases hppos : 0 < p θ x
      · simp only [scoreSqField, jointScore, jointDensity, priorScore, likelihoodScore,
          hwpos, hppos, mul_pos, if_true]
        field_simp
        ring
      · have hpz : p θ x = 0 := le_antisymm (le_of_not_gt hppos) (hp θ x)
        simp [scoreSqField, jointScore, jointDensity, hpz]
    · have hwz : w θ = 0 := le_antisymm (le_of_not_gt hwpos) (hw θ)
      simp [scoreSqField, jointScore, jointDensity, hwz]
  have hsplit :
      (∫ z, scoreSqField w dw p dp z ∂((parameterMeasure a b).prod μ)) =
        (∫ z : ℝ × X,
          w z.1 * p z.1 z.2 * (priorScore w dw z.1) ^ 2
            ∂((parameterMeasure a b).prod μ)) +
        (∫ z : ℝ × X,
          w z.1 * p z.1 z.2 * (likelihoodScore p dp z.1 z.2) ^ 2
            ∂((parameterMeasure a b).prod μ)) +
        2 * (∫ z : ℝ × X,
          w z.1 * p z.1 z.2 *
            (priorScore w dw z.1 * likelihoodScore p dp z.1 z.2)
              ∂((parameterMeasure a b).prod μ)) := by
    calc
      _ = ∫ z : ℝ × X,
          (w z.1 * p z.1 z.2 * (priorScore w dw z.1) ^ 2) +
            ((w z.1 * p z.1 z.2 * (likelihoodScore p dp z.1 z.2) ^ 2) +
              2 * (w z.1 * p z.1 z.2 *
                (priorScore w dw z.1 * likelihoodScore p dp z.1 z.2)))
            ∂((parameterMeasure a b).prod μ) := by
              apply integral_congr_ae
              filter_upwards with z
              exact hscore_expand z.1 z.2
      _ = (∫ z : ℝ × X,
            w z.1 * p z.1 z.2 * (priorScore w dw z.1) ^ 2
              ∂((parameterMeasure a b).prod μ)) +
          ∫ z : ℝ × X,
            (w z.1 * p z.1 z.2 * (likelihoodScore p dp z.1 z.2) ^ 2) +
              2 * (w z.1 * p z.1 z.2 *
                (priorScore w dw z.1 * likelihoodScore p dp z.1 z.2))
              ∂((parameterMeasure a b).prod μ) :=
        integral_add hpriorJointInt (hfisherInt.add (hcrossInt.const_mul 2))
      _ = _ := by
        rw [integral_add hfisherInt (hcrossInt.const_mul 2), integral_const_mul]
        ring
  have hprior_eval :
      (∫ z : ℝ × X,
          w z.1 * p z.1 z.2 * (priorScore w dw z.1) ^ 2
            ∂((parameterMeasure a b).prod μ)) = priorInformation a b w dw := by
    rw [integral_prod _ hpriorJointInt]
    unfold priorInformation
    apply integral_congr_ae
    filter_upwards [hnorm] with θ hnormθ
    calc
      (∫ x, w θ * p θ x * (priorScore w dw θ) ^ 2 ∂μ) =
          ∫ x, (w θ * (priorScore w dw θ) ^ 2) * p θ x ∂μ := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = (w θ * (priorScore w dw θ) ^ 2) * ∫ x, p θ x ∂μ :=
        integral_const_mul (w θ * (priorScore w dw θ) ^ 2) (fun x => p θ x)
      _ = w θ * (priorScore w dw θ) ^ 2 := by rw [hnormθ]; ring
  have hfisher_eval :
      (∫ z : ℝ × X,
          w z.1 * p z.1 z.2 * (likelihoodScore p dp z.1 z.2) ^ 2
            ∂((parameterMeasure a b).prod μ)) =
        ∫ θ, w θ * fisherInformation μ p dp θ ∂parameterMeasure a b := by
    rw [integral_prod _ hfisherInt]
    apply integral_congr_ae
    filter_upwards with θ
    unfold fisherInformation
    calc
      (∫ x, w θ * p θ x * (likelihoodScore p dp θ x) ^ 2 ∂μ) =
          ∫ x, w θ * (p θ x * (likelihoodScore p dp θ x) ^ 2) ∂μ := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = w θ * ∫ x, p θ x * (likelihoodScore p dp θ x) ^ 2 ∂μ :=
        integral_const_mul (w θ) (fun x => p θ x * (likelihoodScore p dp θ x) ^ 2)
  have hcross_eval :
      (∫ z : ℝ × X,
          w z.1 * p z.1 z.2 *
            (priorScore w dw z.1 * likelihoodScore p dp z.1 z.2)
              ∂((parameterMeasure a b).prod μ)) = 0 := by
    rw [integral_prod _ hcrossInt]
    have hinner : ∀ᵐ θ ∂parameterMeasure a b,
        (∫ x, w θ * p θ x *
          (priorScore w dw θ * likelihoodScore p dp θ x) ∂μ) = 0 := by
      filter_upwards [hcenter] with θ hcenterθ
      calc
        (∫ x, w θ * p θ x *
            (priorScore w dw θ * likelihoodScore p dp θ x) ∂μ) =
            ∫ x, (w θ * priorScore w dw θ) *
              (likelihoodScore p dp θ x * p θ x) ∂μ := by
                apply integral_congr_ae
                filter_upwards with x
                ring
        _ = (w θ * priorScore w dw θ) *
            ∫ x, likelihoodScore p dp θ x * p θ x ∂μ :=
              integral_const_mul (w θ * priorScore w dw θ)
                (fun x => likelihoodScore p dp θ x * p θ x)
        _ = 0 := by rw [hcenterθ, mul_zero]
    calc
      (∫ θ, ∫ x, w θ * p θ x *
          (priorScore w dw θ * likelihoodScore p dp θ x) ∂μ
          ∂parameterMeasure a b) = ∫ _θ : ℝ, 0 ∂parameterMeasure a b :=
            integral_congr_ae hinner
      _ = 0 := by simp
  rw [hsplit, hprior_eval, hfisher_eval, hcross_eval]
  ring

end Causalean.Stat.Limit.ObservationDependentVanTrees
