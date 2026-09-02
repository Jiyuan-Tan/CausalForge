/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Limit.ObservationDependentVanTrees.IntegrationByParts
import Causalean.Stat.Limit.ObservationDependentVanTrees.GuardedInformation
import Causalean.Stat.Limit.ObservationDependentVanTrees.WeightedL2

/-!
# Observation-dependent van Trees inequality

This module proves a paper-independent Bayesian Cramér--Rao inequality for a
sigma-finite dominated observation model. Unlike the classical parameter-only
form, the target may depend on both the parameter and the observation. It
assembles the guarded-score, absolute-continuity, product-measure, and weighted
L² ingredients from the accompanying modules.
-/

open MeasureTheory Set

namespace Causalean.Stat.Limit.ObservationDependentVanTrees

/-- A nondegenerate parameter interval with a [continuously differentiable, compactly supported, normalized nonnegative prior; a normalized nonnegative dominated likelihood; the stated differentiation-under-the-integral, sectionwise absolute-continuity, derivative, boundary, product-measurability, and integrability conditions; and strictly positive finite total information](hyp:hellu,hwC1,hwsupport,hwderiv,hwnonneg,hwnorm,hpnonneg,hpnorm,hpint,hdpint,hdiffUnder,hpAC,hgAC,hdp,hdg,hboundary,hbalanceSm,hbalanceInt,herrorScoreSm,herrorScoreInt,hsensitivitySm,hsensitivityInt,herrorSqSm,herrorSqInt,hscoreSqSm,hscoreSqInt,hpriorSqSm,hpriorSqInt,hpriorJointSqSm,hpriorJointSqInt,hfisherSqSm,hfisherSqInt,hcrossSm,hcrossInt,hinfoPos) ensures that [Bayes mean-squared error for an estimator of an observation-dependent target is at least the squared joint mean of the target's parameter derivative divided by prior information plus average Fisher information](goal). -/
theorem observation_dependent_van_trees
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {ell u : ℝ} (hellu : ell < u)
    (w dw : ℝ → ℝ) (p dp g dg : ℝ → X → ℝ) (T : X → ℝ)
    -- Compactly supported C1 prior density and derivative representative.
    (hwC1 : ContDiff ℝ 1 w)
    (hwsupport : Function.support w ⊆ Icc ell u)
    (hwderiv : ∀ θ, HasDerivAt w (dw θ) θ)
    (hwnonneg : ∀ θ, 0 ≤ w θ)
    (hwnorm : ∫ θ, w θ ∂parameterMeasure ell u = 1)
    -- Dominated likelihood density and normalization.
    (hpnonneg : ∀ θ x, 0 ≤ p θ x)
    (hpnorm : ∀ θ ∈ Icc ell u, ∫ x, p θ x ∂μ = 1)
    (hpint : ∀ θ ∈ Icc ell u, Integrable (fun x => p θ x) μ)
    (hdpint : ∀ θ ∈ Icc ell u, Integrable (fun x => dp θ x) μ)
    (hdiffUnder : ∀ θ ∈ Ioo ell u,
      HasDerivAt (fun t => ∫ x, p t x ∂μ) (∫ x, dp θ x ∂μ) θ)
    -- Absolute continuity of observation sections and joint-a.e. derivative representatives.
    (hpAC : ∀ᵐ x ∂μ, AbsolutelyContinuousOnInterval (fun θ => p θ x) ell u)
    (hgAC : ∀ᵐ x ∂μ, AbsolutelyContinuousOnInterval (fun θ => g θ x) ell u)
    (hdp : ∀ᵐ z ∂((parameterMeasure ell u).prod μ),
      HasDerivAt (fun t => p t z.2) (dp z.1 z.2) z.1)
    (hdg : ∀ᵐ z ∂((parameterMeasure ell u).prod μ),
      HasDerivAt (fun t => g t z.2) (dg z.1 z.2) z.1)
    -- Boundary product required by integration by parts.
    (hboundary : ∀ᵐ x ∂μ,
      w u * p u x * (T x - g u x) = 0 ∧
        w ell * p ell x * (T x - g ell x) = 0)
    -- Explicit product-measure measurability and integrability of signed fields.
    (hbalanceSm : AEStronglyMeasurable (derivativeBalanceField w dw p dp g dg T)
      ((parameterMeasure ell u).prod μ))
    (hbalanceInt : Integrable (derivativeBalanceField w dw p dp g dg T)
      ((parameterMeasure ell u).prod μ))
    (herrorScoreSm : AEStronglyMeasurable (errorScoreField w dw p dp g T)
      ((parameterMeasure ell u).prod μ))
    (herrorScoreInt : Integrable (errorScoreField w dw p dp g T)
      ((parameterMeasure ell u).prod μ))
    (hsensitivitySm : AEStronglyMeasurable (sensitivityField w p dg)
      ((parameterMeasure ell u).prod μ))
    (hsensitivityInt : Integrable (sensitivityField w p dg)
      ((parameterMeasure ell u).prod μ))
    -- Explicit product-measure weighted-square and cross-integrability hypotheses.
    (herrorSqSm : AEStronglyMeasurable (errorSqField w p g T)
      ((parameterMeasure ell u).prod μ))
    (herrorSqInt : Integrable (errorSqField w p g T)
      ((parameterMeasure ell u).prod μ))
    (hscoreSqSm : AEStronglyMeasurable (scoreSqField w dw p dp)
      ((parameterMeasure ell u).prod μ))
    (hscoreSqInt : Integrable (scoreSqField w dw p dp)
      ((parameterMeasure ell u).prod μ))
    (hpriorSqSm : AEStronglyMeasurable (fun θ => w θ * (priorScore w dw θ) ^ 2)
      (parameterMeasure ell u))
    (hpriorSqInt : Integrable (fun θ => w θ * (priorScore w dw θ) ^ 2)
      (parameterMeasure ell u))
    (hpriorJointSqSm : AEStronglyMeasurable
      (fun z : ℝ × X => w z.1 * p z.1 z.2 * (priorScore w dw z.1) ^ 2)
      ((parameterMeasure ell u).prod μ))
    (hpriorJointSqInt : Integrable
      (fun z : ℝ × X => w z.1 * p z.1 z.2 * (priorScore w dw z.1) ^ 2)
      ((parameterMeasure ell u).prod μ))
    (hfisherSqSm : AEStronglyMeasurable
      (fun z : ℝ × X =>
        w z.1 * p z.1 z.2 * (likelihoodScore p dp z.1 z.2) ^ 2)
      ((parameterMeasure ell u).prod μ))
    (hfisherSqInt : Integrable
      (fun z : ℝ × X =>
        w z.1 * p z.1 z.2 * (likelihoodScore p dp z.1 z.2) ^ 2)
      ((parameterMeasure ell u).prod μ))
    (hcrossSm : AEStronglyMeasurable
      (fun z : ℝ × X =>
        w z.1 * p z.1 z.2 * (priorScore w dw z.1 * likelihoodScore p dp z.1 z.2))
      ((parameterMeasure ell u).prod μ))
    (hcrossInt : Integrable
      (fun z : ℝ × X =>
        w z.1 * p z.1 z.2 * (priorScore w dw z.1 * likelihoodScore p dp z.1 z.2))
      ((parameterMeasure ell u).prod μ))
    -- Positive finite total prior-plus-Fisher information.
    (hinfoPos : 0 < priorInformation ell u w dw +
      ∫ θ, w θ * fisherInformation μ p dp θ ∂parameterMeasure ell u) :
    (∫ z, sensitivityField w p dg z ∂((parameterMeasure ell u).prod μ)) ^ 2 /
        (priorInformation ell u w dw +
          ∫ θ, w θ * fisherInformation μ p dp θ ∂parameterMeasure ell u) ≤
      ∫ z, errorSqField w p g T z ∂((parameterMeasure ell u).prod μ) := by
  -- Proof roadmap for the filler:
  -- 1. Obtain absolute continuity of `w` from `hwC1`, and obtain derivative-zero
  --    facts for `w` and (joint-a.e.) `p` from global nonnegativity.
  -- 2. Transport `hdp` and `hdg` across `Measure.measurePreserving_swap`, then use
  --    `ae_ae_of_ae_prod` to feed observation-first sections to
  --    `product_integral_derivativeBalance_eq_zero`.
  -- 3. Expand `errorScoreField` with `errorScoreField_eq_numerator`; the zero
  --    derivative-balance integral identifies its integral with sensitivity.
  -- 4. Exclude the two endpoints almost everywhere under `parameterMeasure`,
  --    derive likelihood-score centering, and invoke
  --    `joint_score_information_decomposition`.
  -- 5. Apply `weighted_integral_mul_sq_le` on the product measure with weight
  --    `jointDensity`, error `T - g`, and score `jointScore`, then divide by the
  --    strictly positive information denominator.
  letI : IsFiniteMeasure (parameterMeasure ell u) := by
    unfold parameterMeasure
    infer_instance
  have hwAC : AbsolutelyContinuousOnInterval w ell u :=
    hwC1.contDiffOn.absolutelyContinuousOnInterval
  have hdw : ∀ᵐ θ ∂parameterMeasure ell u, HasDerivAt w (dw θ) θ := by
    filter_upwards with θ
    exact hwderiv θ
  have hwzero : ∀ θ, w θ = 0 → dw θ = 0 := by
    intro θ hzero
    exact derivative_eq_zero_of_nonnegative_of_eq_zero hwnonneg (hwderiv θ) hzero
  have hpzero : ∀ᵐ z ∂((parameterMeasure ell u).prod μ),
      p z.1 z.2 = 0 → dp z.1 z.2 = 0 := by
    filter_upwards [hdp] with z hdpz
    intro hzero
    exact derivative_eq_zero_of_nonnegative_of_eq_zero
      (fun t => hpnonneg t z.2) hdpz hzero
  have hdpSwap : ∀ᵐ z ∂(μ.prod (parameterMeasure ell u)),
      HasDerivAt (fun t => p t z.1) (dp z.2 z.1) z.2 := by
    have h := Measure.measurePreserving_swap.quasiMeasurePreserving.tendsto_ae.eventually hdp
    simpa [Prod.swap] using h
  have hdgSwap : ∀ᵐ z ∂(μ.prod (parameterMeasure ell u)),
      HasDerivAt (fun t => g t z.1) (dg z.2 z.1) z.2 := by
    have h := Measure.measurePreserving_swap.quasiMeasurePreserving.tendsto_ae.eventually hdg
    simpa [Prod.swap] using h
  have hdpSections : ∀ᵐ x ∂μ, ∀ᵐ θ ∂parameterMeasure ell u,
      HasDerivAt (fun t => p t x) (dp θ x) θ := by
    simpa using Measure.ae_ae_of_ae_prod hdpSwap
  have hdgSections : ∀ᵐ x ∂μ, ∀ᵐ θ ∂parameterMeasure ell u,
      HasDerivAt (fun t => g t x) (dg θ x) θ := by
    simpa using Measure.ae_ae_of_ae_prod hdgSwap
  have hbalanceZero :
      ∫ z, derivativeBalanceField w dw p dp g dg T z
          ∂((parameterMeasure ell u).prod μ) = 0 :=
    product_integral_derivativeBalance_eq_zero hellu.le hwAC hpAC hgAC hdw
      hdpSections hdgSections hboundary hbalanceSm hbalanceInt
  have herrorSensitivity :
      (∫ z, errorScoreField w dw p dp g T z ∂((parameterMeasure ell u).prod μ)) =
        ∫ z, sensitivityField w p dg z ∂((parameterMeasure ell u).prod μ) := by
    have hbalanceRewrite :
        (∫ z, derivativeBalanceField w dw p dp g dg T z
            ∂((parameterMeasure ell u).prod μ)) =
          (∫ z, errorScoreField w dw p dp g T z
            ∂((parameterMeasure ell u).prod μ)) -
          ∫ z, sensitivityField w p dg z ∂((parameterMeasure ell u).prod μ) := by
      calc
        _ = ∫ z, errorScoreField w dw p dp g T z - sensitivityField w p dg z
              ∂((parameterMeasure ell u).prod μ) := by
            apply integral_congr_ae
            filter_upwards [hpzero] with z hpzeroz
            rw [errorScoreField_eq_numerator (hwnonneg z.1) (hpnonneg z.1 z.2)
              (hwzero z.1) hpzeroz]
            simp only [derivativeBalanceField, sensitivityField, jointDensity]
            ring
        _ = _ := integral_sub herrorScoreInt hsensitivityInt
    rw [hbalanceZero] at hbalanceRewrite
    linarith
  have hmemIcc : ∀ᵐ θ ∂parameterMeasure ell u, θ ∈ Icc ell u := by
    unfold parameterMeasure
    exact ae_restrict_mem measurableSet_Icc
  have hneEll : ∀ᵐ θ ∂parameterMeasure ell u, θ ≠ ell := by
    unfold parameterMeasure
    exact ae_restrict_of_ae (volume.ae_ne ell)
  have hneU : ∀ᵐ θ ∂parameterMeasure ell u, θ ≠ u := by
    unfold parameterMeasure
    exact ae_restrict_of_ae (volume.ae_ne u)
  have hmemIoo : ∀ᵐ θ ∂parameterMeasure ell u, θ ∈ Ioo ell u := by
    filter_upwards [hmemIcc, hneEll, hneU] with θ hθ hθell hθu
    exact ⟨lt_of_le_of_ne hθ.1 (Ne.symm hθell), lt_of_le_of_ne hθ.2 hθu⟩
  have hpzeroSections : ∀ᵐ θ ∂parameterMeasure ell u,
      ∀ᵐ x ∂μ, p θ x = 0 → dp θ x = 0 :=
    Measure.ae_ae_of_ae_prod hpzero
  have hnormAE : ∀ᵐ θ ∂parameterMeasure ell u, ∫ x, p θ x ∂μ = 1 := by
    filter_upwards [hmemIcc] with θ hθ
    exact hpnorm θ hθ
  have hcenter : ∀ᵐ θ ∂parameterMeasure ell u,
      ∫ x, likelihoodScore p dp θ x * p θ x ∂μ = 0 := by
    filter_upwards [hmemIoo, hpzeroSections] with θ hθ hpzeroθ
    exact likelihoodScore_integral_eq_zero_of_normalization hθ hpnorm
      (hdiffUnder θ hθ) (hpnonneg θ) hpzeroθ (hpint θ ⟨hθ.1.le, hθ.2.le⟩)
        (hdpint θ ⟨hθ.1.le, hθ.2.le⟩)
  have hinformation :
      (∫ z, scoreSqField w dw p dp z ∂((parameterMeasure ell u).prod μ)) =
        priorInformation ell u w dw +
          ∫ θ, w θ * fisherInformation μ p dp θ ∂parameterMeasure ell u :=
    joint_score_information_decomposition hwnonneg hpnonneg
      (by filter_upwards with θ; exact hwzero θ) hpzero hnormAE hcenter
      hscoreSqSm hscoreSqInt hpriorSqSm hpriorSqInt hpriorJointSqSm hpriorJointSqInt
      hfisherSqSm hfisherSqInt hcrossSm hcrossInt
  have hcs :
      (∫ z, errorScoreField w dw p dp g T z
          ∂((parameterMeasure ell u).prod μ)) ^ 2 ≤
        (∫ z, errorSqField w p g T z ∂((parameterMeasure ell u).prod μ)) *
          ∫ z, scoreSqField w dw p dp z ∂((parameterMeasure ell u).prod μ) := by
    simpa only [errorScoreField, errorSqField, scoreSqField] using
      (weighted_integral_mul_sq_le
        (μ := (parameterMeasure ell u).prod μ)
        (q := jointDensity w p)
        (f := fun z : ℝ × X => T z.2 - g z.1 z.2)
        (s := jointScore w dw p dp)
        (by filter_upwards with z; exact mul_nonneg (hwnonneg z.1) (hpnonneg z.1 z.2))
        herrorSqSm hscoreSqSm herrorScoreSm herrorSqInt hscoreSqInt herrorScoreInt)
  apply (div_le_iff₀ hinfoPos).2
  rw [← hinformation, ← herrorSensitivity]
  exact hcs

end Causalean.Stat.Limit.ObservationDependentVanTrees

/-!
## Native-real finite-experiment van Trees assembly

This section packages the model-specific regularity fields for a finite dominated
experiment and turns sensitivity and information estimates into a real-valued
Bayes squared-risk lower bound.  Its canonical specialization discharges all
one-dimensional prior bookkeeping using the scaled quartic prior.
-/

open MeasureTheory Set

namespace Causalean.Stat.Limit.ObservationDependentVanTrees

/-- Finite-experiment van Trees regularity collects the model-specific normalization,
absolute-continuity, derivative, measurability, and integrability conditions for a
fixed prior and counting-measure observation model. -/
structure FiniteVanTreesModelRegularity
    (X : Type*) [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (ell u : ℝ) (w dw : ℝ → ℝ) (p dp g dg : ℝ → X → ℝ) (T : X → ℝ) : Prop where
  /-- Every likelihood mass is nonnegative. -/
  hpnonneg : ∀ θ x, 0 ≤ p θ x
  /-- Every likelihood mass function is normalized on the ambient interval. -/
  hpnorm : ∀ θ ∈ Icc ell u, ∫ x, p θ x ∂Measure.count = 1
  /-- Likelihood sections are integrable on the finite carrier. -/
  hpint : ∀ θ ∈ Icc ell u, Integrable (fun x => p θ x) Measure.count
  /-- Likelihood derivative sections are integrable on the finite carrier. -/
  hdpint : ∀ θ ∈ Icc ell u, Integrable (fun x => dp θ x) Measure.count
  /-- Differentiation of the normalized likelihood integral is valid in the interior. -/
  hdiffUnder : ∀ θ ∈ Ioo ell u,
    HasDerivAt (fun t => ∫ x, p t x ∂Measure.count)
      (∫ x, dp θ x ∂Measure.count) θ
  /-- Almost every likelihood section is absolutely continuous in the parameter. -/
  hpAC : ∀ᵐ x ∂Measure.count,
    AbsolutelyContinuousOnInterval (fun θ => p θ x) ell u
  /-- Almost every observation-dependent target section is absolutely continuous. -/
  hgAC : ∀ᵐ x ∂Measure.count,
    AbsolutelyContinuousOnInterval (fun θ => g θ x) ell u
  /-- The supplied likelihood derivative is valid almost everywhere jointly. -/
  hdp : ∀ᵐ z ∂((parameterMeasure ell u).prod Measure.count),
    HasDerivAt (fun t => p t z.2) (dp z.1 z.2) z.1
  /-- The supplied target derivative is valid almost everywhere jointly. -/
  hdg : ∀ᵐ z ∂((parameterMeasure ell u).prod Measure.count),
    HasDerivAt (fun t => g t z.2) (dg z.1 z.2) z.1
  /-- The derivative-balance field is strongly measurable. -/
  hbalanceSm : AEStronglyMeasurable (derivativeBalanceField w dw p dp g dg T)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The derivative-balance field is integrable. -/
  hbalanceInt : Integrable (derivativeBalanceField w dw p dp g dg T)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The error-score field is strongly measurable. -/
  herrorScoreSm : AEStronglyMeasurable (errorScoreField w dw p dp g T)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The error-score field is integrable. -/
  herrorScoreInt : Integrable (errorScoreField w dw p dp g T)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The sensitivity field is strongly measurable. -/
  hsensitivitySm : AEStronglyMeasurable (sensitivityField w p dg)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The sensitivity field is integrable. -/
  hsensitivityInt : Integrable (sensitivityField w p dg)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The weighted squared-error field is strongly measurable. -/
  herrorSqSm : AEStronglyMeasurable (errorSqField w p g T)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The weighted squared-error field is integrable. -/
  herrorSqInt : Integrable (errorSqField w p g T)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The joint squared-score field is strongly measurable. -/
  hscoreSqSm : AEStronglyMeasurable (scoreSqField w dw p dp)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The joint squared-score field is integrable. -/
  hscoreSqInt : Integrable (scoreSqField w dw p dp)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The lifted prior-score square is strongly measurable. -/
  hpriorJointSqSm : AEStronglyMeasurable
    (fun z : ℝ × X => w z.1 * p z.1 z.2 * (priorScore w dw z.1) ^ 2)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The lifted prior-score square is integrable. -/
  hpriorJointSqInt : Integrable
    (fun z : ℝ × X => w z.1 * p z.1 z.2 * (priorScore w dw z.1) ^ 2)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The lifted likelihood-score square is strongly measurable. -/
  hfisherSqSm : AEStronglyMeasurable
    (fun z : ℝ × X => w z.1 * p z.1 z.2 * (likelihoodScore p dp z.1 z.2) ^ 2)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The lifted likelihood-score square is integrable. -/
  hfisherSqInt : Integrable
    (fun z : ℝ × X => w z.1 * p z.1 z.2 * (likelihoodScore p dp z.1 z.2) ^ 2)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The prior-likelihood score cross field is strongly measurable. -/
  hcrossSm : AEStronglyMeasurable
    (fun z : ℝ × X => w z.1 * p z.1 z.2 *
      (priorScore w dw z.1 * likelihoodScore p dp z.1 z.2))
    ((parameterMeasure ell u).prod Measure.count)
  /-- The prior-likelihood score cross field is integrable. -/
  hcrossInt : Integrable
    (fun z : ℝ × X => w z.1 * p z.1 z.2 *
      (priorScore w dw z.1 * likelihoodScore p dp z.1 z.2))
    ((parameterMeasure ell u).prod Measure.count)

/-- A [nondegenerate parameter interval](hyp:hellu), [finite-model regularity]
(hyp:M), [continuous differentiability](hyp:hwC1), [compact support](hyp:hwsupport),
[a valid prior derivative](hyp:hwderiv), [nonnegativity](hyp:hwnonneg),
[normalization](hyp:hwnorm), [vanishing boundary errors](hyp:hboundary),
[measurability](hyp:hpriorSqSm) and [integrability](hyp:hpriorSqInt) of prior
information, a [nonnegative sensitivity bound](hyp:hs_nonneg) that [lies below average
sensitivity](hyp:hsensitivity), [upper bounds on average likelihood
information](hyp:hlike) and [prior information](hyp:hprior), and [positive total
information](hyp:hinfoPos) imply [a native-real Bayes squared-risk lower bound equal to squared
sensitivity divided by the sum of the two information bounds](goal). -/
theorem finite_vanTrees_lower_bound
    {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    {ell u s I P : ℝ} {w dw : ℝ → ℝ} {p dp g dg : ℝ → X → ℝ} {T : X → ℝ}
    (hellu : ell < u) (M : FiniteVanTreesModelRegularity X ell u w dw p dp g dg T)
    (hwC1 : ContDiff ℝ 1 w) (hwsupport : Function.support w ⊆ Icc ell u)
    (hwderiv : ∀ θ, HasDerivAt w (dw θ) θ) (hwnonneg : ∀ θ, 0 ≤ w θ)
    (hwnorm : ∫ θ, w θ ∂parameterMeasure ell u = 1)
    (hboundary : ∀ᵐ x ∂Measure.count,
      w u * p u x * (T x - g u x) = 0 ∧
        w ell * p ell x * (T x - g ell x) = 0)
    (hpriorSqSm : AEStronglyMeasurable
      (fun θ => w θ * (priorScore w dw θ) ^ 2) (parameterMeasure ell u))
    (hpriorSqInt : Integrable
      (fun θ => w θ * (priorScore w dw θ) ^ 2) (parameterMeasure ell u))
    (hs_nonneg : 0 ≤ s)
    (hsensitivity : s ≤ ∫ z, sensitivityField w p dg z
      ∂((parameterMeasure ell u).prod Measure.count))
    (hlike : (∫ θ, w θ * fisherInformation Measure.count p dp θ
      ∂parameterMeasure ell u) ≤ I)
    (hprior : priorInformation ell u w dw ≤ P)
    (hinfoPos : 0 < priorInformation ell u w dw +
      ∫ θ, w θ * fisherInformation Measure.count p dp θ ∂parameterMeasure ell u) :
    s ^ 2 / (I + P) ≤
      ∫ z, errorSqField w p g T z
        ∂((parameterMeasure ell u).prod Measure.count) := by
  have hvanTrees := observation_dependent_van_trees Measure.count hellu
    w dw p dp g dg T hwC1 hwsupport hwderiv hwnonneg hwnorm
    M.hpnonneg M.hpnorm M.hpint M.hdpint M.hdiffUnder M.hpAC M.hgAC M.hdp M.hdg
    hboundary M.hbalanceSm M.hbalanceInt M.herrorScoreSm M.herrorScoreInt
    M.hsensitivitySm M.hsensitivityInt M.herrorSqSm M.herrorSqInt M.hscoreSqSm
    M.hscoreSqInt hpriorSqSm hpriorSqInt M.hpriorJointSqSm M.hpriorJointSqInt
    M.hfisherSqSm M.hfisherSqInt M.hcrossSm M.hcrossInt hinfoPos
  have hs_sq : s ^ 2 ≤
      (∫ z, sensitivityField w p dg z
        ∂((parameterMeasure ell u).prod Measure.count)) ^ 2 := by
    nlinarith
  have hdenom : priorInformation ell u w dw +
        ∫ θ, w θ * fisherInformation Measure.count p dp θ
          ∂parameterMeasure ell u ≤ I + P := by
    linarith
  exact (div_le_div₀ (sq_nonneg _) hs_sq hinfoPos hdenom).trans hvanTrees

/-- A [positive bandwidth](hyp:ha), [strict containment of the left](hyp:hleft) and
[right](hyp:hright) prior-support endpoints, [finite-model regularity](hyp:M), a
[nonnegative sensitivity bound](hyp:hs_nonneg) that [lies below average
sensitivity](hyp:hsensitivity), a [pointwise likelihood-information bound](hyp:hpointwise), and
[positive total information](hyp:hinfoPos) imply [a native-real Bayes squared-risk
lower bound equal to squared sensitivity divided by likelihood information plus forty
over the squared bandwidth](goal). -/
theorem smoothPrior_finite_vanTrees_lower_bound
    {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    {ell u c a s I : ℝ} {p dp g dg : ℝ → X → ℝ} {T : X → ℝ}
    (ha : 0 < a) (hleft : ell < c - a) (hright : c + a < u)
    (M : FiniteVanTreesModelRegularity X ell u (smoothPrior c a)
      (smoothPriorDeriv c a) p dp g dg T)
    (hs_nonneg : 0 ≤ s)
    (hsensitivity : s ≤ ∫ z, sensitivityField (smoothPrior c a) p dg z
      ∂((parameterMeasure ell u).prod Measure.count))
    (hpointwise : ∀ θ, 0 < smoothPrior c a θ →
      fisherInformation Measure.count p dp θ ≤ I)
    (hinfoPos : 0 < priorInformation ell u (smoothPrior c a) (smoothPriorDeriv c a) +
      ∫ θ, smoothPrior c a θ * fisherInformation Measure.count p dp θ
        ∂parameterMeasure ell u) :
    s ^ 2 / (I + 40 / a ^ 2) ≤
      ∫ z, errorSqField (smoothPrior c a) p g T z
        ∂((parameterMeasure ell u).prod Measure.count) := by
  have hellu : ell < u := by linarith
  have hendpoints := smoothPrior_ambient_endpoints ha hleft hright
  have hboundary : ∀ᵐ x ∂Measure.count,
      smoothPrior c a u * p u x * (T x - g u x) = 0 ∧
        smoothPrior c a ell * p ell x * (T x - g ell x) = 0 := by
    filter_upwards with x
    simp [hendpoints.1, hendpoints.2]
  have hweightedInt : Integrable
      (fun θ => smoothPrior c a θ * fisherInformation Measure.count p dp θ)
      (parameterMeasure ell u) := by
    have h := M.hfisherSqInt.integral_prod_left
    convert h using 1
    funext θ
    rw [fisherInformation, ← integral_const_mul]
    congr 1
    funext x
    ring
  have hlike :
      ∫ θ, smoothPrior c a θ * fisherInformation Measure.count p dp θ
        ∂parameterMeasure ell u ≤ I :=
    average_fisherInformation_le (smoothPrior_nonneg ha)
      (integral_smoothPrior_parameterMeasure ha hleft.le hright.le)
      (smoothPrior_integrable_parameterMeasure ha) hweightedInt hpointwise
  exact finite_vanTrees_lower_bound hellu M (smoothPrior_contDiff ha)
    (support_smoothPrior_subset_Icc ha hleft hright) (hasDerivAt_smoothPrior ha)
    (smoothPrior_nonneg ha)
    (integral_smoothPrior_parameterMeasure ha hleft.le hright.le) hboundary
    (smoothPrior_scoreSq_aestronglyMeasurable ha) (smoothPrior_scoreSq_integrable ha)
    hs_nonneg hsensitivity hlike
    (priorInformation_smoothPrior_le ha hleft.le hright.le) hinfoPos

end Causalean.Stat.Limit.ObservationDependentVanTrees
