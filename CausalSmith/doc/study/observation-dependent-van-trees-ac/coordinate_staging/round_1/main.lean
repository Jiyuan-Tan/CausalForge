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
