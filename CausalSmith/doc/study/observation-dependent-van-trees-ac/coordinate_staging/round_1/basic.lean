/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Basic fields for observation-dependent van Trees bounds

This module defines the restricted parameter measure, guarded prior, likelihood,
and joint scores, and the weighted fields used by the product-measure proof.
The guards make every definition meaningful where a density vanishes.
-/

open MeasureTheory Set

namespace Causalean.Stat.Limit.ObservationDependentVanTrees

/-- The parameter reference measure is Lebesgue measure restricted to the closed parameter interval. -/
noncomputable def parameterMeasure (ell u : ℝ) : Measure ℝ :=
  volume.restrict (Icc ell u)

/-- The joint density is the product of the prior density and the conditional likelihood density. -/
def jointDensity {X : Type*} (w : ℝ → ℝ) (p : ℝ → X → ℝ) (z : ℝ × X) : ℝ :=
  w z.1 * p z.1 z.2

/-- The guarded prior score divides the prior derivative by its positive density and is zero where that density vanishes. -/
noncomputable def priorScore (w dw : ℝ → ℝ) (θ : ℝ) : ℝ :=
  if 0 < w θ then dw θ / w θ else 0

/-- The guarded likelihood score divides the likelihood derivative by its positive density and is zero where that density vanishes. -/
noncomputable def likelihoodScore {X : Type*} (p dp : ℝ → X → ℝ) (θ : ℝ) (x : X) : ℝ :=
  if 0 < p θ x then dp θ x / p θ x else 0

/-- The guarded joint score divides the derivative of the prior--likelihood product by that positive product and is zero elsewhere. -/
noncomputable def jointScore {X : Type*} (w dw : ℝ → ℝ) (p dp : ℝ → X → ℝ)
    (z : ℝ × X) : ℝ :=
  if 0 < jointDensity w p z then
    (dw z.1 * p z.1 z.2 + w z.1 * dp z.1 z.2) / jointDensity w p z
  else 0

/-- The prior Fisher information is the prior-weighted integral of the squared guarded prior score over the parameter interval. -/
noncomputable def priorInformation (ell u : ℝ) (w dw : ℝ → ℝ) : ℝ :=
  ∫ θ, w θ * (priorScore w dw θ) ^ 2 ∂parameterMeasure ell u

/-- The conditional Fisher information is the likelihood-weighted observation integral of the squared guarded likelihood score at one parameter value. -/
noncomputable def fisherInformation {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p dp : ℝ → X → ℝ) (θ : ℝ) : ℝ :=
  ∫ x, p θ x * (likelihoodScore p dp θ x) ^ 2 ∂μ

/-- The signed error--joint-score field is the estimator error times the guarded joint score, weighted by the joint density. -/
noncomputable def errorScoreField {X : Type*} (w dw : ℝ → ℝ) (p dp g : ℝ → X → ℝ)
    (T : X → ℝ) (z : ℝ × X) : ℝ :=
  (T z.2 - g z.1 z.2) * jointScore w dw p dp z * jointDensity w p z

/-- The target-sensitivity field is the target's parameter derivative weighted by the joint density. -/
def sensitivityField {X : Type*} (w : ℝ → ℝ) (p dg : ℝ → X → ℝ)
    (z : ℝ × X) : ℝ :=
  dg z.1 z.2 * jointDensity w p z

/-- The derivative-balance field is the parameter derivative of the joint-density-weighted estimation error. -/
def derivativeBalanceField {X : Type*} (w dw : ℝ → ℝ)
    (p dp g dg : ℝ → X → ℝ) (T : X → ℝ) (z : ℝ × X) : ℝ :=
  (dw z.1 * p z.1 z.2 + w z.1 * dp z.1 z.2) * (T z.2 - g z.1 z.2)
    - jointDensity w p z * dg z.1 z.2

/-- The squared-error field is the squared estimator error weighted by the joint density. -/
def errorSqField {X : Type*} (w : ℝ → ℝ) (p g : ℝ → X → ℝ)
    (T : X → ℝ) (z : ℝ × X) : ℝ :=
  (T z.2 - g z.1 z.2) ^ 2 * jointDensity w p z

/-- The squared-score field is the squared guarded joint score weighted by the joint density. -/
noncomputable def scoreSqField {X : Type*} (w dw : ℝ → ℝ) (p dp : ℝ → X → ℝ)
    (z : ℝ × X) : ℝ :=
  (jointScore w dw p dp z) ^ 2 * jointDensity w p z

end Causalean.Stat.Limit.ObservationDependentVanTrees
