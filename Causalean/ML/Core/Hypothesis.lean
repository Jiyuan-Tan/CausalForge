/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

/-! # Hypothesis classes and parametrized predictors

The standalone ML spine carries two views of a learning method, connected later
by `Causalean.ML.Core.Bridge`:

* the **parametric** view (`Predictor`): a parameter type `Θ` together with an
  admissible set and a prediction map `Θ → X → Y`.  Optimization, convexity and
  regularization live here.
* the **extensional** view (`HypothesisClass`): a set of measurable functions
  `X → Y`.  Population-risk targets and best-in-class statements live here.

`FeatureMap` packages a feature transform `X → (K → ℝ)` so that linear-in-features
regression (and hence series/sieve regression) is a single object.
-/

namespace Causalean.ML

/-- A parametrized family of predictors bundles [an admissible set of parameter
values](hyp:paramSet) together with [a map sending each parameter to a prediction function from
the covariates to the outcome](hyp:predict). -/
structure Predictor (Θ X Y : Type*) where
  /-- The admissible parameter set (e.g. a norm ball, or all of `Θ`). -/
  paramSet : Set Θ
  /-- The prediction map: a parameter yields a function `X → Y`. -/
  predict : Θ → X → Y

/-- A hypothesis class packaged extensionally as [a set of admissible prediction functions from
the covariates to the outcome](hyp:carrier), subject to the requirement that [every function
admitted to the class is measurable](hyp:measurable). -/
structure HypothesisClass (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] where
  /-- The set of admissible prediction functions. -/
  carrier : Set (X → Y)
  /-- Every admissible function is measurable. -/
  measurable : ∀ ⦃h : X → Y⦄, h ∈ carrier → Measurable h

/-- A finite feature map bundles [a transform sending each input to its vector of `K`
feature values](hyp:φ). Linear-in-features predictors use `x ↦ ⟪β, φ x⟫`; the identity feature map
recovers ordinary linear regression, and other choices of the transform recover polynomial,
spline, or Fourier (sieve) regression. -/
structure FeatureMap (X : Type*) (K : Type*) [Fintype K] where
  /-- The feature transform sending an input to its vector of feature values. -/
  φ : X → (K → ℝ)

end Causalean.ML
