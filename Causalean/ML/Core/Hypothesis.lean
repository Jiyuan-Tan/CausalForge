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

/-- A parametrized family of predictors: an admissible parameter set `paramSet`
together with a prediction map sending a parameter to a function `X → Y`. -/
structure Predictor (Θ X Y : Type*) where
  /-- The admissible parameter set (e.g. a norm ball, or all of `Θ`). -/
  paramSet : Set Θ
  /-- The prediction map: a parameter yields a function `X → Y`. -/
  predict : Θ → X → Y

/-- A hypothesis class as an extensional set of measurable functions `X → Y`. -/
structure HypothesisClass (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] where
  /-- The set of admissible prediction functions. -/
  carrier : Set (X → Y)
  /-- Every admissible function is measurable. -/
  measurable : ∀ ⦃h : X → Y⦄, h ∈ carrier → Measurable h

/-- A finite feature map `φ : X → (K → ℝ)`, where `K` indexes the (finitely many)
features.  Linear-in-features predictors use `x ↦ ⟪β, φ x⟫`; the identity feature
map recovers ordinary linear regression and other choices of `φ` recover
polynomial / spline / Fourier (sieve) regression. -/
structure FeatureMap (X : Type*) (K : Type*) [Fintype K] where
  /-- The feature transform sending an input to its vector of feature values. -/
  φ : X → (K → ℝ)

end Causalean.ML
