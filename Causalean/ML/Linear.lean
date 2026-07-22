/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Linear.Finite
import Causalean.ML.Linear.ClosedForm
import Causalean.ML.Linear.Population
import Causalean.ML.Ridge.Finite
import Causalean.ML.Ridge.ClosedForm
import Causalean.ML.Ridge.Population

/-! # `Causalean.ML.Linear` — linear least squares and ridge

Roll-up of the linear-in-features regression family: ordinary least squares and
ridge, including finite-sample optimization, closed-form normal-equation
solutions, and population-risk target results. The `FeatureMap` layer makes
polynomial, spline, and Fourier sieve regressions instances of the same
theorems, while the finite OLS files expose the bridge from `empiricalRisk` to
design-matrix objectives.
-/
