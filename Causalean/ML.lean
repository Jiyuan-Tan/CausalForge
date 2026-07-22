/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Core
import Causalean.ML.Linear
import Causalean.ML.Ridge.Rate
import Causalean.ML.Lasso
import Causalean.ML.Binary
import Causalean.ML.Surrogate.GenericERM
import Causalean.ML.Tree
import Causalean.ML.NeuralNet
import Causalean.ML.Kernel
import Causalean.ML.Margin

/-! # `Causalean.ML` — standalone machine-learning library

A causal-free supervised-learning library built on a dual-view spine (parametric
`Predictor` plus extensional `HypothesisClass`, joined by a `Bridge`).  The root
module collects empirical-risk, population-risk, optimization, and rate abstractions
with concrete learners for regression and classification:

* `Linear`  — least squares and ridge regression, including series/sieve learners via
  `FeatureMap`;
* `Ridge.Rate` — a root-n estimation-rate statement for ridge regression;
* `Lasso`   — L¹-regularized least squares, soft-thresholding, and Rademacher-rate results;
* `Binary`  — logistic losses, logistic regression, Fisher consistency, and rates;
* `Surrogate` — generic convex ERM and proper losses;
* `Tree`    — regression trees / random forests;
* `NeuralNet` — feedforward composition class;
* `Kernel`  — RKHS interfaces, kernel ridge regression, representer theorem, and kernel rates;
* `Margin`  — Lipschitz margin-surrogate classification rates for linear classifiers.

The causal application layer lives separately in `Causalean.ML.CausalApplication`; it connects these
causal-free ML targets to AIPW and DML nuisance functions without being imported by this
standalone roll-up.
-/
