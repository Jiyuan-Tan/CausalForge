/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.DesignBased.Estimators.DifferenceInMeans

/-!
# Design-based estimators

Entry point for paper-agnostic estimators of finite-population causal estimands and their
randomization properties.

This module currently re-exports `Estimators.DifferenceInMeans`, which defines the sample average
treatment effect `sateEstimand`, the arm means `treatedMean` and `controlMean`, the estimator
`diffInMeans`, and the complete-randomization unbiasedness theorem `E_diffInMeans_eq_sate`.
-/
