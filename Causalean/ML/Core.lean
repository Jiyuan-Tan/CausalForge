/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Core.Losses
import Causalean.ML.Core.Hypothesis
import Causalean.ML.Core.Risk
import Causalean.ML.Core.ERM
import Causalean.ML.Core.Bridge
import Causalean.ML.Core.Convex
import Causalean.ML.Core.PopulationTarget
import Causalean.ML.Core.Rate

/-! # `Causalean.ML.Core` — the standalone learning spine

Roll-up of the causal-free machine-learning spine: losses, parametrized
predictors and extensional hypothesis classes, empirical/population risk, the
ERM-minimizer predicates, the parametric↔extensional bridge, the convex-analysis
substrate, and the population-target interface.  Concrete methods (linear, ridge,
lasso, logistic, kernel, neural nets, forests) instantiate these in sibling
directories.
-/
