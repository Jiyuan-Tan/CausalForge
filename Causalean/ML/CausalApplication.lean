/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.CausalApplication.RegressionBridge
import Causalean.ML.CausalApplication.Nuisance
import Causalean.ML.CausalApplication.AIPWExample
import Causalean.ML.CausalApplication.RateAssembly

/-! # `Causalean.ML.CausalApplication` — causal applications of ML learners

This roll-up is the causal-application layer for `Causalean.ML`, kept separate
from the causal-free core. `RegressionBridge` identifies squared-loss population
targets with conditional expectations, `Nuisance` packages those targets as AIPW
outcome-regression and propensity nuisances, `AIPWExample` composes correctly
specified ML nuisances with ATE mean-zero identification, and `RateAssembly`
turns per-method L² rates into the nuisance-rate hypotheses used by DML.
-/
