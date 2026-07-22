/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.LocalPoly.EstimatorRisk.SquareCompletion
import Causalean.Stat.Nonparametric.LocalPoly.EstimatorRisk.DensityConstants
import Causalean.Stat.Nonparametric.LocalPoly.EstimatorRisk.Factorization
import Causalean.Stat.Nonparametric.LocalPoly.EstimatorRisk.DensityLeverage
import Causalean.Stat.Nonparametric.LocalPoly.EstimatorRisk.EstimatorRisk
import Causalean.Stat.Nonparametric.LocalPoly.EstimatorRisk.Unconditional

/-!
# Local-polynomial estimator risk (conditional MSE → unconditional risk)

Pointwise-risk assembly for local-polynomial estimators, including density constants, leverage
bounds, conditional MSE factorization, and unconditional risk lifts.

This barrel collects the local-polynomial pointwise-risk assembly: square completion of the
conditional bias/variance trade-off, the density-constant and leverage bounds, the conditional
MSE factorization, and the unconditional (bandwidth-optimized) risk bound.
-/
