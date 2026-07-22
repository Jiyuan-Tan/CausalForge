/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Coupling.ProductLossMonotoneCoupling.PIT
import Causalean.Stat.Coupling.ProductLossMonotoneCoupling.Coupling
import Causalean.Stat.Coupling.ProductLossMonotoneCoupling.FrechetHoeffding
import Causalean.Stat.Coupling.ProductLossMonotoneCoupling.FrechetHoeffdingAttainment
import Causalean.Stat.Coupling.ProductLossMonotoneCoupling.TailIntegral
import Causalean.Stat.Coupling.ProductLossMonotoneCoupling.Survival
import Causalean.Stat.Coupling.ProductLossMonotoneCoupling.HoeffdingFubini
import Causalean.Stat.Coupling.ProductLossMonotoneCoupling.HoeffdingFubiniIntegrability
import Causalean.Stat.Coupling.ProductLossMonotoneCoupling.Hoeffding
import Causalean.Stat.Coupling.ProductLossMonotoneCoupling.Optimality

/-!
# Product-loss monotone couplings

This module collects the coupling construction and optimality theorem showing
that, among all couplings of two real probability measures with finite second
moments, the product expectation is largest at the comonotone quantile coupling
and smallest at the countermonotone quantile coupling.

The leaf files provide the probability integral transform for the quantile,
explicit monotone couplings, sharp Fréchet-Hoeffding cdf bounds, Hoeffding's
covariance identity, and the product-expectation optimality capstone.
-/
