/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.LocalPoly.Weights
import Causalean.Stat.Nonparametric.LocalPoly.DesignMatrixPosDef
import Causalean.Stat.Nonparametric.LocalPoly.Bias
import Causalean.Stat.Nonparametric.LocalPoly.SmootherVariance
import Causalean.Stat.Nonparametric.LocalPoly.Rate
import Causalean.Stat.Nonparametric.LocalPoly.Rate.IntegralMoment
import Causalean.Stat.Nonparametric.LocalPoly.EstimatorRisk

/-!
# Local-polynomial estimator substrate

Degree-`p` local-polynomial regression substrate: equivalent-kernel weights, design positive
definiteness, bias, variance, leverage rates, and pointwise risk bounds.

This barrel collects the degree-`p` local-polynomial regression substrate:

* `LocalPoly/Weights.lean` — the design moment matrix `designMatrix` and the equivalent-kernel
  weights `equivKernelWeight`.
* `LocalPoly/DesignMatrixPosDef.lean` — the empirical-Gram positive-definiteness lemmas.
* `LocalPoly/Bias.lean` — the interior local-polynomial bias bound.
* `LocalPoly/SmootherVariance.lean` — the local-polynomial specialization of the spherical
  smoother variance bound (`localPoly_intercept_variance_le`).
* `LocalPoly/Rate.lean` (+ `Rate/Conjugation.lean`, `Rate/IntegralMoment.lean`) — the
  design-inverse concentration conjugation and the bias/variance rate assembly.
* `LocalPoly/EstimatorRisk.lean` — the conditional → unconditional pointwise-risk assembly.
-/
