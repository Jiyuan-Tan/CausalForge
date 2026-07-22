/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.Approximation.HolderTaylor
import Causalean.Stat.Nonparametric.Approximation.HolderTaylorMonomial
import Causalean.Stat.Nonparametric.Approximation.Kernel
import Causalean.Stat.Nonparametric.Approximation.HolderInterpolation


/-!
# Approximation substrate (shared deterministic approximation-theory layer)

Deterministic approximation-theory primitives for nonparametric bias analysis, including
Hölder–Taylor remainder bounds and kernel smoothing bias estimates.

This barrel collects the deterministic approximation-theory primitives used on the bias side of
both estimators:

* `Approximation/HolderTaylor.lean` — Hölder-class Taylor remainder bounds.
* `Approximation/HolderTaylorMonomial.lean` — multivariate local monomial approximations.
* `Approximation/Kernel.lean` — kernel moment / smoothing-bias primitives.
-/
