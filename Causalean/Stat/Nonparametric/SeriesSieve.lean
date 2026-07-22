/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.SeriesSieve.Jackson
import Causalean.Stat.Nonparametric.SeriesSieve.Prediction

/-!
# Series / sieve `L²` substrate

This barrel collects reusable series/sieve approximation and least-squares prediction tools for
nonparametric regression and projection arguments.

* `SeriesSieve/Jackson.lean` — a **from-scratch Jackson theorem** for the one-dimensional
  piecewise-Taylor sieve: `sup |f − g| ≤ C·J^{−β}` on an `(β, M)`-Hölder window
  (`piecewiseTaylor_sup_approx`, `piecewiseTaylor_sup_approx_rate`). This is the `d = 1` instance of
  the best `J`-term approximation rate `J^{−s/d}`.
* `SeriesSieve/Prediction.lean` — the **least-squares prediction rate** `O(J^{−s/d} + √(J/N))`:
  the empirical approximation reduction (`seriesApprox_le_of_sup`), the exact Pythagorean
  decomposition of the prediction error (`seriesLS_prediction_decomp`), the spherical
  stochastic-term expectation (`expected_weighted_sq_image_spherical`), and the assembled rate
  (`seriesLS_expected_prediction_le`).

Built on the shared least-squares normal-equation / projection-optimality layer
(`LeastSquares/NormalEquations.lean`) and the Gauss–Markov spherical-variance layer.
-/
