/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.LeastSquares
import Causalean.Stat.Nonparametric.Approximation
import Causalean.Stat.Nonparametric.LocalPoly
import Causalean.Stat.Nonparametric.SeriesSieve
import Causalean.Stat.Nonparametric.HOIF
import Causalean.Stat.Nonparametric.MomentProblems.ResidualQuadratic.MomentAlgebra
import Causalean.Stat.Nonparametric.MomentProblems.ResidualQuadratic.MeasureBridge
import Causalean.Stat.Nonparametric.MomentProblems.ResidualQuadratic.ProjectionResidual
import Causalean.Stat.Nonparametric.MomentProblems.ScoreProgram.ScoreProgram
import Causalean.Stat.Nonparametric.MomentProblems.BoundedOutcomeEnvelope.QuarticRoot
import Causalean.Stat.Nonparametric.MomentProblems.BoundedOutcomeEnvelope.Defs
import Causalean.Stat.Nonparametric.MomentProblems.BoundedOutcomeEnvelope.Bounds
import Causalean.Stat.Nonparametric.MomentProblems.BoundedOutcomeEnvelope.Attainment
import Causalean.Stat.Nonparametric.MomentProblems.BoundedOutcomeEnvelope.Envelope
import Causalean.Stat.Nonparametric.MomentProblems.Cumulant
import Causalean.Stat.Nonparametric.MomentProblems.AtomicLaw
import Causalean.Stat.Nonparametric.MomentProblems.MomentCumulantInversion
import Causalean.Stat.Nonparametric.MomentProblems.SymmetricAtomSolve
import Causalean.Stat.Nonparametric.MomentProblems.TruncatedCumulantInterior

/-!
# Nonparametric methods

Top barrel for reusable nonparametric statistical methods: approximation theory, weighted least
squares, local-polynomial and series/sieve estimators, and higher-order influence-function tools.
Organized into the following reusable layers:

* `Concentration` — empirical design-matrix-inverse concentration (scalar i.i.d. sums → resolvent
  perturbation → union bound → `designMatrix_inv_concentration`).
* `LeastSquares` — design-agnostic weighted-least-squares primitives (normal equations, smoother
  bias, generic spherical smoother variance), shared by local-polynomial and series/sieve.
* `Approximation` — deterministic approximation-theory bias primitives (Hölder–Taylor, kernel).
* `LocalPoly` — the degree-`p` local-polynomial estimator substrate (weights, design positive
  definiteness, bias, variance, rate, estimator risk).
* `SeriesSieve` — the series/sieve `L²` approximation-and-prediction substrate.
* `HOIF` — higher-order influence-function machinery.
* `MomentProblems` — raw-moment algebra, L² projection residuals, constrained score programs,
  sharp bounded-outcome residual envelopes, cumulant coordinates, finite atomic witness laws, the
  triangular moment↔cumulant inversion, and the nonempty interior of the truncated cumulant range.
-/
