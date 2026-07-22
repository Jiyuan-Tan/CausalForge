/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.LeastSquares.NormalEquations
import Causalean.Stat.Nonparametric.LeastSquares.SmootherBias
import Causalean.Stat.Nonparametric.LeastSquares.SmootherVariance

/-!
# Least-squares substrate (shared by local-polynomial and series/sieve estimators)

Design-agnostic weighted least-squares primitives for nonparametric estimators: normal equations,
projection optimality, smoother bias, and spherical-error variance.

This barrel collects the design-agnostic weighted-least-squares primitives consumed by both the
local-polynomial and the series/sieve estimators:

* `LeastSquares/NormalEquations.lean` — the weighted normal equations, residual orthogonality, and
  projection-optimality (Pythagorean) identities.
* `LeastSquares/SmootherBias.lean` — the deterministic bias of a fixed-weight linear smoother.
* `LeastSquares/SmootherVariance.lean` — the generic spherical-error variance identity
  `Var[∑ᵢ Sᵢ Yᵢ] = σ²·∑ᵢ Sᵢ²` and its leverage bound.
-/
