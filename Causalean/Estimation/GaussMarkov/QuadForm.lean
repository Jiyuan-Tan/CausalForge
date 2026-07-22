/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Finite variance quadratic form for linear estimators

Foundational layer for the finite Gauss-Markov / BLUE theory.

Given a finite family of observations with covariance matrix `S : Matrix Obs Obs ℝ`
(written `Σ` in the prose), a *linear estimator* with weight vector `w : Obs → ℝ`
evaluates to `∑ i, w i * Yᵢ`.  Its variance is the quadratic form `wᵀ Σ w`.  This
file defines that functional (`quadVar`), the spherical-errors condition
`Σ = σ² • I`, and the two basic facts the ordering theory needs: the spherical
reduction `quadVar = σ² ‖w‖²` and nonnegativity for a positive-semidefinite
covariance.

The probability-theoretic justification that `Var(∑ wᵢ Yᵢ) = wᵀ Σ w` (where
`Σ i j = cov(Yᵢ, Yⱼ)`) lives in `Causalean/Estimation/GaussMarkov/Variance.lean`;
the minimum-variance ordering theorems live in
`Causalean/Estimation/GaussMarkov/LeastNorm.lean`.
-/

import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Quadratic Variance Form

This file provides the deterministic quadratic-form layer of the finite
Gauss-Markov theory.  The definition `quadVar S w = w ⬝ᵥ S *ᵥ w` is the
weight-covariance-weight variance functional for a finite linear estimator, and
`SphericalErrors S σ` records the scalar-identity covariance condition
`S = σ² • I`.

The main reusable facts are `quadVar_nonneg`, nonnegativity under a
positive-semidefinite covariance matrix, and `quadVar_spherical`, the reduction
`quadVar S w = σ² * (w ⬝ᵥ w)` under spherical errors.  The probability-theoretic
bridge to actual random variables is in `GaussMarkov/Variance.lean`; the
least-variance ordering theorems are in `GaussMarkov/LeastNorm.lean`. -/

namespace Causalean.GaussMarkov

open Matrix

variable {Obs : Type*} [Fintype Obs]

/-- This is the covariance quadratic form that gives the variance of a linear estimator.

This is the deterministic algebraic object; the bridge to
`ProbabilityTheory.variance` of an actual random linear combination is
`variance_linearCombination` in `Variance.lean`. -/
def quadVar (S : Matrix Obs Obs ℝ) (w : Obs → ℝ) : ℝ := w ⬝ᵥ S *ᵥ w

/-- The quadratic variance form unfolds to the weight-covariance-weight product. -/
lemma quadVar_def (S : Matrix Obs Obs ℝ) (w : Obs → ℝ) :
    quadVar S w = w ⬝ᵥ S *ᵥ w := rfl

/-- A positive-semidefinite covariance matrix gives a nonnegative variance for
every linear weight. -/
lemma quadVar_nonneg {S : Matrix Obs Obs ℝ} (hS : S.PosSemidef) (w : Obs → ℝ) :
    0 ≤ quadVar S w := by
  have h := hS.dotProduct_mulVec_nonneg w
  simpa [quadVar] using h

variable [DecidableEq Obs]

/-- This condition says the covariance matrix has homoskedastic uncorrelated errors. -/
def SphericalErrors (S : Matrix Obs Obs ℝ) (σ : ℝ) : Prop :=
  S = σ ^ 2 • (1 : Matrix Obs Obs ℝ)

/-- Under spherical errors, the linear-estimator variance reduces to the common
variance times the squared weight length. -/
lemma quadVar_spherical {S : Matrix Obs Obs ℝ} {σ : ℝ} (h : SphericalErrors S σ)
    (w : Obs → ℝ) : quadVar S w = σ ^ 2 * (w ⬝ᵥ w) := by
  subst h
  rw [quadVar, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]

end Causalean.GaussMarkov
