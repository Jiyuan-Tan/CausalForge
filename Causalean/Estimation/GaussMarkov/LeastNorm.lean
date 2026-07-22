/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Finite Gauss-Markov / least-norm ordering theorems

The mathematical core of the finite Gauss-Markov theory.  A linear estimator with
weight vector `w` is *unbiased* for the linear functional `c' β` (under the mean
model `E[Y] = X β`) exactly when `w ᵥ* X = c`.  Two unbiased weights differ by a
vector in the **left null space** of `X` (`z ᵥ* X = 0`).

* `gauss_markov_spherical`: under spherical errors `Σ = σ² I`, an OLS weight — one
  lying in the column span of `X` (`wStar = X *ᵥ g`) — has minimum variance in the
  unbiased class.  Proof: the OLS weight is Euclidean-orthogonal to every left-null
  direction, so Pythagoras gives `‖w‖² = ‖wStar‖² + ‖w - wStar‖² ≥ ‖wStar‖²`.

* `gauss_markov_gls`: for a general positive-semidefinite covariance `Σ`, a GLS
  weight — one with `Σ *ᵥ wStar` in the column span of `X` — has minimum variance.
  Proof: the same Pythagorean decomposition in the `Σ`-inner product, whose cross
  terms vanish because `Σ *ᵥ wStar` lies in the column span and `z` in the left null
  space.

`gauss_markov_spherical` is the version Borusyak-Jaravel-Spiess needs; the GLS
result is the general known-covariance BLUE statement.
-/

import Causalean.Estimation.GaussMarkov.QuadForm

/-! # Least-Norm Gauss-Markov Ordering

This file proves the algebraic core of the finite Gauss-Markov theorem. It
shows that, among linear-estimator weights satisfying the same unbiasedness
constraint `w ᵥ* X = c`, an ordinary least-squares weight in the column span of
`X` is variance-minimizing under spherical errors and a generalized least-squares
weight is variance-minimizing under a known positive-semidefinite covariance
matrix.

The main public results are `gauss_markov_spherical`, the finite BLUE ordering
for spherical covariance `Σ = σ² I`, and `gauss_markov_gls`, the corresponding
ordering for a general positive-semidefinite covariance.  The supporting lemma
`colSpan_dotProduct_leftNull` records the orthogonality between the column span
of `X` and the left null space that drives the Pythagorean variance comparison. -/

namespace Causalean.GaussMarkov

open Matrix

variable {Obs Param : Type*} [Fintype Obs] [Fintype Param]

/-- Column span is Euclidean-orthogonal to the left null space: if `z` lies in the
left null space of `X` (`z ᵥ* X = 0`), then any column-span vector `X *ᵥ g` is
orthogonal to `z`. -/
lemma colSpan_dotProduct_leftNull {X : Matrix Obs Param ℝ} {g : Param → ℝ}
    {z : Obs → ℝ} (hz : z ᵥ* X = 0) : (X *ᵥ g) ⬝ᵥ z = 0 := by
  rw [dotProduct_comm, dotProduct_mulVec, hz, zero_dotProduct]

/-- Nonnegativity of the Euclidean self dot product. -/
lemma dotProduct_self_nonneg' (v : Obs → ℝ) : 0 ≤ v ⬝ᵥ v := by
  rw [dotProduct]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- **Finite Gauss-Markov theorem, spherical case.**  Among all linear estimators
whose weights satisfy the same unbiasedness constraint `w ᵥ* X = c`, an OLS weight
`wStar = X *ᵥ g` (lying in the column span of `X`) has minimum variance under
spherical errors `Σ = σ² I`. -/
theorem gauss_markov_spherical [DecidableEq Obs] {X : Matrix Obs Param ℝ} {c : Param → ℝ}
    {S : Matrix Obs Obs ℝ} {σ : ℝ} (hS : SphericalErrors S σ)
    {w wStar : Obs → ℝ} {g : Param → ℝ}
    (hStar : wStar = X *ᵥ g)
    (hUStar : wStar ᵥ* X = c) (hU : w ᵥ* X = c) :
    quadVar S wStar ≤ quadVar S w := by
  -- `z := w - wStar` lies in the left null space of `X`.
  have hz : (w - wStar) ᵥ* X = 0 := by rw [sub_vecMul, hU, hUStar, sub_self]
  -- The OLS weight is orthogonal to `z` (it lies in the column span of `X`).
  have hortho : wStar ⬝ᵥ (w - wStar) = 0 := by
    have h := colSpan_dotProduct_leftNull (g := g) hz
    rwa [← hStar] at h
  -- Pythagoras: `‖w - wStar‖² = ‖w‖² - ‖wStar‖²`.
  have hcomm : w ⬝ᵥ wStar = wStar ⬝ᵥ w := dotProduct_comm w wStar
  have hcross : wStar ⬝ᵥ w = wStar ⬝ᵥ wStar := by
    have h := hortho; rw [dotProduct_sub] at h; linarith
  have key : (w - wStar) ⬝ᵥ (w - wStar) = w ⬝ᵥ w - wStar ⬝ᵥ wStar := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub]
    linarith
  have hznn := dotProduct_self_nonneg' (w - wStar)
  have hle : wStar ⬝ᵥ wStar ≤ w ⬝ᵥ w := by linarith
  rw [quadVar_spherical hS, quadVar_spherical hS]
  exact mul_le_mul_of_nonneg_left hle (sq_nonneg σ)

/-- **Finite Gauss-Markov theorem, general covariance (GLS).**  Among all linear
estimators with the same unbiasedness constraint `w ᵥ* X = c`, a GLS weight `wStar`
— one for which `Σ *ᵥ wStar` lies in the column span of `X` — has minimum variance
for any positive-semidefinite covariance `Σ`.  Specializes to `gauss_markov_spherical`
when `Σ = σ² I`. -/
theorem gauss_markov_gls {X : Matrix Obs Param ℝ} {c : Param → ℝ}
    {S : Matrix Obs Obs ℝ} (hS : S.PosSemidef)
    {w wStar : Obs → ℝ} {g : Param → ℝ}
    (hGLS : S *ᵥ wStar = X *ᵥ g)
    (hUStar : wStar ᵥ* X = c) (hU : w ᵥ* X = c) :
    quadVar S wStar ≤ quadVar S w := by
  have hsymm : Sᵀ = S := by
    have h := hS.isHermitian.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at h
  set z := w - wStar with hzdef
  have hz : z ᵥ* X = 0 := by rw [hzdef, sub_vecMul, hU, hUStar, sub_self]
  -- Both `Σ`-inner-product cross terms vanish.
  have term1 : z ⬝ᵥ S *ᵥ wStar = 0 := by
    rw [hGLS, dotProduct_mulVec, hz, zero_dotProduct]
  have term2 : wStar ⬝ᵥ S *ᵥ z = 0 := by
    rw [dotProduct_mulVec, ← hsymm, vecMul_transpose, hGLS]
    exact colSpan_dotProduct_leftNull hz
  have hwz : w = wStar + z := by rw [hzdef]; abel
  have hexpand : quadVar S w = quadVar S wStar + quadVar S z := by
    simp only [quadVar]
    rw [hwz, mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, term1, term2]
    ring
  rw [hexpand]
  have := quadVar_nonneg hS z
  linarith

end Causalean.GaussMarkov
