/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Ordinary least squares weights via the normal-equations inverse

For a full-column-rank design `X : Matrix Obs Param ℝ` (i.e. `Xᵀ X` invertible),
the OLS weight estimating `c' β` is `wStar = X (XᵀX)⁻¹ c`.  It satisfies the
unbiasedness constraint `wStar ᵥ* X = c` and lies in the column span of `X`, so by
`gauss_markov_spherical` it is the minimum-variance (BLUE) weight under spherical
errors.
-/

import Causalean.Estimation.GaussMarkov.LeastNorm

/-! # Ordinary Least Squares Weights

This file defines the ordinary least-squares weight vector `olsWeight X c` for
estimating a specified linear combination `c'β` from a finite design matrix `X`.
The definition uses the ordinary inverse of the normal-equations matrix
`Xᵀ * X`; the unbiasedness theorem therefore assumes `IsUnit (Xᵀ * X).det`,
the finite full-column-rank condition.

The public facts are `olsWeight_unbiased`, which proves the constraint
`olsWeight X c ᵥ* X = c`, and `olsWeight_blue_spherical`, which applies
`gauss_markov_spherical` to show that this OLS weight is BLUE under spherical
errors. -/

namespace Causalean.GaussMarkov

open Matrix

variable {Obs Param : Type*} [Fintype Obs] [Fintype Param] [DecidableEq Param]

/-- OLS weight via the normal-equations inverse: `wStar = X (XᵀX)⁻¹ c`.

This uses Lean's ordinary matrix inverse of `XᵀX`, not a Moore-Penrose
pseudoinverse; the unbiasedness theorem below separately assumes
`IsUnit (Xᵀ * X).det`. -/
noncomputable def olsWeight (X : Matrix Obs Param ℝ) (c : Param → ℝ) : Obs → ℝ :=
  X *ᵥ ((Xᵀ * X)⁻¹ *ᵥ c)

/-- The OLS weight lies in the column span of `X`. -/
lemma olsWeight_mem_colSpan (X : Matrix Obs Param ℝ) (c : Param → ℝ) :
    olsWeight X c = X *ᵥ ((Xᵀ * X)⁻¹ *ᵥ c) := rfl

/-- The OLS weight satisfies the unbiasedness constraint `wStar ᵥ* X = c`,
provided `XᵀX` is invertible (full column rank). -/
lemma olsWeight_unbiased {X : Matrix Obs Param ℝ} (c : Param → ℝ)
    (h : IsUnit (Xᵀ * X).det) : olsWeight X c ᵥ* X = c := by
  have h1 : ∀ g : Param → ℝ, (X *ᵥ g) ᵥ* X = (Xᵀ * X) *ᵥ g := by
    intro g
    rw [← mulVec_transpose, mulVec_mulVec]
  calc olsWeight X c ᵥ* X
      = (Xᵀ * X) *ᵥ ((Xᵀ * X)⁻¹ *ᵥ c) := by rw [olsWeight, h1]
    _ = ((Xᵀ * X) * (Xᵀ * X)⁻¹) *ᵥ c := by rw [mulVec_mulVec]
    _ = (1 : Matrix Param Param ℝ) *ᵥ c := by rw [mul_nonsing_inv (Xᵀ * X) h]
    _ = c := one_mulVec c

/-- **OLS is BLUE under spherical errors.**  For an invertible `XᵀX`, the OLS weight
has minimum variance among all linear estimators satisfying the same unbiasedness
constraint `w ᵥ* X = c`, under spherical errors. -/
theorem olsWeight_blue_spherical [DecidableEq Obs] {X : Matrix Obs Param ℝ} (c : Param → ℝ)
    (h : IsUnit (Xᵀ * X).det) {S : Matrix Obs Obs ℝ} {σ : ℝ}
    (hS : SphericalErrors S σ) {w : Obs → ℝ} (hU : w ᵥ* X = c) :
    quadVar S (olsWeight X c) ≤ quadVar S w :=
  gauss_markov_spherical hS (olsWeight_mem_colSpan X c) (olsWeight_unbiased c h) hU

end Causalean.GaussMarkov
