/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Ridge.Finite
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Ridge regression — closed form

For `λ > 0` the ridge Gram matrix `XᵀX + λI` is positive definite, hence
invertible, so the ridge coefficient `β̂ = (XᵀX + λI)⁻¹ Xᵀy` is the unique
solution of the ridge normal equations — no full-rank assumption on `X` needed.
-/

namespace Causalean.ML

open Matrix BigOperators

variable {Obs Param : Type*} [Fintype Obs] [Fintype Param] [DecidableEq Param]

/-- The ridge closed-form coefficient `(XᵀX + λI)⁻¹ Xᵀy`. -/
noncomputable def ridgeCoef
    (X : Matrix Obs Param ℝ) (y : Obs → ℝ) (lam : ℝ) : Param → ℝ :=
  ((Xᵀ * X) + lam • (1 : Matrix Param Param ℝ))⁻¹ *ᵥ (Xᵀ *ᵥ y)

set_option linter.unusedFintypeInType false in
/-- For `λ > 0`, the ridge Gram matrix is positive definite. -/
theorem ridgeGram_posDef
    (X : Matrix Obs Param ℝ) {lam : ℝ} (hlam : 0 < lam) :
    ((Xᵀ * X) + lam • (1 : Matrix Param Param ℝ)).PosDef := by
  have hpsd : (Xᵀ * X).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self X)
  have hI : (lam • (1 : Matrix Param Param ℝ)).PosDef := by
    exact Matrix.PosDef.smul Matrix.PosDef.one hlam
  exact Matrix.PosDef.posSemidef_add hpsd hI

/-- For `λ > 0`, the closed-form ridge coefficient solves the ridge normal
equations. -/
theorem ridgeCoef_normalEq
    (X : Matrix Obs Param ℝ) (y : Obs → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    ((Xᵀ * X) + lam • (1 : Matrix Param Param ℝ)) *ᵥ ridgeCoef X y lam = Xᵀ *ᵥ y := by
  let G : Matrix Param Param ℝ := (Xᵀ * X) + lam • (1 : Matrix Param Param ℝ)
  have hGpos : G.PosDef := by
    dsimp [G]
    exact ridgeGram_posDef X hlam
  have hGdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hGpos.isUnit
  dsimp [ridgeCoef, G]
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hGdet, Matrix.one_mulVec]

/-- For `λ > 0`, every solution of the ridge normal equations is the closed-form
ridge coefficient. -/
theorem ridgeCoef_unique
    (X : Matrix Obs Param ℝ) (y : Obs → ℝ) {lam : ℝ} (hlam : 0 < lam)
    {β : Param → ℝ}
    (hNE : ((Xᵀ * X) + lam • (1 : Matrix Param Param ℝ)) *ᵥ β = Xᵀ *ᵥ y) :
    β = ridgeCoef X y lam := by
  let G : Matrix Param Param ℝ := (Xᵀ * X) + lam • (1 : Matrix Param Param ℝ)
  have hGpos : G.PosDef := by
    dsimp [G]
    exact ridgeGram_posDef X hlam
  have hGdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hGpos.isUnit
  have hclosed : G *ᵥ ridgeCoef X y lam = Xᵀ *ᵥ y := by
    dsimp [G]
    exact ridgeCoef_normalEq X y hlam
  have hsame : G *ᵥ β = G *ᵥ ridgeCoef X y lam := by
    dsimp [G] at hclosed ⊢
    rw [hNE, hclosed]
  have hcancel := congrArg (fun v : Param → ℝ => G⁻¹ *ᵥ v) hsame
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hGdet, Matrix.one_mulVec] using hcancel

end Causalean.ML
