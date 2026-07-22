/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Core
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Linear least squares — finite design-matrix layer

The ordinary-least-squares objective on a finite design matrix `X : Matrix Obs
Param ℝ` and its optimization property: any solution of the normal equations
`XᵀX β = Xᵀy` minimizes the sum of squared errors. The bridge theorem
`empiricalRisk_squaredLoss_linear` identifies the spine's `empiricalRisk`
(squared loss, linear-in-features predictor) with `(card)⁻¹` times this
objective, so finite OLS is a genuine ERM.
-/

namespace Causalean.ML

open Matrix BigOperators

variable {Obs Param : Type*} [Fintype Obs] [Fintype Param]

/-- The linear prediction vector `X β` for a design matrix `X` and coefficients `β`. -/
def linearPredict (X : Matrix Obs Param ℝ) (β : Param → ℝ) : Obs → ℝ := X *ᵥ β

/-- The ordinary-least-squares objective: the sum of squared residuals
`∑ᵢ (yᵢ − (Xβ)ᵢ)²`. -/
noncomputable def olsObjective (X : Matrix Obs Param ℝ) (y : Obs → ℝ) (β : Param → ℝ) : ℝ :=
  ∑ i, (y i - (X *ᵥ β) i) ^ 2

/-- Any solution `β̂` of the normal equations `XᵀX β̂ = Xᵀy` minimizes the
least-squares objective. -/
theorem ols_is_squaredLoss_ERM_of_normalEq
    (X : Matrix Obs Param ℝ) (y : Obs → ℝ) (βhat : Param → ℝ)
    (hNE : (Xᵀ * X) *ᵥ βhat = Xᵀ *ᵥ y) :
    ∀ β : Param → ℝ, olsObjective X y βhat ≤ olsObjective X y β := by
  intro β
  let δ : Param → ℝ := β - βhat
  let r : Obs → ℝ := fun i => y i - (X *ᵥ βhat) i
  let z : Obs → ℝ := X *ᵥ δ
  have hr : Xᵀ *ᵥ r = 0 := by
    have hNE' : Xᵀ *ᵥ (X *ᵥ βhat) = Xᵀ *ᵥ y := by
      simpa only [Matrix.mulVec_mulVec] using hNE
    change Xᵀ *ᵥ (y - X *ᵥ βhat) = 0
    rw [Matrix.mulVec_sub, hNE'.symm]
    simp
  have hβ : β = βhat + δ := by
    ext k
    simp [δ]
  have hres : ∀ i, y i - (X *ᵥ β) i = r i - z i := by
    intro i
    have hx : X *ᵥ β = X *ᵥ βhat + z := by
      rw [hβ, Matrix.mulVec_add]
    rw [hx]
    simp [r, z]
    ring
  have hcross : r ⬝ᵥ z = 0 := by
    calc
      r ⬝ᵥ z = r ⬝ᵥ X *ᵥ δ := rfl
      _ = r ᵥ* X ⬝ᵥ δ := Matrix.dotProduct_mulVec r X δ
      _ = (Xᵀ *ᵥ r) ⬝ᵥ δ := by rw [Matrix.mulVec_transpose]
      _ = 0 := by simp [hr]
  have hobj : olsObjective X y β =
      olsObjective X y βhat - 2 * (r ⬝ᵥ z) + ∑ i, z i ^ 2 := by
    unfold olsObjective
    simp_rw [hres]
    change (∑ i, (r i - z i) ^ 2) =
      (∑ i, r i ^ 2) - 2 * (r ⬝ᵥ z) + ∑ i, z i ^ 2
    calc
      (∑ i, (r i - z i) ^ 2) =
          ∑ i, (r i ^ 2 - 2 * (r i * z i) + z i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = (∑ i, r i ^ 2) - 2 * (r ⬝ᵥ z) + ∑ i, z i ^ 2 := by
        simp [dotProduct, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  have hnonneg : 0 ≤ ∑ i, z i ^ 2 :=
    Finset.sum_nonneg fun i _hi => sq_nonneg (z i)
  nlinarith

/-- Bridge to the spine: the empirical squared-loss risk of the linear-in-features
predictor `x ↦ ⟪β, φ x⟫` equals `(card ι)⁻¹` times the OLS objective of the design
matrix `Xᵢₖ = (φ xᵢ)ₖ`. -/
theorem empiricalRisk_squaredLoss_linear
    {ι K X' : Type*} [Fintype ι] [Nonempty ι] [Fintype K]
    (φ : FeatureMap X' K) (S : ι → X' × ℝ) (β : K → ℝ) :
    empiricalRisk squaredLoss S (fun x => ∑ k, β k * φ.φ x k)
      = (Fintype.card ι : ℝ)⁻¹ *
          olsObjective (fun i k => φ.φ (S i).1 k) (fun i => (S i).2) β := by
  simp [empiricalRisk, squaredLoss, olsObjective, Matrix.mulVec, dotProduct, mul_comm]

end Causalean.ML
