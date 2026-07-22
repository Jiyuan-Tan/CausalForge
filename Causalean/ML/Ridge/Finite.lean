/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Linear.Finite

/-! # Ridge regression — finite design-matrix layer

This file defines the finite-sample ridge objective `ridgeObjective`, the
ordinary least-squares error plus the L² penalty `λ‖β‖²`.  Its main theorem,
`ridge_is_regularized_squaredLoss_ERM_of_normalEq`, proves that any coefficient
vector satisfying the ridge normal equations `(XᵀX + λI) β̂ = Xᵀy` with `λ ≥ 0`
minimizes this penalized objective.
-/

namespace Causalean.ML

open Matrix BigOperators

variable {Obs Param : Type*} [Fintype Obs] [Fintype Param] [DecidableEq Param]

/-- The ridge objective: least-squares error plus the L² penalty `λ‖β‖²`. -/
noncomputable def ridgeObjective
    (X : Matrix Obs Param ℝ) (y : Obs → ℝ) (lam : ℝ) (β : Param → ℝ) : ℝ :=
  olsObjective X y β + lam * (β ⬝ᵥ β)

/-- With `λ ≥ 0`, any solution of the ridge normal equations
`(XᵀX + λI) β̂ = Xᵀy` minimizes the ridge objective. -/
theorem ridge_is_regularized_squaredLoss_ERM_of_normalEq
    (X : Matrix Obs Param ℝ) (y : Obs → ℝ) {lam : ℝ} (hlam : 0 ≤ lam)
    (βhat : Param → ℝ)
    (hNE : ((Xᵀ * X) + lam • (1 : Matrix Param Param ℝ)) *ᵥ βhat = Xᵀ *ᵥ y) :
    ∀ β : Param → ℝ, ridgeObjective X y lam βhat ≤ ridgeObjective X y lam β := by
  intro β
  let δ : Param → ℝ := β - βhat
  let r : Obs → ℝ := y - X *ᵥ βhat
  let z : Obs → ℝ := X *ᵥ δ
  have hβ : β = βhat + δ := by
    ext j
    simp [δ]
  have hcross : Xᵀ *ᵥ r = lam • βhat := by
    dsimp [r]
    ext j
    have hj := congrFun hNE j
    simp [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
      Matrix.mulVec_mulVec] at hj ⊢
    linarith
  have hcross_dot : r ⬝ᵥ z = lam * (βhat ⬝ᵥ δ) := by
    calc
      r ⬝ᵥ z = (Xᵀ *ᵥ r) ⬝ᵥ δ := by
        dsimp [z]
        rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
      _ = (lam • βhat) ⬝ᵥ δ := by rw [hcross]
      _ = lam * (βhat ⬝ᵥ δ) := by
        exact smul_dotProduct lam βhat δ
  have hsq (r z : Obs → ℝ) :
      (∑ i, (r i - z i) ^ 2) - (∑ i, (r i) ^ 2) =
        (∑ i, (z i) ^ 2) - 2 * (r ⬝ᵥ z) := by
    calc
      (∑ i, (r i - z i) ^ 2) - (∑ i, (r i) ^ 2)
          = ∑ i, ((r i - z i) ^ 2 - (r i) ^ 2) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ i, ((z i) ^ 2 - 2 * (r i * z i)) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = (∑ i, (z i) ^ 2) - ∑ i, 2 * (r i * z i) := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ i, (z i) ^ 2) - 2 * (r ⬝ᵥ z) := by
            simp [dotProduct, Finset.mul_sum]
  have hdot (a d : Param → ℝ) :
      (a + d) ⬝ᵥ (a + d) - a ⬝ᵥ a = 2 * (a ⬝ᵥ d) + d ⬝ᵥ d := by
    calc
      (a + d) ⬝ᵥ (a + d) - a ⬝ᵥ a
          = ∑ i, (((a i + d i) * (a i + d i)) - a i * a i) := by
            simp [dotProduct, Finset.sum_sub_distrib]
      _ = ∑ i, (2 * (a i * d i) + d i * d i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = 2 * (a ⬝ᵥ d) + d ⬝ᵥ d := by
            simp [dotProduct, Finset.sum_add_distrib, Finset.mul_sum]
  have hols : olsObjective X y β - olsObjective X y βhat =
      (∑ i, z i ^ 2) - 2 * (r ⬝ᵥ z) := by
    rw [hβ]
    dsimp [olsObjective, r, z]
    rw [Matrix.mulVec_add]
    convert hsq (y - X *ᵥ βhat) (X *ᵥ δ) using 2
    · congr 1
      ext i
      simp
      ring
  have hpen : lam * (β ⬝ᵥ β) - lam * (βhat ⬝ᵥ βhat) =
      lam * (2 * (βhat ⬝ᵥ δ) + δ ⬝ᵥ δ) := by
    rw [hβ]
    nlinarith [hdot βhat δ]
  have hdiff : ridgeObjective X y lam β - ridgeObjective X y lam βhat =
      (∑ i, z i ^ 2) + lam * (δ ⬝ᵥ δ) := by
    dsimp [ridgeObjective]
    calc
      olsObjective X y β + lam * (β ⬝ᵥ β) -
          (olsObjective X y βhat + lam * (βhat ⬝ᵥ βhat))
          = (olsObjective X y β - olsObjective X y βhat) +
              (lam * (β ⬝ᵥ β) - lam * (βhat ⬝ᵥ βhat)) := by ring
      _ = ((∑ i, z i ^ 2) - 2 * (r ⬝ᵥ z)) +
            lam * (2 * (βhat ⬝ᵥ δ) + δ ⬝ᵥ δ) := by rw [hols, hpen]
      _ = (∑ i, z i ^ 2) + lam * (δ ⬝ᵥ δ) := by
        rw [hcross_dot]
        ring
  have hdot_nonneg : 0 ≤ δ ⬝ᵥ δ := by
    simpa [dotProduct, pow_two] using
      Finset.sum_nonneg (s := Finset.univ) (fun i _ => mul_self_nonneg (δ i))
  have hnonneg : 0 ≤ ridgeObjective X y lam β - ridgeObjective X y lam βhat := by
    rw [hdiff]
    exact add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (mul_nonneg hlam hdot_nonneg)
  linarith

end Causalean.ML
