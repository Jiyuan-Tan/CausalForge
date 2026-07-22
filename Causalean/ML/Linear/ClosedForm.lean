/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Linear.Finite

/-! # Linear least squares — closed form

The structural closed-form content of OLS. This file defines `olsCoef`, proves
`ols_normalEq_of_minimizer` from global optimality, and shows that invertible
`XᵀX` makes the normal-equation solution unique with closed form
`β̂ = (XᵀX)⁻¹ Xᵀy`.
-/

namespace Causalean.ML

open Matrix BigOperators

variable {Obs Param : Type*} [Fintype Obs] [Fintype Param]

/-- The OLS closed-form coefficient `(XᵀX)⁻¹ Xᵀy`. -/
noncomputable def olsCoef [DecidableEq Param]
    (X : Matrix Obs Param ℝ) (y : Obs → ℝ) : Param → ℝ :=
  (Xᵀ * X)⁻¹ *ᵥ (Xᵀ *ᵥ y)

/-- A minimizer of the least-squares objective solves the normal equations. -/
theorem ols_normalEq_of_minimizer
    (X : Matrix Obs Param ℝ) (y : Obs → ℝ) (βhat : Param → ℝ)
    (hmin : ∀ β, olsObjective X y βhat ≤ olsObjective X y β) :
    (Xᵀ * X) *ᵥ βhat = Xᵀ *ᵥ y := by
  classical
  let r : Obs → ℝ := fun i => y i - (X *ᵥ βhat) i
  let g : Param → ℝ := Xᵀ *ᵥ r
  have hdot_zero : ∀ v : Param → ℝ, g ⬝ᵥ v = 0 := by
    intro v
    let a : ℝ := ∑ i, (X *ᵥ v) i ^ 2
    let c : ℝ := g ⬝ᵥ v
    have ha : 0 ≤ a :=
      Finset.sum_nonneg fun i _hi => sq_nonneg ((X *ᵥ v) i)
    have hquad : ∀ t : ℝ, 0 ≤ -2 * t * c + t ^ 2 * a := by
      intro t
      let δ : Param → ℝ := t • v
      let z : Obs → ℝ := X *ᵥ δ
      have hres : ∀ i, y i - (X *ᵥ (βhat + t • v)) i = r i - z i := by
        intro i
        have hx : X *ᵥ (βhat + t • v) = X *ᵥ βhat + z := by
          change X *ᵥ (βhat + δ) = X *ᵥ βhat + z
          rw [Matrix.mulVec_add]
        rw [hx]
        simp [r, z]
        ring
      have hcross : r ⬝ᵥ z = t * c := by
        calc
          r ⬝ᵥ z = r ⬝ᵥ X *ᵥ δ := rfl
          _ = r ᵥ* X ⬝ᵥ δ := Matrix.dotProduct_mulVec r X δ
          _ = (Xᵀ *ᵥ r) ⬝ᵥ δ := by rw [Matrix.mulVec_transpose]
          _ = t * c := by simp [g, δ, c, dotProduct_smul, smul_eq_mul]
      have hzsum : ∑ i, z i ^ 2 = t ^ 2 * a := by
        simp [z, δ, a, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
          Finset.mul_sum]
        ring_nf
      have htmp : olsObjective X y (βhat + t • v) =
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
            simp [dotProduct, Finset.sum_sub_distrib, Finset.sum_add_distrib,
              Finset.mul_sum]
      have hmin_t := hmin (βhat + t • v)
      nlinarith
    let t : ℝ := c / (a + 1)
    have hq := hquad t
    have hpos : 0 < a + 1 := by linarith
    have hpos2 : 0 < (a + 1) ^ 2 := sq_pos_of_pos hpos
    have hmul : 0 ≤ (-2 * t * c + t ^ 2 * a) * (a + 1) ^ 2 :=
      mul_nonneg hq (le_of_lt hpos2)
    have hcalc : (-2 * t * c + t ^ 2 * a) * (a + 1) ^ 2 =
        - (a + 2) * c ^ 2 := by
      subst t
      field_simp [ne_of_gt hpos]
      ring
    have hc_nonpos : c ^ 2 ≤ 0 := by
      nlinarith [hmul, hcalc, sq_nonneg c]
    have hc : c = 0 := by
      nlinarith [sq_nonneg c]
    simpa [c] using hc
  have hg_zero : g = 0 := by
    ext j
    have hj := hdot_zero (Pi.single j 1)
    simpa [g, dotProduct, Pi.single_apply] using hj
  have hz : Xᵀ *ᵥ y - (Xᵀ * X) *ᵥ βhat = 0 := by
    have hg' : Xᵀ *ᵥ (y - X *ᵥ βhat) = 0 := by
      simpa [g, r] using hg_zero
    rw [Matrix.mulVec_sub] at hg'
    simpa [Matrix.mulVec_mulVec] using hg'
  exact (sub_eq_zero.mp hz).symm

/-- When `XᵀX` is invertible, the closed-form OLS coefficient solves the normal
equations. -/
theorem olsCoef_normalEq [DecidableEq Param]
    (X : Matrix Obs Param ℝ) (y : Obs → ℝ) (hX : IsUnit (Xᵀ * X).det) :
    (Xᵀ * X) *ᵥ olsCoef X y = Xᵀ *ᵥ y := by
  unfold olsCoef
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hX, Matrix.one_mulVec]

/-- When `XᵀX` is invertible, every normal-equation solution equals the closed
form OLS coefficient. -/
theorem olsCoef_unique [DecidableEq Param]
    (X : Matrix Obs Param ℝ) (y : Obs → ℝ) (hX : IsUnit (Xᵀ * X).det)
    {β : Param → ℝ} (hNE : (Xᵀ * X) *ᵥ β = Xᵀ *ᵥ y) :
    β = olsCoef X y := by
  unfold olsCoef
  rw [← hNE, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hX, Matrix.one_mulVec]

end Causalean.ML
