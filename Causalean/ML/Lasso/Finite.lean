/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Linear.Finite
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex

/-! # Lasso — L1-regularized least squares (definitions + convexity)

The lasso objective is least squares plus the non-smooth convex penalty
`λ‖β‖₁ = λ ∑ₖ |βₖ|`. This file defines `l1penalty`, `lassoObjective`, and
`softThreshold`, and proves the nonnegativity and convexity facts needed by the
finite lasso objective. The scalar soft-thresholding optimality theorem is in
`Lasso/Optimality.lean`.
-/

namespace Causalean.ML

open Matrix BigOperators

variable {Obs Param : Type*} [Fintype Obs] [Fintype Param]

/-- The L1 penalty `‖β‖₁ = ∑ₖ |βₖ|`. -/
noncomputable def l1penalty (β : Param → ℝ) : ℝ := ∑ k, |β k|

/-- The lasso objective: least-squares error plus the L1 penalty `λ‖β‖₁`. -/
noncomputable def lassoObjective
    (X : Matrix Obs Param ℝ) (y : Obs → ℝ) (lam : ℝ) (β : Param → ℝ) : ℝ :=
  olsObjective X y β + lam * l1penalty β

/-- The soft-thresholding operator, in the sign-free form
`S_λ(z) = max(z − λ, 0) − max(−z − λ, 0)` (equal to `sign z · max(|z| − λ, 0)`). -/
noncomputable def softThreshold (lam z : ℝ) : ℝ := max (z - lam) 0 - max (-z - lam) 0

/-- The L1 penalty is nonnegative. -/
theorem l1penalty_nonneg (β : Param → ℝ) : 0 ≤ l1penalty β :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The L1 penalty is convex. -/
theorem convexOn_l1penalty : ConvexOn ℝ Set.univ (l1penalty (Param := Param)) := by
  classical
  unfold l1penalty
  let coord : Param → ((Param → ℝ) →ₗ[ℝ] ℝ) := fun k => LinearMap.proj k
  have hcoord : ∀ k : Param, ConvexOn ℝ Set.univ (fun β : Param → ℝ => ‖β k‖) := by
    intro k
    simpa [Function.comp_def, coord] using
      (convexOn_univ_norm (E := ℝ)).comp_linearMap (coord k)
  have hfin : ∀ t : Finset Param,
      ConvexOn ℝ Set.univ (fun β : Param → ℝ => t.sum fun k => ‖β k‖) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        simpa using
          (convexOn_const (𝕜 := ℝ) (E := Param → ℝ) (β := ℝ)
            (s := Set.univ) (0 : ℝ) convex_univ)
    | insert k t hk ht =>
        simpa [Finset.sum_insert hk, Pi.add_apply] using (hcoord k).add ht
  simpa [Real.norm_eq_abs] using hfin Finset.univ

/-- The least-squares objective is convex in the coefficients. -/
theorem convexOn_olsObjective (X : Matrix Obs Param ℝ) (y : Obs → ℝ) :
    ConvexOn ℝ Set.univ (olsObjective X y) := by
  classical
  unfold olsObjective
  let lin : Obs → ((Param → ℝ) →ₗ[ℝ] ℝ) := fun i =>
    { toFun := fun β => (X *ᵥ β) i
      map_add' := by
        intro β γ
        simp [Matrix.mulVec_add]
      map_smul' := by
        intro c β
        simp [Matrix.mulVec_smul] }
  let aff : Obs → ((Param → ℝ) →ᵃ[ℝ] ℝ) := fun i =>
    { toFun := fun β => y i - (X *ᵥ β) i
      linear := -lin i
      map_vadd' := by
        intro β δ
        simp only [vadd_eq_add]
        rw [Matrix.mulVec_add]
        simp [lin]
        ring }
  have hsquare : ConvexOn ℝ Set.univ (fun t : ℝ => t ^ 2) := by
    simpa using (show Even 2 from by decide).convexOn_pow (𝕜 := ℝ)
  have hsummand :
      ∀ i : Obs, ConvexOn ℝ Set.univ (fun β : Param → ℝ => (y i - (X *ᵥ β) i) ^ 2) := by
    intro i
    simpa [Function.comp_def, aff] using hsquare.comp_affineMap (aff i)
  have hfin : ∀ t : Finset Obs,
      ConvexOn ℝ Set.univ
        (fun β : Param → ℝ => t.sum fun i => (y i - (X *ᵥ β) i) ^ 2) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        simpa using
          (convexOn_const (𝕜 := ℝ) (E := Param → ℝ) (β := ℝ)
            (s := Set.univ) (0 : ℝ) convex_univ)
    | insert i t hi ht =>
        simpa [Finset.sum_insert hi, Pi.add_apply] using (hsummand i).add ht
  simpa using hfin Finset.univ

/-- The lasso objective is convex for `λ ≥ 0`. -/
theorem convexOn_lassoObjective
    (X : Matrix Obs Param ℝ) (y : Obs → ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    ConvexOn ℝ Set.univ (lassoObjective X y lam) := by
  unfold lassoObjective
  simpa [smul_eq_mul] using
    (convexOn_olsObjective X y).add ((convexOn_l1penalty (Param := Param)).smul hlam)

end Causalean.ML
