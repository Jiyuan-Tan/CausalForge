/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Constrained least squares in finite Euclidean coordinates

This module proves the deterministic projection bound for least squares over an
arbitrary subset of a linear model. Convexity of the feasible set is not
required: comparison of the fitted residual with the residual at the truth is
the only optimization input.
-/

namespace CausalSmith.Substrate.MeasurableFiniteLinearERM

open scoped BigOperators RealInnerProductSpace
open InnerProductSpace Set Submodule

variable {n : ℕ}

/-- The squared empirical seminorm, normalized by the number of coordinates. -/
noncomputable def empiricalSqNorm (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, x i ^ 2

/-- In finite real coordinates, the Euclidean norm squared is the sum of the
coordinate squares. -/
theorem norm_sq_eq_sum_sq (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
  simpa [Real.norm_eq_abs] using EuclideanSpace.norm_sq_eq x

/-- Comparing the fitted residual with the residual at the truth gives the
least-squares basic inequality. -/
theorem leastSquares_basic_inequality
    (f0 fhat eps y : EuclideanSpace ℝ (Fin n))
    (hy : y = f0 + eps)
    (hresidual : ‖y - fhat‖ ^ 2 ≤ ‖y - f0‖ ^ 2) :
    ‖fhat - f0‖ ^ 2 ≤
      2 * @inner ℝ (EuclideanSpace ℝ (Fin n)) _ eps (fhat - f0) := by
  have hyhat : y - fhat = eps - (fhat - f0) := by
    rw [hy]
    abel
  have hyzero : y - f0 = eps := by
    rw [hy]
    abel
  rw [hyhat, hyzero, norm_sub_sq_real] at hresidual
  linarith

/-- An idempotent linear map fixes every vector in its range. -/
theorem idempotent_fixes_of_mem_range
    (Pi : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hPi_idem : ∀ x, Pi (Pi x) = Pi x)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ LinearMap.range Pi) :
    Pi x = x := by
  obtain ⟨z, rfl⟩ := hx
  exact hPi_idem z

/-- For a symmetric idempotent projector, pairing with a vector in the range
allows the other vector to be replaced by its projection. -/
theorem inner_projector_eq_of_mem_range
    (Pi : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hPi_symm : ∀ x z,
      @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (Pi x) z =
        @inner ℝ (EuclideanSpace ℝ (Fin n)) _ x (Pi z))
    (hPi_idem : ∀ x, Pi (Pi x) = Pi x)
    (eps : EuclideanSpace ℝ (Fin n)) {v : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ LinearMap.range Pi) :
    @inner ℝ (EuclideanSpace ℝ (Fin n)) _ eps v =
      @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (Pi eps) v := by
  rw [hPi_symm eps v, idempotent_fixes_of_mem_range Pi hPi_idem hv]

/-- The constrained least-squares basic inequality with the noise replaced by
its projection onto the linear model. The feasible set need not be convex. -/
theorem constrainedLeastSquares_projected_basic_inequality
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (Pi : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (f0 fhat eps y : EuclideanSpace ℝ (Fin n))
    (hK_V : K ⊆ V)
    (hf0 : f0 ∈ K) (hfhat : fhat ∈ K)
    (hy : y = f0 + eps)
    (hmin : ∀ f ∈ K, ‖y - fhat‖ ^ 2 ≤ ‖y - f‖ ^ 2)
    (hPi_symm : ∀ x z,
      @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (Pi x) z =
        @inner ℝ (EuclideanSpace ℝ (Fin n)) _ x (Pi z))
    (hPi_idem : ∀ x, Pi (Pi x) = Pi x)
    (hPi_range : LinearMap.range Pi = V) :
    ‖fhat - f0‖ ^ 2 ≤
      2 * @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (Pi eps) (fhat - f0) := by
  have hdeltaV : fhat - f0 ∈ V :=
    V.sub_mem (hK_V hfhat) (hK_V hf0)
  have hdeltaRange : fhat - f0 ∈ LinearMap.range Pi := by
    rw [hPi_range]
    exact hdeltaV
  rw [← inner_projector_eq_of_mem_range Pi hPi_symm hPi_idem eps hdeltaRange]
  exact leastSquares_basic_inequality f0 fhat eps y hy (hmin f0 hf0)

/-- A constrained least-squares minimizer is within twice the projected-noise
norm of the truth, in squared Euclidean norm. No convexity of the feasible set
is needed. -/
theorem constrainedLeastSquares_projection_bound
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (Pi : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (f0 fhat eps y : EuclideanSpace ℝ (Fin n))
    (hK_V : K ⊆ V)
    (hf0 : f0 ∈ K) (hfhat : fhat ∈ K)
    (hy : y = f0 + eps)
    (hmin : ∀ f ∈ K, ‖y - fhat‖ ^ 2 ≤ ‖y - f‖ ^ 2)
    (hPi_symm : ∀ x z,
      @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (Pi x) z =
        @inner ℝ (EuclideanSpace ℝ (Fin n)) _ x (Pi z))
    (hPi_idem : ∀ x, Pi (Pi x) = Pi x)
    (hPi_range : LinearMap.range Pi = V) :
    ‖fhat - f0‖ ^ 2 ≤ 4 * ‖Pi eps‖ ^ 2 := by
  have hbasic :=
    constrainedLeastSquares_projected_basic_inequality
      V K Pi f0 fhat eps y hK_V hf0 hfhat hy hmin
        hPi_symm hPi_idem hPi_range
  have hinner :
      @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (Pi eps) (fhat - f0) ≤
        ‖Pi eps‖ * ‖fhat - f0‖ :=
    real_inner_le_norm _ _
  nlinarith [norm_nonneg (Pi eps), norm_nonneg (fhat - f0)]

/-- The projection bound in the normalized empirical squared seminorm. -/
theorem constrainedLeastSquares_empiricalSqNorm_bound
    (hn : 0 < n)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (Pi : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (f0 fhat eps y : EuclideanSpace ℝ (Fin n))
    (hK_V : K ⊆ V)
    (hf0 : f0 ∈ K) (hfhat : fhat ∈ K)
    (hy : y = f0 + eps)
    (hmin : ∀ f ∈ K, ‖y - fhat‖ ^ 2 ≤ ‖y - f‖ ^ 2)
    (hPi_symm : ∀ x z,
      @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (Pi x) z =
        @inner ℝ (EuclideanSpace ℝ (Fin n)) _ x (Pi z))
    (hPi_idem : ∀ x, Pi (Pi x) = Pi x)
    (hPi_range : LinearMap.range Pi = V) :
    empiricalSqNorm (fhat - f0) ≤
      4 * empiricalSqNorm (Pi eps) := by
  have hbound :=
    constrainedLeastSquares_projection_bound
      V K Pi f0 fhat eps y hK_V hf0 hfhat hy hmin
        hPi_symm hPi_idem hPi_range
  unfold empiricalSqNorm
  rw [← norm_sq_eq_sum_sq (fhat - f0), ← norm_sq_eq_sum_sq (Pi eps)]
  calc
    (n : ℝ)⁻¹ * ‖fhat - f0‖ ^ 2 ≤
        (n : ℝ)⁻¹ * (4 * ‖Pi eps‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hbound
        (inv_nonneg.mpr (Nat.cast_pos.mpr hn).le)
    _ = 4 * ((n : ℝ)⁻¹ * ‖Pi eps‖ ^ 2) := by ring

end CausalSmith.Substrate.MeasurableFiniteLinearERM
