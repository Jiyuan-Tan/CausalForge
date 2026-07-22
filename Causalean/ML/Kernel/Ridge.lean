/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Kernel.RKHS
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! # Kernel ridge regression — the representer theorem

Kernel ridge regression minimizes the regularized empirical risk over an RKHS.
This file defines `krrRisk` and proves `representer_theorem`: under `λ > 0`, any
global minimizer is a finite linear combination of the sample representers
`k(·, xᵢ)`. The theorem is the dimension-reduction step from an RKHS-valued
optimization problem to a finite coefficient problem.
-/

namespace Causalean.ML

open BigOperators

/-- The kernel-ridge regularized empirical risk of an RKHS element `f`:
`(1/n) ∑ᵢ (f(xᵢ) − yᵢ)² + λ‖f‖²`. -/
noncomputable def krrRisk {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (feval : H → X → ℝ) {n : ℕ} (x : Fin n → X) (y : Fin n → ℝ) (lam : ℝ) (f : H) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, (feval f (x i) - y i) ^ 2 + lam * ‖f‖ ^ 2

/-- With `λ > 0`, every kernel-ridge minimizer over a complete RKHS lies in the
span of the sample representers `k(·, xᵢ)`. -/
theorem representer_theorem {X H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {feval : H → X → ℝ} {representer : X → H} (hrkhs : IsRKHS X H feval representer)
    {n : ℕ} (x : Fin n → X) (y : Fin n → ℝ) {lam : ℝ} (hlam : 0 < lam) {fhat : H}
    (hmin : ∀ g : H, krrRisk feval x y lam fhat ≤ krrRisk feval x y lam g) :
    ∃ α : Fin n → ℝ, fhat = ∑ i, α i • representer (x i) := by
  classical
  let M : Submodule ℝ H := Submodule.span ℝ (Set.range fun i : Fin n => representer (x i))
  haveI : FiniteDimensional ℝ M := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  haveI : CompleteSpace M := by infer_instance
  let p : H := M.orthogonalProjectionFn fhat
  have hp_mem : p ∈ M := by
    exact Submodule.orthogonalProjectionFn_mem (K := M) fhat
  have hrep_mem : ∀ i : Fin n, representer (x i) ∈ M := by
    intro i
    exact Submodule.subset_span ⟨i, rfl⟩
  have heval_eq : ∀ i : Fin n, feval fhat (x i) = feval p (x i) := by
    intro i
    have horth : inner ℝ (fhat - p) (representer (x i)) = 0 := by
      exact Submodule.orthogonalProjectionFn_inner_eq_zero (K := M) fhat
        (representer (x i)) (hrep_mem i)
    rw [hrkhs.reproducing fhat (x i), hrkhs.reproducing p (x i)]
    calc
      inner ℝ fhat (representer (x i))
          = inner ℝ ((fhat - p) + p) (representer (x i)) := by
              rw [sub_add_cancel]
      _ = inner ℝ (fhat - p) (representer (x i))
            + inner ℝ p (representer (x i)) := by
              rw [inner_add_left]
      _ = inner ℝ p (representer (x i)) := by
              rw [horth, zero_add]
  have hdata_eq :
      (∑ i, (feval fhat (x i) - y i) ^ 2)
        = ∑ i, (feval p (x i) - y i) ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [heval_eq i]
  have hmin_p : krrRisk feval x y lam fhat ≤ krrRisk feval x y lam p := hmin p
  have hnorm_le : ‖fhat‖ ^ 2 ≤ ‖p‖ ^ 2 := by
    have hmul_le : lam * ‖fhat‖ ^ 2 ≤ lam * ‖p‖ ^ 2 := by
      unfold krrRisk at hmin_p
      rw [hdata_eq] at hmin_p
      linarith
    nlinarith
  have hnorm_decomp :
      ‖fhat‖ ^ 2 = ‖p‖ ^ 2 + ‖((Mᗮ).orthogonalProjection fhat : H)‖ ^ 2 := by
    simpa [p, Submodule.orthogonalProjectionFn_eq] using
      (Submodule.norm_sq_eq_add_norm_sq_projection fhat M)
  have hperp_sq :
      ‖((Mᗮ).orthogonalProjection fhat : H)‖ ^ 2 = 0 := by
    have hnonneg : 0 ≤ ‖((Mᗮ).orthogonalProjection fhat : H)‖ ^ 2 :=
      sq_nonneg _
    nlinarith
  have hperp_zero : ((Mᗮ).orthogonalProjection fhat : H) = 0 := by
    apply norm_eq_zero.mp
    have hnonneg : 0 ≤ ‖((Mᗮ).orthogonalProjection fhat : H)‖ :=
      norm_nonneg _
    nlinarith
  have hfhat_eq_p : fhat = p := by
    have hsplit := Submodule.starProjection_add_starProjection_orthogonal (K := M) fhat
    have hperp_star : (Mᗮ).starProjection fhat = 0 := by
      change ((Mᗮ).orthogonalProjection fhat : H) = 0
      exact hperp_zero
    calc
      fhat = M.starProjection fhat + (Mᗮ).starProjection fhat := hsplit.symm
      _ = M.starProjection fhat + 0 := by rw [hperp_star]
      _ = p := by
          rw [add_zero]
          change M.orthogonalProjectionFn fhat = p
          rfl
  have hfhat_mem : fhat ∈ M := by
    simpa [hfhat_eq_p] using hp_mem
  rcases (Submodule.mem_span_range_iff_exists_fun (R := ℝ)
      (v := fun i : Fin n => representer (x i)) (x := fhat)).mp hfhat_mem with ⟨α, hα⟩
  exact ⟨α, hα.symm⟩

end Causalean.ML
