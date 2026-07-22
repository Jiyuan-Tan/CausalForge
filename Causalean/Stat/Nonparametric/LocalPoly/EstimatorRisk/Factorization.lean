/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.LocalPoly.EstimatorRisk.DensityConstants
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Change-of-variables factorization of the population design moment matrix

The population design moment matrix of the interior local-polynomial fit at bandwidth `h` and
target `t`, against a design law with Lebesgue density `p`, has entries

`S_{jk} = N · ∫ K((a−t)/h) · (a−t)^{j+k} · p(a) da`.

The substitution `u = (a−t)/h` (`a = t + h·u`, `da = h·du`) factors it as a diagonal conjugation
of the bandwidth-free shape matrix `T_{jk} = ∫ K(u) u^{j+k} p(t+h·u) du`:

`S_{jk} = N · h^{j+k+1} · T_{jk} = (N·h) · (D · T · D)_{jk}`,  `D = diagonal (fun j => h^j)`.

This is the literal factorization consumed by `population_scaling_of_conj`: it exposes the `Θ(Nh)`
scale and the bandwidth-free shape matrix `T` (whose density-constant leverage bounds come from
`DensityConstants`). The change of variables reuses the affine-rescaling pattern of
`Approximation/Kernel.lean`.
-/

namespace Causalean.Stat.Nonparametric

open MeasureTheory
open scoped BigOperators
open Matrix

variable {p : ℕ}

/-- **Change of variables for a single moment entry.** For `h > 0`,
`∫ a, K((a−t)/h) · (a−t)^m · p(a) da = h^{m+1} · ∫ u, K(u) · u^m · p(t+h·u) du`: the substitution
`a = t + h·u` contributes the Jacobian `h` and turns `(a−t)^m` into `(h·u)^m = h^m u^m`. -/
theorem popMomentEntry_changeOfVar (K pdens : ℝ → ℝ) (t h : ℝ) (hh : 0 < h) (m : ℕ) :
    (∫ a, K ((a - t) / h) * (a - t) ^ m * pdens a)
      = h ^ (m + 1) * ∫ u, K u * u ^ m * pdens (t + h * u) := by
  set ψ : ℝ → ℝ := fun a => K ((a - t) / h) * (a - t) ^ m * pdens a with hψ
  have hrescale : (∫ a, ψ a) = h * ∫ u, ψ (t + h * u) := by
    have hcv : (∫ u, ψ (t + h * u)) = h⁻¹ * ∫ a, ψ a := by
      calc
        (∫ u, ψ (t + h * u))
            = ∫ u, (fun w => ψ (t + w)) (h * u) := rfl
        _ = |h⁻¹| • ∫ w, (fun w => ψ (t + w)) w := by
            simpa using Measure.integral_comp_mul_left (fun w : ℝ => ψ (t + w)) h
        _ = |h⁻¹| • ∫ w, ψ (t + w) := rfl
        _ = |h⁻¹| • ∫ a, ψ a := by rw [integral_add_left_eq_self ψ t]
        _ = h⁻¹ * ∫ a, ψ a := by rw [smul_eq_mul, abs_of_pos (inv_pos.mpr hh)]
    calc
      (∫ a, ψ a) = h * (h⁻¹ * ∫ a, ψ a) := by
        field_simp [hh.ne']
      _ = h * ∫ u, ψ (t + h * u) := by rw [hcv]
  have hinner :
      (∫ u, ψ (t + h * u)) = h ^ m * ∫ u, K u * u ^ m * pdens (t + h * u) := by
    calc
      (∫ u, ψ (t + h * u))
          = ∫ u, h ^ m * (K u * u ^ m * pdens (t + h * u)) := by
            refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
            simp only [hψ]
            rw [show t + h * u - t = h * u from by ring]
            rw [show (h * u) / h = u from by
              rw [mul_comm, mul_div_assoc, div_self hh.ne', mul_one]]
            rw [mul_pow]
            ring
      _ = h ^ m * ∫ u, K u * u ^ m * pdens (t + h * u) := by
            rw [MeasureTheory.integral_const_mul]
  calc
    (∫ a, K ((a - t) / h) * (a - t) ^ m * pdens a)
        = ∫ a, ψ a := rfl
    _ = h * ∫ u, ψ (t + h * u) := hrescale
    _ = h * (h ^ m * ∫ u, K u * u ^ m * pdens (t + h * u)) := by rw [hinner]
    _ = h ^ (m + 1) * ∫ u, K u * u ^ m * pdens (t + h * u) := by
        rw [pow_succ]
        ring

/-- The population design moment matrix `S_{jk} = N · ∫ K((a−t)/h) (a−t)^{j+k} p(a) da`. -/
noncomputable def popDesignMatrix (p N : ℕ) (K pdens : ℝ → ℝ) (t h : ℝ) :
    Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ :=
  Matrix.of (fun j k =>
    (N : ℝ) * ∫ a, K ((a - t) / h) * (a - t) ^ ((j : ℕ) + (k : ℕ)) * pdens a)

/-- **Diagonal-conjugation factorization of the population moment matrix.** With `T` the kernel
shape matrix `weightMomentMatrix p (fun u => K u · p(t+h·u))` and `D = diagonal (fun j => h^j)`,

`popDesignMatrix p N K p t h = (N·h) • (D · T · D)`.

This is the literal `S = (Nh)·(D T D)` hypothesis of `population_scaling_of_conj`, proved by the
single-entry change of variables `popMomentEntry_changeOfVar`. -/
theorem popDesignMatrix_factor (N : ℕ) (K pdens : ℝ → ℝ) (t h : ℝ) (hh : 0 < h) :
    popDesignMatrix p N K pdens t h
      = ((N : ℝ) * h) •
        (Matrix.diagonal (fun j : Fin (p + 1) => h ^ (j : ℕ)) *
          weightMomentMatrix p (fun u => K u * pdens (t + h * u)) *
          Matrix.diagonal (fun j : Fin (p + 1) => h ^ (j : ℕ))) := by
  ext j k
  simp only [popDesignMatrix, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.diagonal_mul, Matrix.mul_diagonal, weightMomentMatrix]
  rw [popMomentEntry_changeOfVar K pdens t h hh ((j : ℕ) + (k : ℕ))]
  have hint :
      (∫ u, K u * u ^ ((j : ℕ) + (k : ℕ)) * pdens (t + h * u))
        = ∫ u, (K u * pdens (t + h * u)) * (u ^ (j : ℕ) * u ^ (k : ℕ)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    ring
  rw [hint]
  ring

end Causalean.Stat.Nonparametric
