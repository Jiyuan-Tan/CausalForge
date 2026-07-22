/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic

/-!
# Diagonal-conjugation scaling of the design moment matrix inverse

The interior local-polynomial leverage `(M⁻¹)₀₀` lives on the population moment matrix `S` at the
scale `Θ(Nh)`. The change of variables `u = (a−t)/h` factors the population matrix as a diagonal
conjugation of a *bandwidth-free* shape matrix `T`:

`S = (N·h) • (D · T · D)`,  with `D = diagonal (fun j => h^j)`,

so that `D₀₀ = h⁰ = 1`. This file isolates the **pure linear algebra** of that factorization: if
`S = κ • (D · T · D)` with `D` an invertible diagonal matrix whose `(0,0)` entry is `1`, `T`
invertible, and `κ ≠ 0`, then `S` is invertible and its leverage entry collapses to

`(S⁻¹)₀₀ = κ⁻¹ · (T⁻¹)₀₀`.

The `D₀₀ = 1` cancellation is exactly why the bandwidth powers drop out of the `(0,0)` entry,
leaving the clean `Θ(1/(Nh))` rate (the off-diagonal `h^j` factors never touch the intercept). The
companion top-entry identity `S₀₀ = κ · T₀₀` is recorded for the leverage product `M₀₀·(M⁻¹)₀₀`.
-/

namespace Causalean.Stat.Nonparametric

open scoped BigOperators
open Matrix

variable {p : ℕ}

/-- **Diagonal-conjugation inverse formula.** If `S = κ • (D · T · D)` with `κ ≠ 0` and
`D = diagonal d` an invertible diagonal matrix (`d i ≠ 0`), `T` invertible, then `S` is invertible
with
`S⁻¹ = κ⁻¹ • (D⁻¹ · T⁻¹ · D⁻¹)` where `D⁻¹ = diagonal (fun i => (d i)⁻¹)`. -/
theorem inv_diag_conj {κ : ℝ} (hκ : κ ≠ 0)
    {d : Fin (p + 1) → ℝ} (hd : ∀ i, d i ≠ 0)
    {T S : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ} (hT : IsUnit T.det)
    (hS : S = κ • (Matrix.diagonal d * T * Matrix.diagonal d)) :
    IsUnit S.det ∧
      S⁻¹ = κ⁻¹ • (Matrix.diagonal (fun i => (d i)⁻¹) * T⁻¹ *
        Matrix.diagonal (fun i => (d i)⁻¹)) := by
  let D : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ := Matrix.diagonal d
  let D' : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ :=
    Matrix.diagonal (fun i => (d i)⁻¹)
  let X : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ := κ⁻¹ • (D' * T⁻¹ * D')
  have hDD' : D * D' = 1 := by
    dsimp [D, D']
    rw [Matrix.diagonal_mul_diagonal]
    simp [Matrix.diagonal_one, fun i => mul_inv_cancel₀ (hd i)]
  have hcore : (D * T * D) * (D' * T⁻¹ * D') = 1 := by
    calc
      (D * T * D) * (D' * T⁻¹ * D') = D * T * (D * D') * T⁻¹ * D' := by
        simp [mul_assoc]
      _ = D * (T * T⁻¹) * D' := by
        rw [hDD']
        simp [mul_assoc]
      _ = D * 1 * D' := by
        rw [Matrix.mul_nonsing_inv T hT]
      _ = D * D' := by
        simp
      _ = 1 := hDD'
  have hSX : S * X = 1 := by
    rw [hS]
    dsimp [X]
    change (κ • (D * T * D)) * (κ⁻¹ • (D' * T⁻¹ * D')) = 1
    calc
      (κ • (D * T * D)) * (κ⁻¹ • (D' * T⁻¹ * D')) =
          (κ⁻¹ * κ) • ((D * T * D) * (D' * T⁻¹ * D')) := by
        simp [smul_smul]
      _ = 1 := by
        rw [inv_mul_cancel₀ hκ]
        simp [hcore]
  exact ⟨Matrix.isUnit_det_of_right_inverse hSX, Matrix.inv_eq_right_inv hSX⟩

/-- **Leverage entry under diagonal-conjugation scaling.** If `S = κ • (D · T · D)` with `κ ≠ 0`,
`D = diagonal d` invertible, `d 0 = 1`, and `T` invertible, then the `(0,0)` inverse entry collapses
to `(S⁻¹)₀₀ = κ⁻¹ · (T⁻¹)₀₀`: the diagonal bandwidth powers cancel at the intercept because
`D₀₀ = 1`. -/
theorem inv00_diag_conj {κ : ℝ} (hκ : κ ≠ 0)
    {d : Fin (p + 1) → ℝ} (hd : ∀ i, d i ≠ 0) (hd0 : d 0 = 1)
    {T S : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ} (hT : IsUnit T.det)
    (hS : S = κ • (Matrix.diagonal d * T * Matrix.diagonal d)) :
    IsUnit S.det ∧ S⁻¹ 0 0 = κ⁻¹ * T⁻¹ 0 0 := by
  obtain ⟨hdet, hform⟩ := inv_diag_conj hκ hd hT hS
  refine ⟨hdet, ?_⟩
  rw [hform]
  simp [Matrix.smul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, hd0]

/-- **Top entry under diagonal-conjugation scaling.** Under the same factorization
`S = κ • (D · T · D)` with `d 0 = 1`, the `(0,0)` entry of `S` itself is `S₀₀ = κ · T₀₀`. -/
theorem top00_diag_conj {κ : ℝ}
    {d : Fin (p + 1) → ℝ} (hd0 : d 0 = 1)
    {T S : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ}
    (hS : S = κ • (Matrix.diagonal d * T * Matrix.diagonal d)) :
    S 0 0 = κ * T 0 0 := by
  rw [hS]
  simp [Matrix.smul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, hd0]

end Causalean.Stat.Nonparametric
