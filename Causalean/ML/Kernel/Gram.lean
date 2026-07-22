/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

/-! # Gram matrices of a kernel

The file defines the Gram matrix `gram k x`, the positive-semidefinite-kernel
predicate `IsPSDkernel`, and the regularized-Gram positive-definiteness theorem
`gram_add_lambda_posDef`: if `k` is positive semidefinite and `λ > 0`, then
`K + λI ≻ 0`.  This is the finite-sample invertibility fact used by kernel ridge
regression.
-/

namespace Causalean.ML

open Matrix

/-- The Gram matrix `Kᵢⱼ = k(xᵢ, xⱼ)` of a kernel `k` on a finite sample `x`. -/
def gram {X : Type*} {n : ℕ} (k : X → X → ℝ) (x : Fin n → X) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => k (x i) (x j)

/-- A kernel is positive semidefinite when every Gram matrix is PSD. -/
def IsPSDkernel {X : Type*} (k : X → X → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → X), (gram k x).PosSemidef

/-- For a PSD kernel and `λ > 0`, the regularized Gram matrix `K + λI` is positive
definite (hence invertible). -/
theorem gram_add_lambda_posDef {X : Type*} {n : ℕ} {k : X → X → ℝ}
    (hk : IsPSDkernel k) (x : Fin n → X) {lam : ℝ} (hlam : 0 < lam) :
    (gram k x + lam • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
  have hpsd : (gram k x).PosSemidef := hk n x
  have hI : (lam • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
    exact Matrix.PosDef.smul Matrix.PosDef.one hlam
  exact Matrix.PosDef.posSemidef_add hpsd hI

end Causalean.ML
