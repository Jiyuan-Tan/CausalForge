/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.LinearDisentanglement.Model

/-!
# Linear causal disentanglement: the key rank-one identity

The algebraic backbone of the identifiability results (Squires–Seigal–Bhate–Uhler,
§3.1).  `fact_transpose_mul` is the rank-one decomposition `BᵀB = Σᵢ (Bᵀeᵢ)⊗²`;
`key_identity` (their Proposition driving everything) computes the difference of
precision matrices between an interventional and the observational context as a
difference of two rank-one (outer-product) matrices, using that a single-node
intervention changes only one row of `B`.
-/

namespace Causalean.Discovery.LinearDisentanglement

open scoped Matrix BigOperators

variable {d p K : ℕ}

/-- Conjugation of a rank-one (outer-product) matrix: `A · (u vᵀ) · B = (A u)(Bᵀ v)ᵀ`. -/
private theorem conj_vecMulVec {l m n : ℕ} (A : Matrix (Fin l) (Fin m) ℝ)
    (u : Fin m → ℝ) (v : Fin m → ℝ) (B : Matrix (Fin m) (Fin n) ℝ) :
    A * Matrix.vecMulVec u v * B
      = Matrix.vecMulVec (A *ᵥ u) (B.transpose *ᵥ v) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose]

/-- **Fact (rank-one decomposition).**  For any square `B`, `BᵀB = Σᵢ (Bᵀeᵢ)⊗²`,
where `v⊗² = v vᵀ` (`Matrix.vecMulVec v v`). -/
theorem fact_transpose_mul (B : Matrix (Fin d) (Fin d) ℝ) :
    B.transpose * B
      = ∑ i, Matrix.vecMulVec (B.transpose *ᵥ stdVec d i) (B.transpose *ᵥ stdVec d i) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.sum_apply,
    Matrix.vecMulVec_apply, stdVec, Matrix.mulVec_single_one, Matrix.col_apply]

/-- **Key identity (Proposition).**  For an interventional context `k` with target
`iₖ`, the difference of precision matrices is exactly the difference between two
outer products: one built from the target row of the interventional structural matrix
and one built from the target row of the observational structural matrix. -/
theorem key_identity (S : Solution d p K) (k : Fin K) :
    S.Theta k - S.Theta0
      = Matrix.vecMulVec
          (S.H.transpose *ᵥ ((S.Bint k).transpose *ᵥ stdVec d (S.target k)))
          (S.H.transpose *ᵥ ((S.Bint k).transpose *ᵥ stdVec d (S.target k)))
        - Matrix.vecMulVec
          (S.H.transpose *ᵥ (S.B0.transpose *ᵥ stdVec d (S.target k)))
          (S.H.transpose *ᵥ (S.B0.transpose *ᵥ stdVec d (S.target k))) := by
  -- Off-target rows of `Bₖ` agree with `B₀`, so the rank-one decompositions cancel
  -- except in the target row; conjugating by `Hᵀ · _ · H` gives the two outer products.
  have hBlevel : ∀ (M B0 : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) (c : Fin d → ℝ),
      M = B0 + Matrix.vecMulVec (stdVec d i) c →
        M.transpose * M - B0.transpose * B0 =
          Matrix.vecMulVec (M.transpose *ᵥ stdVec d i) (M.transpose *ᵥ stdVec d i) -
            Matrix.vecMulVec (B0.transpose *ᵥ stdVec d i) (B0.transpose *ᵥ stdVec d i) := by
    intro M B0 i c hM
    have hrow : ∀ l : Fin d, l ≠ i →
        (M.transpose *ᵥ stdVec d l) = (B0.transpose *ᵥ stdVec d l) := by
      intro l hl
      subst hM
      funext a
      simp only [stdVec, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.transpose_apply,
        Matrix.add_apply, Matrix.vecMulVec_apply, Pi.single_eq_of_ne hl, zero_mul, add_zero]
    rw [fact_transpose_mul M, fact_transpose_mul B0,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hcancel :
        (∑ l ∈ Finset.univ.erase i,
            Matrix.vecMulVec (M.transpose *ᵥ stdVec d l) (M.transpose *ᵥ stdVec d l)) =
          ∑ l ∈ Finset.univ.erase i,
            Matrix.vecMulVec (B0.transpose *ᵥ stdVec d l) (B0.transpose *ᵥ stdVec d l) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [hrow l (Finset.ne_of_mem_erase hl)]
    rw [hcancel]
    abel
  rw [Solution.Theta, Solution.Theta0]
  have hfactor :
      S.H.transpose * (S.Bint k).transpose * S.Bint k * S.H -
          S.H.transpose * S.B0.transpose * S.B0 * S.H =
        S.H.transpose * ((S.Bint k).transpose * S.Bint k - S.B0.transpose * S.B0) * S.H := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc (S.H.transpose) ((S.Bint k).transpose),
      Matrix.mul_assoc (S.H.transpose) (S.B0.transpose)]
  rw [hfactor, hBlevel (S.Bint k) S.B0 (S.target k) _ (S.hInt k),
    Matrix.mul_sub, Matrix.sub_mul, conj_vecMulVec, conj_vecMulVec]

end Causalean.Discovery.LinearDisentanglement
