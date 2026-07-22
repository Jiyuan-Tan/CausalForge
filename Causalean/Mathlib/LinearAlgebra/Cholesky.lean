/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.Matrix.LDL
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Real.Sqrt

/-! # Real Cholesky factorization: existence and uniqueness

This file proves that every real symmetric positive-definite matrix factors as the product of the
transpose of an upper-triangular matrix with positive diagonal and that matrix itself, and that
this factorization is unique. Concretely, for a positive-definite matrix `M` there is a unique
upper-triangular matrix `U` with strictly positive diagonal entries such that `M` equals the
transpose of `U` times `U`.

The public API consists of the predicate `IsUpperTri`, the existence theorem
`cholesky_exists`, and the uniqueness theorem `cholesky_unique`; the LDL and orthogonal
triangular lemmas expose the proof ingredients needed by those results. Existence is
obtained from the LDL decomposition by absorbing the square roots of the diagonal factor;
uniqueness reduces to `orthogonal_upperTri_pos_diag_eq_one`, the fact that an orthogonal
upper-triangular matrix with positive diagonal is the identity. -/

open Matrix OrderDual

namespace Causalean.Mathlib.LinearAlgebra

variable {d : ℕ}

/-- An upper-triangular matrix in the sense `j < i → U i j = 0`, i.e. all entries strictly below
the diagonal vanish. -/
def IsUpperTri (U : Matrix (Fin d) (Fin d) ℝ) : Prop := ∀ i j, j < i → U i j = 0

/-- The entrywise upper-triangular predicate is exactly Mathlib's block-triangular predicate
for the identity order. -/
theorem isUpperTri_iff_blockTriangular {U : Matrix (Fin d) (Fin d) ℝ} :
    IsUpperTri U ↔ U.BlockTriangular id := by
  rfl

/-! ### Existence -/

section Existence

variable {M : Matrix (Fin d) (Fin d) ℝ}

/-- The Gram-Schmidt lower-inverse matrix is unitriangular: its diagonal entries are `1`. -/
theorem ldl_lowerInv_diag_one (hM : M.PosDef) (i : Fin d) : LDL.lowerInv hM i i = 1 := by
  letI := (Mᵀ.toNormedAddCommGroup hM.transpose)
  letI := (Mᵀ.toInnerProductSpace hM.transpose.posSemidef)
  have key : ∀ (c : Fin d), c < i →
      InnerProductSpace.gramSchmidt ℝ (⇑(Pi.basisFun ℝ (Fin d))) c i = 0 := by
    intro c hc
    have h2 := InnerProductSpace.gramSchmidt_triangular (𝕜 := ℝ) hc (Pi.basisFun ℝ (Fin d))
    simpa using h2
  rw [LDL.lowerInv, InnerProductSpace.gramSchmidt_def]
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.basisFun_apply, Pi.single_eq_same, sub_eq_self]
  refine Finset.sum_eq_zero (fun c hc => ?_)
  rw [Submodule.starProjection_singleton]
  change _ * InnerProductSpace.gramSchmidt ℝ (⇑(Pi.basisFun ℝ (Fin d))) c i = 0
  rw [key c (Finset.mem_Iio.mp hc), mul_zero]

/-- The diagonal entries of the LDL decomposition of a real positive-definite matrix are
strictly positive. -/
theorem ldl_diagEntries_pos (hM : M.PosDef) (i : Fin d) : 0 < LDL.diagEntries hM i := by
  have hne : LDL.lowerInv hM i ≠ 0 := by
    intro h
    have h1 := ldl_lowerInv_diag_one hM i
    rw [h] at h1
    simp at h1
  rw [LDL.diagEntries]
  simp only [EuclideanSpace.inner_toLp_toLp, star_trivial]
  rw [dotProduct_comm]
  exact hM.dotProduct_mulVec_pos hne

/-- `LDL.lowerInv` is lower-triangular in the `BlockTriangular toDual` sense. -/
theorem ldl_lowerInv_blockTriangular (hM : M.PosDef) :
    (LDL.lowerInv hM).BlockTriangular toDual := by
  intro i j hij
  exact LDL.lowerInv_triangular hM (by simpa using hij)

/-- `LDL.lower` (the inverse of `LDL.lowerInv`) is lower-triangular. -/
theorem ldl_lower_blockTriangular (hM : M.PosDef) :
    (LDL.lower hM).BlockTriangular toDual := by
  rw [LDL.lower]
  exact blockTriangular_inv_of_blockTriangular (ldl_lowerInv_blockTriangular hM)

/-- `LDL.lower` is unitriangular: its diagonal entries are `1`. -/
theorem ldl_lower_diag_one (hM : M.PosDef) (i : Fin d) : LDL.lower hM i i = 1 := by
  have hlow := ldl_lower_blockTriangular hM
  have hupp := ldl_lowerInv_blockTriangular hM
  have hmul : LDL.lower hM * LDL.lowerInv hM = 1 := by
    rw [LDL.lower]; exact Matrix.inv_mul_of_invertible _
  have hii : (LDL.lower hM * LDL.lowerInv hM) i i = 1 := by rw [hmul]; simp
  rw [Matrix.mul_apply] at hii
  rw [Finset.sum_eq_single i] at hii
  · rw [ldl_lowerInv_diag_one hM i, mul_one] at hii; exact hii
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hk | hk
    · rw [hupp (by simpa using hk), mul_zero]
    · rw [hlow (by simpa using hk), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Every real positive-definite matrix has an upper-triangular Cholesky factor with strictly
positive diagonal. -/
theorem cholesky_exists (hM : M.PosDef) :
    ∃ U : Matrix (Fin d) (Fin d) ℝ,
      (∀ i j, j < i → U i j = 0) ∧ (∀ i, 0 < U i i) ∧ M = U.transpose * U := by
  classical
  set s : Fin d → ℝ := fun i => Real.sqrt (LDL.diagEntries hM i) with hs
  set Dsqrt : Matrix (Fin d) (Fin d) ℝ := Matrix.diagonal s with hDsqrt
  refine ⟨Dsqrt * (LDL.lower hM)ᵀ, ?_, ?_, ?_⟩
  · -- upper triangular
    have hd : Dsqrt.BlockTriangular id := blockTriangular_diagonal s
    have hL : ((LDL.lower hM)ᵀ).BlockTriangular id := (ldl_lower_blockTriangular hM).transpose
    exact (hd.mul hL)
  · -- positive diagonal
    intro i
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single i]
    · simp only [hDsqrt, Matrix.diagonal_apply_eq, Matrix.transpose_apply, ldl_lower_diag_one hM i,
        mul_one, hs]
      exact Real.sqrt_pos.mpr (ldl_diagEntries_pos hM i)
    · intro k _ hki
      rw [hDsqrt, Matrix.diagonal_apply_ne' s hki, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  · -- M = Uᵀ U
    have hLH : (LDL.lower hM)ᴴ = (LDL.lower hM)ᵀ :=
      Matrix.conjTranspose_eq_transpose_of_trivial _
    have hDD : Dsqrt * Dsqrt = LDL.diag hM := by
      rw [hDsqrt, diagonal_mul_diagonal]
      rw [LDL.diag]
      congr 1
      ext i
      simp only [hs, Real.mul_self_sqrt (le_of_lt (ldl_diagEntries_pos hM i))]
    have hkey := LDL.lower_conj_diag hM
    rw [hLH] at hkey
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose]
    rw [← hDsqrt, Matrix.mul_assoc (LDL.lower hM) Dsqrt, ← Matrix.mul_assoc Dsqrt Dsqrt, hDD,
      ← Matrix.mul_assoc]
    exact hkey.symm

end Existence

/-! ### Uniqueness -/

section Uniqueness

/-- An orthogonal (`Wᵀ * W = 1`) upper-triangular matrix with strictly positive diagonal is the
identity matrix. -/
theorem orthogonal_upperTri_pos_diag_eq_one {W : Matrix (Fin d) (Fin d) ℝ}
    (hortho : Wᵀ * W = 1) (hupp : ∀ i j, j < i → W i j = 0) (hpos : ∀ i, 0 < W i i) :
    W = 1 := by
  classical
  haveI : Invertible W := invertibleOfLeftInverse _ _ hortho
  -- `W⁻¹ = Wᵀ`
  have hinv : W⁻¹ = Wᵀ := Matrix.inv_eq_left_inv hortho
  have hWupp : W.BlockTriangular id := hupp
  -- `Wᵀ` is upper-triangular (as `W⁻¹`) and lower-triangular (as a transpose of upper).
  have hWTupp : (Wᵀ).BlockTriangular id := hinv ▸ blockTriangular_inv_of_blockTriangular hWupp
  have hWTlow : (Wᵀ).BlockTriangular toDual := hWupp.transpose
  -- Hence `Wᵀ` is diagonal: off-diagonal entries vanish.
  have hWTdiag : ∀ i j, i ≠ j → (Wᵀ) i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hWTlow (by simpa using h)
    · exact hWTupp (by simpa using h)
  -- The diagonal entries square to one and are positive, hence equal one.
  ext i j
  have hsq : ∀ k, W k k * W k k = 1 := by
    intro k
    have := congrFun (congrFun hortho k) k
    rw [Matrix.mul_apply] at this
    rw [Finset.sum_eq_single k] at this
    · simpa [Matrix.transpose_apply] using this
    · intro l _ hlk
      have hz : (Wᵀ) k l = 0 := hWTdiag k l (Ne.symm hlk)
      rw [hz, zero_mul]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hdiagone : ∀ k, W k k = 1 := by
    intro k
    have h1 := hsq k
    nlinarith [hpos k]
  rcases eq_or_ne i j with rfl | hne
  · simp [hdiagone i]
  · rcases lt_or_gt_of_ne hne with h | h
    · -- `i < j`: read off `W i j` from the vanishing transpose entry `Wᵀ j i`
      have : (Wᵀ) j i = 0 := hWTdiag j i (Ne.symm hne)
      simpa [Matrix.transpose_apply, Matrix.one_apply_ne hne] using this
    · -- `j < i`: upper-triangularity kills it
      rw [hupp i j h, Matrix.one_apply_ne (Ne.symm (by simpa using h.ne))]

/-- Two upper-triangular positive-diagonal Cholesky factors of the same real positive-definite
matrix are equal. -/
theorem cholesky_unique {M U V : Matrix (Fin d) (Fin d) ℝ}
    (hUu : ∀ i j, j < i → U i j = 0) (hUp : ∀ i, 0 < U i i)
    (hVu : ∀ i j, j < i → V i j = 0) (hVp : ∀ i, 0 < V i i)
    (hU : M = U.transpose * U) (hV : M = V.transpose * V) : U = V := by
  classical
  have hUu' : U.BlockTriangular id := hUu
  have hVu' : V.BlockTriangular id := hVu
  -- `U` is invertible (positive diagonal ⟹ positive determinant).
  have hUdet : (0 : ℝ) < U.det := by
    rw [Matrix.det_of_upperTriangular hUu']; exact Finset.prod_pos (fun i _ => hUp i)
  haveI : Invertible U := U.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hUdet.ne')
  -- `U⁻¹` is upper-triangular with reciprocal diagonal entries.
  have hUinvU : U⁻¹.BlockTriangular id := blockTriangular_inv_of_blockTriangular hUu'
  have hUinv_diag : ∀ i, U⁻¹ i i = (U i i)⁻¹ := by
    intro i
    have hmul : (U⁻¹ * U) i i = 1 := by rw [Matrix.inv_mul_of_invertible]; simp
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at hmul
    · field_simp [(hUp i).ne'] at hmul ⊢
      linarith [hmul]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with hk | hk
      · rw [hUinvU (by simpa using hk), zero_mul]
      · rw [hUu k i hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  -- The transition matrix `W = V * U⁻¹`.
  set W : Matrix (Fin d) (Fin d) ℝ := V * U⁻¹ with hW
  -- `W` is upper-triangular.
  have hWupp : ∀ i j, j < i → W i j = 0 := hVu'.mul hUinvU
  -- `W` has strictly positive diagonal.
  have hWdiag : ∀ i, W i i = V i i * (U i i)⁻¹ := by
    intro i
    rw [hW, Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hUinv_diag i]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with hk | hk
      · rw [hVu i k (by simpa using hk), zero_mul]
      · rw [hUinvU (by simpa using hk), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hWpos : ∀ i, 0 < W i i := by
    intro i
    rw [hWdiag i]
    exact mul_pos (hVp i) (inv_pos.mpr (hUp i))
  -- `W` is orthogonal: `Wᵀ * W = 1`.
  have hMUV : Uᵀ * U = Vᵀ * V := hU ▸ hV
  have hWortho : Wᵀ * W = 1 := by
    rw [hW, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ V, ← hMUV,
      Matrix.mul_assoc Uᵀ, Matrix.mul_inv_of_invertible, Matrix.mul_one,
      Matrix.transpose_nonsing_inv, Matrix.inv_mul_of_invertible]
  -- Therefore `W = 1`, i.e. `V * U⁻¹ = 1`, i.e. `V = U`.
  have hWeq : W = 1 := orthogonal_upperTri_pos_diag_eq_one hWortho hWupp hWpos
  rw [hW] at hWeq
  have : V = 1 * U := by rw [← hWeq, Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.mul_one]
  rw [this, Matrix.one_mul]

end Uniqueness

end Causalean.Mathlib.LinearAlgebra
