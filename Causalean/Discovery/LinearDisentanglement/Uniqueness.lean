/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.LinearDisentanglement.Rowspan
import Causalean.Discovery.LinearDisentanglement.SigmaSolutions
import Causalean.Mathlib.LinearAlgebra.Cholesky
import Mathlib.Data.Real.StarOrdered

/-!
# Linear causal disentanglement: uniqueness (⊆ direction of Theorem 2)

This is the hard half of the flagship: any two parameter tuples producing the same
family of precision matrices `{Θ_k}` differ by a single order-preserving relabeling
`σ ∈ S(𝒢)`.  The proof follows the constructive argument of the paper:

1. recover the orthogonal factor `Q` of a partial order RQ decomposition of `H`, up
   to `S(𝒢)` and signs, from the spans `rowspan(Θₖ − Θ₀)` (`rowspan_inclusion`);
2. orthogonalize: `(Q⁺)ᵀ Θₖ Q⁺` is the Cholesky factor of the latent precision, which
   recovers `R` and hence `H = R Q` up to `S(𝒢)`;
3. read off `{Bₖ}` from `H` and `{Θₖ}` via Cholesky factorization.

The main public declarations expose these stages.  `exists_change_of_basis`
recovers the invertible matrix `M` with `H' = M H`; `gram_identity` and
`gram_diff_transport` move the precision equalities down to latent `d × d`
Gram identities; `central_rank2_eq` rewrites those identities in rank-two
outer-product form; `exists_orderPerm` performs the orthogonal-correctness
collapse and reads off the target relabeling; and `disentanglement_uniqueness`
packages the final signed-monomial conclusion.

The order-preservation pinning runs the same triangular-support logic as
`Causalean.Mathlib.LinearAlgebra.perm_uniqueness`: positive diagonals,
triangularity, and nonzero support entries force the recovered relabeling to lie
in `S(𝒢)`.
-/

namespace Causalean.Discovery.LinearDisentanglement

open scoped Matrix

variable {d p K : ℕ}

/-! ### General matrix helpers (route-agnostic) -/

/-- **(L3) Gram ⟹ orthogonal.**  If `XᵀX = YᵀY` with `X`, `Y` invertible, then the
transition matrix `O = Y X⁻¹` is orthogonal: `Oᵀ O = 1`.  This is the algebraic step that
turns the equality of Gram matrices `BᵀB = (B' M)ᵀ(B' M)` into an orthogonality statement
about `O = B' M B⁻¹`. -/
theorem gram_to_orthogonal {q : ℕ} {X Y : Matrix (Fin q) (Fin q) ℝ}
    [Invertible X] [Invertible Y] (h : Xᵀ * X = Yᵀ * Y) :
    (Y * X⁻¹)ᵀ * (Y * X⁻¹) = 1 := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Yᵀ Y, ← h, Matrix.mul_assoc Xᵀ,
    Matrix.mul_inv_of_invertible, Matrix.mul_one, Matrix.transpose_nonsing_inv,
    Matrix.inv_mul_of_invertible]

/-! ### Invertibility of the structural matrices

`B0` and every `Bint k` are upper triangular with strictly positive diagonal, hence have
positive determinant and are invertible. -/

/-- `B0` is upper triangular in the `BlockTriangular id` sense. -/
theorem B0_blockTriangular (S : Solution d p K) : S.B0.BlockTriangular id := S.hB0up

/-- `Bint k` is upper triangular: the perfect intervention only rewrites the target row
(which keeps the diagonal at `λₖ` and zeroes the strictly-lower entries already zero in
`B0`). -/
theorem Bint_blockTriangular (S : Solution d p K) (k : Fin K) :
    (S.Bint k).BlockTriangular id := by
  intro i j hji
  simp only [id_eq] at hji
  rw [S.hInt k, Matrix.add_apply, S.hB0up i j hji, zero_add, Matrix.vecMulVec_apply]
  by_cases hi : i = S.target k
  · -- target row: off-diagonal lower entries vanish since `j < i = target k`
    have hjlt : j < S.target k := hi ▸ hji
    have hjne : j ≠ S.target k := ne_of_lt hjlt
    rw [S.hB0up (S.target k) j hjlt]
    simp [stdVec, Pi.single_eq_of_ne hjne]
  · simp [stdVec, Pi.single_eq_of_ne hi]

/-- `det B0 = ∏ᵢ (B0)ᵢᵢ > 0`. -/
theorem B0_det_pos (S : Solution d p K) : 0 < S.B0.det := by
  rw [Matrix.det_of_upperTriangular (B0_blockTriangular S)]
  exact Finset.prod_pos (fun i _ => S.hB0pos i)

/-- `(Bint k)ᵢᵢ = (B0)ᵢᵢ` off the target, and `= λₖ` on the target — in both cases
strictly positive. -/
theorem Bint_diag_pos (S : Solution d p K) (k : Fin K) (i : Fin d) : 0 < S.Bint k i i := by
  rw [S.hInt k, Matrix.add_apply, Matrix.vecMulVec_apply]
  by_cases hi : i = S.target k
  · rw [hi]
    simp only [stdVec, Pi.single_eq_same, one_mul]
    have : S.B0 (S.target k) (S.target k)
        + (S.lam k * 1 - S.B0 (S.target k) (S.target k)) = S.lam k := by ring
    rw [this]; exact S.hlam k
  · simp only [stdVec, Pi.single_eq_of_ne hi, zero_mul, add_zero]
    exact S.hB0pos i

/-- `det (Bint k) = ∏ᵢ (Bint k)ᵢᵢ > 0`. -/
theorem Bint_det_pos (S : Solution d p K) (k : Fin K) : 0 < (S.Bint k).det := by
  rw [Matrix.det_of_upperTriangular (Bint_blockTriangular S k)]
  exact Finset.prod_pos (fun i _ => Bint_diag_pos S k i)

/-- `B0` is invertible. -/
noncomputable instance B0_invertible (S : Solution d p K) : Invertible S.B0 :=
  S.B0.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr (B0_det_pos S).ne')

/-- `Bint k` is invertible. -/
noncomputable instance Bint_invertible (S : Solution d p K) (k : Fin K) :
    Invertible (S.Bint k) :=
  (S.Bint k).invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr (Bint_det_pos S k).ne')

/-! ### The latent Gram matrix `H Hᵀ` is positive definite, hence invertible -/

/-- `vecMul · H` is injective (full row rank of `H`). -/
theorem vecMul_H_injective (S : Solution d p K) :
    Function.Injective (fun v => Matrix.vecMul v S.H) :=
  Matrix.vecMul_injective_iff.mpr (by rw [Matrix.row_def]; exact S.hH)

/-- The latent Gram matrix `H Hᵀ` is positive definite. -/
theorem HHt_posDef (S : Solution d p K) : (S.H * S.H.transpose).PosDef := by
  have := Matrix.PosDef.mul_conjTranspose_self S.H (vecMul_H_injective S)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-- `H Hᵀ` is invertible. -/
noncomputable instance HHt_invertible (S : Solution d p K) :
    Invertible (S.H * S.H.transpose) :=
  (S.H * S.H.transpose).invertibleOfIsUnitDet
    ((Matrix.isUnit_iff_isUnit_det _).mp (HHt_posDef S).isUnit)

/-- The Gram matrix `(B₀H)(B₀H)ᵀ = B₀ (H Hᵀ) B₀ᵀ` is invertible (product of invertibles). -/
noncomputable instance B0H_gram_invertible (S : Solution d p K) :
    Invertible ((S.B0 * S.H) * (S.B0 * S.H).transpose) := by
  rw [Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc S.B0]
  exact ((B0_invertible S).mul (HHt_invertible S)).mul
    (inferInstanceAs (Invertible S.B0.transpose))

/-- `R := Hᵀ (H Hᵀ)⁻¹` is a right inverse of `H`: `H R = 1`. -/
theorem H_mul_rightInv (S : Solution d p K) :
    S.H * (S.H.transpose * (S.H * S.H.transpose)⁻¹) = 1 := by
  rw [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible]

/-- `L := (H Hᵀ)⁻¹ H` is a left inverse of `Hᵀ`: `L Hᵀ = 1`. -/
theorem leftInv_mul_Ht (S : Solution d p K) :
    ((S.H * S.H.transpose)⁻¹ * S.H) * S.H.transpose = 1 := by
  rw [Matrix.mul_assoc, Matrix.inv_mul_of_invertible]

/-! ### (L1) Recovery of the mixing change-of-basis `M`

From `Θ₀ = Θ₀'`, the two mixing matrices `H`, `H'` have the same rowspace, so
`H' = M H` for an invertible `M`.  The cleanest derivation avoids any dimension count:
writing `C = B₀ H` (full row rank, `Θ₀ = Cᵀ C`), the Gram `C Cᵀ` is invertible, so
`H = B₀⁻¹ (C Cᵀ)⁻¹ C · Θ₀`, i.e. every row of `H` is an explicit `vecMul` of `Θ₀`.
Applied to the primed system and substituting `Θ₀' = Θ₀`, this exhibits `H' = M H`. -/

/-- **The recovery identity `H = W Θ₀`.**  With `C = B₀ H` and `Θ₀ = Cᵀ C`, the matrix
`W = B₀⁻¹ (C Cᵀ)⁻¹ C` satisfies `W Θ₀ = H`. -/
theorem H_eq_recover_mul_Theta0 (S : Solution d p K) :
    (S.B0⁻¹ * ((S.B0 * S.H) * (S.B0 * S.H).transpose)⁻¹ * (S.B0 * S.H)) * S.Theta0 = S.H := by
  have hΘ : S.Theta0 = (S.B0 * S.H).transpose * (S.B0 * S.H) := by
    simp only [Solution.Theta0, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hΘ]
  set G := (S.B0 * S.H) * (S.B0 * S.H).transpose with hG
  rw [Matrix.mul_assoc (S.B0⁻¹ * G⁻¹), ← Matrix.mul_assoc (S.B0 * S.H), ← hG,
    ← Matrix.mul_assoc, Matrix.mul_assoc S.B0⁻¹, Matrix.inv_mul_of_invertible, Matrix.mul_one,
    ← Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.one_mul]

/-- **(L1) The change-of-basis matrix.**  There is an invertible `M` with `H' = M H`.
`M` is built from the recovery identity for `H'` (`H' = W' Θ₀'`) by substituting
`Θ₀' = Θ₀ = Hᵀ B₀ᵀ B₀ H`, giving `H' = (W' Hᵀ B₀ᵀ B₀) H`.  Invertibility follows from
the symmetric matrix `N` with `H = N H'` by right-cancelling the full-row-rank `H`/`H'`. -/
theorem exists_change_of_basis (S S' : Solution d p K) (hΘ0 : S.Theta0 = S'.Theta0) :
    ∃ M : Matrix (Fin d) (Fin d) ℝ, IsUnit M ∧ S'.H = M * S.H := by
  -- `M := W' Hᵀ B₀ᵀ B₀` from `H' = W' Θ₀' = W' Θ₀ = W' (Hᵀ B₀ᵀ B₀ H)`.
  set W' := S'.B0⁻¹ * ((S'.B0 * S'.H) * (S'.B0 * S'.H).transpose)⁻¹ * (S'.B0 * S'.H) with hW'
  set N' := S.B0⁻¹ * ((S.B0 * S.H) * (S.B0 * S.H).transpose)⁻¹ * (S.B0 * S.H) with hN'
  have hH' : S'.H = (W' * S.H.transpose * S.B0.transpose * S.B0) * S.H := by
    have h1 : W' * S'.Theta0 = S'.H := H_eq_recover_mul_Theta0 S'
    rw [← hΘ0, Solution.Theta0] at h1
    rw [← h1]
    simp only [Matrix.mul_assoc]
  have hH : S.H = (N' * S'.H.transpose * S'.B0.transpose * S'.B0) * S'.H := by
    have h1 : N' * S.Theta0 = S.H := H_eq_recover_mul_Theta0 S
    rw [hΘ0, Solution.Theta0] at h1
    rw [← h1]
    simp only [Matrix.mul_assoc]
  set M := W' * S.H.transpose * S.B0.transpose * S.B0 with hM
  set N := N' * S'.H.transpose * S'.B0.transpose * S'.B0 with hN
  refine ⟨M, ?_, hH'⟩
  -- `M` is a unit: `M N = 1` via right-cancellation by the full-row-rank `H`.
  have hMN : M * N = 1 := by
    have hcomp : (M * N) * S'.H = (1 : Matrix (Fin d) (Fin d) ℝ) * S'.H := by
      rw [Matrix.mul_assoc, ← hH, ← hH', Matrix.one_mul]
    -- right-cancel `H'` (it has right inverse `H'ᵀ (H' H'ᵀ)⁻¹`).
    have hrcancel : ∀ A B : Matrix (Fin d) (Fin d) ℝ, A * S'.H = B * S'.H → A = B := by
      intro A B hAB
      have h2 := congrArg (fun X => X * (S'.H.transpose * (S'.H * S'.H.transpose)⁻¹)) hAB
      simp only [Matrix.mul_assoc] at h2
      rwa [H_mul_rightInv S', Matrix.mul_one, Matrix.mul_one] at h2
    exact hrcancel _ _ hcomp
  exact IsUnit.of_mul_eq_one N hMN

/-! ### (L2) Cancellation: the `d×d` Gram identity in each context

From `Θₖ = Θₖ'` and `H' = M H`, cancelling `Hᵀ` on the left and `H` on the right gives
the `d × d` identity `BₖᵀBₖ = (B'ₖ M)ᵀ (B'ₖ M)`. -/

/-- Left-cancel `Hᵀ` and right-cancel `H` in `Hᵀ X H = Hᵀ Y H`.  `H` has full row rank,
so `Hᵀ` has a left inverse and `H` a right inverse. -/
theorem cancel_Ht_H (S : Solution d p K) {X Y : Matrix (Fin d) (Fin d) ℝ}
    (h : S.H.transpose * X * S.H = S.H.transpose * Y * S.H) : X = Y := by
  set R := S.H.transpose * (S.H * S.H.transpose)⁻¹ with hR
  set L := (S.H * S.H.transpose)⁻¹ * S.H with hL
  -- right-cancel `H`: multiply by `R` on the right.
  have hr : S.H.transpose * X = S.H.transpose * Y := by
    have h2 := congrArg (fun Z => Z * R) h
    simp only [Matrix.mul_assoc] at h2
    rwa [H_mul_rightInv S, Matrix.mul_one, Matrix.mul_one] at h2
  -- left-cancel `Hᵀ`: multiply by `L` on the left.
  have h3 := congrArg (fun Z => L * Z) hr
  simp only [← Matrix.mul_assoc] at h3
  rwa [leftInv_mul_Ht S, Matrix.one_mul, Matrix.one_mul] at h3

/-- **(L2) The per-context Gram identity.**  Given `H' = M H` and `Θₖ = Θₖ'` for the
observational (`B₀`/`B'₀`) and interventional (`Bₖ`/`B'ₖ`) matrices, the `d × d` Gram
identity `BᵀB = (B' M)ᵀ (B' M)` holds. -/
theorem gram_identity (S S' : Solution d p K) {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : S'.H = M * S.H) {B B' : Matrix (Fin d) (Fin d) ℝ}
    (hΘ : S.H.transpose * B.transpose * B * S.H
      = S'.H.transpose * B'.transpose * B' * S'.H) :
    B.transpose * B = (B' * M).transpose * (B' * M) := by
  apply cancel_Ht_H S
  have e1 : S.H.transpose * (B.transpose * B) * S.H
      = S'.H.transpose * B'.transpose * B' * S'.H := by
    rw [← hΘ]; simp only [Matrix.mul_assoc]
  rw [e1, hM]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

/-! ### Latent-level structural lemmas (sub-lemmas (A)–(D) of the roadmap)

These work entirely with `d × d` matrices and feed the orthogonal-correctness core.  They
isolate the **algebraic** content of perfect single-node interventions: the rank-one
perturbation `Bₖ − B₀ = e_{iₖ} cₖᵀ`, the orthogonality of the transition factor
`Oₖ = B'ₖ M Bₖ⁻¹`, and (the part that survives into the conclusion) the read-off of the
permuted intervention targets `i'ₖ = σ(iₖ)`. -/

/-- The perturbation row `cₖ : Fin d → ℝ` of a perfect intervention:
`cₖ j = λₖ (eᵢₖ)ⱼ − (B₀)_{iₖ,j}`, so that `Bₖ = B₀ + e_{iₖ} cₖᵀ`. -/
def cvec (S : Solution d p K) (k : Fin K) : Fin d → ℝ :=
  fun j => S.lam k * stdVec d (S.target k) j - S.B0 (S.target k) j

/-- **Rank-one perturbation.**  `Bₖ − B₀ = e_{iₖ} cₖᵀ` (`Matrix.vecMulVec`): a perfect
single-node intervention rewrites only the target row of `B₀`. -/
theorem Bint_sub_B0 (S : Solution d p K) (k : Fin K) :
    S.Bint k - S.B0 = Matrix.vecMulVec (stdVec d (S.target k)) (cvec S k) := by
  rw [S.hInt k, add_sub_cancel_left]; rfl

/-- **(C, target-row form / sub-lemma (B)).**  The perturbation row is non-degenerate
exactly when the intervention changes the precision matrix.  Under `Θₖ ≠ Θ₀`, `cₖ ≠ 0`
(equivalently `Bₖ ≠ B₀`): if `cₖ = 0` then `Bₖ = B₀`, hence `Θₖ = Θ₀`. -/
theorem cvec_ne_zero (S : Solution d p K) (k : Fin K) (hk : S.Theta k ≠ S.Theta0) :
    cvec S k ≠ 0 := by
  intro hc
  apply hk
  have hBeq : S.Bint k = S.B0 := by
    have := Bint_sub_B0 S k
    rw [hc, Matrix.vecMulVec_zero] at this
    exact sub_eq_zero.mp this
  rw [Solution.Theta, Solution.Theta0, hBeq]

/-- **(B) Target row of `Bₖ`.**  `(Bₖ)ᵀ *ᵥ e_{iₖ} = λₖ • e_{iₖ}`: the `iₖ`-th row of a
perfect-intervention matrix is `λₖ e_{iₖ}ᵀ` (the intervention zeroes the parent entries and
sets the diagonal to `λₖ`). -/
theorem Bint_transpose_mulVec_target (S : Solution d p K) (k : Fin K) :
    (S.Bint k).transpose *ᵥ stdVec d (S.target k) = (S.lam k) • stdVec d (S.target k) := by
  funext j
  rw [Matrix.mulVec_transpose, Matrix.vecMul_eq_sum]
  simp only [stdVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_single (S.target k)]
  · by_cases hj : j = S.target k
    · rw [hj, S.hInt k]; simp [Matrix.add_apply, Matrix.vecMulVec_apply, stdVec]
    · simp only [if_neg hj, mul_zero]
      rw [S.hInt k]; simp [Matrix.add_apply, Matrix.vecMulVec_apply, stdVec, hj]
  · intro x _ hx; simp [if_neg hx]
  · intro hx; exact absurd (Finset.mem_univ _) hx

/-- **(C) Latent key identity.**  At the `d × d` (latent) level the difference of Gram
matrices is a difference of two rank-one (outer-product) matrices:
`BₖᵀBₖ − B₀ᵀB₀ = λₖ² (e_{iₖ} e_{iₖ}ᵀ) − wₖ wₖᵀ` where `wₖ = B₀ᵀ *ᵥ e_{iₖ}` is the `iₖ`-th
row of `B₀` (supported on `Pa(iₖ)`).  This is the latent analogue of `key_identity`, and
the structural engine of the orthogonal-correctness core. -/
theorem latent_key_identity (S : Solution d p K) (k : Fin K) :
    (S.Bint k).transpose * S.Bint k - S.B0.transpose * S.B0
      = (S.lam k) ^ 2 • Matrix.vecMulVec (stdVec d (S.target k)) (stdVec d (S.target k))
        - Matrix.vecMulVec (S.B0.transpose *ᵥ stdVec d (S.target k))
            (S.B0.transpose *ᵥ stdVec d (S.target k)) := by
  -- Off-target rows of `Bₖ` agree with `B₀`, so the rank-one decompositions cancel except
  -- in the target row (mirrors the latent step inside `key_identity`).
  set i := S.target k with hi
  have hrow : ∀ l : Fin d, l ≠ i →
      ((S.Bint k).transpose *ᵥ stdVec d l) = (S.B0.transpose *ᵥ stdVec d l) := by
    intro l hl
    have hl' : l ≠ S.target k := hi ▸ hl
    funext a
    rw [S.hInt k]
    simp only [stdVec, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.transpose_apply,
      Matrix.add_apply, Matrix.vecMulVec_apply, Pi.single_eq_of_ne hl', zero_mul, add_zero]
  rw [fact_transpose_mul (S.Bint k), fact_transpose_mul S.B0,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hcancel :
      (∑ l ∈ Finset.univ.erase i, Matrix.vecMulVec
          ((S.Bint k).transpose *ᵥ stdVec d l) ((S.Bint k).transpose *ᵥ stdVec d l))
        = ∑ l ∈ Finset.univ.erase i,
          Matrix.vecMulVec (S.B0.transpose *ᵥ stdVec d l) (S.B0.transpose *ᵥ stdVec d l) := by
    refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [hrow l (Finset.ne_of_mem_erase hl)]
  rw [hcancel, Bint_transpose_mulVec_target, Matrix.vecMulVec_smul, Matrix.smul_vecMulVec,
    smul_smul, ← pow_two]
  abel

/-- **(D) The transition factor is orthogonal.**  From the per-context Gram identity
`BₖᵀBₖ = (B'ₖ M)ᵀ(B'ₖ M)` and invertibility, `Oₖ = B'ₖ M Bₖ⁻¹` satisfies `Oₖᵀ Oₖ = 1`. -/
theorem transition_orthogonal (S S' : Solution d p K) {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : S'.H = M * S.H) {B B' : Matrix (Fin d) (Fin d) ℝ} [Invertible B] [Invertible (B' * M)]
    (hΘ : S.H.transpose * B.transpose * B * S.H
      = S'.H.transpose * B'.transpose * B' * S'.H) :
    ((B' * M) * B⁻¹)ᵀ * ((B' * M) * B⁻¹) = 1 :=
  gram_to_orthogonal (gram_identity S S' hM hΘ)

/-! ### (R1) Latent Gram-difference transport

The per-context Gram identity (`gram_identity`) says `Bₖᵀ Bₖ = Mᵀ B'ₖᵀ B'ₖ M` for every
context (including `k = 0`).  Subtracting the observational equation gives the **latent
Gram-difference transport**: `Δₖ = Mᵀ Δ'ₖ M`, where `Δₖ = Bₖᵀ Bₖ − B₀ᵀ B₀` (and `Δ'ₖ`
likewise).  This is the algebraic content of (R1): the change-of-basis `M` conjugates the
primed Gram differences into the unprimed ones. -/

/-- The per-context Gram identity in the symmetric form `BᵀB = Mᵀ B'ᵀ B' M` (the conjugation
form of `gram_identity`). -/
theorem gram_identity_conj (S S' : Solution d p K) {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : S'.H = M * S.H) {B B' : Matrix (Fin d) (Fin d) ℝ}
    (hΘ : S.H.transpose * B.transpose * B * S.H
      = S'.H.transpose * B'.transpose * B' * S'.H) :
    B.transpose * B = M.transpose * (B'.transpose * B') * M := by
  rw [gram_identity S S' hM hΘ, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- **(R1) Latent Gram-difference transport.**  `Bₖᵀ Bₖ − B₀ᵀ B₀ = Mᵀ (B'ₖᵀ B'ₖ − B'₀ᵀ B'₀) M`.
Subtracting the observational conjugation identity from the `k`-th one. -/
theorem gram_diff_transport (S S' : Solution d p K) {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : S'.H = M * S.H) (hΘ0 : S.Theta0 = S'.Theta0) (hΘ : ∀ k, S.Theta k = S'.Theta k)
    (k : Fin K) :
    (S.Bint k).transpose * S.Bint k - S.B0.transpose * S.B0
      = M.transpose * ((S'.Bint k).transpose * S'.Bint k - (S'.B0).transpose * S'.B0) * M := by
  have hk : (S.Bint k).transpose * S.Bint k
      = M.transpose * ((S'.Bint k).transpose * S'.Bint k) * M := by
    refine gram_identity_conj S S' hM ?_
    have := hΘ k
    simp only [Solution.Theta, Matrix.mul_assoc] at this ⊢
    exact this
  have h0 : S.B0.transpose * S.B0
      = M.transpose * ((S'.B0).transpose * S'.B0) * M := by
    refine gram_identity_conj S S' hM ?_
    simp only [Solution.Theta0, Matrix.mul_assoc] at hΘ0 ⊢
    exact hΘ0
  rw [hk, h0, Matrix.mul_sub, Matrix.sub_mul]

/-- `Mᵀ (u vᵀ) M = (Mᵀ u)(Mᵀ v)ᵀ` (conjugation of a rank-one matrix by `Mᵀ · M`). -/
theorem conj_vecMulVec_transpose {q : ℕ} (M : Matrix (Fin q) (Fin q) ℝ) (u v : Fin q → ℝ) :
    M.transpose * Matrix.vecMulVec u v * M
      = Matrix.vecMulVec (M.transpose *ᵥ u) (M.transpose *ᵥ v) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose]

/-- **(R1+C) The central rank-≤2 equation.**  Combining the Gram-difference transport
`Δₖ = Mᵀ Δ'ₖ M` (`gram_diff_transport`) with the latent key identity (C) on both sides,
`Δₖ = λₖ²(eₖeₖᵀ) − wₖwₖᵀ` and `Δ'ₖ = λ'ₖ²(e'ₖe'ₖᵀ) − w'ₖw'ₖᵀ`, gives the rank-≤2 identity
in fully outer-product form, with the primed outer products transported by `Mᵀ`:
`λₖ²(eₖeₖᵀ) − wₖwₖᵀ = λ'ₖ²((Mᵀe'ₖ)(Mᵀe'ₖ)ᵀ) − (Mᵀw'ₖ)(Mᵀw'ₖ)ᵀ`. -/
theorem central_rank2_eq (S S' : Solution d p K) {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : S'.H = M * S.H) (hΘ0 : S.Theta0 = S'.Theta0) (hΘ : ∀ k, S.Theta k = S'.Theta k)
    (k : Fin K) :
    (S.lam k) ^ 2 • Matrix.vecMulVec (stdVec d (S.target k)) (stdVec d (S.target k))
        - Matrix.vecMulVec (S.B0.transpose *ᵥ stdVec d (S.target k))
            (S.B0.transpose *ᵥ stdVec d (S.target k))
      = (S'.lam k) ^ 2 • Matrix.vecMulVec (M.transpose *ᵥ stdVec d (S'.target k))
            (M.transpose *ᵥ stdVec d (S'.target k))
        - Matrix.vecMulVec (M.transpose *ᵥ (S'.B0.transpose *ᵥ stdVec d (S'.target k)))
            (M.transpose *ᵥ (S'.B0.transpose *ᵥ stdVec d (S'.target k))) := by
  have htrans := gram_diff_transport S S' hM hΘ0 hΘ k
  rw [latent_key_identity, latent_key_identity] at htrans
  rw [htrans, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    conj_vecMulVec_transpose, conj_vecMulVec_transpose]

/-- `Mᵀ *ᵥ eᵢ` is the `i`-th **row** of `M`, viewed as a vector: `(Mᵀ *ᵥ eᵢ) j = Mᵢⱼ`.
This is the bridge that turns the transported outer products of `central_rank2_eq` into
statements about the rows of `M`. -/
theorem transpose_mulVec_stdVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    M.transpose *ᵥ stdVec n i = (fun j => M i j) := by
  funext j
  rw [Matrix.mulVec_transpose, stdVec, Matrix.single_vecMul, one_smul, Matrix.row_apply]

/-- **(R3 ingredient) The `iₖ`-th row of `B₀` at a source.**  If `iₖ` is a *source* node
(no parents: `(B₀)_{iₖ,j} = 0` for every `j ≠ iₖ`), then `wₖ = B₀ᵀ *ᵥ e_{iₖ} = β e_{iₖ}`
with `β = (B₀)_{iₖ,iₖ} > 0`.  This collapses the latent key identity (C) to the rank-one
`Δₖ = (λₖ² − β²) e_{iₖ} e_{iₖ}ᵀ`, the base case of the monomial induction (R3): the
transported equation then forces the `i'ₖ`-th row of `M` to be a multiple of `e_{iₖ}`. -/
theorem B0_source_row (S : Solution d p K) (i : Fin d)
    (hsrc : ∀ j, j ≠ i → S.B0 i j = 0) :
    S.B0.transpose *ᵥ stdVec d i = (S.B0 i i) • stdVec d i := by
  funext j
  rw [Matrix.mulVec_transpose, Matrix.vecMul_eq_sum]
  simp only [stdVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, one_mul]
    by_cases hj : j = i
    · subst hj; rw [Pi.single_eq_same, mul_one]
    · rw [Pi.single_eq_of_ne hj, mul_zero]; exact hsrc j hj
  · intro x _ hx; rw [Pi.single_eq_of_ne hx, zero_mul]
  · intro hx; exact absurd (Finset.mem_univ _) hx

/-! ### Reading off the permuted targets from the collapse (sub-lemma feeding the core)

If the orthogonal-correctness core has produced a single permutation `σ` and row-sign
diagonal `ν` with `B'ₖ M = diagonal ν permMat σ Bₖ` in every context (including `k = 0`),
then subtracting the observational equation isolates the rank-one rows and forces
`i'ₖ = σ(iₖ)`. -/

/-- `permMat σ *ᵥ eᵢ = e_{σ i}`: the permutation matrix sends the `i`-th basis vector to the
`σ(i)`-th. -/
theorem permMat_mulVec_stdVec (σ : Equiv.Perm (Fin d)) (i : Fin d) :
    permMat σ *ᵥ stdVec d i = stdVec d (σ i) := by
  rw [stdVec, Matrix.mulVec_single_one]
  funext a
  simp only [permMat, Matrix.col_apply, Matrix.of_apply, stdVec, Pi.single_apply]

/-- A signed permutation matrix sends `eᵢ` to the signed basis vector
`ν (σ i) • e_{σ i}`. -/
theorem diag_permMat_mulVec_stdVec (σ : Equiv.Perm (Fin d)) (ν : Fin d → ℝ) (i : Fin d) :
    (Matrix.diagonal ν * permMat σ) *ᵥ stdVec d i =
      (ν (σ i)) • stdVec d (σ i) := by
  rw [← Matrix.mulVec_mulVec, permMat_mulVec_stdVec]
  funext a
  rw [Matrix.mulVec_diagonal]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases ha : a = σ i
  · subst ha
    rw [stdVec, Pi.single_eq_same, mul_one]
  · rw [stdVec, Pi.single_eq_of_ne ha, mul_zero, mul_zero]

/-- Left multiplication by a diagonal matrix rescales rows. -/
private theorem diagonal_mul_apply (ν : Fin d → ℝ) (X : Matrix (Fin d) (Fin d) ℝ)
    (a b : Fin d) :
    (Matrix.diagonal ν * X) a b = ν a * X a b := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single a]
  · rw [Matrix.diagonal_apply_eq]
  · intro x _ hx; rw [Matrix.diagonal_apply_ne _ (Ne.symm hx), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Signed target read-off.**  Suppose the collapse holds for context `k` and the
observational context:
`B'ₖ M = diagonal ν permMat σ Bₖ` and `B'₀ M = diagonal ν permMat σ B₀`, with `Θₖ ≠ Θ₀`.
Then the primed target equals the relabelled target: `i'ₖ = σ(iₖ)`.

Subtracting the two relations gives `(B'ₖ − B'₀) M = diagonal ν permMat σ (Bₖ − B₀)`,
i.e. `e_{i'ₖ} (Mᵀ c'ₖ)ᵀ = (ν_{σ iₖ} e_{σ iₖ}) cₖᵀ` as rank-one matrices.  Since
`cₖ ≠ 0` (`cvec_ne_zero`) and `ν_{σ iₖ} ≠ 0`, comparing the `(σ iₖ, ·)` row forces the
basis index `i'ₖ` to be `σ iₖ`. -/
theorem target_readoff (S S' : Solution d p K) {M : Matrix (Fin d) (Fin d) ℝ}
    {σ : Equiv.Perm (Fin d)} {ν : Fin d → ℝ} (k : Fin K) (hk : S.Theta k ≠ S.Theta0)
    (hν : ∀ i, ν i = 1 ∨ ν i = -1)
    (hBk : S'.Bint k * M = Matrix.diagonal ν * permMat σ * S.Bint k)
    (hB0 : S'.B0 * M = Matrix.diagonal ν * permMat σ * S.B0) :
    S'.target k = σ (S.target k) := by
  -- Subtract the observational relation:
  -- `(B'ₖ − B'₀) M = diagonal ν permMat σ (Bₖ − B₀)`.
  have hsub : (S'.Bint k - S'.B0) * M =
      Matrix.diagonal ν * permMat σ * (S.Bint k - S.B0) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, hBk, hB0]
  -- Rewrite both sides as rank-one (outer-product) matrices.
  rw [Bint_sub_B0, Bint_sub_B0, Matrix.vecMulVec_mul, Matrix.mul_vecMulVec,
    diag_permMat_mulVec_stdVec] at hsub
  -- Pick an index `b` where `cₖ` is non-zero.
  obtain ⟨b, hb⟩ := Function.ne_iff.mp (cvec_ne_zero S k hk)
  rw [Pi.zero_apply] at hb
  -- Compare the `(σ iₖ, b)` entries of the two rank-one matrices.
  have hentry := congrFun (congrFun hsub (σ (S.target k))) b
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, stdVec,
    Pi.single_eq_same] at hentry
  have hνne : ν (σ (S.target k)) ≠ 0 := by
    rcases hν (σ (S.target k)) with h | h <;> rw [h] <;> norm_num
  -- LHS `(e_{i'ₖ})_{σ iₖ} · (Mᵀ c'ₖ)_b = (cₖ)_b ≠ 0` forces `(e_{i'ₖ})_{σ iₖ} ≠ 0`.
  by_contra hne
  rw [Pi.single_eq_of_ne (fun h => hne h.symm), zero_mul] at hentry
  exact (mul_ne_zero (mul_ne_zero hνne one_ne_zero) hb) hentry.symm

/-! ### (S1) The SUM TRICK — diagonalizing the unprimed Gram differences

Summing the latent key identity (C) over a *section* `kof` of the (surjective) target map
`S.target` collapses the unprimed side to `diagonal(d) − B₀ᵀB₀` with `d n = (λ_{kof n})² > 0`:
the rank-one targets `e_{i_{kof n}} = e_n` sum to the identity-weighting `diagonal(d)`, and the
rows `w_n = B₀ᵀ e_n` sum, via `fact_transpose_mul`, to `B₀ᵀB₀`. -/

/-- `∑ n, (c n) • (e_n e_nᵀ) = diagonal c` (the rank-one standard-basis outer products sum to a
diagonal matrix). -/
theorem sum_smul_vecMulVec_stdVec_eq_diagonal {n : ℕ} (c : Fin n → ℝ) :
    (∑ i, (c i) • Matrix.vecMulVec (stdVec n i) (stdVec n i)) = Matrix.diagonal c := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, stdVec,
    Pi.single_apply, smul_eq_mul, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single a]
  · by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  · intro x _ hx; simp [Ne.symm hx]
  · intro hx; exact absurd (Finset.mem_univ a) hx

/-- **(S1) The unprimed SUM TRICK.**  Let `kof` be a section of the surjective target map
(`S.target (kof n) = n`).  Summing the latent key identity over `kof` gives
`∑ₙ (B_{kof n}ᵀ B_{kof n} − B₀ᵀB₀) = diagonal(d) − B₀ᵀB₀` with `d n = (λ_{kof n})²`. -/
theorem sum_latent_diff_unprimed (S : Solution d p K)
    (kof : Fin d → Fin K) (hkof : ∀ n, S.target (kof n) = n) :
    (∑ n, ((S.Bint (kof n)).transpose * S.Bint (kof n) - S.B0.transpose * S.B0))
      = Matrix.diagonal (fun n => (S.lam (kof n)) ^ 2) - S.B0.transpose * S.B0 := by
  -- Rewrite each summand by the latent key identity.
  have hterm : ∀ n,
      (S.Bint (kof n)).transpose * S.Bint (kof n) - S.B0.transpose * S.B0
        = (S.lam (kof n)) ^ 2 • Matrix.vecMulVec (stdVec d n) (stdVec d n)
          - Matrix.vecMulVec (S.B0.transpose *ᵥ stdVec d n) (S.B0.transpose *ᵥ stdVec d n) := by
    intro n
    rw [latent_key_identity S (kof n), hkof n]
  rw [Finset.sum_congr rfl (fun n _ => hterm n)]
  have hdistrib :
      (∑ n, ((S.lam (kof n)) ^ 2 • Matrix.vecMulVec (stdVec d n) (stdVec d n)
          - Matrix.vecMulVec (S.B0.transpose *ᵥ stdVec d n) (S.B0.transpose *ᵥ stdVec d n)))
        = (∑ n, (S.lam (kof n)) ^ 2 • Matrix.vecMulVec (stdVec d n) (stdVec d n))
          - ∑ n, Matrix.vecMulVec (S.B0.transpose *ᵥ stdVec d n) (S.B0.transpose *ᵥ stdVec d n) :=
    Finset.sum_sub_distrib ..
  rw [hdistrib, sum_smul_vecMulVec_stdVec_eq_diagonal, ← fact_transpose_mul S.B0]

/-- **(S1') The primed SUM TRICK with reindexed targets.**  If the primed targets along
the same section `kof` are `σ n`, summing the primed latent key identities gives a diagonal
whose `m`-th entry comes from the unique preimage `σ.symm m`. -/
private theorem sum_latent_diff_primed_reindexed (S' : Solution d p K)
    (kof : Fin d → Fin K) (σ : Equiv.Perm (Fin d))
    (hσtarget : ∀ n, S'.target (kof n) = σ n) :
    (∑ n, ((S'.Bint (kof n)).transpose * S'.Bint (kof n)
        - S'.B0.transpose * S'.B0))
      = Matrix.diagonal (fun m => (S'.lam (kof (σ.symm m))) ^ 2)
        - S'.B0.transpose * S'.B0 := by
  have hterm : ∀ n,
      (S'.Bint (kof n)).transpose * S'.Bint (kof n) - S'.B0.transpose * S'.B0
        = (S'.lam (kof n)) ^ 2 • Matrix.vecMulVec (stdVec d (σ n)) (stdVec d (σ n))
          - Matrix.vecMulVec (S'.B0.transpose *ᵥ stdVec d (σ n))
              (S'.B0.transpose *ᵥ stdVec d (σ n)) := by
    intro n
    rw [latent_key_identity S' (kof n), hσtarget n]
  rw [Finset.sum_congr rfl (fun n _ => hterm n)]
  have hdistrib :
      (∑ n, ((S'.lam (kof n)) ^ 2 • Matrix.vecMulVec (stdVec d (σ n)) (stdVec d (σ n))
          - Matrix.vecMulVec (S'.B0.transpose *ᵥ stdVec d (σ n))
              (S'.B0.transpose *ᵥ stdVec d (σ n))))
        = (∑ n, (S'.lam (kof n)) ^ 2 • Matrix.vecMulVec (stdVec d (σ n)) (stdVec d (σ n)))
          - ∑ n, Matrix.vecMulVec (S'.B0.transpose *ᵥ stdVec d (σ n))
              (S'.B0.transpose *ᵥ stdVec d (σ n)) :=
    Finset.sum_sub_distrib ..
  rw [hdistrib]
  have hdiag :
      (∑ n, (S'.lam (kof n)) ^ 2 • Matrix.vecMulVec (stdVec d (σ n)) (stdVec d (σ n)))
        = ∑ m, (S'.lam (kof (σ.symm m))) ^ 2 • Matrix.vecMulVec (stdVec d m) (stdVec d m) := by
    let f : Fin d → Matrix (Fin d) (Fin d) ℝ :=
      fun m => (S'.lam (kof (σ.symm m))) ^ 2 • Matrix.vecMulVec (stdVec d m) (stdVec d m)
    simpa [f] using (Equiv.sum_comp σ f)
  have hgram :
      (∑ n, Matrix.vecMulVec (S'.B0.transpose *ᵥ stdVec d (σ n))
              (S'.B0.transpose *ᵥ stdVec d (σ n)))
        = ∑ m, Matrix.vecMulVec (S'.B0.transpose *ᵥ stdVec d m)
              (S'.B0.transpose *ᵥ stdVec d m) := by
    let f : Fin d → Matrix (Fin d) (Fin d) ℝ :=
      fun m => Matrix.vecMulVec (S'.B0.transpose *ᵥ stdVec d m)
        (S'.B0.transpose *ᵥ stdVec d m)
    simpa [f] using (Equiv.sum_comp σ f)
  rw [hdiag, hgram, sum_smul_vecMulVec_stdVec_eq_diagonal, ← fact_transpose_mul S'.B0]

/-- Summing the per-context Gram-difference transport pulls the common conjugation
`Mᵀ · _ · M` outside the finite sum. -/
private theorem sum_gram_diff_transport (S S' : Solution d p K)
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : S'.H = M * S.H)
    (hΘ0 : S.Theta0 = S'.Theta0) (hΘ : ∀ k, S.Theta k = S'.Theta k)
    (kof : Fin d → Fin K) :
    (∑ n, ((S.Bint (kof n)).transpose * S.Bint (kof n) - S.B0.transpose * S.B0))
      = M.transpose *
          (∑ n, ((S'.Bint (kof n)).transpose * S'.Bint (kof n)
            - S'.B0.transpose * S'.B0)) * M := by
  calc
    (∑ n, ((S.Bint (kof n)).transpose * S.Bint (kof n) - S.B0.transpose * S.B0))
        = ∑ n, M.transpose *
            (((S'.Bint (kof n)).transpose * S'.Bint (kof n)
              - S'.B0.transpose * S'.B0)) * M := by
          exact Finset.sum_congr rfl
            (fun n _ => gram_diff_transport S S' hM hΘ0 hΘ (kof n))
    _ = M.transpose *
          (∑ n, ((S'.Bint (kof n)).transpose * S'.Bint (kof n)
            - S'.B0.transpose * S'.B0)) * M := by
          rw [Finset.mul_sum, Finset.sum_mul]

/-- **(S1+R1) The SUM TRICK after transport.**  The summed transport identity cancels the
observational Gram term and leaves a diagonal conjugation. -/
private theorem diagonal_conj_from_sum_trick (S S' : Solution d p K)
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : S'.H = M * S.H)
    (hΘ0 : S.Theta0 = S'.Theta0) (hΘ : ∀ k, S.Theta k = S'.Theta k)
    (kof : Fin d → Fin K) (hkof : ∀ n, S.target (kof n) = n)
    (σ : Equiv.Perm (Fin d)) (hσtarget : ∀ n, S'.target (kof n) = σ n) :
    M.transpose * Matrix.diagonal (fun m => (S'.lam (kof (σ.symm m))) ^ 2) * M
      = Matrix.diagonal (fun n => (S.lam (kof n)) ^ 2) := by
  have hunprimed := sum_latent_diff_unprimed S kof hkof
  have hprimed := sum_latent_diff_primed_reindexed S' kof σ hσtarget
  have htransport := sum_gram_diff_transport S S' hM hΘ0 hΘ kof
  have h0 : S.B0.transpose * S.B0
      = M.transpose * (S'.B0.transpose * S'.B0) * M := by
    refine gram_identity_conj S S' hM ?_
    simp only [Solution.Theta0, Matrix.mul_assoc] at hΘ0 ⊢
    exact hΘ0
  have hsub :
      Matrix.diagonal (fun n => (S.lam (kof n)) ^ 2) - S.B0.transpose * S.B0
        = M.transpose * Matrix.diagonal (fun m => (S'.lam (kof (σ.symm m))) ^ 2) * M
          - S.B0.transpose * S.B0 := by
    calc
      Matrix.diagonal (fun n => (S.lam (kof n)) ^ 2) - S.B0.transpose * S.B0
          = (∑ n, ((S.Bint (kof n)).transpose * S.Bint (kof n)
              - S.B0.transpose * S.B0)) := hunprimed.symm
      _ = M.transpose *
            (∑ n, ((S'.Bint (kof n)).transpose * S'.Bint (kof n)
              - S'.B0.transpose * S'.B0)) * M := htransport
      _ = M.transpose *
            (Matrix.diagonal (fun m => (S'.lam (kof (σ.symm m))) ^ 2)
              - S'.B0.transpose * S'.B0) * M := by rw [hprimed]
      _ = M.transpose * Matrix.diagonal (fun m => (S'.lam (kof (σ.symm m))) ^ 2) * M
          - S.B0.transpose * S.B0 := by
            rw [Matrix.mul_sub, Matrix.sub_mul, h0]
  exact (sub_left_inj.mp hsub).symm

/-! ### (S2) Orthogonalizing the change-of-basis from a diagonal conjugation identity

If `Mᵀ diag(d') M = diag(d)` with `d, d' > 0`, then `O := diag(√d') M diag(1/√d)` is
orthogonal (`Oᵀ O = 1`).  This is the algebraic step turning the diagonalized SUM TRICK output
into an orthogonality statement on a *rescaled* `M`. -/

/-- **(S2) Diagonal conjugation ⟹ orthogonal rescaling.**  From `Mᵀ diag(d') M = diag(d)` with
`d, d'` strictly positive, the matrix `O = diag(fun i => √(d' i)) * M * diag(fun i => (√(d i))⁻¹)`
is orthogonal: `Oᵀ O = 1`. -/
theorem orthogonal_of_diag_conj {q : ℕ} {M : Matrix (Fin q) (Fin q) ℝ} {dv dv' : Fin q → ℝ}
    (hd : ∀ i, 0 < dv i) (hd' : ∀ i, 0 < dv' i)
    (hconj : M.transpose * Matrix.diagonal dv' * M = Matrix.diagonal dv) :
    (Matrix.diagonal (fun i => Real.sqrt (dv' i)) * M
        * Matrix.diagonal (fun i => (Real.sqrt (dv i))⁻¹)).transpose
      * (Matrix.diagonal (fun i => Real.sqrt (dv' i)) * M
        * Matrix.diagonal (fun i => (Real.sqrt (dv i))⁻¹)) = 1 := by
  -- `diag(√d')ᵀ diag(√d') = diag(d')` and `diag(1/√d) diag(d) diag(1/√d) = 1`.
  have hsqrt' : Matrix.diagonal (fun i => Real.sqrt (dv' i)) *
      Matrix.diagonal (fun i => Real.sqrt (dv' i)) = Matrix.diagonal dv' := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    exact Real.mul_self_sqrt (le_of_lt (hd' i))
  have hdpos : ∀ i, Real.sqrt (dv i) ≠ 0 := fun i => (Real.sqrt_pos.mpr (hd i)).ne'
  have hkill : Matrix.diagonal (fun i => (Real.sqrt (dv i))⁻¹) * Matrix.diagonal dv
      * Matrix.diagonal (fun i => (Real.sqrt (dv i))⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    rw [show (fun i => (Real.sqrt (dv i))⁻¹ * dv i * (Real.sqrt (dv i))⁻¹)
        = (fun _ => (1 : ℝ)) from ?_, Matrix.diagonal_one]
    funext i
    have hsq : Real.sqrt (dv i) * Real.sqrt (dv i) = dv i :=
      Real.mul_self_sqrt (le_of_lt (hd i))
    have : (Real.sqrt (dv i))⁻¹ * dv i * (Real.sqrt (dv i))⁻¹
        = (Real.sqrt (dv i))⁻¹ * (Real.sqrt (dv i) * Real.sqrt (dv i)) * (Real.sqrt (dv i))⁻¹ := by
      rw [hsq]
    rw [this]
    field_simp
    rw [div_self (hdpos i)]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose,
    Matrix.diagonal_transpose]
  -- Regroup everything right-associated, insert `D₁ D₁ = diag(d')`, then `Mᵀ diag(d') M = diag(d)`.
  -- Target: D₂ (Mᵀ (D₁ D₁) M) D₂ = D₂ (Mᵀ diag(d') M) D₂ = D₂ diag(d) D₂ = 1.
  have key : Matrix.diagonal (fun i => (Real.sqrt (dv i))⁻¹)
        * (M.transpose * Matrix.diagonal dv' * M)
        * Matrix.diagonal (fun i => (Real.sqrt (dv i))⁻¹) = 1 := by
    rw [hconj]; exact hkill
  -- Normalize `key` to right-associated form, insert `diag(d') = D₁ D₁`, finish.
  have key' := key
  simp only [Matrix.mul_assoc] at key' ⊢
  rw [← hsqrt'] at key'
  simp only [Matrix.mul_assoc] at key'
  exact key'

/-! ### (L4) Orthogonal correctness — the geometric core

This is the geometric heart of the paper (`prop:orthogonal-correctness`).  After (L1)–(L3)
the change-of-basis `M` is invertible, `H' = M H`, and the **SUM TRICK** plus orthogonalization
build an orthogonal `O = diag(√d')·M·diag(√d⁻¹)`.  A decreasing topological-order induction on
the rows of `O` (support `⊆ Pa(n)` from `central_rank2_eq`, parent-rows eliminated by
orthogonality, unit norm) shows each row of `O` is `± eₙ`, so `O` is a signed permutation and
`M = diagonal μ · permMat σ` with `μ` nonzero.  The per-context relations then follow by a
signed-Cholesky read-off, whose only graph-theoretic input — the σ-triangularity
`S'.B₀ (σ a)(σ b) = 0` for `b < a` — is itself read off cleanly from the `(b,a)` entry of
`central_rank2_eq` (no extra induction).  `orthogonal_collapse` adds the
order-preservation `InSG σ`. -/

/-- `M = diagonal μ permMat σ` with nonzero `μ` has explicit inverse
`M⁻¹ = (permMat σ)ᵀ diagonal μ⁻¹`. -/
private theorem diagPerm_mul_inv (σ : Equiv.Perm (Fin d)) {μ : Fin d → ℝ}
    (hμ : ∀ i, μ i ≠ 0) :
    (Matrix.diagonal μ * permMat σ)
        * ((permMat σ).transpose * Matrix.diagonal (fun i => (μ i)⁻¹)) = 1 := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (permMat σ), permMat_mul_transpose, Matrix.one_mul,
    Matrix.diagonal_mul_diagonal,
    show (fun i => μ i * (μ i)⁻¹) = (fun _ => (1 : ℝ)) from
      funext (fun i => mul_inv_cancel₀ (hμ i)), Matrix.diagonal_one]

/-- **Signed conjugation read-off.**  Given `M = diagonal μ permMat σ` and
`B' M = diagonal ν permMat σ B`, recover
`B' = diagonal ν permMat σ B (permMat σ)ᵀ diagonal μ⁻¹`. -/
private theorem conj_readoff {σ : Equiv.Perm (Fin d)} {μ ν : Fin d → ℝ} (hμ : ∀ i, μ i ≠ 0)
    {M B B' : Matrix (Fin d) (Fin d) ℝ}
    (hMeq : M = Matrix.diagonal μ * permMat σ)
    (hrel : B' * M = Matrix.diagonal ν * permMat σ * B) :
    B' = Matrix.diagonal ν * permMat σ * B * (permMat σ).transpose
        * Matrix.diagonal (fun i => (μ i)⁻¹) := by
  have hMinv : M * ((permMat σ).transpose * Matrix.diagonal (fun i => (μ i)⁻¹)) = 1 := by
    rw [hMeq]; exact diagPerm_mul_inv σ hμ
  have hMU : M⁻¹ = (permMat σ).transpose * Matrix.diagonal (fun i => (μ i)⁻¹) :=
    Matrix.inv_eq_right_inv hMinv
  have hMMinv : M * M⁻¹ = 1 := by
    have hu : IsUnit M := IsUnit.of_mul_eq_one _ hMinv
    exact Matrix.mul_nonsing_inv M (by rwa [Matrix.isUnit_iff_isUnit_det] at hu)
  have hsplit : B' = (B' * M) * M⁻¹ := by rw [Matrix.mul_assoc, hMMinv, Matrix.mul_one]
  rw [hsplit, hrel, hMU]
  simp only [Matrix.mul_assoc]

/-- `(permMat σ) a c = 1` iff `c = σ.symm a`, else `0` (column read-off of `permMat`). -/
theorem permMat_apply_symm (σ : Equiv.Perm (Fin d)) (a c : Fin d) :
    permMat σ a c = if c = σ.symm a then (1 : ℝ) else 0 := by
  simp only [permMat, Matrix.of_apply]
  by_cases h : c = σ.symm a
  · subst h; simp [Equiv.apply_symm_apply]
  · rw [if_neg h, if_neg]
    exact fun hac => h (by rw [hac, Equiv.symm_apply_apply])

/-- **Permutation conjugation entry.**
`(permMat σ * X * (permMat σ)ᵀ) a b = X (σ.symm a) (σ.symm b)`:
conjugating `X` by `permMat σ` relabels rows and columns by `σ.symm`. -/
theorem permMat_conj_apply (σ : Equiv.Perm (Fin d)) (X : Matrix (Fin d) (Fin d) ℝ) (a b : Fin d) :
    (permMat σ * X * (permMat σ).transpose) a b = X (σ.symm a) (σ.symm b) := by
  rw [Matrix.mul_apply]
  have hstep : ∀ c, (permMat σ * X) a c = X (σ.symm a) c := by
    intro c
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (σ.symm a)]
    · rw [permMat_apply_symm, if_pos rfl, one_mul]
    · intro x _ hx; rw [permMat_apply_symm, if_neg hx, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [hstep, Matrix.transpose_apply, permMat_apply_symm]
  rw [Finset.sum_eq_single (σ.symm b)]
  · rw [if_pos rfl, mul_one]
  · intro x _ hx; rw [if_neg hx, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `(permMat σ)ᵀ = permMat σ⁻¹`: the transpose of a permutation matrix is the matrix of
the inverse permutation. -/
private theorem permMat_transpose_eq (σ : Equiv.Perm (Fin d)) :
    (permMat σ).transpose = permMat σ⁻¹ := by
  ext i j
  simp only [Matrix.transpose_apply, permMat, Matrix.of_apply]
  by_cases h : j = σ i
  · subst h; simp [Equiv.symm_apply_apply]
  · rw [if_neg h, if_neg (fun hc => h (by rw [hc]; simp))]

/-- **Inverse-permutation conjugation entry.**
`((permMat σ)ᵀ * X * permMat σ) a b = X (σ a) (σ b)`: conjugating `X` by `(permMat σ)ᵀ`
relabels rows and columns by `σ`. -/
private theorem permMat_conj_apply' (σ : Equiv.Perm (Fin d)) (X : Matrix (Fin d) (Fin d) ℝ)
    (a b : Fin d) :
    ((permMat σ).transpose * X * permMat σ) a b = X (σ a) (σ b) := by
  rw [permMat_transpose_eq]
  have h2 : permMat σ = (permMat σ⁻¹).transpose := by
    rw [permMat_transpose_eq]; simp
  rw [h2, permMat_conj_apply σ⁻¹ X a b]
  rfl

/-- **Diagonal-through-permutation.**  `permMat σ * diagonal s = diagonal (s ∘ σ.symm) * permMat σ`:
moving a diagonal rescaling across a permutation matrix relabels its entries by `σ.symm`. -/
private theorem permMat_mul_diagonal (σ : Equiv.Perm (Fin d)) (s : Fin d → ℝ) :
    permMat σ * Matrix.diagonal s = Matrix.diagonal (fun i => s (σ.symm i)) * permMat σ := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, permMat_apply_symm]
  by_cases h : b = σ.symm a
  · subst h; rw [if_pos rfl]; simp
  · rw [if_neg h, mul_zero, zero_mul]

/-- **Orthogonal upper-triangular ⟹ signed diagonal.**  An orthogonal (`Wᵀ W = 1`)
upper-triangular matrix is diagonal with `±1` entries.  This is the signed analogue of
`orthogonal_upperTri_pos_diag_eq_one` (which assumed a positive diagonal and concluded `W = 1`):
without the sign condition the diagonal entries are pinned only up to sign. -/
private theorem orthogonal_upperTri_signed_diag {q : ℕ} {W : Matrix (Fin q) (Fin q) ℝ}
    (hortho : Wᵀ * W = 1) (hupp : ∀ i j, j < i → W i j = 0) :
    (∀ i j, i ≠ j → W i j = 0) ∧ (∀ i, W i i = 1 ∨ W i i = -1) := by
  classical
  haveI : Invertible W := invertibleOfLeftInverse _ _ hortho
  have hinv : W⁻¹ = Wᵀ := Matrix.inv_eq_left_inv hortho
  have hWupp : W.BlockTriangular id := hupp
  have hWTupp : (Wᵀ).BlockTriangular id :=
    hinv ▸ Matrix.blockTriangular_inv_of_blockTriangular hWupp
  have hWTlow : (Wᵀ).BlockTriangular OrderDual.toDual := hWupp.transpose
  -- `Wᵀ` is both upper- and lower-triangular, hence diagonal.
  have hWTdiag : ∀ i j, i ≠ j → (Wᵀ) i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hWTlow (by simpa using h)
    · exact hWTupp (by simpa using h)
  -- Off-diagonal entries of `W` vanish (transpose of `Wᵀ`'s vanishing entries).
  have hWdiag : ∀ i j, i ≠ j → W i j = 0 := by
    intro i j hij
    have : (Wᵀ) j i = 0 := hWTdiag j i (Ne.symm hij)
    rwa [Matrix.transpose_apply] at this
  refine ⟨hWdiag, ?_⟩
  -- Diagonal entries square to one.
  intro i
  have hcol := congrFun (congrFun hortho i) i
  rw [Matrix.one_apply_eq, Matrix.mul_apply] at hcol
  simp only [Matrix.transpose_apply] at hcol
  rw [Finset.sum_eq_single i] at hcol
  · rw [← sq] at hcol; exact sq_eq_one_iff.mp hcol
  · intro l _ hli
    have : W l i = 0 := hWdiag l i hli
    rw [this, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Signed Cholesky read-off.**  If `Pᵀ P = Bᵀ B` with `P` upper-triangular and `B`
upper-triangular with strictly positive diagonal, then `P = diagonal s · B` for a unique
`±1`-valued sign vector `s`, with `s i · B i i = P i i`.  This generalizes `cholesky_unique`
(both factors positive-diagonal) to the case where only one factor's diagonal sign is fixed. -/
private theorem signed_cholesky {q : ℕ} {P B : Matrix (Fin q) (Fin q) ℝ}
    (hPu : ∀ i j, j < i → P i j = 0) (hBu : ∀ i j, j < i → B i j = 0)
    (hBp : ∀ i, 0 < B i i) (hgram : Pᵀ * P = Bᵀ * B) :
    ∃ s : Fin q → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
      (∀ i, s i * B i i = P i i) ∧ P = Matrix.diagonal s * B := by
  classical
  have hBu' : B.BlockTriangular id := hBu
  have hBdet : (0 : ℝ) < B.det := by
    rw [Matrix.det_of_upperTriangular hBu']; exact Finset.prod_pos (fun i _ => hBp i)
  haveI : Invertible B := B.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hBdet.ne')
  have hBinvU : B⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hBu'
  have hBinv_diag : ∀ i, B⁻¹ i i = (B i i)⁻¹ := by
    intro i
    have hmul : (B⁻¹ * B) i i = 1 := by rw [Matrix.inv_mul_of_invertible]; simp
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at hmul
    · field_simp [(hBp i).ne'] at hmul ⊢; linarith [hmul]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with hk | hk
      · rw [hBinvU (by simpa using hk), zero_mul]
      · rw [hBu k i hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  -- `W := P * B⁻¹` is orthogonal and upper-triangular.
  set W : Matrix (Fin q) (Fin q) ℝ := P * B⁻¹ with hW
  have hWupp : ∀ i j, j < i → W i j = 0 := (Matrix.BlockTriangular.mul (hPu) hBinvU)
  have hWortho : Wᵀ * W = 1 := by
    rw [hW, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Pᵀ P, hgram,
      Matrix.mul_assoc Bᵀ, Matrix.mul_inv_of_invertible, Matrix.mul_one,
      Matrix.transpose_nonsing_inv, Matrix.inv_mul_of_invertible]
  obtain ⟨hWoff, hWsign⟩ := orthogonal_upperTri_signed_diag hWortho hWupp
  -- The sign vector is the diagonal of `W`.
  refine ⟨fun i => W i i, hWsign, ?_, ?_⟩
  · -- `W i i · B i i = P i i`.
    intro i
    change W i i * B i i = P i i
    have hWii : W i i = P i i * (B i i)⁻¹ := by
      rw [hW, Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [hBinv_diag i]
      · intro k _ hki
        rcases lt_or_gt_of_ne hki with hk | hk
        · rw [hPu i k (by simpa using hk), zero_mul]
        · rw [hBinvU (by simpa using hk), mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hWii]
    field_simp [(hBp i).ne']
  · -- `P = diagonal (W ·ᵢᵢ) * B`, since `W = diagonal` and `P = W B`.
    have hWdiagonal : W = Matrix.diagonal (fun i => W i i) := by
      ext a b
      by_cases hab : a = b
      · subst hab; rw [Matrix.diagonal_apply_eq]
      · rw [Matrix.diagonal_apply_ne _ hab, hWoff a b hab]
    have hPWB : P = W * B := by
      rw [hW, Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.mul_one]
    rw [hPWB]
    conv_lhs => rw [hWdiagonal]

/-- The remaining geometric core after the permutation choice, SUM TRICK, and diagonal
orthogonalization have all been made explicit.

The proof has three parts.  **(D)** A decreasing strong induction on the rows of
`O = diag(√d') M diag(√d⁻¹)` (orthogonal by `hO`), using `central_rank2_eq` and the
`e_c`-support / parent-elimination argument, shows that the `σ n`-row of `O` is `±eₙ`;
**(E)** reading `O`'s monomial structure back through the positive diagonal
rescalings gives `M = diagonal μ · permMat σ` with nonzero `μ`; and **(F)** the
signed-Cholesky read-off (`signed_cholesky`, `orthogonal_upperTri_signed_diag`)
then produces the per-context relations
`B'ₖ M = diagonal ν · permMat σ · Bₖ` with the shared sign vector `ν = sign ∘ μ`.  Its only
graph-theoretic input — the σ-triangularity `S'.B₀ (σ a)(σ b) = 0` for `b < a` (that `σ`
carries the partial order of `𝒢` into that of `𝒢'`) — is read off directly from the `(b,a)`
entry of `central_rank2_eq` (`hB0σtri`). -/
private theorem monomial_relations_from_orthogonal_core (S S' : Solution d p K)
    (hNondeg : ∀ k, S.Theta k ≠ S.Theta0)
    (hΘ0 : S.Theta0 = S'.Theta0) (hΘ : ∀ k, S.Theta k = S'.Theta k)
    {M : Matrix (Fin d) (Fin d) ℝ} (hMunit : IsUnit M) (hM : S'.H = M * S.H)
    (kof : Fin d → Fin K) (hkof : ∀ n, S.target (kof n) = n)
    (σ : Equiv.Perm (Fin d)) (hσtarget : ∀ n, S'.target (kof n) = σ n)
    (hdiag :
      M.transpose * Matrix.diagonal (fun m => (S'.lam (kof (σ.symm m))) ^ 2) * M
        = Matrix.diagonal (fun n => (S.lam (kof n)) ^ 2))
    (hO :
      (Matrix.diagonal (fun m => Real.sqrt ((S'.lam (kof (σ.symm m))) ^ 2)) * M
          * Matrix.diagonal (fun n => (Real.sqrt ((S.lam (kof n)) ^ 2))⁻¹)).transpose
        * (Matrix.diagonal (fun m => Real.sqrt ((S'.lam (kof (σ.symm m))) ^ 2)) * M
          * Matrix.diagonal (fun n => (Real.sqrt ((S.lam (kof n)) ^ 2))⁻¹)) = 1) :
    ∃ (σ : Equiv.Perm (Fin d)) (μ ν : Fin d → ℝ),
      (∀ i, μ i ≠ 0) ∧ (∀ i, ν i = 1 ∨ ν i = -1) ∧
      M = Matrix.diagonal μ * permMat σ ∧
      S'.B0 * M = Matrix.diagonal ν * permMat σ * S.B0 ∧
      (∀ k, S'.Bint k * M = Matrix.diagonal ν * permMat σ * S.Bint k) := by
  classical
  -- Positive diagonal rescalings turning `M` into the orthogonal `O`.
  set sd : Fin d → ℝ := fun n => Real.sqrt ((S.lam (kof n)) ^ 2) with hsd
  set sd' : Fin d → ℝ := fun m => Real.sqrt ((S'.lam (kof (σ.symm m))) ^ 2) with hsd'
  have hsd_pos : ∀ n, 0 < sd n := fun n =>
    Real.sqrt_pos.mpr (sq_pos_of_ne_zero (ne_of_gt (S.hlam (kof n))))
  have hsd'_pos : ∀ m, 0 < sd' m := fun m =>
    Real.sqrt_pos.mpr (sq_pos_of_ne_zero (ne_of_gt (S'.hlam (kof (σ.symm m)))))
  set O : Matrix (Fin d) (Fin d) ℝ :=
    Matrix.diagonal sd' * M * Matrix.diagonal (fun n => (sd n)⁻¹) with hOdef
  -- Entrywise: `O a b = sd' a · M a b · (sd b)⁻¹`.
  have hOentry : ∀ a b : Fin d, O a b = sd' a * M a b * (sd b)⁻¹ := by
    intro a b
    rw [hOdef, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hO1 : Oᵀ * O = 1 := hO
  -- `O` is square with left inverse `Oᵀ`, hence `O Oᵀ = 1` (orthonormal rows too).
  haveI : Invertible O := invertibleOfLeftInverse _ _ hO1
  have hO2 : O * Oᵀ = 1 := by
    have := Matrix.mul_inv_of_invertible O
    rwa [Matrix.inv_eq_left_inv hO1] at this
  -- `M a b = (sd' a)⁻¹ · O a b · sd b`.
  have hMentry : ∀ a b : Fin d, M a b = (sd' a)⁻¹ * O a b * sd b := by
    intro a b
    rw [hOentry]
    have ha : sd' a ≠ 0 := ne_of_gt (hsd'_pos a)
    have hb : sd b ≠ 0 := ne_of_gt (hsd_pos b)
    field_simp
  -- `O a b = 0 ↔ M a b = 0` (the scalings are nonzero).
  have hMO_zero : ∀ a b : Fin d, M a b = 0 ↔ O a b = 0 := by
    intro a b
    rw [hOentry]
    constructor
    · intro h; rw [h]; ring
    · intro h
      have := mul_eq_zero.mp h
      rcases this with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact absurd h2 (ne_of_gt (hsd'_pos a))
        · exact h2
      · exact absurd h1 (inv_ne_zero (ne_of_gt (hsd_pos b)))
  -- **STEP (D).** Decreasing induction: the `σ n`-th row of `O` is `(O (σ n) n) • eₙ`
  -- with `O (σ n) n = ±1`.
  have hD : ∀ n : Fin d,
      (∀ j, j ≠ n → O (σ n) j = 0) ∧ (O (σ n) n = 1 ∨ O (σ n) n = -1) := by
    intro n
    induction n using WellFoundedGT.induction with
    | _ n hIH =>
      -- Abbreviations for `central_rank2_eq` at context `kof n`.
      set lam := S.lam (kof n) with hlam
      set lam' := S'.lam (kof n) with hlam'
      set wn : Fin d → ℝ := fun j => S.B0 n j with hwn
      set mrow : Fin d → ℝ := fun j => M (σ n) j with hmrow
      set wn' : Fin d → ℝ :=
        Mᵀ *ᵥ (S'.B0.transpose *ᵥ stdVec d (σ n)) with hwn'
      -- The central rank-≤2 equation, rewritten with the target identifications.
      have hCR :
          lam ^ 2 • Matrix.vecMulVec (stdVec d n) (stdVec d n)
              - Matrix.vecMulVec wn wn
            = lam' ^ 2 • Matrix.vecMulVec mrow mrow - Matrix.vecMulVec wn' wn' := by
        have hbase := central_rank2_eq S S' hM hΘ0 hΘ (kof n)
        rw [hkof n, hσtarget n] at hbase
        rw [transpose_mulVec_stdVec S.B0 n] at hbase
        rw [transpose_mulVec_stdVec M (σ n)] at hbase
        simpa [hlam, hlam', hwn, hmrow, hwn'] using hbase
      -- **(D1) Support of `mrow ⊆ Pa(n)`.**
      have hD1 : ∀ c, c ≠ n → ¬ S.Edge c n → mrow c = 0 := by
        intro c hcn hce
        -- `wn c = B0 n c = 0`: off-diagonal nonzero requires an edge.
        have hwnc : wn c = 0 := by
          rw [hwn]
          by_contra h
          exact hce ((S.hB0supp n c (Ne.symm hcn)).mp h)
        have hsnc : (stdVec d n) c = 0 := by simp [stdVec, hcn]
        -- Take the `(·, c)` column of (CR).  LHS vanishes (`eₙ c = 0`, `wn c = 0`).
        -- Result: `lam'² (mrow c) • mrow = (wn' c) • wn'`  as functions of `a`.
        have hstar : ∀ a, lam' ^ 2 * mrow c * mrow a = wn' c * wn' a := by
          intro a
          have hcol := congrFun (congrFun hCR a) c
          simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
            smul_eq_mul] at hcol
          rw [hsnc, mul_zero, mul_zero,
            hwnc, mul_zero, sub_zero] at hcol
          -- `0 = lam'² (mrow a)(mrow c) - (wn' a)(wn' c)`
          have : lam' ^ 2 * (mrow a * mrow c) - wn' a * wn' c = 0 := by linarith [hcol]
          nlinarith [this]
        by_contra hmc
        -- `mrow c ≠ 0`.  Two cases on `wn' c`.
        by_cases hwc : wn' c = 0
        · -- Then `lam'² (mrow c) • mrow = 0`, forcing `mrow c = 0`.
          have := hstar c
          rw [hwc, zero_mul] at this
          have hl2 : (0 : ℝ) < lam' ^ 2 := sq_pos_of_ne_zero (ne_of_gt (S'.hlam (kof n)))
          have : mrow c = 0 := by
            rcases mul_eq_zero.mp this with h | h
            · rcases mul_eq_zero.mp h with h' | h'
              · exact absurd h' (ne_of_gt hl2)
              · exact h'
            · exact h
          exact hmc this
        · -- `wn' = β • mrow` with `β = lam'² (mrow c)/(wn' c)`.
          set β := lam' ^ 2 * mrow c / wn' c with hβ
          have hwn'_eq : ∀ a, wn' a = β * mrow a := by
            intro a
            rw [hβ]
            field_simp
            linarith [hstar a]
          -- Substitute into (CR): the primed side collapses to `(lam'² - β²) • mrow⊗mrow`.
          have hCR2 :
              lam ^ 2 • Matrix.vecMulVec (stdVec d n) (stdVec d n)
                  - Matrix.vecMulVec wn wn
                = (lam' ^ 2 - β ^ 2) • Matrix.vecMulVec mrow mrow := by
            rw [hCR]
            ext a b
            simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
              smul_eq_mul]
            rw [hwn'_eq a, hwn'_eq b]
            ring
          -- The `(c,c)` entry: LHS `= 0`, RHS `= (lam'²-β²)(mrow c)²`, so `lam'² = β²`.
          have hcc := congrFun (congrFun hCR2 c) c
          simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
            smul_eq_mul] at hcc
          rw [hsnc, mul_zero, mul_zero,
            hwnc, mul_zero, sub_zero] at hcc
          -- `0 = (lam'² - β²)(mrow c)²`, `mrow c ≠ 0`, so `lam'² = β²`.
          have hβsq : lam' ^ 2 - β ^ 2 = 0 := by
            have : (lam' ^ 2 - β ^ 2) * (mrow c * mrow c) = 0 := by linarith [hcc]
            rcases mul_eq_zero.mp this with h | h
            · exact h
            · exact absurd (mul_self_eq_zero.mp h) hmc
          -- Then the whole primed side is `0`, so the latent Gram difference is `0`,
          -- contradicting `hNondeg`.
          rw [hβsq, zero_smul] at hCR2
          -- `λ²(eₙeₙᵀ) − wₙwₙᵀ = 0`, hence `Bₖᵀ Bₖ − B₀ᵀ B₀ = 0`, so `Θₖ = Θ₀`.
          have hlatent :
              (S.Bint (kof n)).transpose * S.Bint (kof n) - S.B0.transpose * S.B0 = 0 := by
            rw [latent_key_identity S (kof n), hkof n]
            rw [show (S.B0.transpose *ᵥ stdVec d n) = wn from transpose_mulVec_stdVec S.B0 n]
            rw [show (S.lam (kof n)) = lam from rfl]
            exact hCR2
          apply hNondeg (kof n)
          rw [Solution.Theta, Solution.Theta0]
          have hΘdiff :
              (S.Bint (kof n)).transpose * S.Bint (kof n) = S.B0.transpose * S.B0 :=
            sub_eq_zero.mp hlatent
          have : S.H.transpose * ((S.Bint (kof n)).transpose * S.Bint (kof n)) * S.H
              = S.H.transpose * (S.B0.transpose * S.B0) * S.H := by rw [hΘdiff]
          simpa [Matrix.mul_assoc] using this
      -- **(D2) Parent elimination** + combine to get the row collapse.
      -- First: the `σn`-row of `O` vanishes off `{n}`.
      have hrow_off : ∀ j, j ≠ n → O (σ n) j = 0 := by
        intro j hjn
        by_cases hedge : S.Edge j n
        · -- `j` is a parent: `n < j`, so IH applies to `j`.
          have hnj : n < j := S.hAcyc j n hedge
          obtain ⟨hIHzero, hIHsign⟩ := hIH j hnj
          -- `(σn, σj)` entry of `Oᵀ O = 1`: `∑ᵢ O (σn) i · O (σj) i = 0`.
          have hne : σ n ≠ σ j := fun h => (ne_of_lt hnj) (σ.injective h)
          have hsum := congrFun (congrFun hO2 (σ n)) (σ j)
          rw [Matrix.one_apply_ne hne, Matrix.mul_apply] at hsum
          simp only [Matrix.transpose_apply] at hsum
          -- `O (σj) i = 0` unless `i = j`; collapse the sum.
          rw [Finset.sum_eq_single j] at hsum
          · -- `O (σn) j · O (σj) j = 0`, `O (σj) j ≠ 0`.
            have hOjj : O (σ j) j ≠ 0 := by
              rcases hIHsign with h | h <;> rw [h] <;> norm_num
            rcases mul_eq_zero.mp hsum with h | h
            · exact h
            · exact absurd h hOjj
          · intro i _ hij
            rw [hIHzero i hij, mul_zero]
          · intro h; exact absurd (Finset.mem_univ _) h
        · -- `j` is not a parent and `j ≠ n`: D1 + the `M↔O` zero transfer.
          have hmrowj : M (σ n) j = 0 := hD1 j hjn hedge
          exact (hMO_zero (σ n) j).mp hmrowj
      -- The `(σn, σn)` entry of `Oᵀ O = 1` collapses to `(O (σn) n)² = 1`.
      have hsq : (O (σ n) n) ^ 2 = 1 := by
        have hsum := congrFun (congrFun hO2 (σ n)) (σ n)
        rw [Matrix.one_apply_eq, Matrix.mul_apply] at hsum
        simp only [Matrix.transpose_apply] at hsum
        rw [Finset.sum_eq_single n] at hsum
        · rw [← sq] at hsum; exact hsum
        · intro i _ hin
          have : O (σ n) i = 0 := hrow_off i hin
          rw [this, mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      exact ⟨hrow_off, sq_eq_one_iff.mp hsq⟩
  -- **STEP (E).** Monomial form of `M`.
  -- The `σ n`-row of `M` vanishes off `{n}`, and `M (σ n) n ≠ 0`.
  have hMrow_off : ∀ n j, j ≠ n → M (σ n) j = 0 := by
    intro n j hjn
    exact (hMO_zero (σ n) j).mpr ((hD n).1 j hjn)
  have hMdiag_ne : ∀ n, M (σ n) n ≠ 0 := by
    intro n
    rw [Ne, hMO_zero (σ n) n]
    rcases (hD n).2 with h | h <;> rw [h] <;> norm_num
  -- The scalings `μ` (nonzero diagonal of `M`) and `ν` (row signs of `O`).
  set μ : Fin d → ℝ := fun i => M i (σ.symm i) with hμdef
  set ν : Fin d → ℝ := fun i => O i (σ.symm i) with hνdef
  have hμ : ∀ i, μ i ≠ 0 := by
    intro i
    have : μ i = M (σ (σ.symm i)) (σ.symm i) := by rw [hμdef, Equiv.apply_symm_apply]
    rw [this]; exact hMdiag_ne (σ.symm i)
  have hν : ∀ i, ν i = 1 ∨ ν i = -1 := by
    intro i
    have : ν i = O (σ (σ.symm i)) (σ.symm i) := by rw [hνdef, Equiv.apply_symm_apply]
    rw [this]; exact (hD (σ.symm i)).2
  -- `M = diagonal μ * permMat σ`.
  have hMeq : M = Matrix.diagonal μ * permMat σ := by
    ext i j
    rw [Matrix.diagonal_mul, permMat_apply_symm]
    by_cases hij : j = σ.symm i
    · -- `i = σ j`, the diagonal entry.
      subst hij
      rw [if_pos rfl, mul_one, hμdef]
    · -- off-diagonal: `M i j = 0`.
      rw [if_neg hij, mul_zero]
      -- `i = σ (σ.symm i)`; row `σ (σ.symm i)` of `M` vanishes off `{σ.symm i}`.
      have hi : i = σ (σ.symm i) := (Equiv.apply_symm_apply σ i).symm
      rw [hi]
      exact hMrow_off (σ.symm i) j hij
  -- **STEP (F).** The signed per-context relations, with the shared sign vector
  -- `ν i = sign(μ i)`.
  set νF : Fin d → ℝ := fun i => if 0 < μ i then (1 : ℝ) else -1 with hνF
  have hνF_sign : ∀ i, νF i = 1 ∨ νF i = -1 := by
    intro i; rw [hνF]; by_cases h : 0 < μ i <;> simp [h]
  -- **(F-core) The per-context signed relation**, given the σ-triangularity of `B'`.
  -- `B' M = diagonal νF · permMat σ · B`.
  have bRel : ∀ B B' : Matrix (Fin d) (Fin d) ℝ,
      (∀ i j, j < i → B i j = 0) → (∀ i, 0 < B i i) →
      (∀ i, 0 < B' i i) →
      (∀ a b, b < a → B' (σ a) (σ b) = 0) →
      B.transpose * B = M.transpose * (B'.transpose * B') * M →
      B' * M = Matrix.diagonal νF * permMat σ * B := by
    intro B B' hBu hBp hB'p hB'tri hgram
    -- `P := (permMat σ)ᵀ * B' * M`, then `Pᵀ P = Bᵀ B` and `P` is upper-triangular.
    set P : Matrix (Fin d) (Fin d) ℝ := (permMat σ).transpose * B' * M with hP
    -- `P a b = B' (σ a) (σ b) · μ (σ b)`.
    have hPentry : ∀ a b, P a b = B' (σ a) (σ b) * μ (σ b) := by
      intro a b
      have hPeq : P = (permMat σ).transpose * (B' * Matrix.diagonal μ) * permMat σ := by
        rw [hP, hMeq]; simp only [Matrix.mul_assoc]
      rw [hPeq, permMat_conj_apply' σ (B' * Matrix.diagonal μ) a b, Matrix.mul_diagonal]
    -- `P` is upper-triangular (from `B'`'s σ-triangularity).
    have hPu : ∀ i j, j < i → P i j = 0 := by
      intro i j hji
      rw [hPentry, hB'tri i j hji, zero_mul]
    -- `Pᵀ P = Bᵀ B`.
    have hPgram : P.transpose * P = B.transpose * B := by
      rw [hP, hgram]
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (permMat σ) (permMat σ).transpose, permMat_mul_transpose,
        Matrix.one_mul]
    -- Signed Cholesky: `P = diagonal s · B` with `s i = ±1` and `s i · B i i = P i i`.
    obtain ⟨s, hssign, hsval, hPsB⟩ := signed_cholesky hPu hBu hBp hPgram
    -- The sign equals `νF (σ ·)`: `s i = sign(μ (σ i))`.
    have hs_eq : ∀ i, s i = νF (σ i) := by
      intro i
      have hval := hsval i
      rw [hPentry] at hval
      -- `s i · B i i = B' (σ i)(σ i) · μ (σ i)`; both diagonals positive.
      have hBii : 0 < B i i := hBp i
      have hB'ii : 0 < B' (σ i) (σ i) := hB'p (σ i)
      change s i = if 0 < μ (σ i) then (1 : ℝ) else -1
      by_cases hμpos : 0 < μ (σ i)
      · rw [if_pos hμpos]
        rcases hssign i with h | h
        · exact h
        · -- `s i = -1` contradicts the signs: LHS `< 0`, RHS `> 0`.
          exfalso
          rw [h] at hval
          have hlhs : (-1 : ℝ) * B i i < 0 := by nlinarith [hBii]
          have hrhs : 0 < B' (σ i) (σ i) * μ (σ i) := mul_pos hB'ii hμpos
          linarith [hval]
      · rw [if_neg hμpos]
        have hμneg : μ (σ i) < 0 := lt_of_le_of_ne (not_lt.mp hμpos) (hμ (σ i))
        rcases hssign i with h | h
        · exfalso
          rw [h] at hval
          have hlhs : (0 : ℝ) < 1 * B i i := by nlinarith [hBii]
          have hrhs : B' (σ i) (σ i) * μ (σ i) < 0 := mul_neg_of_pos_of_neg hB'ii hμneg
          linarith [hval]
        · exact h
    -- Assemble: `B' M = permMat σ · P = permMat σ · diagonal s · B`.
    have hBM : B' * M = permMat σ * P := by
      rw [hP, ← Matrix.mul_assoc, ← Matrix.mul_assoc, permMat_mul_transpose, Matrix.one_mul]
    rw [hBM, hPsB, ← Matrix.mul_assoc, permMat_mul_diagonal]
    -- `s ∘ σ.symm = νF`.
    have hsσ : (fun i => s (σ.symm i)) = νF := by
      funext i; rw [hs_eq, Equiv.apply_symm_apply]
    rw [hsσ]
  -- The per-context Gram identities (conjugation form).
  have hgram0 : S.B0.transpose * S.B0
      = M.transpose * (S'.B0.transpose * S'.B0) * M := by
    refine gram_identity_conj S S' hM ?_
    simp only [Solution.Theta0, Matrix.mul_assoc] at hΘ0 ⊢
    exact hΘ0
  have hgramk : ∀ k, (S.Bint k).transpose * S.Bint k
      = M.transpose * ((S'.Bint k).transpose * S'.Bint k) * M := by
    intro k
    refine gram_identity_conj S S' hM ?_
    have := hΘ k
    simp only [Solution.Theta, Matrix.mul_assoc] at this ⊢
    exact this
  -- **(F-crux) The σ-triangularity / graph correspondence: `S'.B0 (σ a)(σ b) = 0` for `b < a`.**
  -- (`σ` carries the order support of `𝒢` into that of `𝒢'`.)  This is read off directly from
  -- the `(b, a)` entry of `central_rank2_eq` at context `kof a`: since `M` is monomial (its
  -- `σ a`-row is `μ_{σa}·eₐ`) and `B₀` is upper triangular (`(B₀)_{a,b} = 0` for `b < a`), the
  -- unprimed side of that entry vanishes, forcing `μ_{σb}·(B'₀)_{σa,σb}·μ_{σa}·(B'₀)_{σa,σa} = 0`;
  -- the three known-nonzero factors then give `(B'₀)_{σa,σb} = 0`.  No extra induction needed.
  have hB0σtri : ∀ a b, b < a → S'.B0 (σ a) (σ b) = 0 := by
    -- `(Mᵀ *ᵥ w) j = w (σ j) * M (σ j) j`, since `M` is monomial (row `σ j` supported on `{j}`).
    have hMtw : ∀ (w : Fin d → ℝ) (j : Fin d),
        (M.transpose *ᵥ w) j = w (σ j) * M (σ j) j := by
      intro w j
      rw [Matrix.mulVec_transpose, Matrix.vecMul_eq_sum]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single (σ j)]
      · intro l _ hl
        have hMlj : M l j = 0 := by
          have hlj : j ≠ σ.symm l := fun h => hl (by rw [h, Equiv.apply_symm_apply])
          have h2 := hMrow_off (σ.symm l) j hlj
          rwa [Equiv.apply_symm_apply] at h2
        rw [hMlj, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    intro a b hba
    have hba' : b ≠ a := ne_of_lt hba
    have hcr := central_rank2_eq S S' hM hΘ0 hΘ (kof a)
    rw [hkof a, hσtarget a] at hcr
    have h := congrFun (congrFun hcr b) a
    -- Evaluate the `(b, a)` entry; the unprimed (LHS) part vanishes (`b < a`, `B₀` upper-tri).
    have hub : (stdVec d a) b = 0 := by rw [stdVec, Pi.single_eq_of_ne hba']
    have hvb : (S.B0.transpose *ᵥ stdVec d a) b = 0 := by
      rw [transpose_mulVec_stdVec]; exact S.hB0up a b hba
    have hu'b : (M.transpose *ᵥ stdVec d (σ a)) b = 0 := by
      rw [hMtw, stdVec, Pi.single_eq_of_ne (show σ b ≠ σ a from fun h => hba' (σ.injective h)),
        zero_mul]
    have hw''b : (M.transpose *ᵥ (S'.B0.transpose *ᵥ stdVec d (σ a))) b
        = S'.B0 (σ a) (σ b) * M (σ b) b := by
      rw [hMtw, transpose_mulVec_stdVec]
    have hw''a : (M.transpose *ᵥ (S'.B0.transpose *ᵥ stdVec d (σ a))) a
        = S'.B0 (σ a) (σ a) * M (σ a) a := by
      rw [hMtw, transpose_mulVec_stdVec]
    rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Matrix.vecMulVec_apply, Matrix.vecMulVec_apply,
      Matrix.vecMulVec_apply, hub, hvb, hu'b, hw''b, hw''a] at h
    simp only [zero_mul, mul_zero, sub_zero, zero_sub, smul_eq_mul] at h
    -- `h : 0 = -(S'.B0 (σ a) (σ b) * M (σ b) b * (S'.B0 (σ a) (σ a) * M (σ a) a))`.
    have hprod : S'.B0 (σ a) (σ b) * M (σ b) b * (S'.B0 (σ a) (σ a) * M (σ a) a) = 0 := by
      linarith [h]
    have h1 : M (σ b) b ≠ 0 := hMdiag_ne b
    have h2 : M (σ a) a ≠ 0 := hMdiag_ne a
    have h3 : S'.B0 (σ a) (σ a) ≠ 0 := ne_of_gt (S'.hB0pos (σ a))
    have hsnd : S'.B0 (σ a) (σ a) * M (σ a) a ≠ 0 := mul_ne_zero h3 h2
    rcases mul_eq_zero.mp hprod with hx | hx
    · rcases mul_eq_zero.mp hx with hy | hy
      · exact hy
      · exact absurd hy h1
    · exact absurd hx hsnd
  -- The interventional σ-triangularity follows from the observational one: an intervention
  -- only rewrites the target row, which (off its diagonal) vanishes; all other rows agree
  -- with `B'₀`.
  have hBintσtri : ∀ k a b, b < a → S'.Bint k (σ a) (σ b) = 0 := by
    intro k a b hba
    have hσne : σ b ≠ σ a := fun h => (ne_of_lt hba) (σ.injective h)
    by_cases hi : σ a = S'.target k
    · -- target row of `B'ₖ` is `λ'ₖ · e_{target}`; off the diagonal it vanishes.
      have hrow : (fun j => S'.Bint k (S'.target k) j)
          = (S'.lam k) • stdVec d (S'.target k) := by
        rw [← transpose_mulVec_stdVec (S'.Bint k) (S'.target k)]
        exact Bint_transpose_mulVec_target S' k
      have hbne : σ b ≠ S'.target k := hi ▸ hσne
      have := congrFun hrow (σ b)
      rw [hi]
      simp only [Pi.smul_apply, smul_eq_mul, stdVec, Pi.single_eq_of_ne hbne, mul_zero] at this
      exact this
    · -- non-target row: agrees with `B'₀`.
      rw [S'.hInt k, Matrix.add_apply, Matrix.vecMulVec_apply]
      rw [hB0σtri a b hba, zero_add]
      simp only [stdVec, Pi.single_eq_of_ne hi, zero_mul]
  -- Apply `bRel` per context.
  have hB0rel : S'.B0 * M = Matrix.diagonal νF * permMat σ * S.B0 :=
    bRel S.B0 S'.B0 S.hB0up S.hB0pos S'.hB0pos hB0σtri hgram0
  have hBintrel : ∀ k, S'.Bint k * M = Matrix.diagonal νF * permMat σ * S.Bint k := by
    intro k
    exact bRel (S.Bint k) (S'.Bint k) (Bint_blockTriangular S k) (Bint_diag_pos S k)
      (Bint_diag_pos S' k) (hBintσtri k) (hgramk k)
  exact ⟨σ, μ, νF, hμ, hνF_sign, hMeq, hB0rel, hBintrel⟩

/-- **(S3 — the geometric core: monomial collapse + per-context relations.)**

This is the paper's `prop:orthogonal-correctness`, without a sign-fixing assumption.  It
produces the order relabeling `σ`, a nonzero signed diagonal scaling `μ`, a row-sign diagonal
`ν`, the signed monomial form `M = diagonal μ · permMat σ`, and the per-context structural
relations `B'₀ M = diagonal ν permMat σ B₀`, `B'ₖ M = diagonal ν permMat σ Bₖ`.  It is
everything in `orthogonal_collapse` except the order-preservation `InSG σ`, derived from
these relations below.

The SUM TRICK (`sum_latent_diff_unprimed`) and orthogonalization
(`orthogonal_of_diag_conj`) produce an orthogonal `O`; a decreasing topological
induction on its rows (`central_rank2_eq` support + orthogonality + unit norm)
makes `O` a signed permutation, hence `M = diagonal μ · permMat σ`.  The
per-context relations follow by the signed-Cholesky read-off, whose
σ-triangularity input is read off from the `(b,a)` entry of `central_rank2_eq`
(`monomial_relations_from_orthogonal_core`). -/
private theorem monomial_relations (S S' : Solution d p K)
    (hcov : Function.Bijective S.target) (hcov' : Function.Bijective S'.target)
    (hNondeg : ∀ k, S.Theta k ≠ S.Theta0)
    (hΘ0 : S.Theta0 = S'.Theta0) (hΘ : ∀ k, S.Theta k = S'.Theta k)
    {M : Matrix (Fin d) (Fin d) ℝ} (hMunit : IsUnit M) (hM : S'.H = M * S.H) :
    ∃ (σ : Equiv.Perm (Fin d)) (μ ν : Fin d → ℝ),
      (∀ i, μ i ≠ 0) ∧ (∀ i, ν i = 1 ∨ ν i = -1) ∧
      M = Matrix.diagonal μ * permMat σ ∧
      S'.B0 * M = Matrix.diagonal ν * permMat σ * S.B0 ∧
      (∀ k, S'.Bint k * M = Matrix.diagonal ν * permMat σ * S.Bint k) := by
  classical
  let τ : Fin K ≃ Fin d := Equiv.ofBijective S.target hcov
  let kof : Fin d → Fin K := τ.symm
  have hkof : ∀ n, S.target (kof n) = n := by
    intro n
    exact τ.apply_symm_apply n
  let ψ : Fin d → Fin d := fun n => S'.target (kof n)
  have hψbij : Function.Bijective ψ := by
    constructor
    · intro a b hab
      apply τ.symm.injective
      exact hcov'.1 hab
    · intro y
      obtain ⟨k, hk⟩ := hcov'.2 y
      refine ⟨τ k, ?_⟩
      simp [ψ, kof, hk]
  let σ : Equiv.Perm (Fin d) := Equiv.ofBijective ψ hψbij
  have hσtarget : ∀ n, S'.target (kof n) = σ n := by
    intro n
    rfl
  have hdiag :
      M.transpose * Matrix.diagonal (fun m => (S'.lam (kof (σ.symm m))) ^ 2) * M
        = Matrix.diagonal (fun n => (S.lam (kof n)) ^ 2) :=
    diagonal_conj_from_sum_trick S S' hM hΘ0 hΘ kof hkof σ hσtarget
  have hd : ∀ n, 0 < (S.lam (kof n)) ^ 2 := by
    intro n
    exact sq_pos_of_ne_zero (ne_of_gt (S.hlam (kof n)))
  have hd' : ∀ m, 0 < (S'.lam (kof (σ.symm m))) ^ 2 := by
    intro m
    exact sq_pos_of_ne_zero (ne_of_gt (S'.hlam (kof (σ.symm m))))
  have hO :
      (Matrix.diagonal (fun m => Real.sqrt ((S'.lam (kof (σ.symm m))) ^ 2)) * M
          * Matrix.diagonal (fun n => (Real.sqrt ((S.lam (kof n)) ^ 2))⁻¹)).transpose
        * (Matrix.diagonal (fun m => Real.sqrt ((S'.lam (kof (σ.symm m))) ^ 2)) * M
          * Matrix.diagonal (fun n => (Real.sqrt ((S.lam (kof n)) ^ 2))⁻¹)) = 1 :=
    orthogonal_of_diag_conj hd hd' hdiag
  exact monomial_relations_from_orthogonal_core S S' hNondeg hΘ0 hΘ hMunit hM
    kof hkof σ hσtarget hdiag hO

private theorem orthogonal_collapse (S S' : Solution d p K)
    (hcov : Function.Bijective S.target) (hcov' : Function.Bijective S'.target)
    (hNondeg : ∀ k, S.Theta k ≠ S.Theta0)
    (hΘ0 : S.Theta0 = S'.Theta0) (hΘ : ∀ k, S.Theta k = S'.Theta k)
    {M : Matrix (Fin d) (Fin d) ℝ} (hMunit : IsUnit M) (hM : S'.H = M * S.H) :
    ∃ (σ : Equiv.Perm (Fin d)) (μ ν : Fin d → ℝ), S.InSG σ ∧
      (∀ i, μ i ≠ 0) ∧ (∀ i, ν i = 1 ∨ ν i = -1) ∧
      M = Matrix.diagonal μ * permMat σ ∧
      S'.B0 * M = Matrix.diagonal ν * permMat σ * S.B0 ∧
      (∀ k, S'.Bint k * M = Matrix.diagonal ν * permMat σ * S.Bint k) := by
  -- Get the monomial collapse and per-context relations (the isolated residual core).
  obtain ⟨σ, μ, ν, hμ, hν, hMeq, hB0rel, hBintrel⟩ :=
    monomial_relations S S' hcov hcov' hNondeg hΘ0 hΘ hMunit hM
  refine ⟨σ, μ, ν, ?_, hμ, hν, hMeq, hB0rel, hBintrel⟩
  -- **(S4) Derive `InSG σ`** from the signed `B'₀ M` relation and monomial form.
  -- Signed conjugation read-off: row signs and nonzero column scalings do not affect support.
  have hB0' : S'.B0 =
      Matrix.diagonal ν * permMat σ * S.B0 * (permMat σ).transpose
        * Matrix.diagonal (fun i => (μ i)⁻¹) :=
    conj_readoff hμ hMeq hB0rel
  intro j i hEdge
  -- `Edge j i ⟹ i < j` (acyclicity), so `i ≠ j`.
  have hij : i < j := S.hAcyc j i hEdge
  have hine : i ≠ j := ne_of_lt hij
  -- `B₀ i j ≠ 0` since `Edge j i` is in the off-diagonal support of `B₀`.
  have hB0ne : S.B0 i j ≠ 0 := (S.hB0supp i j hine).mpr hEdge
  -- Suppose `σ j < σ i`; read off `B'₀` at the upper-triangular zero entry `(σ i, σ j)`.
  by_contra hnotlt
  push_neg at hnotlt  -- `σ j ≤ σ i`
  have hlt : σ j < σ i := lt_of_le_of_ne hnotlt (fun h => hine.symm (σ.injective h))
  -- `B'₀ (σ i) (σ j) = 0` by upper-triangularity (`σ j < σ i`).
  have hzero : S'.B0 (σ i) (σ j) = 0 := S'.hB0up (σ i) (σ j) hlt
  -- But the read-off gives `B'₀ (σ i) (σ j) = ν (σ i) · B₀ i j · (μ (σ j))⁻¹ ≠ 0`.
  rw [hB0', Matrix.mul_apply] at hzero
  have hentry : (permMat σ * S.B0 * (permMat σ).transpose) (σ i) (σ j) = S.B0 i j := by
    rw [permMat_conj_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have hAentry :
      (Matrix.diagonal ν * permMat σ * S.B0 * (permMat σ).transpose) (σ i) (σ j)
        = ν (σ i) * S.B0 i j := by
    calc
      (Matrix.diagonal ν * permMat σ * S.B0 * (permMat σ).transpose) (σ i) (σ j)
          = (Matrix.diagonal ν * (permMat σ * S.B0 * (permMat σ).transpose))
              (σ i) (σ j) := by
            simp only [Matrix.mul_assoc]
      _ = ν (σ i) * (permMat σ * S.B0 * (permMat σ).transpose) (σ i) (σ j) := by
            rw [diagonal_mul_apply]
      _ = ν (σ i) * S.B0 i j := by rw [hentry]
  have hνne : ν (σ i) ≠ 0 := by
    rcases hν (σ i) with h | h <;> rw [h] <;> norm_num
  rw [Finset.sum_eq_single (σ j)] at hzero
  · rw [Matrix.diagonal_apply_eq, hAentry] at hzero
    exact (mul_ne_zero (mul_ne_zero hνne hB0ne) (inv_ne_zero (hμ (σ j)))) hzero
  · intro x _ hx; rw [Matrix.diagonal_apply_ne _ hx, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **(L4) Orthogonal correctness (full statement).**

Given the recovered invertible change-of-basis `M` with `H' = M H`, there is a single
order-preserving relabeling `σ ∈ S(𝒢)`, a nonzero signed diagonal scaling `μ`, and a row-sign
diagonal `ν` such that `M = diagonal μ · permMat σ` and, in every context, the structural
matrices satisfy `B'ₖ M = diagonal ν permMat σ Bₖ` (`k=0` and interventional), and the
intervention targets relabel as `i'ₖ = σ(iₖ)`.

The monomial collapse `orthogonal_collapse` supplies `σ`, `μ`, `ν`, `InSG σ` and the
per-context signed relations; the order-preservation `InSG σ` and the target relabeling
`i'ₖ = σ(iₖ)` are derived from those relations. -/
theorem exists_orderPerm (S S' : Solution d p K)
    (hcov : Function.Bijective S.target) (hcov' : Function.Bijective S'.target)
    (hNondeg : ∀ k, S.Theta k ≠ S.Theta0)
    (hΘ0 : S.Theta0 = S'.Theta0) (hΘ : ∀ k, S.Theta k = S'.Theta k)
    {M : Matrix (Fin d) (Fin d) ℝ} (hMunit : IsUnit M) (hM : S'.H = M * S.H) :
    ∃ (σ : Equiv.Perm (Fin d)) (μ ν : Fin d → ℝ), S.InSG σ ∧
      (∀ i, μ i ≠ 0) ∧ (∀ i, ν i = 1 ∨ ν i = -1) ∧
      M = Matrix.diagonal μ * permMat σ ∧
      S'.B0 * M = Matrix.diagonal ν * permMat σ * S.B0 ∧
      (∀ k, S'.Bint k * M = Matrix.diagonal ν * permMat σ * S.Bint k) ∧
      (∀ k, S'.target k = σ (S.target k)) := by
  obtain ⟨σ, μ, ν, hσ, hμ, hν, hMeq, hB0rel, hBintrel⟩ :=
    orthogonal_collapse S S' hcov hcov' hNondeg hΘ0 hΘ hMunit hM
  exact ⟨σ, μ, ν, hσ, hμ, hν, hMeq, hB0rel, hBintrel,
    fun k => target_readoff S S' k (hNondeg k) hν (hBintrel k) hB0rel⟩

/-! ### (L5) Deriving the conclusion from (L4) -/

/-- **Uniqueness (⊆ direction of Theorem 2).**  If every latent node is intervened on
(`hcov`), every intervention is non-degenerate (`hNondeg`, the paper's genericity /
Assumption 1(b): `Θ_k ≠ Θ_0`, so each context is observably distinct), and two
solutions produce the same precision matrices in every context, then they are related
by a single order-preserving relabeling `σ ∈ S(𝒢)` and nonzero signed diagonal scaling.

The proof is the clean orthogonal-matrix route:
(L1) `H' = M H` for an invertible `M` (`exists_change_of_basis`, from rowspace equality
forced by `Θ₀ = Θ₀'`); (L2) the per-context Gram identity `BᵀB = (B'M)ᵀ(B'M)`
(`gram_identity`); (L3) hence `Oₖ = B'ₖ M Bₖ⁻¹` is orthogonal (`gram_to_orthogonal`);
(L4) the orthogonal-correctness collapse to a single order-preserving permutation
(`exists_orderPerm`, the geometric core); (L5) the signed conclusion is obtained by
substituting the monomial form of `M`. -/
theorem disentanglement_uniqueness (S S' : Solution d p K)
    (hcov : Function.Bijective S.target) (hcov' : Function.Bijective S'.target)
    (hNondeg : ∀ k, S.Theta k ≠ S.Theta0)
    (hΘ0 : S.Theta0 = S'.Theta0) (hΘ : ∀ k, S.Theta k = S'.Theta k) :
    ∃ (σ : Equiv.Perm (Fin d)) (μ ν : Fin d → ℝ), S.InSG σ ∧
      (∀ i, μ i ≠ 0) ∧ (∀ i, ν i = 1 ∨ ν i = -1) ∧
      S'.H = Matrix.diagonal μ * permMat σ * S.H ∧
      S'.B0 * (Matrix.diagonal μ * permMat σ) =
        Matrix.diagonal ν * permMat σ * S.B0 ∧
      (∀ k, S'.Bint k * (Matrix.diagonal μ * permMat σ) =
        Matrix.diagonal ν * permMat σ * S.Bint k) ∧
      (∀ k, S'.target k = σ (S.target k)) := by
  -- (L1) recover the invertible change-of-basis `M` with `H' = M H`.
  obtain ⟨M, hMunit, hM⟩ := exists_change_of_basis S S' hΘ0
  -- (L4) the orthogonal-correctness collapse (the isolated hard core).
  obtain ⟨σ, μ, ν, hσ, hμ, hν, hMeq, hB0rel, hBintrel, htarget⟩ :=
    exists_orderPerm S S' hcov hcov' hNondeg hΘ0 hΘ hMunit hM
  refine ⟨σ, μ, ν, hσ, hμ, hν, ?_, ?_, ?_, htarget⟩
  · -- `H' = diagonal μ permMat σ H`.
    rw [hM, hMeq]
  · -- Signed observational relation after substituting `M`.
    rwa [hMeq] at hB0rel
  · -- Signed interventional relations after substituting `M`.
    intro k
    rw [← hMeq]
    exact hBintrel k

end Causalean.Discovery.LinearDisentanglement
