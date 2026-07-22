/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

/-! # Generalized-permutation (monomial) matrices

This file collects the linear-algebra facts about generalized-permutation (monomial) matrices
that underlie linear causal-discovery identification arguments. A generalized-permutation matrix
has exactly one non-zero entry in each row and column — equivalently, it is a permutation composed
with a non-zero diagonal rescaling. Such matrices are the ambiguity group of independent component
analysis: a mixing matrix is recovered only up to relabelling and rescaling its columns. The three
results here are: (1) an invertible matrix with at most one non-zero entry per column is
automatically of this generalized-permutation form; (2) a simultaneous row/column permutation of a
lower-triangular matrix with non-zero diagonal keeps a non-zero diagonal exactly when the two
permutations agree; and (3) two unit-diagonal matrices related by a generalized permutation, one of
them triangular in a causal order, must be equal. They are consumed by the LiNGAM and
linear-causal-disentanglement developments to turn an ICA-level identification (sharp only up to
generalized permutation) into a sharp structural identification.
-/

namespace Causalean.Mathlib.LinearAlgebra

open scoped Matrix BigOperators

/-- An invertible square matrix with at most one non-zero entry per column is a generalized
permutation matrix: there are a permutation `τ` and non-zero scalings `d` with
`W i j = if j = τ i then d i else 0`. -/
theorem genPerm_of_invertible_of_colSupport {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : IsUnit W.det)
    (hcol : ∀ j i k, i ≠ k → W i j = 0 ∨ W k j = 0) :
    ∃ (τ : Equiv.Perm (Fin n)) (d : Fin n → ℝ), (∀ i, d i ≠ 0) ∧
      ∀ i j, W i j = if j = τ i then d i else 0 := by
  classical
  have hcol_nonzero : ∀ j, ∃ i, W i j ≠ 0 := by
    intro j
    by_contra hzero
    have hcol_zero : ∀ i, W i j = 0 := by
      intro i
      by_contra hi
      exact hzero ⟨i, hi⟩
    exact hW.ne_zero (Matrix.det_eq_zero_of_column_eq_zero j hcol_zero)
  let ρ : Fin n → Fin n := fun j => Classical.choose (hcol_nonzero j)
  have hρ_ne : ∀ j, W (ρ j) j ≠ 0 := by
    intro j
    exact Classical.choose_spec (hcol_nonzero j)
  have hρ_unique : ∀ j i, W i j ≠ 0 → i = ρ j := by
    intro j i hi
    by_contra hne
    cases hcol j i (ρ j) hne with
    | inl h => exact hi h
    | inr h => exact hρ_ne j h
  have hρ_zero : ∀ j i, i ≠ ρ j → W i j = 0 := by
    intro j i hi
    by_contra hne
    exact hi (hρ_unique j i hne)
  have hρ_surj : Function.Surjective ρ := by
    by_contra hsurj
    have hmissing : ∃ i, ∀ j, ρ j ≠ i := by
      simpa [Function.Surjective] using hsurj
    obtain ⟨i, hi⟩ := hmissing
    have hrow_zero : ∀ j, W i j = 0 := by
      intro j
      exact hρ_zero j i (fun h => hi j h.symm)
    exact hW.ne_zero (Matrix.det_eq_zero_of_row_eq_zero i hrow_zero)
  have hρ_inj : Function.Injective ρ := (Finite.injective_iff_surjective).2 hρ_surj
  let ρE : Equiv.Perm (Fin n) := Equiv.ofBijective ρ ⟨hρ_inj, hρ_surj⟩
  let τ : Equiv.Perm (Fin n) := ρE.symm
  let d : Fin n → ℝ := fun i => W i (τ i)
  refine ⟨τ, d, ?_, ?_⟩
  · intro i
    have hρτ : ρ (τ i) = i := by
      change ρE (ρE.symm i) = i
      simp
    have hne := hρ_ne (τ i)
    simpa [d, hρτ] using hne
  · intro i j
    by_cases hj : j = τ i
    · simp [d, hj]
    · have hiρ : i ≠ ρ j := by
        intro hi
        apply hj
        calc
          j = ρE.symm (ρE j) := by simp
          _ = ρE.symm (ρ j) := rfl
          _ = ρE.symm i := by rw [← hi]
          _ = τ i := rfl
      have hzero : W i j = 0 := hρ_zero j i hiρ
      simp [hj, hzero]

/-- **Permutation uniqueness for lower-triangular matrices** (LiNGAM Appendix A, Lemma 1).
Let `M` be a lower-triangular matrix (`M i j = 0` whenever `i < j`) with non-zero diagonal.
For permutations `σ, τ` of the index set, the row/column-permuted matrix `(i ↦ M (σ i) (τ i))`
has a non-zero diagonal if and only if `σ = τ`. -/
theorem perm_uniqueness {n : ℕ} {K : Type*} [Zero K] {M : Matrix (Fin n) (Fin n) K}
    (hLT : ∀ i j, i < j → M i j = 0) (hdiag : ∀ i, M i i ≠ 0)
    {σ τ : Equiv.Perm (Fin n)} :
    (∀ i, M (σ i) (τ i) ≠ 0) ↔ σ = τ := by
  constructor
  · intro h
    have hge : ∀ i, (τ i : ℕ) ≤ (σ i : ℕ) := by
      intro i
      by_contra hlt
      push_neg at hlt
      exact h i (hLT (σ i) (τ i) (by exact_mod_cast hlt))
    have hsum : ∑ i, (σ i : ℕ) = ∑ i, (τ i : ℕ) := by
      rw [Equiv.sum_comp σ (fun i => (i : ℕ)), Equiv.sum_comp τ (fun i => (i : ℕ))]
    have heq : ∀ i, (σ i : ℕ) = (τ i : ℕ) := by
      have hle : ∀ i ∈ Finset.univ, (τ i : ℕ) ≤ (σ i : ℕ) := fun i _ => hge i
      have := (Finset.sum_eq_sum_iff_of_le hle).1 hsum.symm
      intro i; exact ((this i (Finset.mem_univ i)).symm)
    exact Equiv.ext fun i => Fin.val_injective (heq i)
  · rintro rfl i
    exact hdiag (σ i)

/-- **Generalized-permutation reduction.** Let `C, C'` be matrices with unit diagonal; suppose `C`
is lower triangular in some causal order `σ` (`C i j = 0` when `σ i < σ j`), and that `C'` is
obtained from `C` by a generalized permutation `C' i j = d i · C (τ i) j`. Then `C = C'`: the unit
diagonal plus triangularity force the underlying permutation to be the identity and every scaling
to be one. (Formerly `Discovery.LiNGAM.lingam_reduction`.) -/
theorem eq_of_genPerm_triangular_unitDiag {n : ℕ} {C C' : Matrix (Fin n) (Fin n) ℝ}
    (hCdiag : ∀ i, C i i = 1) (hC'diag : ∀ i, C' i i = 1)
    {σ : Equiv.Perm (Fin n)} (hCtri : ∀ i j, σ i < σ j → C i j = 0)
    {τ : Equiv.Perm (Fin n)} {d : Fin n → ℝ}
    (hW : ∀ i j, C' i j = d i * C (τ i) j) :
    C = C' := by
  have hne : ∀ i, C (τ i) i ≠ 0 := by
    intro i hzero
    have h := hW i i
    rw [hzero, mul_zero, hC'diag i] at h
    exact one_ne_zero h
  have hle : ∀ i, (σ i : ℕ) ≤ (σ (τ i) : ℕ) := by
    intro i
    by_contra h
    push_neg at h
    exact hne i (hCtri (τ i) i (by exact_mod_cast h))
  have hsum : ∑ i, (σ (τ i) : ℕ) = ∑ i, (σ i : ℕ) :=
    Equiv.sum_comp τ (fun i => (σ i : ℕ))
  have heqσ : ∀ i, (σ (τ i) : ℕ) = (σ i : ℕ) := by
    have hle' : ∀ i ∈ Finset.univ, (σ i : ℕ) ≤ (σ (τ i) : ℕ) := fun i _ => hle i
    exact fun i => ((Finset.sum_eq_sum_iff_of_le hle').1 hsum.symm i (Finset.mem_univ i)).symm
  have hτ : ∀ i, τ i = i := fun i => σ.injective (Fin.val_injective (heqσ i))
  have hd1 : ∀ i, d i = 1 := by
    intro i
    have h := hW i i
    rw [hτ i, hCdiag i, mul_one, hC'diag i] at h
    exact h.symm
  ext i j
  rw [hW i j, hτ i, hd1 i, one_mul]

end Causalean.Mathlib.LinearAlgebra
