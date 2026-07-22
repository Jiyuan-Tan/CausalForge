/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.LinearDisentanglement.Model

/-!
# Linear causal disentanglement: solution orbits under order-preserving permutations

This file proves the solution-orbit direction of the linear-disentanglement
identifiability result.  The definition `Solution.permute` constructs the
relabelled model: it sends `H` to `Pσ H`, conjugates `B₀` and every `Bₖ` by the
permutation matrix, and sends each intervention target `iₖ` to `σ(iₖ)`.  The
order-preservation hypothesis `σ ∈ S(𝒢)` is exactly what keeps the transformed
observational matrix triangular in the ambient node order.

The theorem `sigma_solutions` then proves that this transformed solution has the
same observable precision matrices `Θ₀` and `Θₖ`.  Together with
`disentanglement_identifiability`, it gives the orbit characterization of all
solutions.
-/

namespace Causalean.Discovery.LinearDisentanglement

open scoped Matrix

variable {d p K : ℕ}

/-- Orthogonality telescoping: conjugating `A` by `permMat σ` and permuting the rows
of `H` leaves the quadratic form `Hᵀ Aᵀ A H` unchanged.  Pure consequence of
`(permMat σ)ᵀ * permMat σ = 1`; no order-preservation hypothesis is used. -/
private theorem conj_telescope (σ : Equiv.Perm (Fin d))
    (H : Matrix (Fin d) (Fin p) ℝ) (A : Matrix (Fin d) (Fin d) ℝ) :
    (permMat σ * H).transpose
        * (permMat σ * A * (permMat σ).transpose).transpose
        * (permMat σ * A * (permMat σ).transpose) * (permMat σ * H)
      = H.transpose * A.transpose * A * H := by
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (permMat σ).transpose, permMat_transpose_mul, Matrix.one_mul]

/-- Left multiplication by a permutation matrix permutes the rows. -/
private theorem permMat_mul_apply (σ : Equiv.Perm (Fin d))
    (M : Matrix (Fin d) (Fin p) ℝ) (i : Fin d) (a : Fin p) :
    (permMat σ * M) i a = M (σ.symm i) a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ.symm i)]
  · simp [permMat]
  · intro j _ hj
    have hij : i ≠ σ j := fun h => hj (by rw [h, Equiv.symm_apply_apply])
    simp [permMat, hij]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Conjugation by a permutation matrix relabels both indices. -/
private theorem perm_conj_apply (σ : Equiv.Perm (Fin d))
    (M : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    (permMat σ * M * (permMat σ).transpose) i j =
      M (σ.symm i) (σ.symm j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ.symm j)]
  · rw [permMat_mul_apply]
    simp [permMat]
  · intro a _ ha
    have hja : j ≠ σ a := fun h => ha (by rw [h, Equiv.symm_apply_apply])
    simp [Matrix.transpose_apply, permMat, hja]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A standard basis vector relabels contravariantly under the inverse permutation. -/
private theorem stdVec_perm_symm (σ : Equiv.Perm (Fin d)) (t i : Fin d) :
    stdVec d t (σ.symm i) = stdVec d (σ t) i := by
  unfold stdVec
  by_cases hi : i = σ t
  · subst i
    rw [Equiv.symm_apply_apply]
    simp
  · have hsymm : σ.symm i ≠ t := by
      intro h
      exact hi (by rw [← h, Equiv.apply_symm_apply])
    simp [hi, hsymm]

namespace Solution

/-- Relabeling a solution by an order-preserving permutation gives another valid solution.

The transformed model has mixing pseudoinverse `Pσ H`, observational matrix
`Pσ B₀ Pσᵀ`, interventional matrices `Pσ Bₖ Pσᵀ`, and targets `σ(iₖ)`.  The
order-preservation assumption `σ ∈ S(𝒢)` is essential: it is what keeps the conjugated
observational matrix upper triangular in the ambient node order. -/
def permute (S : Solution d p K) (σ : Equiv.Perm (Fin d)) (hσ : S.InSG σ) :
    Solution d p K where
  H := permMat σ * S.H
  hH := by
    have hrow :
        (fun i : Fin d => ((permMat σ * S.H) i : Fin p → ℝ)) =
          fun i : Fin d => (S.H (σ.symm i) : Fin p → ℝ) := by
      funext i a
      exact permMat_mul_apply σ S.H i a
    rw [hrow]
    exact S.hH.comp σ.symm σ.symm.injective
  Edge := fun j i => S.Edge (σ.symm j) (σ.symm i)
  hAcyc := by
    intro j i hji
    have hlt := hσ (σ.symm j) (σ.symm i) hji
    simpa using hlt
  B0 := permMat σ * S.B0 * (permMat σ).transpose
  hB0up := by
    intro i j hji
    rw [perm_conj_apply]
    by_contra hne
    have hneq : σ.symm i ≠ σ.symm j := by
      intro h
      exact (ne_of_gt hji) (by simpa using congrArg σ h)
    have hedge : S.Edge (σ.symm j) (σ.symm i) :=
      (S.hB0supp (σ.symm i) (σ.symm j) hneq).1 hne
    have hlt : i < j := by
      have := hσ (σ.symm j) (σ.symm i) hedge
      simpa using this
    exact (not_lt_of_gt hji) hlt
  hB0pos := by
    intro i
    rw [perm_conj_apply]
    exact S.hB0pos (σ.symm i)
  hB0supp := by
    intro i j hij
    rw [perm_conj_apply]
    have hneq : σ.symm i ≠ σ.symm j := by
      intro h
      exact hij (by simpa using congrArg σ h)
    exact S.hB0supp (σ.symm i) (σ.symm j) hneq
  Bint := fun k => permMat σ * S.Bint k * (permMat σ).transpose
  target := fun k => σ (S.target k)
  lam := S.lam
  hlam := S.hlam
  hInt := by
    intro k
    ext i j
    rw [S.hInt k]
    simp [perm_conj_apply, Matrix.vecMulVec_apply, stdVec_perm_symm]

end Solution

/-- Every order-preserving relabeling of a solution is a valid transformed solution with
the same observational and interventional precision matrices.

This is the solution-orbit direction: for any `σ ∈ S(𝒢)`, the permuted solution
`S.permute σ hσ` produces exactly the original precision family `{Θ₀, Θₖ}`. -/
theorem sigma_solutions (S : Solution d p K) (σ : Equiv.Perm (Fin d)) (hσ : S.InSG σ) :
    (S.permute σ hσ).Theta0 = S.Theta0
    ∧ ∀ k, (S.permute σ hσ).Theta k = S.Theta k := by
  refine ⟨?_, fun k => ?_⟩
  · change (permMat σ * S.H).transpose
        * (permMat σ * S.B0 * (permMat σ).transpose).transpose
        * (permMat σ * S.B0 * (permMat σ).transpose) * (permMat σ * S.H) = S.Theta0
    rw [conj_telescope]
    rfl
  · change (permMat σ * S.H).transpose
        * (permMat σ * S.Bint k * (permMat σ).transpose).transpose
        * (permMat σ * S.Bint k * (permMat σ).transpose) * (permMat σ * S.H) = S.Theta k
    rw [conj_telescope]
    rfl

end Causalean.Discovery.LinearDisentanglement
