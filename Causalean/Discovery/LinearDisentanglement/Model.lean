/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

/-!
# Linear causal disentanglement: model layer

Formalization of the setup of Squires, Seigal, Bhate & Uhler, *Linear Causal
Disentanglement via Interventions* (ICML 2023), `arXiv:2211.16467`.

We work over `d` latent variables (`Fin d`) and `p ≥ d` observed variables
(`Fin p`).  The latent DAG `𝒢` is ordered so that an edge `j → i` implies `j > i`;
this makes the structural matrices upper triangular in the `Fin d` order.

For a fixed context, the latent SEM is `Z = A Z + Ω^{1/2} ε`, equivalently
`Z = B⁻¹ ε` with `B = Ω^{-1/2}(I − A)`.  The observed vector is `X = G Z` with
`G ∈ ℝ^{p×d}` full column rank, and `H := G⁺` its left inverse (a full-**row**-rank
`d × p` matrix with `H G = I_d`).  The only **observable** content is the family of
precision matrices `Θ_k = Hᵀ Bₖᵀ Bₖ H ∈ ℝ^{p×p}` (one per context).

We take the **algebraic** (matrix-level) view of the paper's Theorem 2: the data of
a disentanglement model is a tuple `(H, {B_k}, {i_k}, {λ_k})` satisfying the
structural assumptions, and identifiability compares two such tuples that produce
the *same* family `{Θ_k}`.  No Moore–Penrose pseudoinverse is needed: `H` enters
only through `LinearIndependent ℝ H` (full row rank) and the formula for `Θ_k`.

Conventions for a `Solution d p K`:
* context `0` is observational with matrix `B0`; contexts `1 … K` are interventional
  with matrices `Bint k`, intervention target `target k`, and (perfect-intervention)
  scaling `lam k > 0`;
* `Edge j i` means the latent edge `j → i` (`j` a parent of `i`), forced by `hAcyc`
  to satisfy `i < j`;
* `B0` is upper triangular (`B0 i j = 0` for `j < i`), has positive diagonal, and its
  off-diagonal support is exactly `Edge` — this is what *defines* `𝒢`;
* `hInt` is Assumption 1(b) specialized to perfect interventions (Assumption 2):
  `Bₖ = B₀ + e_{iₖ} cₖᵀ` with `cₖ = λₖ e_{iₖ} − B₀ᵀ e_{iₖ}`.

`S(𝒢)` is the set of node relabelings preserving edge orientation
(`Edge j i → σ i < σ j`); `permMat σ` is the corresponding permutation matrix
`(P_σ)_{ij} = ⟦i = σ j⟧`, matching the paper.
-/

namespace Causalean.Discovery.LinearDisentanglement

open scoped BigOperators

/-- Standard basis (column) vector `e_i : Fin d → ℝ`, `e_i j = ⟦j = i⟧`. -/
abbrev stdVec (d : ℕ) (i : Fin d) : Fin d → ℝ := Pi.single i (1 : ℝ)

/-- The permutation matrix of `σ`, with `(permMat σ) i j = 1` if `i = σ j` and `0`
otherwise — the convention `(P_σ)_{ij} = ⟦i = σ(j)⟧` of the paper. -/
def permMat {d : ℕ} (σ : Equiv.Perm (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => if i = σ j then (1 : ℝ) else 0

/-- A linear causal disentanglement model with `d` latent variables, `p` observed
variables, and `K` interventional contexts (plus one observational context). -/
structure Solution (d p K : ℕ) where
  /-- The (transpose of the) mixing pseudoinverse: a `d × p` matrix. -/
  H : Matrix (Fin d) (Fin p) ℝ
  /-- `H` has full row rank: its rows are linearly independent. -/
  hH : LinearIndependent ℝ (fun i : Fin d => (H i : Fin p → ℝ))
  /-- The latent DAG edge relation; `Edge j i` means `j → i`. -/
  Edge : Fin d → Fin d → Prop
  /-- Edges respect the node order: `j → i` implies `i < j`. -/
  hAcyc : ∀ j i, Edge j i → i < j
  /-- Observational structural matrix `B₀`. -/
  B0 : Matrix (Fin d) (Fin d) ℝ
  /-- `B₀` is upper triangular in the node order. -/
  hB0up : ∀ i j, j < i → B0 i j = 0
  /-- `B₀` has positive diagonal. -/
  hB0pos : ∀ i, 0 < B0 i i
  /-- The off-diagonal support of `B₀` is exactly the edge set: this defines `𝒢`. -/
  hB0supp : ∀ i j, i ≠ j → (B0 i j ≠ 0 ↔ Edge j i)
  /-- Interventional structural matrices `Bₖ`, `k ∈ {1,…,K}`. -/
  Bint : Fin K → Matrix (Fin d) (Fin d) ℝ
  /-- The intervention target `iₖ` of context `k`. -/
  target : Fin K → Fin d
  /-- The perfect-intervention scaling `λₖ`. -/
  lam : Fin K → ℝ
  /-- `λₖ > 0`. -/
  hlam : ∀ k, 0 < lam k
  /-- Assumption 1(b) + Assumption 2 (perfect single-node interventions):
  `Bₖ = B₀ + e_{iₖ} cₖᵀ` with `cₖ = λₖ e_{iₖ} − B₀ᵀ e_{iₖ}`. -/
  hInt : ∀ k, Bint k =
    B0 + Matrix.vecMulVec (stdVec d (target k))
      (fun j => lam k * stdVec d (target k) j - B0 (target k) j)

namespace Solution

variable {d p K : ℕ}

/-- The observational precision matrix `Θ₀ = Hᵀ B₀ᵀ B₀ H ∈ ℝ^{p×p}`. -/
def Theta0 (S : Solution d p K) : Matrix (Fin p) (Fin p) ℝ :=
  S.H.transpose * S.B0.transpose * S.B0 * S.H

/-- The interventional precision matrix `Θ_k = Hᵀ Bₖᵀ Bₖ H ∈ ℝ^{p×p}`. -/
def Theta (S : Solution d p K) (k : Fin K) : Matrix (Fin p) (Fin p) ℝ :=
  S.H.transpose * (S.Bint k).transpose * (S.Bint k) * S.H

/-- The order-preserving relabelings `S(𝒢)`: permutations `σ` with `σ i < σ j` for
every edge `j → i`. -/
def InSG (S : Solution d p K) (σ : Equiv.Perm (Fin d)) : Prop :=
  ∀ j i, S.Edge j i → σ i < σ j

end Solution

/-! ### Basic facts about permutation matrices -/

/-- `permMat σ` is orthogonal: `permMat σ * (permMat σ)ᵀ = 1`. -/
theorem permMat_mul_transpose {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    permMat σ * (permMat σ).transpose = 1 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.transpose_apply, permMat, Matrix.of_apply]
  rw [Finset.sum_eq_single (σ.symm i)]
  · simp only [Equiv.apply_symm_apply]
    by_cases h : i = k
    · subst h; simp
    · simp [h, Ne.symm h]
  · intro j _ hj
    have : i ≠ σ j := fun h => hj (by rw [h, Equiv.symm_apply_apply])
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `permMat σ` is orthogonal: `(permMat σ)ᵀ * permMat σ = 1`. -/
theorem permMat_transpose_mul {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    (permMat σ).transpose * permMat σ = 1 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.transpose_apply, permMat, Matrix.of_apply]
  rw [Finset.sum_eq_single (σ i)]
  · simp [σ.injective.eq_iff]
  · intro j _ hj
    simp [hj]
  · intro h; exact absurd (Finset.mem_univ _) h

end Causalean.Discovery.LinearDisentanglement
