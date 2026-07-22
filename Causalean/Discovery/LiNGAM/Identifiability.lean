/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.LinearAlgebra.MonomialMatrix

/-!
# LiNGAM structural identifiability

This is the structural linear-algebra step in the LiNGAM identification argument
(Shimizu et al. 2006): once two coefficient matrices are related by a generalized
permutation, acyclicity and unit-diagonal normalization pin the coefficient matrix
uniquely.

Write `C = I − B` for the coefficient matrix of a LiNGAM model `x = B x + e`
(so `x = C⁻¹ e`, `C` has unit diagonal because `Bᵢᵢ = 0`, and `C` is lower
triangular in the causal order because `B` is acyclic).  ICA identifiability says
that two observationally-equivalent models have mixing matrices related by a
generalized permutation, i.e. `C' = W C` with `W` a permutation composed with a
non-zero diagonal scaling: `C' i j = d i · C (τ i) j` with `d i ≠ 0`.

The public theorem `lingam_identifiable` specializes
`Causalean.Mathlib.LinearAlgebra.eq_of_genPerm_triangular_unitDiag` to `C = I − B`.
The kurtosis route in `LiNGAMKurtosis.lean` supplies the generalized-permutation
relation through column support, so this file isolates the deterministic
acyclicity-and-unit-diagonal pinning step.
-/

namespace Causalean.Discovery.LiNGAM

open Causalean.Mathlib.LinearAlgebra
open scoped BigOperators

/-- **LiNGAM coefficient identifiability (modulo ICA).**  Two LiNGAM coefficient
matrices `B, B'` with zero diagonal (`Bᵢᵢ = 0`) and `B` acyclic in causal order `σ`
(`B i j = 0` whenever `σ i < σ j`) that are related, via ICA identifiability, by a
generalized permutation of their `I − B` matrices (`(1 − B') i j = d i · (1 − B) (τ i) j`)
must be equal.  This packages `eq_of_genPerm_triangular_unitDiag` for `C = I − B`. -/
theorem lingam_identifiable {n : ℕ} {B B' : Matrix (Fin n) (Fin n) ℝ}
    (hBdiag : ∀ i, B i i = 0) (hB'diag : ∀ i, B' i i = 0)
    {σ : Equiv.Perm (Fin n)} (hBacyc : ∀ i j, σ i < σ j → B i j = 0)
    {τ : Equiv.Perm (Fin n)} {d : Fin n → ℝ}
    (hICA : ∀ i j, (1 - B') i j = d i * (1 - B) (τ i) j) :
    B = B' := by
  have hC : (1 - B) = (1 - B') := by
    refine eq_of_genPerm_triangular_unitDiag (σ := σ) (τ := τ) (d := d) ?_ ?_ ?_ hICA
    · intro i; rw [Matrix.sub_apply, Matrix.one_apply_eq, hBdiag i, sub_zero]
    · intro i; rw [Matrix.sub_apply, Matrix.one_apply_eq, hB'diag i, sub_zero]
    · intro i j hlt
      have hij : i ≠ j := fun h => (ne_of_lt hlt) (congrArg σ h)
      rw [Matrix.sub_apply, Matrix.one_apply_ne hij, hBacyc i j hlt, sub_zero]
  exact sub_right_injective hC

end Causalean.Discovery.LiNGAM
