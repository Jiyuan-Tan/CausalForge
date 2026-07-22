/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension.Irreducibility

/-!
# Chain dimension for complex affine algebraic sets

This file defines exact affine Zariski dimension using strict chains of
nonempty irreducible affine-closed subsets.
-/

namespace Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension

noncomputable section

/-- Exact affine Zariski dimension is the largest number of strict containments
in a chain of nonempty irreducible polynomially closed subsets of a set. -/
def HasAffineZariskiDimension {ι : Type*} (d : ℕ) (Z : Set (ι → ℂ)) : Prop :=
  (∃ chain : Fin (d + 1) → Set (ι → ℂ),
      StrictMono chain ∧
      (∀ i, IsIrreducibleAffineClosed (chain i)) ∧
      (∀ i, chain i ⊆ Z)) ∧
  ¬ ∃ chain : Fin (d + 2) → Set (ι → ℂ),
      StrictMono chain ∧
      (∀ i, IsIrreducibleAffineClosed (chain i)) ∧
      (∀ i, chain i ⊆ Z)

end

end Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension
