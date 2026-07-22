/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension.Irreducibility

/-! # Finite-valued coordinates on irreducible affine sets

This file proves that a coordinate which takes only finitely many values on a
nonempty irreducible affine algebraic set over the complex numbers must in fact
be constant on that set.  The argument writes the finite value set as the zero
locus of a one-variable product polynomial, so each admissible value carves out
a Zariski-closed piece; irreducibility then forces a single piece to exhaust the
set.  The headline result `irreducible_coordinate_constant_of_finite_range`
supplies the rigidity step used by the polynomial image-dimension development.
-/

namespace Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension

open scoped BigOperators

noncomputable section

private def coordinateValuePolynomial {κ : Type*} (c : κ) (S : Finset ℂ) :
    MvPolynomial κ ℂ :=
  ∏ z ∈ S, (MvPolynomial.X c - MvPolynomial.C z)

private lemma finiteCoordinateRange_closed {κ : Type*} (c : κ) (S : Finset ℂ) :
    affineZariskiClosure {x : κ → ℂ | x c ∈ S} = {x | x c ∈ S} := by
  have heq : {x : κ → ℂ | x c ∈ S} =
      {x | MvPolynomial.eval x (coordinateValuePolynomial c S) = 0} := by
    ext x
    simp [coordinateValuePolynomial, Finset.prod_eq_zero_iff, sub_eq_zero]
  rw [heq]
  exact affineZariskiClosure_zero_of_polynomial _

/-- A regular coordinate taking only finitely many values on a nonempty
irreducible affine algebraic set is constant. -/
theorem irreducible_coordinate_constant_of_finite_range {κ : Type*}
    {Z : Set (κ → ℂ)} (hZ : IsIrreducibleAffineClosed Z)
    (c : κ) (S : Finset ℂ) (hrange : ∀ x ∈ Z, x c ∈ S) :
    ∃ z ∈ S, ∀ x ∈ Z, x c = z := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      obtain ⟨x, hx⟩ := hZ.2.1
      exact (by simpa using hrange x hx)
  | @insert z S hz ih =>
      let A := Z ∩ {x | x c = z}
      let B := Z ∩ {x | x c ∈ S}
      have hhyper : affineZariskiClosure {x : κ → ℂ | x c = z} =
          {x | x c = z} := by
        have heq : {x : κ → ℂ | x c = z} =
            {x | MvPolynomial.eval x (MvPolynomial.X c - MvPolynomial.C z) = 0} := by
          ext x
          simp [sub_eq_zero]
        rw [heq]
        exact affineZariskiClosure_zero_of_polynomial _
      have hA : affineZariskiClosure A = A :=
        affineZariskiClosure_inter hZ.1 hhyper
      have hB : affineZariskiClosure B = B :=
        affineZariskiClosure_inter hZ.1 (finiteCoordinateRange_closed c S)
      have hAB : Z = A ∪ B := by
        ext x
        constructor
        · intro hx
          have := hrange x hx
          rw [Finset.mem_insert] at this
          exact this.elim (fun h => Or.inl ⟨hx, h⟩) (fun h => Or.inr ⟨hx, h⟩)
        · rintro (hx | hx) <;> exact hx.1
      rcases hZ.2.2 A B hA hB hAB with hZA | hZB
      · exact ⟨z, Finset.mem_insert_self z S, fun x hx => (hZA ▸ hx).2⟩
      · obtain ⟨w, hwS, hw⟩ := ih (fun x hx => (hZB ▸ hx).2)
        exact ⟨w, Finset.mem_insert_of_mem hwS, hw⟩

end

end Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension
