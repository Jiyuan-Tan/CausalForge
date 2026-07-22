/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Affine Zariski closure over the complex numbers

This file defines affine Zariski closure by the vanishing ideal and proves its
elementary closure laws, including finite unions and density of principal open
sets.
-/

namespace Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension

noncomputable section

/-- Algebraic closure in a complex affine space. -/
def affineZariskiClosure {ι : Type*} (A : Set (ι → ℂ)) : Set (ι → ℂ) :=
  MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ A)

/-- Every set is contained in its affine Zariski closure. -/
lemma affineZariskiClosure_extensive {ι : Type*} (A : Set (ι → ℂ)) :
    A ⊆ affineZariskiClosure A :=
  MvPolynomial.zeroLocus_vanishingIdeal_le A

/-- Affine Zariski closure is monotone. -/
lemma affineZariskiClosure_mono {ι : Type*} {A B : Set (ι → ℂ)} (h : A ⊆ B) :
    affineZariskiClosure A ⊆ affineZariskiClosure B := by
  exact MvPolynomial.zeroLocus_anti_mono
    (MvPolynomial.vanishingIdeal_anti_mono h)

/-- Affine Zariski closure is idempotent. -/
lemma affineZariskiClosure_idem {ι : Type*} (A : Set (ι → ℂ)) :
    affineZariskiClosure (affineZariskiClosure A) = affineZariskiClosure A := by
  apply Set.Subset.antisymm
  · intro x hx P hP
    exact hx P (fun y hy => hy P hP)
  · exact affineZariskiClosure_extensive _

/-- A closed affine set is the zero locus of its vanishing ideal. -/
lemma affineZariskiClosure_eq_zeroLocus {ι : Type*}
    {Z : Set (ι → ℂ)} (hZ : affineZariskiClosure Z = Z) :
    Z = MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ Z) := by
  exact hZ.symm

/-- The intersection of two affine-closed sets is affine-closed. -/
lemma affineZariskiClosure_inter {ι : Type*}
    {A B : Set (ι → ℂ)}
    (hA : affineZariskiClosure A = A) (hB : affineZariskiClosure B = B) :
    affineZariskiClosure (A ∩ B) = A ∩ B := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨hA ▸ affineZariskiClosure_mono Set.inter_subset_left hx,
      hB ▸ affineZariskiClosure_mono Set.inter_subset_right hx⟩
  · exact affineZariskiClosure_extensive _

/-- The zero set of one multivariate polynomial is affine-closed. -/
lemma affineZariskiClosure_zero_of_polynomial {ι : Type*}
    (P : MvPolynomial ι ℂ) :
    affineZariskiClosure {x | MvPolynomial.eval x P = 0} =
      {x | MvPolynomial.eval x P = 0} := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx P (fun y hy => by simpa [MvPolynomial.aeval_def] using hy)
  · exact affineZariskiClosure_extensive _

/-- The union of two affine-closed sets is affine-closed. -/
lemma affineZariskiClosure_union {ι : Type*} {A B : Set (ι → ℂ)}
    (hA : affineZariskiClosure A = A) (hB : affineZariskiClosure B = B) :
    affineZariskiClosure (A ∪ B) = A ∪ B := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hnot
    have hxA : x ∉ A := fun h => hnot (Or.inl h)
    have hxB : x ∉ B := fun h => hnot (Or.inr h)
    have hxAc : x ∉ affineZariskiClosure A := by simpa [hA] using hxA
    have hxBc : x ∉ affineZariskiClosure B := by simpa [hB] using hxB
    simp only [affineZariskiClosure, MvPolynomial.mem_zeroLocus_iff,
      MvPolynomial.aeval_def] at hxAc hxBc
    push_neg at hxAc hxBc
    obtain ⟨P, hPA, hPx⟩ := hxAc
    obtain ⟨Q, hQB, hQx⟩ := hxBc
    have hpq : P * Q ∈ MvPolynomial.vanishingIdeal ℂ (A ∪ B) := by
      intro y hy
      rcases hy with hy | hy
      · rw [map_mul, hPA y hy, zero_mul]
      · rw [map_mul, hQB y hy, mul_zero]
    have := hx (P * Q) hpq
    rw [map_mul] at this
    exact mul_ne_zero hPx hQx this
  · exact affineZariskiClosure_extensive _

/-- The nonvanishing locus of a nonzero polynomial is Zariski dense. -/
lemma affineZariskiClosure_nonvanishing_eq_univ {ι : Type*}
    (P : MvPolynomial ι ℂ) (hP : P ≠ 0) :
    affineZariskiClosure {x : ι → ℂ | MvPolynomial.eval x P ≠ 0} = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x Q hQ
  have hmul_eval : ∀ y : ι → ℂ, MvPolynomial.eval y (Q * P) = 0 := by
    intro y
    by_cases hy : MvPolynomial.eval y P = 0
    · simp [hy]
    · rw [map_mul]
      have hQy : MvPolynomial.eval y Q = 0 := by
        simpa [MvPolynomial.aeval_def, MvPolynomial.eval₂_id] using hQ y hy
      rw [hQy, zero_mul]
  have hmul : Q * P = 0 := by
    apply MvPolynomial.funext
    exact hmul_eval
  have hQzero : Q = 0 := (mul_eq_zero.mp hmul).resolve_right hP
  simp [hQzero]

end

end Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension
