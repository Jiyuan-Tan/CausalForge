/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension.ZariskiClosure

/-!
# Irreducible affine-closed sets

This file relates the elementary finite-union definition of irreducibility to
primality of the vanishing ideal and records the strict order reversal between
closed sets and their ideals.
-/

namespace Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension

noncomputable section

/-- An irreducible affine-closed set is a nonempty polynomially closed set that
cannot be expressed as the union of two smaller polynomially closed sets. -/
def IsIrreducibleAffineClosed {ι : Type*} (Z : Set (ι → ℂ)) : Prop :=
  affineZariskiClosure Z = Z ∧ Z.Nonempty ∧
    ∀ Z₁ Z₂ : Set (ι → ℂ),
      affineZariskiClosure Z₁ = Z₁ → affineZariskiClosure Z₂ = Z₂ →
      Z = Z₁ ∪ Z₂ → Z = Z₁ ∨ Z = Z₂

/-- A nonempty affine set has a proper vanishing ideal. -/
lemma vanishingIdeal_ne_top_of_nonempty {ι : Type*} {Z : Set (ι → ℂ)}
    (hZ : Z.Nonempty) : MvPolynomial.vanishingIdeal ℂ Z ≠ ⊤ := by
  rintro htop
  obtain ⟨x, hx⟩ := hZ
  have hone : (1 : MvPolynomial ι ℂ) ∈ MvPolynomial.vanishingIdeal ℂ Z := by
    rw [htop]
    trivial
  simpa using hone x hx

/-- A prime ideal in a finite complex polynomial ring has a nonempty zero locus. -/
lemma nonempty_zeroLocus_of_prime {ι : Type*} [Finite ι]
    (P : Ideal (MvPolynomial ι ℂ)) [P.IsPrime] :
    (MvPolynomial.zeroLocus ℂ P).Nonempty := by
  by_contra hempty
  have htop : MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ P) = ⊤ := by
    rw [Set.not_nonempty_iff_eq_empty.mp hempty,
      MvPolynomial.vanishingIdeal_empty]
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus P] at htop
  exact Ideal.IsPrime.ne_top' htop

/-- A nonempty polynomially closed complex set is irreducible exactly when the
polynomial equations that vanish on it form a prime ideal. -/
theorem irreducibleAffineClosed_iff_isPrime {ι : Type*} [Finite ι]
    {Z : Set (ι → ℂ)} (hclosed : affineZariskiClosure Z = Z)
    (hnonempty : Z.Nonempty) :
    IsIrreducibleAffineClosed Z ↔
      (MvPolynomial.vanishingIdeal ℂ Z).IsPrime := by
  constructor
  · intro hirr
    refine ⟨vanishingIdeal_ne_top_of_nonempty hnonempty, ?_⟩
    intro p q hpq
    let A := Z ∩ {x | MvPolynomial.eval x p = 0}
    let B := Z ∩ {x | MvPolynomial.eval x q = 0}
    have hA : affineZariskiClosure A = A :=
      affineZariskiClosure_inter hclosed (affineZariskiClosure_zero_of_polynomial p)
    have hB : affineZariskiClosure B = B :=
      affineZariskiClosure_inter hclosed (affineZariskiClosure_zero_of_polynomial q)
    have hAB : Z = A ∪ B := by
      ext x
      constructor
      · intro hx
        have hz := hpq x hx
        rw [map_mul, mul_eq_zero] at hz
        rcases hz with hz | hz
        · exact Or.inl ⟨hx, hz⟩
        · exact Or.inr ⟨hx, hz⟩
      · rintro (hx | hx) <;> exact hx.1
    rcases hirr.2.2 A B hA hB hAB with hZA | hZB
    · left
      intro x hx
      have : x ∈ A := hZA ▸ hx
      exact this.2
    · right
      intro x hx
      have : x ∈ B := hZB ▸ hx
      exact this.2
  · intro hprime
    refine ⟨hclosed, hnonempty, ?_⟩
    intro A B hA hB hZ
    by_cases hAI : MvPolynomial.vanishingIdeal ℂ A ≤
        MvPolynomial.vanishingIdeal ℂ Z
    · left
      apply le_antisymm
      · intro x hx
        rw [← hA]
        apply MvPolynomial.zeroLocus_anti_mono hAI
        simpa [affineZariskiClosure] using
          (show x ∈ affineZariskiClosure Z from hclosed.symm ▸ hx)
      · rw [hZ]
        exact Set.subset_union_left
    · right
      have hBI : MvPolynomial.vanishingIdeal ℂ B ≤
          MvPolynomial.vanishingIdeal ℂ Z := by
        intro q hq
        obtain ⟨p, hpA, hpZ⟩ := Set.not_subset.mp hAI
        have hpq : p * q ∈ MvPolynomial.vanishingIdeal ℂ Z := by
          intro x hx
          rw [hZ] at hx
          rcases hx with hx | hx
          · rw [map_mul, hpA x hx, zero_mul]
          · rw [map_mul, hq x hx, mul_zero]
        exact (hprime.mem_or_mem hpq).resolve_left hpZ
      apply le_antisymm
      · intro x hx
        rw [← hB]
        apply MvPolynomial.zeroLocus_anti_mono hBI
        simpa [affineZariskiClosure] using
          (show x ∈ affineZariskiClosure Z from hclosed.symm ▸ hx)
      · rw [hZ]
        exact Set.subset_union_right

/-- The zero locus of a prime ideal is irreducible affine-closed. -/
theorem irreducible_zeroLocus_of_prime {ι : Type*} [Finite ι]
    (P : Ideal (MvPolynomial ι ℂ)) [P.IsPrime] :
    IsIrreducibleAffineClosed (MvPolynomial.zeroLocus ℂ P) := by
  have hc : affineZariskiClosure (MvPolynomial.zeroLocus ℂ P) =
      MvPolynomial.zeroLocus ℂ P := by
    unfold affineZariskiClosure
    rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus P]
  have hn := nonempty_zeroLocus_of_prime P
  apply (irreducibleAffineClosed_iff_isPrime hc hn).mpr
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus P]
  infer_instance

/-- Strict inclusion of affine-closed sets strictly reverses their vanishing ideals. -/
lemma vanishingIdeal_strict_anti {ι : Type*} [Finite ι]
    {A B : Set (ι → ℂ)} (hA : affineZariskiClosure A = A)
    (hB : affineZariskiClosure B = B) (hAB : A ⊂ B) :
    MvPolynomial.vanishingIdeal ℂ B < MvPolynomial.vanishingIdeal ℂ A := by
  refine lt_of_le_of_ne (MvPolynomial.vanishingIdeal_anti_mono hAB.le) ?_
  intro heq
  apply hAB.ne
  rw [← hA, ← hB, affineZariskiClosure, affineZariskiClosure, heq]

/-- Strict inclusion of prime ideals strictly reverses their complex zero loci. -/
lemma zeroLocus_strict_anti {ι : Type*} [Finite ι]
    {P Q : Ideal (MvPolynomial ι ℂ)} [P.IsPrime] [Q.IsPrime] (hPQ : P < Q) :
    MvPolynomial.zeroLocus ℂ Q ⊂ MvPolynomial.zeroLocus ℂ P := by
  refine lt_of_le_of_ne (MvPolynomial.zeroLocus_anti_mono hPQ.le) ?_
  intro heq
  have := congrArg (MvPolynomial.vanishingIdeal ℂ) heq
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus Q,
    MvPolynomial.IsPrime.vanishingIdeal_zeroLocus P] at this
  exact hPQ.ne this.symm

end

end Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension
