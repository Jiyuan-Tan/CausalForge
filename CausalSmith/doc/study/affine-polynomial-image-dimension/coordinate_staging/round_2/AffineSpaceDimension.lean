/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension.ChainDimension
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Exact algebraic dimension of complex affine space

This file computes the irreducible-chain dimension of finite-dimensional
complex affine space from the Krull dimension of its polynomial ring.
-/

namespace Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension

open Order

noncomputable section

private def primeOfIrreducible {ι : Type*} [Finite ι]
    (Z : Set (ι → ℂ)) (hZ : IsIrreducibleAffineClosed Z) :
    PrimeSpectrum (MvPolynomial ι ℂ) :=
  ⟨MvPolynomial.vanishingIdeal ℂ Z,
    (irreducibleAffineClosed_iff_isPrime hZ.1 hZ.2.1).mp hZ⟩

private lemma primeOfIrreducible_lt {ι : Type*} [Finite ι]
    {A B : Set (ι → ℂ)} (hA : IsIrreducibleAffineClosed A)
    (hB : IsIrreducibleAffineClosed B) (hAB : A ⊂ B) :
    primeOfIrreducible B hB < primeOfIrreducible A hA := by
  exact vanishingIdeal_strict_anti hA.1 hB.1 hAB

private lemma polynomialRing_dimension (d : ℕ) :
    ringKrullDim (MvPolynomial (Fin d) ℂ) = d := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]
  simp

/-- Complex affine `d`-space has dimension exactly `d` in the explicit
irreducible-chain sense. -/
theorem affineSpace_hasAffineZariskiDimension (d : ℕ) :
    HasAffineZariskiDimension d (Set.univ : Set (Fin d → ℂ)) := by
  have hdim : ringKrullDim (MvPolynomial (Fin d) ℂ) = d :=
    polynomialRing_dimension d
  have hle : (d : WithBot ℕ∞) ≤
      Order.krullDim (PrimeSpectrum (MvPolynomial (Fin d) ℂ)) := by
    simpa [ringKrullDim] using hdim.ge
  obtain ⟨series, hseries⟩ := Order.le_krullDim_iff.mp hle
  let castIndex : Fin (d + 1) → Fin (series.length + 1) :=
    Fin.cast (congrArg (· + 1) hseries.symm)
  constructor
  · let chain : Fin (d + 1) → Set (Fin d → ℂ) := fun i =>
      MvPolynomial.zeroLocus ℂ (series (castIndex i.rev)).asIdeal
    refine ⟨chain, ?_, ?_, fun _ => Set.subset_univ _⟩
    · intro i j hij
      have hrev : j.rev < i.rev := by
        simpa using hij
      have hcast : castIndex j.rev < castIndex i.rev := by
        simpa [castIndex] using hrev
      have hp : series (castIndex j.rev) < series (castIndex i.rev) :=
        series.strictMono hcast
      exact zeroLocus_strict_anti hp
    · intro i
      exact irreducible_zeroLocus_of_prime (series (castIndex i.rev)).asIdeal
  · rintro ⟨chain, hmono, hirr, _⟩
    let primes : Fin (d + 2) → PrimeSpectrum (MvPolynomial (Fin d) ℂ) :=
      fun i => primeOfIrreducible (chain i.rev) (hirr i.rev)
    have hprimes : StrictMono primes := by
      intro i j hij
      have hrev : j.rev < i.rev := by simpa using hij
      exact primeOfIrreducible_lt (hirr j.rev) (hirr i.rev) (hmono hrev)
    let tooLong : LTSeries (PrimeSpectrum (MvPolynomial (Fin d) ℂ)) :=
      LTSeries.mk (d + 1) primes hprimes
    have hbound := tooLong.length_le_krullDim
    rw [show tooLong.length = d + 1 by rfl, ← ringKrullDim, hdim] at hbound
    have htop : (d + 1 : WithTop ℕ) ≤ (d : WithTop ℕ) :=
      WithBot.coe_le_coe.mp hbound
    have hnat : d + 1 ≤ d := WithTop.coe_le_coe.mp htop
    exact (Nat.not_succ_le_self d) hnat

end

end Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension
