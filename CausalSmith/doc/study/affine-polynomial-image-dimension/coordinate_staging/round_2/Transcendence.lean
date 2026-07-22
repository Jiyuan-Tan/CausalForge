import Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension.CoordinateRing
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Transcendence degree computes polynomial-image dimension

The central commutative-algebra input is the finite-type domain theorem: Krull
dimension equals transcendence degree.  It is then transported through the
coordinate-ring equivalence of the preceding module.
-/

namespace Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension

open Cardinal
set_option maxSynthPendingDepth 16

noncomputable section

-- The project-wide synthesis depth is intentionally small; expose the canonical
-- subalgebra instance directly so `Algebra.trdeg` elaborates robustly here.
local instance coordinateSubalgebraAlgebra {ι κ : Type*}
    (f : κ → MvPolynomial ι ℂ) :
    Algebra ℂ (polynomialCoordinateSubalgebra f) :=
  Subalgebra.algebra (polynomialCoordinateSubalgebra f)

/-- A finitely generated integral algebra over a field has Krull dimension equal
to its finite transcendence degree, the number of algebraically independent
coordinates it contains. -/
theorem finiteTypeDomain_ringKrullDim_eq_trdeg
    (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [IsDomain A] [Algebra.FiniteType K A] (d : ℕ)
    (htrdeg : Algebra.trdeg K A = d) :
    ringKrullDim A = d := by
  -- `exists_finite_inj_algHom_of_fg` gives `g : K[X₁, ..., Xₛ] →ₐ[K] A`.
  -- For the upper dimension inequality, contract prime chains along `g`; strictness
  -- follows from `Ideal.comap_lt_comap_of_integral_mem_sdiff`.  For the lower
  -- inequality, lift each finite `LTSeries` one prime at a time with
  -- `Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime` (going up).
  -- `MvPolynomial.ringKrullDim_of_isNoetherianRing` computes the normalized ring.
  -- Finally `Algebra.trdeg_add_eq`, `Algebra.IsAlgebraic.trdeg_eq_zero`, and
  -- `MvPolynomial.trdeg_of_isDomain` identify `s` with the certified `d`.
  obtain ⟨s, g, hg_inj, hg_int⟩ := exists_integral_inj_algHom_of_fg K A
  let a : Algebra (MvPolynomial (Fin s) K) A := g.toRingHom.toAlgebra
  letI : Algebra (MvPolynomial (Fin s) K) A := a
  have ha_int : @Algebra.IsIntegral (MvPolynomial (Fin s) K) A _ _ a := by
    refine @Algebra.IsIntegral.mk (MvPolynomial (Fin s) K) A _ _ a ?_
    intro x
    exact hg_int x
  let f : PrimeSpectrum A → PrimeSpectrum (MvPolynomial (Fin s) K) :=
    PrimeSpectrum.comap g.toRingHom
  have hf_mono : StrictMono f := by
    intro I J hIJ
    change I.asIdeal < J.asIdeal at hIJ
    change I.asIdeal.comap g.toRingHom < J.asIdeal.comap g.toRingHom
    obtain ⟨hIJle, x, hxJ, hxI⟩ := SetLike.lt_iff_le_and_exists.mp hIJ
    apply @Ideal.comap_lt_comap_of_integral_mem_sdiff (MvPolynomial (Fin s) K) _ A _
      I.asIdeal J.asIdeal a I.isPrime hIJle
    · exact ⟨hxJ, hxI⟩
    · exact hg_int x
  have lift_chain : ∀ (n : ℕ) (p : LTSeries (PrimeSpectrum (MvPolynomial (Fin s) K))),
      p.length = n → ∃ q : LTSeries (PrimeSpectrum A), q.length = n ∧ f q.last = p.last := by
    intro n
    induction n with
    | zero =>
      intro p hp
      obtain ⟨Q, hQ⟩ := hg_int.comap_surjective hg_inj p.last
      refine ⟨LTSeries.mk 0 (fun _ => Q) (by
        intro i j hij
        fin_cases i
        fin_cases j
        exact (lt_irrefl _ hij).elim), rfl, ?_⟩
      simpa [f] using hQ
    | succ n ih =>
      intro p hp
      let p' : LTSeries (PrimeSpectrum (MvPolynomial (Fin s) K)) := p.eraseLast
      have hp' : p'.length = n := by
        simp [p', hp]
      obtain ⟨q, hq_len, hq_last⟩ := ih p' hp'
      have hlast : p'.last < p.last := by
        simpa [p'] using p.eraseLast_last_rel_last (by simp [hp])
      have hle : q.last.asIdeal.comap g.toRingHom ≤ p.last.asIdeal := by
        calc
          q.last.asIdeal.comap g.toRingHom = (f q.last).asIdeal := rfl
          _ = p'.last.asIdeal := congrArg PrimeSpectrum.asIdeal hq_last
          _ ≤ p.last.asIdeal := hlast.le
      obtain ⟨Q, hQ_ge, hQ_prime, hQ_comap⟩ :=
        @Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime (MvPolynomial (Fin s) K) _ A _
          a ha_int p.last.asIdeal p.last.isPrime q.last.asIdeal q.last.isPrime hle
      let Q' : PrimeSpectrum A := ⟨Q, hQ_prime⟩
      have hqQ : q.last < Q' := by
        change q.last.asIdeal < Q
        refine lt_of_le_of_ne hQ_ge ?_
        intro h_eq
        have h_eq' : p'.last.asIdeal = p.last.asIdeal := by
          calc
            p'.last.asIdeal = q.last.asIdeal.comap g.toRingHom := by
              exact (congrArg PrimeSpectrum.asIdeal hq_last).symm
            _ = Q.comap g.toRingHom := congrArg (Ideal.comap g.toRingHom) h_eq
            _ = p.last.asIdeal := hQ_comap
        apply hlast.ne
        exact PrimeSpectrum.ext h_eq'
      refine ⟨q.snoc Q' hqQ, ?_, ?_⟩
      · simpa [hq_len]
      · apply PrimeSpectrum.ext
        simp only [RelSeries.last_snoc]
        change Q.comap g.toRingHom = p.last.asIdeal
        exact hQ_comap
  have hdim : ringKrullDim A = ringKrullDim (MvPolynomial (Fin s) K) := by
    apply le_antisymm
    · exact Order.krullDim_le_of_strictMono f hf_mono
    · rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]
      rw [ringKrullDim_eq_zero_of_field]
      simp only [zero_add, Nat.card_eq_fintype_card, Fintype.card_fin]
      apply (Order.le_krullDim_iff).mpr
      have hpoly : (s : WithBot ℕ∞) =
          Order.krullDim (PrimeSpectrum (MvPolynomial (Fin s) K)) := by
        change (s : WithBot ℕ∞) = ringKrullDim (MvPolynomial (Fin s) K)
        rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
        simp
      obtain ⟨p, hp⟩ := (Order.le_krullDim_iff.mp hpoly.le)
      obtain ⟨q, hq, _⟩ := lift_chain s p hp
      exact ⟨q, hq⟩
  rw [hdim, MvPolynomial.ringKrullDim_of_isNoetherianRing]
  have ha_alg : @Algebra.IsAlgebraic (MvPolynomial (Fin s) K) A _ _ a :=
    @Algebra.IsIntegral.isAlgebraic (MvPolynomial (Fin s) K) A _ _ a (inferInstance) ha_int
  haveI : IsScalarTower K (MvPolynomial (Fin s) K) A :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      exact (g.commutes x).symm)
  haveI : FaithfulSMul (MvPolynomial (Fin s) K) A :=
    (faithfulSMul_iff_algebraMap_injective (MvPolynomial (Fin s) K) A).mpr (by
      change Function.Injective g.toRingHom
      exact hg_inj)
  have hzero : @Algebra.trdeg (MvPolynomial (Fin s) K) A _ _ a = 0 :=
    @trdeg_eq_zero (MvPolynomial (Fin s) K) A _ _ a ha_alg
  have h := @lift_trdeg_add_eq K (MvPolynomial (Fin s) K) A _ _ _
    (inferInstance) (inferInstance) a (inferInstance) (inferInstance) (inferInstance)
    (inferInstance) (inferInstance)
  rw [hzero, lift_zero, add_zero] at h
  have hs : s = d := by
    have hnat := congrArg Cardinal.toNat h
    simp only [Cardinal.toNat_lift] at hnat
    rw [MvPolynomial.trdeg_of_isDomain, htrdeg] at hnat
    simpa using hnat
  simpa [ringKrullDim_eq_zero_of_field, hs]

/-- If the coordinate polynomials of a finite polynomial parameterization have
exactly a given transcendence degree, the Zariski closure of its image has that
same exact affine dimension. -/
theorem polynomialImageClosure_dimension_of_trdeg
    {ι κ : Type*} [Finite ι] [Finite κ]
    (f : κ → MvPolynomial ι ℂ) (d : ℕ)
    (htrdeg : @Algebra.trdeg ℂ (polynomialCoordinateSubalgebra f) _ _
      (coordinateSubalgebraAlgebra f) = d) :
    HasAffineZariskiDimension d (polynomialImageClosure f) := by
  -- The range subalgebra is a finite-type domain: use `Subalgebra.FG.map` on
  -- `Algebra.FiniteType.out` for the finite-variable source polynomial ring.
  -- Apply `finiteTypeDomain_ringKrullDim_eq_trdeg`, transport Krull dimension
  -- through `polynomialImageClosure_coordinateRing`, and finish with
  -- `affineZariskiDimension_iff_coordinateRingKrullDim`.  Closedness is closure
  -- idempotence; the image of the zero source point witnesses nonemptiness.
  let S : Subalgebra ℂ (MvPolynomial ι ℂ) := polynomialCoordinateSubalgebra f
  letI : Algebra ℂ S := coordinateSubalgebraAlgebra f
  let sDom : IsDomain S := inferInstance
  letI : IsDomain S := sDom
  have hfg : S.FG := by
    simpa [S, polynomialCoordinateSubalgebra] using
      (Subalgebra.FG.map (polynomialPullback f) Algebra.FiniteType.out)
  let sFT : Algebra.FiniteType ℂ S := S.fg_iff_finiteType.mp hfg
  letI : Algebra.FiniteType ℂ S := sFT
  have hdimS : ringKrullDim S = d := by
    exact @finiteTypeDomain_ringKrullDim_eq_trdeg ℂ S _ _ (coordinateSubalgebraAlgebra f) sDom sFT d
      (by simpa [S] using htrdeg)
  have hcoord : ringKrullDim
      (MvPolynomial κ ℂ ⧸ MvPolynomial.vanishingIdeal ℂ (polynomialImageClosure f)) = d := by
    rw [ringKrullDim_eq_of_ringEquiv
      (polynomialImageClosure_coordinateRing f).toRingEquiv]
    exact hdimS
  refine (affineZariskiDimension_iff_coordinateRingKrullDim
    (affineZariskiClosure_idem _) ?_).mpr hcoord
  refine ⟨polynomialCoordinateMap f 0, ?_⟩
  exact affineZariskiClosure_extensive _ ⟨0, rfl⟩

/-- A surjective presentation by a polynomial algebra in a given number of
generators certifies that the coordinate subalgebra has no larger transcendence
degree. -/
theorem coordinateSubalgebra_trdeg_le_of_surjection
    {ι κ : Type*} (f : κ → MvPolynomial ι ℂ) (d : ℕ)
    (present : MvPolynomial (Fin d) ℂ →ₐ[ℂ]
      polynomialCoordinateSubalgebra f)
    (hsurj : Function.Surjective present) :
    @Algebra.trdeg ℂ (polynomialCoordinateSubalgebra f) _ _
      (coordinateSubalgebraAlgebra f) ≤ d := by
  -- Apply `Algebra.trdeg_le_of_surjective present hsurj`, rewrite the source
  -- with `MvPolynomial.trdeg_of_isDomain`, then simplify `#(Fin d)` to `d`.
  let calgebra : Algebra ℂ (polynomialCoordinateSubalgebra f) :=
    coordinateSubalgebraAlgebra f
  have h := @lift_trdeg_le_of_surjective ℂ (MvPolynomial (Fin d) ℂ)
    (polynomialCoordinateSubalgebra f) _ _ _ _ calgebra present hsurj
  simpa [calgebra] using h

end

end Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension
