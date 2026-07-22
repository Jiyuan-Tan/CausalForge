/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Generator-envelope upper bounds for the exceptional image dimensions
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ExceptionalImageDimension

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension

noncomputable section

/-- The retained generators for the full forward image: all loading slopes,
all cumulant coordinates through order `m`, and all source weights from order
`m+1` through order `2m+2`. -/
abbrev ForwardImageGenerator (m : ℕ) :=
  (Unit ⊕ Fin m) ⊕ RetainedCumCoord m ⊕ (Fin (m + 2) × Fin (m + 2))

private def lowCumCoordLift (m : ℕ) :
    RetainedCumCoord m → RetainedCumCoord (2 * m + 2) :=
  fun q =>
    ⟨(⟨q.1.1, by omega⟩, ⟨q.1.2.1, by omega⟩), q.2.1, q.2.2⟩

private def highWeightBandIndex (m : ℕ) (hm : 1 ≤ m) (k : Fin (m + 2)) :
    Fin (2 * m + 1) :=
  ⟨m - 1 + k.1, by omega⟩

private def slopeBandCoord (m : ℕ) :
    Unit ⊕ Fin m → BandParamCoord m (2 * m + 2)
  | Sum.inl u => Sum.inl u
  | Sum.inr i => Sum.inr (Sum.inl i)

private def forwardImageGeneratorPolynomial (m : ℕ) (hm : 1 ≤ m) :
    ForwardImageGenerator m →
      MvPolynomial (BandParamCoord m (2 * m + 2)) ℂ
  | Sum.inl s => MvPolynomial.X (slopeBandCoord m s)
  | Sum.inr (Sum.inl q) =>
      forwardBandCoordinatePolynomial m (2 * m + 2) (by omega)
        (lowCumCoordLift m q)
  | Sum.inr (Sum.inr (j, k)) =>
      MvPolynomial.X (Sum.inr (Sum.inr (j, highWeightBandIndex m hm k)))

private def bandParamToForwardGeneratorPolynomial (m : ℕ) (hm : 1 ≤ m) :
    BandParamCoord m (2 * m + 2) → MvPolynomial (ForwardImageGenerator m) ℂ
  | Sum.inl u => MvPolynomial.X (Sum.inl (Sum.inl u))
  | Sum.inr (Sum.inl i) => MvPolynomial.X (Sum.inl (Sum.inr i))
  | Sum.inr (Sum.inr (j, k)) =>
      if h : m + 1 ≤ k.1 + 2 then
        MvPolynomial.X
          (Sum.inr (Sum.inr (j, ⟨k.1 + 2 - (m + 1), by omega⟩)))
      else 0

private def retainedCumCoordLow? (m : ℕ)
    (q : RetainedCumCoord (2 * m + 2)) : Option (RetainedCumCoord m) :=
  if h : q.1.1 ≤ m then
    some ⟨(⟨q.1.1, by omega⟩, ⟨q.1.2.1, by omega⟩), q.2.1, q.2.2⟩
  else none

private def forwardImageFactorPolynomial (m : ℕ) (hm : 1 ≤ m)
    (q : RetainedCumCoord (2 * m + 2)) :
    MvPolynomial (ForwardImageGenerator m) ℂ :=
  match retainedCumCoordLow? m q with
  | some qlow => MvPolynomial.X (Sum.inr (Sum.inl qlow))
  | none => MvPolynomial.bind₁ (bandParamToForwardGeneratorPolynomial m hm)
      (forwardBandCoordinatePolynomial m (2 * m + 2) (by omega) q)

private lemma lowCumCoordLift_of_low (m : ℕ)
    (q : RetainedCumCoord (2 * m + 2)) (h : q.1.1 ≤ m) :
    lowCumCoordLift m
      ⟨(⟨q.1.1, by omega⟩, ⟨q.1.2.1, by omega⟩), q.2.1, q.2.2⟩ = q := by
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> rfl

private lemma eval_forwardImageGeneratorPolynomial
    (m : ℕ) (hm : 1 ≤ m) (x : BandParamCoord m (2 * m + 2) → ℂ) :
    (fun g => MvPolynomial.eval x (forwardImageGeneratorPolynomial m hm g)) =
      (fun g => match g with
        | Sum.inl s => x (slopeBandCoord m s)
        | Sum.inr (Sum.inl q) => forwardBandFiniteMap m (2 * m + 2) x
            (lowCumCoordLift m q)
        | Sum.inr (Sum.inr (j, k)) =>
            x (Sum.inr (Sum.inr (j, highWeightBandIndex m hm k)))) := by
  funext g
  rcases g with s | (q | jk)
  · rcases s with u | i <;>
      simp [forwardImageGeneratorPolynomial, slopeBandCoord]
  · exact eval_forwardBandCoordinatePolynomial m (2 * m + 2) (by omega) x _
  · simp [forwardImageGeneratorPolynomial]

private lemma eval_bandParamToForwardGeneratorPolynomial
    (m : ℕ) (hm : 1 ≤ m) (x : BandParamCoord m (2 * m + 2) → ℂ)
    (c : BandParamCoord m (2 * m + 2)) :
    MvPolynomial.eval
        (fun g => MvPolynomial.eval x (forwardImageGeneratorPolynomial m hm g))
        (bandParamToForwardGeneratorPolynomial m hm c) =
      match c with
      | Sum.inl u => x (Sum.inl u)
      | Sum.inr (Sum.inl i) => x (Sum.inr (Sum.inl i))
      | Sum.inr (Sum.inr (j, k)) =>
          if m + 1 ≤ k.1 + 2 then x (Sum.inr (Sum.inr (j, k))) else 0 := by
  rcases c with u | (i | ⟨j, k⟩)
  · simp [bandParamToForwardGeneratorPolynomial,
      forwardImageGeneratorPolynomial, slopeBandCoord]
  · simp [bandParamToForwardGeneratorPolynomial,
      forwardImageGeneratorPolynomial, slopeBandCoord]
  · by_cases h : m + 1 ≤ k.1 + 2
    · simp [bandParamToForwardGeneratorPolynomial, h,
        forwardImageGeneratorPolynomial, highWeightBandIndex]
      congr 3
      apply Prod.ext
      · rfl
      · apply Fin.ext
        simp only [Prod.snd]
        change m - 1 + (k.1 + 1 - m) = k.1
        omega
    · simp [bandParamToForwardGeneratorPolynomial, h]

private lemma forwardBandFiniteMap_lowWeight_independent
    (m : ℕ) (q : RetainedCumCoord (2 * m + 2))
    (hq : m < q.1.1) (x : BandParamCoord m (2 * m + 2) → ℂ) :
    forwardBandFiniteMap m (2 * m + 2)
        (fun c => match c with
          | Sum.inl u => x (Sum.inl u)
          | Sum.inr (Sum.inl i) => x (Sum.inr (Sum.inl i))
          | Sum.inr (Sum.inr (j, k)) =>
              if m + 1 ≤ k.1 + 2 then x (Sum.inr (Sum.inr (j, k))) else 0)
        q = forwardBandFiniteMap m (2 * m + 2) x q := by
  simp only [forwardBandFiniteMap, restrictCumBand, forwardCumulantMap]
  have hr : q.1.1 ≤ 2 * m + 2 := by omega
  rw [if_pos ⟨q.2.1, hr, q.2.2⟩, if_pos ⟨q.2.1, hr, q.2.2⟩]
  apply Finset.sum_congr rfl
  intro j _
  congr 3
  have hnot : ¬ q.1.1 - 2 + 1 < m := by omega
  simp [decodeBandParam, q.2.1, hr, hnot]

private lemma eval_bind_bandParamToForwardGeneratorPolynomial
    (m : ℕ) (hm : 1 ≤ m) (x : BandParamCoord m (2 * m + 2) → ℂ)
    (c : BandParamCoord m (2 * m + 2)) :
    MvPolynomial.eval x
        (MvPolynomial.bind₁ (forwardImageGeneratorPolynomial m hm)
          (bandParamToForwardGeneratorPolynomial m hm c)) =
      match c with
      | Sum.inl u => x (Sum.inl u)
      | Sum.inr (Sum.inl i) => x (Sum.inr (Sum.inl i))
      | Sum.inr (Sum.inr (j, k)) =>
          if m + 1 ≤ k.1 + 2 then x (Sum.inr (Sum.inr (j, k))) else 0 := by
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) x
      (MvPolynomial.bind₁ _ _) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  change MvPolynomial.eval _ _ = _
  exact eval_bandParamToForwardGeneratorPolynomial m hm x c

/-- Every forward coordinate polynomial factors through the retained generator
family.  This is the model-specific content of the upper dimension bound. -/
theorem forwardBandCoordinatePolynomial_factorization (m : ℕ) (hm : 1 ≤ m) :
    ∀ q, MvPolynomial.bind₁ (forwardImageGeneratorPolynomial m hm)
        (forwardImageFactorPolynomial m hm q) =
      forwardBandCoordinatePolynomial m (2 * m + 2) (by omega) q := by
  intro q
  unfold forwardImageFactorPolynomial
  split
  · rename_i qlow heq
    rw [MvPolynomial.bind₁_X_right]
    simp only [forwardImageGeneratorPolynomial]
    unfold retainedCumCoordLow? at heq
    split at heq
    · rename_i hlow
      simp only [Option.some.injEq] at heq
      subst qlow
      rw [lowCumCoordLift_of_low m q hlow]
    · contradiction
  · rename_i hnone
    rw [MvPolynomial.bind₁_bind₁]
    apply MvPolynomial.funext
    intro x
    change MvPolynomial.eval₂Hom (RingHom.id ℂ) x
        (MvPolynomial.bind₁ _ _) = _
    rw [MvPolynomial.eval₂Hom_bind₁]
    change MvPolynomial.eval _ _ = MvPolynomial.eval x _
    rw [eval_forwardBandCoordinatePolynomial,
      eval_forwardBandCoordinatePolynomial]
    have hhigh : m < q.1.1 := by
      unfold retainedCumCoordLow? at hnone
      split at hnone
      · contradiction
      · omega
    have hargs :
        (fun c => MvPolynomial.eval₂Hom (RingHom.id ℂ) x
          (MvPolynomial.bind₁ (forwardImageGeneratorPolynomial m hm)
            (bandParamToForwardGeneratorPolynomial m hm c))) =
        (fun c => match c with
          | Sum.inl u => x (Sum.inl u)
          | Sum.inr (Sum.inl i) => x (Sum.inr (Sum.inl i))
          | Sum.inr (Sum.inr (j, k)) =>
              if m + 1 ≤ k.1 + 2 then x (Sum.inr (Sum.inr (j, k))) else 0) := by
      funext c
      change MvPolynomial.eval x
          (MvPolynomial.bind₁ (forwardImageGeneratorPolynomial m hm)
            (bandParamToForwardGeneratorPolynomial m hm c)) = _
      exact eval_bind_bandParamToForwardGeneratorPolynomial m hm x c
    rw [hargs]
    exact forwardBandFiniteMap_lowWeight_independent m q hhigh x

/-- The full forward coordinate algebra is generated by the slopes, low-order
outputs, and high-order weights retained above. -/
theorem forwardBandCoordinateSubalgebra_trdeg_le_generatorCard
    (m : ℕ) (hm : 1 ≤ m) :
    @Algebra.trdeg ℂ
      (polynomialCoordinateSubalgebra
        (forwardBandCoordinatePolynomial m (2 * m + 2) (by omega))) _ _
      (Subalgebra.algebra (polynomialCoordinateSubalgebra
        (forwardBandCoordinatePolynomial m (2 * m + 2) (by omega)))) ≤
      Fintype.card (ForwardImageGenerator m) := by
  exact coordinateSubalgebra_trdeg_le_of_polynomial_factorization
    (forwardBandCoordinatePolynomial m (2 * m + 2) (by omega))
    (forwardImageGeneratorPolynomial m hm)
    (forwardImageFactorPolynomial m hm)
    (forwardBandCoordinatePolynomial_factorization m hm)

private def fixedAxisForwardGenerator (m : ℕ) (hm : 1 ≤ m) :
    ForwardImageGenerator m :=
  Sum.inl (Sum.inr (⟨0, hm⟩ : Fin m))

/-- The common-axis generator family is obtained by deleting the pinned
`rho_0` slope from the full generator family. -/
abbrev CommonAxisImageGenerator (m : ℕ) (hm : 1 ≤ m) :=
  {g : ForwardImageGenerator m // g ≠ fixedAxisForwardGenerator m hm}

private def commonAxisGeneratorPolynomial (m : ℕ) (hm : 1 ≤ m) :
    CommonAxisImageGenerator m hm →
      MvPolynomial (CommonAxisBandCoord m (2 * m + 2) hm) ℂ
  | ⟨Sum.inl s, hs⟩ => MvPolynomial.X ⟨slopeBandCoord m s, by
      intro h
      rcases s with u | i
      · cases h
      · have hi : i = (⟨0, hm⟩ : Fin m) := by
          exact Sum.inl.inj (Sum.inr.inj h)
        subst i
        exact hs rfl⟩
  | ⟨Sum.inr (Sum.inl q), _⟩ =>
      forwardCommonAxisCoordinatePolynomial m (2 * m + 2) hm (by omega)
      (lowCumCoordLift m q)
  | ⟨Sum.inr (Sum.inr (j, k)), _⟩ =>
      MvPolynomial.X ⟨Sum.inr (Sum.inr (j, highWeightBandIndex m hm k)), by
        intro h
        have h' :
            (Sum.inr (j, highWeightBandIndex m hm k) :
              Fin m ⊕ (Fin (m + 2) × Fin (2 * m + 1))) =
              Sum.inl (⟨0, hm⟩ : Fin m) := Sum.inr.inj h
        cases h'⟩

private def fullToCommonAxisGeneratorPolynomial (m : ℕ) (hm : 1 ≤ m) :
    ForwardImageGenerator m → MvPolynomial (CommonAxisImageGenerator m hm) ℂ :=
  fun g => if h : g = fixedAxisForwardGenerator m hm then 0
    else MvPolynomial.X ⟨g, h⟩

private def commonAxisImageFactorPolynomial (m : ℕ) (hm : 1 ≤ m)
    (q : RetainedCumCoord (2 * m + 2)) :
    MvPolynomial (CommonAxisImageGenerator m hm) ℂ :=
  MvPolynomial.bind₁ (fullToCommonAxisGeneratorPolynomial m hm)
    (forwardImageFactorPolynomial m hm q)

private def commonAxisVariablePolynomial (m : ℕ) (hm : 1 ≤ m) :
    BandParamCoord m (2 * m + 2) →
      MvPolynomial (CommonAxisBandCoord m (2 * m + 2) hm) ℂ :=
  fun c => if h : c = Sum.inr (Sum.inl (⟨0, hm⟩ : Fin m)) then 0
    else MvPolynomial.X ⟨c, h⟩

private lemma commonAxisPolynomial_eq_bind (m : ℕ) (hm : 1 ≤ m)
    (P : MvPolynomial (BandParamCoord m (2 * m + 2)) ℂ) :
    commonAxisPolynomial hm P =
      MvPolynomial.bind₁ (commonAxisVariablePolynomial m hm) P := by
  unfold commonAxisPolynomial commonAxisVariablePolynomial
  rw [MvPolynomial.eval₂Hom_C_eq_bind₁]
  rfl

private lemma commonAxisPolynomial_forwardBandCoordinatePolynomial
    (m : ℕ) (hm : 1 ≤ m) (q : RetainedCumCoord (2 * m + 2)) :
    commonAxisPolynomial hm
        (forwardBandCoordinatePolynomial m (2 * m + 2) (by omega) q) =
      forwardCommonAxisCoordinatePolynomial m (2 * m + 2) hm (by omega) q := by
  apply MvPolynomial.funext
  intro x
  rw [eval_commonAxisPolynomial,
    eval_forwardBandCoordinatePolynomial]
  exact (Classical.choose_spec
    (forwardCommonAxisFiniteMap_isPolynomial m (2 * m + 2) hm (by omega) q) x).symm

private lemma commonAxisGeneratorPolynomial_compat
    (m : ℕ) (hm : 1 ≤ m) (g : ForwardImageGenerator m) :
    MvPolynomial.bind₁ (commonAxisGeneratorPolynomial m hm)
        (fullToCommonAxisGeneratorPolynomial m hm g) =
      commonAxisPolynomial hm (forwardImageGeneratorPolynomial m hm g) := by
  rw [commonAxisPolynomial_eq_bind]
  rcases g with s | (q | ⟨j, k⟩)
  · rcases s with u | i
    · simp [fullToCommonAxisGeneratorPolynomial, fixedAxisForwardGenerator,
        commonAxisGeneratorPolynomial, forwardImageGeneratorPolynomial,
        commonAxisVariablePolynomial, slopeBandCoord, commonAxisBandInsert]
    · by_cases hi : i = (⟨0, hm⟩ : Fin m)
      · subst i
        simp [fullToCommonAxisGeneratorPolynomial, fixedAxisForwardGenerator,
          forwardImageGeneratorPolynomial, commonAxisVariablePolynomial,
          slopeBandCoord]
      · simp [fullToCommonAxisGeneratorPolynomial, fixedAxisForwardGenerator, hi,
          commonAxisGeneratorPolynomial, forwardImageGeneratorPolynomial,
          commonAxisVariablePolynomial, slopeBandCoord, commonAxisBandInsert]
        intro h
        apply hi
        exact Sum.inl.inj (Sum.inr.inj h)
  · simp only [fullToCommonAxisGeneratorPolynomial, fixedAxisForwardGenerator,
      reduceCtorEq, ↓reduceDIte, MvPolynomial.bind₁_X_right,
      commonAxisGeneratorPolynomial, forwardImageGeneratorPolynomial]
    exact (commonAxisPolynomial_forwardBandCoordinatePolynomial m hm _).symm
  · simp [fullToCommonAxisGeneratorPolynomial, fixedAxisForwardGenerator,
      commonAxisGeneratorPolynomial, forwardImageGeneratorPolynomial,
      commonAxisVariablePolynomial, commonAxisBandInsert, highWeightBandIndex]
    intro h
    have h' :
        (Sum.inr (j, highWeightBandIndex m hm k) :
          Fin m ⊕ (Fin (m + 2) × Fin (2 * m + 1))) =
          Sum.inl (⟨0, hm⟩ : Fin m) := Sum.inr.inj h
    cases h'

/-- Every common-axis coordinate polynomial factors through the generator
family obtained by deleting the fixed slope. -/
theorem forwardCommonAxisCoordinatePolynomial_factorization
    (m : ℕ) (hm : 1 ≤ m) :
    ∀ q, MvPolynomial.bind₁ (commonAxisGeneratorPolynomial m hm)
        (commonAxisImageFactorPolynomial m hm q) =
      forwardCommonAxisCoordinatePolynomial m (2 * m + 2) hm (by omega) q := by
  intro q
  unfold commonAxisImageFactorPolynomial
  rw [MvPolynomial.bind₁_bind₁]
  rw [show (fun g => MvPolynomial.bind₁ (commonAxisGeneratorPolynomial m hm)
      (fullToCommonAxisGeneratorPolynomial m hm g)) =
      (fun g => commonAxisPolynomial hm
        (forwardImageGeneratorPolynomial m hm g)) from
    funext (commonAxisGeneratorPolynomial_compat m hm)]
  calc
    _ = commonAxisPolynomial hm
        (MvPolynomial.bind₁ (forwardImageGeneratorPolynomial m hm)
          (forwardImageFactorPolynomial m hm q)) := by
      rw [commonAxisPolynomial_eq_bind]
      exact (MvPolynomial.bind₁_bind₁ _ _ _).symm
    _ = _ := by
      rw [forwardBandCoordinatePolynomial_factorization m hm q]
      exact commonAxisPolynomial_forwardBandCoordinatePolynomial m hm q

private lemma two_dvd_generator_quadratic (m : ℕ) :
    2 ∣ m * (m + 3) := by
  rw [show m * (m + 3) = m * (m + 1) + 2 * m by ring]
  exact dvd_add (Nat.two_dvd_mul_add_one m) ⟨m, by omega⟩

/-- The generator envelope has exactly the full expected image dimension. -/
theorem card_forwardImageGenerator (m : ℕ) (hm : 1 ≤ m) :
    Fintype.card (ForwardImageGenerator m) =
      commonAxisExpectedDimension m + 1 := by
  simp only [ForwardImageGenerator, Fintype.card_sum, Fintype.card_unit,
    Fintype.card_fin, Fintype.card_prod, card_retainedCumCoord]
  unfold qDim commonAxisExpectedDimension
  let x := m * (m + 3)
  let y := (m + 2) ^ 2
  have hx : 2 ∣ x := by
    simpa [x] using two_dvd_generator_quadratic m
  have hpoly : 3 * y + (m + 2) = x + 2 * (y + m + 3) := by
    dsimp [x, y]
    ring
  have hxlower : 2 ≤ x / 2 := by
    have hfour : 4 ≤ x := by
      dsimp [x]
      nlinarith
    omega
  rw [show 3 * (m + 2) ^ 2 + (m + 2) =
      x + 2 * (y + m + 3) by simpa [y] using hpoly]
  rw [Nat.add_div_of_dvd_right hx]
  dsimp [x, y]
  simp only [pow_two]
  omega

/-- Deleting the pinned common-axis slope removes exactly one generator. -/
theorem card_commonAxisImageGenerator (m : ℕ) (hm : 1 ≤ m) :
    Fintype.card (CommonAxisImageGenerator m hm) =
      commonAxisExpectedDimension m := by
  change Fintype.card
      {g : ForwardImageGenerator m // g ≠ fixedAxisForwardGenerator m hm} = _
  have hsingle : Fintype.card
      {g : ForwardImageGenerator m // g = fixedAxisForwardGenerator m hm} = 1 :=
    Fintype.card_subtype_eq _
  rw [Fintype.card_subtype_compl
    (fun g : ForwardImageGenerator m => g = fixedAxisForwardGenerator m hm),
    hsingle, card_forwardImageGenerator m hm]
  omega

/-- Exact full-image transcendence upper bound supplied by the generator
envelope, with no fiber-dimension interface. -/
theorem forwardBandCoordinateSubalgebra_trdeg_le_expected
    (m : ℕ) (hm : 1 ≤ m) :
    @Algebra.trdeg ℂ
      (polynomialCoordinateSubalgebra
        (forwardBandCoordinatePolynomial m (2 * m + 2) (by omega))) _ _
      (Subalgebra.algebra (polynomialCoordinateSubalgebra
        (forwardBandCoordinatePolynomial m (2 * m + 2) (by omega)))) ≤
      commonAxisExpectedDimension m + 1 := by
  have hcard : (Fintype.card (ForwardImageGenerator m) : Cardinal) =
      (commonAxisExpectedDimension m : Cardinal) + 1 := by
    exact_mod_cast card_forwardImageGenerator m hm
  exact (forwardBandCoordinateSubalgebra_trdeg_le_generatorCard m hm).trans_eq hcard

/-- Exact common-axis transcendence upper bound supplied by the generator
envelope with the pinned slope deleted. -/
theorem forwardCommonAxisCoordinateSubalgebra_trdeg_le_expected
    (m : ℕ) (hm : 1 ≤ m) :
    @Algebra.trdeg ℂ
      (polynomialCoordinateSubalgebra
        (forwardCommonAxisCoordinatePolynomial m (2 * m + 2) hm (by omega))) _ _
      (Subalgebra.algebra (polynomialCoordinateSubalgebra
        (forwardCommonAxisCoordinatePolynomial m (2 * m + 2) hm (by omega)))) ≤
      commonAxisExpectedDimension m := by
  have hcard : @Algebra.trdeg ℂ
      (polynomialCoordinateSubalgebra
        (forwardCommonAxisCoordinatePolynomial m (2 * m + 2) hm (by omega))) _ _
      (Subalgebra.algebra (polynomialCoordinateSubalgebra
        (forwardCommonAxisCoordinatePolynomial m (2 * m + 2) hm (by omega)))) ≤
      Fintype.card (CommonAxisImageGenerator m hm) :=
    coordinateSubalgebra_trdeg_le_of_polynomial_factorization
      (forwardCommonAxisCoordinatePolynomial m (2 * m + 2) hm (by omega))
      (commonAxisGeneratorPolynomial m hm)
      (commonAxisImageFactorPolynomial m hm)
      (forwardCommonAxisCoordinatePolynomial_factorization m hm)
  have heq : (Fintype.card (CommonAxisImageGenerator m hm) : Cardinal) =
      (commonAxisExpectedDimension m : Cardinal) := by
    exact_mod_cast card_commonAxisImageGenerator m hm
  exact hcard.trans_eq heq

end

/-- The common-axis generator family is unchanged when equal model orders and equal admissibility
conditions are substituted. -/
add_decl_doc CommonAxisImageGenerator.congr_simp

/-- A forward-band coordinate polynomial is unchanged when all of its indexing inputs and its
retained cumulant coordinate are replaced by equal ones. -/
add_decl_doc forwardBandCoordinatePolynomial.congr_simp

/-- A forward common-axis coordinate polynomial is unchanged when all model, band, and retained
cumulant inputs are replaced by equal ones. -/
add_decl_doc forwardCommonAxisCoordinatePolynomial.congr_simp

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
