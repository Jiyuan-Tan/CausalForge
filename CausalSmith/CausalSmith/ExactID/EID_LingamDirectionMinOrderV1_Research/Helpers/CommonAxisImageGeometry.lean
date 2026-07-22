/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Irreducibility of the common-axis polynomial-image closure
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.CommonAxisTwin
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.BandParameterCoordinates
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.PolynomialRetractDimension
import Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension.DenseImage

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

noncomputable section

/-! ### General finite-affine image lemmas -/

export Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension
  (affineZariskiClosure_union affineZariskiClosure_nonvanishing_eq_univ
   affineZariskiClosure_polynomial_image_of_dense
   irreducible_affineClosure_polynomial_image_of_dense
   polynomialImageClosure_isIrreducible)

/-! ### The finite common-axis source -/

/-- Proves the stated mathematical property of Common Axis Band Coord. -/
abbrev CommonAxisBandCoord (m L : ℕ) (hm : 1 ≤ m) :=
  {c : BandParamCoord m L // c ≠ Sum.inr (Sum.inl (⟨0, hm⟩ : Fin m))}

/-- Defines the mathematical object called the common Axis Band Insert. -/
def commonAxisBandInsert {m L : ℕ} (hm : 1 ≤ m)
    (x : CommonAxisBandCoord m L hm → ℂ) : BandParamCoord m L → ℂ :=
  fun c => if h : c = Sum.inr (Sum.inl (⟨0, hm⟩ : Fin m)) then 0 else x ⟨c, h⟩

private def commonAxisBandErase {m L : ℕ} (hm : 1 ≤ m)
    (x : BandParamCoord m L → ℂ) : CommonAxisBandCoord m L hm → ℂ :=
  fun c => x c.1

private lemma commonAxisBandErase_insert {m L : ℕ} (hm : 1 ≤ m)
    (x : CommonAxisBandCoord m L hm → ℂ) :
    commonAxisBandErase hm (commonAxisBandInsert hm x) = x := by
  funext c
  simp [commonAxisBandErase, commonAxisBandInsert, c.2]

/-- Defines the mathematical object called the common Axis Param. -/
def commonAxisParam {m L : ℕ} (hm : 1 ≤ m)
    (x : CommonAxisBandCoord m L hm → ℂ) : ParamSpace ℂ m :=
  decodeBandParam (commonAxisBandInsert hm x)

private lemma commonAxisParam_supported {m L : ℕ} (hm : 1 ≤ m)
    (x : CommonAxisBandCoord m L hm → ℂ) :
    commonAxisParam hm x ∈ bandSupportedParams m L :=
  decodeBandParam_supported _

private lemma commonAxisParam_axis {m L : ℕ} (hm : 1 ≤ m)
    (x : CommonAxisBandCoord m L hm → ℂ) :
    (commonAxisParam hm x).2.1 ⟨0, hm⟩ = 0 := by
  simp [commonAxisParam, decodeBandParam, commonAxisBandInsert]

/-- Defines the polynomial called the common Axis Polynomial. -/
def commonAxisPolynomial {m L : ℕ} (hm : 1 ≤ m)
    (P : MvPolynomial (BandParamCoord m L) ℂ) :
    MvPolynomial (CommonAxisBandCoord m L hm) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun c =>
    if h : c = Sum.inr (Sum.inl (⟨0, hm⟩ : Fin m)) then 0
    else MvPolynomial.X ⟨c, h⟩) P

/-- Proves that the map called the eval common Axis Polynomial is polynomial. -/
lemma eval_commonAxisPolynomial {m L : ℕ} (hm : 1 ≤ m)
    (x : CommonAxisBandCoord m L hm → ℂ)
    (P : MvPolynomial (BandParamCoord m L) ℂ) :
    MvPolynomial.eval x (commonAxisPolynomial hm P) =
      MvPolynomial.eval (commonAxisBandInsert hm x) P := by
  change MvPolynomial.eval x (MvPolynomial.eval₂ MvPolynomial.C _ P) = _
  rw [MvPolynomial.eval_eval₂]
  have hC : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℂ := by
    ext z
    simp
  rw [hC, MvPolynomial.eval₂_id]
  apply congrArg (fun v => MvPolynomial.eval v P)
  funext c
  by_cases h : c = Sum.inr (Sum.inl (⟨0, hm⟩ : Fin m)) <;>
    simp [commonAxisBandInsert, h]

private def commonAxisParamPolynomial {m L : ℕ} (hm : 1 ≤ m)
    (P : MvPolynomial (ParamCoord m) ℂ) :
    MvPolynomial (CommonAxisBandCoord m L hm) ℂ :=
  commonAxisPolynomial hm (restrictParamPolynomial P)

private lemma eval_commonAxisParamPolynomial {m L : ℕ} (hL : 2 ≤ L)
    (hm : 1 ≤ m) (x : CommonAxisBandCoord m L hm → ℂ)
    (P : MvPolynomial (ParamCoord m) ℂ) :
    MvPolynomial.eval x (commonAxisParamPolynomial hm P) =
      MvPolynomial.eval (paramEval (commonAxisParam hm x)) P := by
  rw [commonAxisParamPolynomial, eval_commonAxisPolynomial,
    eval_restrictParamPolynomial hL]
  rfl

/-- Defines the mathematical object called the forward Common Axis Finite Map. -/
def forwardCommonAxisFiniteMap (m L : ℕ) (hm : 1 ≤ m)
    (x : CommonAxisBandCoord m L hm → ℂ) : RetainedCumCoord L → ℂ :=
  restrictCumBand L (forwardCumulantMap m L (commonAxisParam hm x))

/-- Proves that the map called the forward Common Axis Finite Map is Polynomial is polynomial. -/
lemma forwardCommonAxisFiniteMap_isPolynomial (m L : ℕ) (hm : 1 ≤ m)
    (hL : 2 ≤ L) : IsPolynomialMap (forwardCommonAxisFiniteMap m L hm) := by
  obtain ⟨coord, hcoord⟩ := forwardCumulantMap_isPolynomial m L
  intro q
  refine ⟨commonAxisParamPolynomial hm (coord (q.1.1, q.1.2.1)), ?_⟩
  intro x
  rw [eval_commonAxisParamPolynomial hL, hcoord]
  rfl

private def commonAxisGenericWitness (m L : ℕ) : ParamSpace ℂ m :=
  (((m + 1 : ℕ) : ℂ), (fun i => (i.val : ℂ)),
    fun _ r => if 2 ≤ r ∧ r ≤ L then 1 else 0)

private lemma commonAxisGenericWitness_mem {m L : ℕ} (hm : 1 ≤ m) :
    commonAxisGenericWitness m L ∈ genericParameterLocus m L := by
  refine ⟨?_, ?_⟩
  · intro j r hr
    simp only [commonAxisGenericWitness]
    split_ifs with h
    · omega
    · rfl
  · apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · change (((m + 1 : ℕ) : ℂ)) ≠ 0
          exact_mod_cast Nat.succ_ne_zero m
        · rw [Finset.prod_ne_zero_iff]
          intro i _
          apply sub_ne_zero.mpr
          intro h
          change (((m + 1 : ℕ) : ℂ)) = (i.val : ℂ) at h
          have : m + 1 = i.val := by exact_mod_cast h
          omega
      · rw [Finset.prod_ne_zero_iff]
        intro i _
        rw [Finset.prod_ne_zero_iff]
        intro j _
        by_cases hij : i < j
        · simp only [hij, if_true]
          apply sub_ne_zero.mpr
          intro h
          change (i.val : ℂ) = (j.val : ℂ) at h
          have : i.val = j.val := by exact_mod_cast h
          exact (ne_of_lt hij) (Fin.ext this)
        · simp [hij]
    · rw [Finset.prod_ne_zero_iff]
      intro j _
      rw [Finset.prod_ne_zero_iff]
      intro r hr
      simp only [commonAxisGenericWitness]
      rw [if_pos]
      · exact one_ne_zero
      · exact ⟨Finset.mem_Icc.mp hr |>.1, Finset.mem_Icc.mp hr |>.2⟩

private lemma commonAxisGenericWitness_axis {m L : ℕ} (hm : 1 ≤ m) :
    (commonAxisGenericWitness m L).2.1 ⟨0, hm⟩ = 0 := by
  simp [commonAxisGenericWitness]

private lemma commonAxisGenericWitness_supported {m L : ℕ} (hm : 1 ≤ m) :
    commonAxisGenericWitness m L ∈ bandSupportedParams m L :=
  genericParameterLocus_bandSupported (commonAxisGenericWitness_mem hm)

private def commonAxisGenericPolynomial (m L : ℕ) (hm : 1 ≤ m) :
    MvPolynomial (CommonAxisBandCoord m L hm) ℂ :=
  commonAxisParamPolynomial hm (genericParameterPolynomial m L)

private lemma commonAxisGenericPolynomial_ne_zero {m L : ℕ}
    (hm : 1 ≤ m) (hL : 2 ≤ L) : commonAxisGenericPolynomial m L hm ≠ 0 := by
  intro hzero
  let θ := commonAxisGenericWitness m L
  let x : CommonAxisBandCoord m L hm → ℂ :=
    commonAxisBandErase hm (encodeBandParam θ)
  have hinsert : commonAxisBandInsert hm x = encodeBandParam θ := by
    funext c
    by_cases hc : c = Sum.inr (Sum.inl (⟨0, hm⟩ : Fin m))
    · subst c
      change 0 = θ.2.1 ⟨0, hm⟩
      exact (commonAxisGenericWitness_axis hm).symm
    · simp [x, commonAxisBandInsert, commonAxisBandErase, hc]
  have hparam : commonAxisParam hm x = θ := by
    rw [commonAxisParam, hinsert,
      decode_encodeBandParam hL (commonAxisGenericWitness_supported hm)]
  have hne : MvPolynomial.eval (paramEval θ)
      (genericParameterPolynomial m L) ≠ 0 := by
    rw [eval_genericParameterPolynomial]
    exact genericParameterLocus_prod_ne_zero (commonAxisGenericWitness_mem hm)
  apply hne
  rw [← hparam, ← eval_commonAxisParamPolynomial hL hm x,
    ← commonAxisGenericPolynomial, hzero, map_zero]

/-- Defines the mathematical object called the common Axis Source. -/
def commonAxisSource (m L : ℕ) (hm : 1 ≤ m) :
    Set (CommonAxisBandCoord m L hm → ℂ) :=
  {x | MvPolynomial.eval x (commonAxisGenericPolynomial m L hm) ≠ 0}

/-- Proves the stated mathematical property of common Axis Source dense. -/
lemma commonAxisSource_dense {m L : ℕ} (hm : 1 ≤ m) (hL : 2 ≤ L) :
    affineZariskiClosure (commonAxisSource m L hm) = Set.univ :=
  affineZariskiClosure_nonvanishing_eq_univ _
    (commonAxisGenericPolynomial_ne_zero hm hL)

private lemma commonAxisSource_nonempty {m L : ℕ} (hm : 1 ≤ m) (hL : 2 ≤ L) :
    (commonAxisSource m L hm).Nonempty := by
  by_contra h
  have hempty : commonAxisSource m L hm = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  have := commonAxisSource_dense hm hL
  rw [hempty] at this
  have hclEmpty : affineZariskiClosure
      (∅ : Set (CommonAxisBandCoord m L hm → ℂ)) = ∅ := by
    apply Set.Subset.antisymm
    · intro x hx
      have hone : (1 : MvPolynomial (CommonAxisBandCoord m L hm) ℂ) ∈
          MvPolynomial.vanishingIdeal ℂ
            (∅ : Set (CommonAxisBandCoord m L hm → ℂ)) := by simp
      simpa using hx 1 hone
    · exact Set.empty_subset _
  rw [hclEmpty] at this
  exact Set.empty_ne_univ this

/-- Proves the stated equality or equivalence for common Axis Finite Image eq. -/
lemma commonAxisFiniteImage_eq (m L : ℕ) (hm : 1 ≤ m) (hL : 2 ≤ L) :
    forwardCommonAxisFiniteMap m L hm '' commonAxisSource m L hm =
      restrictCumBand L ''
        (forwardCumulantMap m L ''
          {θ | θ ∈ genericParameterLocus m L ∧ θ.2.1 ⟨0, hm⟩ = 0}) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨forwardCumulantMap m L (commonAxisParam hm x), ?_, rfl⟩
    refine ⟨commonAxisParam hm x, ⟨?_, commonAxisParam_axis hm x⟩, rfl⟩
    rw [genericParameterLocus_eq_nonvanishing_poly]
    refine ⟨commonAxisParam_supported hm x, ?_⟩
    change MvPolynomial.eval x (commonAxisGenericPolynomial m L hm) ≠ 0 at hx
    rw [commonAxisGenericPolynomial,
      eval_commonAxisParamPolynomial hL] at hx
    exact hx
  · rintro ⟨_, ⟨θ, ⟨hgen, haxis⟩, rfl⟩, rfl⟩
    let x : CommonAxisBandCoord m L hm → ℂ :=
      commonAxisBandErase hm (encodeBandParam θ)
    have hinsert : commonAxisBandInsert hm x = encodeBandParam θ := by
      funext c
      by_cases hc : c = Sum.inr (Sum.inl (⟨0, hm⟩ : Fin m))
      · subst c
        simp [x, commonAxisBandInsert, commonAxisBandErase,
          encodeBandParam, haxis]
      · simp [x, commonAxisBandInsert, commonAxisBandErase, hc]
    have hparam : commonAxisParam hm x = θ := by
      rw [commonAxisParam, hinsert,
        decode_encodeBandParam hL (genericParameterLocus_bandSupported hgen)]
    refine ⟨x, ?_, ?_⟩
    · change MvPolynomial.eval x (commonAxisGenericPolynomial m L hm) ≠ 0
      rw [commonAxisGenericPolynomial,
        eval_commonAxisParamPolynomial hL, hparam,
        eval_genericParameterPolynomial]
      exact genericParameterLocus_prod_ne_zero hgen
    · simp [forwardCommonAxisFiniteMap, hparam]

/-- Restriction to the retained band commutes with Zariski closure for a
band-supported set. -/
lemma restrictCumBand_image_zariskiClosure {L : ℕ} {A : Set (CumVec ℂ)}
    (hA : A ⊆ bandSupportedCumulants L) :
    restrictCumBand L '' zariskiClosure A =
      affineZariskiClosure (restrictCumBand L '' A) := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact (mem_zariskiClosure_iff_mem_affineZariskiClosure hA
      (zariskiClosure_subset_band hA ht)).mp ht
  · intro hx
    let t := extendCumBand L x
    have ht : t ∈ zariskiClosure A :=
      (mem_zariskiClosure_iff_mem_affineZariskiClosure hA
        (extendCumBand_mem_band L x)).mpr (by simpa [t] using hx)
    exact ⟨t, ht, restrict_extendCumBand L x⟩

/-- The finite retained-coordinate closure of the explicit common-axis image
is irreducible. -/
theorem restrict_forwardCommonAxisImageClosure_isIrreducible
    (m : ℕ) (hm : 1 ≤ m) :
    IsIrreducibleAffineClosed
      (restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm) := by
  let L := 2 * m + 2
  let A : Set (CumVec ℂ) :=
    forwardCumulantMap m L '' forwardCommonAxisDivisor m hm
  have hA : A ⊆ bandSupportedCumulants L := by
    rintro _ ⟨θ, _, rfl⟩
    exact forwardCumulantMap_mem_bandSupportedCumulants m L θ
  have himage : restrictCumBand L '' A =
      forwardCommonAxisFiniteMap m L hm '' commonAxisSource m L hm := by
    rw [commonAxisFiniteImage_eq m L hm (by omega)]
    rfl
  have hirr := irreducible_affineClosure_polynomial_image_of_dense
    (forwardCommonAxisFiniteMap_isPolynomial m L hm (by omega))
    (commonAxisSource_dense hm (by omega))
    (commonAxisSource_nonempty hm (by omega))
  change IsIrreducibleAffineClosed
    (restrictCumBand L '' zariskiClosure A)
  rw [restrictCumBand_image_zariskiClosure hA, himage]
  exact hirr

end

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
