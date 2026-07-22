/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The pinned confluent top block for the common-axis Jacobian
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ExceptionalJacobianCoordinates

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

noncomputable section

/-! ### Differentiating after pinning the common-axis variable -/

private lemma commonAxisPolynomial_add {m L : ℕ} (hm : 1 ≤ m)
    (P Q : MvPolynomial (BandParamCoord m L) ℂ) :
    commonAxisPolynomial hm (P + Q) =
      commonAxisPolynomial hm P + commonAxisPolynomial hm Q := by
  unfold commonAxisPolynomial
  let φ : MvPolynomial (BandParamCoord m L) ℂ →+*
      MvPolynomial (CommonAxisBandCoord m L hm) ℂ :=
    MvPolynomial.eval₂Hom MvPolynomial.C (fun c : BandParamCoord m L =>
      if h : c = Sum.inr (Sum.inl (⟨0, hm⟩ : Fin m)) then 0
      else MvPolynomial.X (⟨c, h⟩ : CommonAxisBandCoord m L hm))
  change φ (P + Q) = φ P + φ Q
  exact map_add φ P Q

private lemma commonAxisPolynomial_mul {m L : ℕ} (hm : 1 ≤ m)
    (P Q : MvPolynomial (BandParamCoord m L) ℂ) :
    commonAxisPolynomial hm (P * Q) =
      commonAxisPolynomial hm P * commonAxisPolynomial hm Q := by
  unfold commonAxisPolynomial
  let φ : MvPolynomial (BandParamCoord m L) ℂ →+*
      MvPolynomial (CommonAxisBandCoord m L hm) ℂ :=
    MvPolynomial.eval₂Hom MvPolynomial.C (fun c : BandParamCoord m L =>
      if h : c = Sum.inr (Sum.inl (⟨0, hm⟩ : Fin m)) then 0
      else MvPolynomial.X (⟨c, h⟩ : CommonAxisBandCoord m L hm))
  change φ (P * Q) = φ P * φ Q
  exact map_mul φ P Q

/-- Pinning one variable to zero commutes with partial differentiation in
every retained variable. -/
theorem pderiv_commonAxisPolynomial {m L : ℕ} (hm : 1 ≤ m)
    (c : CommonAxisBandCoord m L hm)
    (P : MvPolynomial (BandParamCoord m L) ℂ) :
    MvPolynomial.pderiv c (commonAxisPolynomial hm P) =
      commonAxisPolynomial hm (MvPolynomial.pderiv c.1 P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp [commonAxisPolynomial]
  | add P Q hP hQ =>
      rw [commonAxisPolynomial_add, map_add, map_add, hP, hQ,
        commonAxisPolynomial_add]
  | mul_X P d hP =>
      rw [commonAxisPolynomial_mul, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_mul, commonAxisPolynomial_add,
        commonAxisPolynomial_mul, commonAxisPolynomial_mul, hP]
      by_cases hd : d = Sum.inr (Sum.inl (⟨0, hm⟩ : Fin m))
      · subst d
        have hne :
            (Sum.inr (Sum.inl (⟨0, hm⟩ : Fin m)) : BandParamCoord m L) ≠
              c.1 := by
          intro h
          exact c.2 h.symm
        simp [commonAxisPolynomial, hne, hP]
      · by_cases hdc : d = c.1
        · subst d
          simp [commonAxisPolynomial, c.2, hP, mul_comm]
        · have hsub : (⟨d, hd⟩ : CommonAxisBandCoord m L hm) ≠ c := by
            intro h
            exact hdc (congrArg Subtype.val h)
          simp [commonAxisPolynomial, hd, hdc, hsub, hP, mul_comm]

/-- Evaluation form of `pderiv_commonAxisPolynomial`. -/
theorem eval_pderiv_commonAxisPolynomial {m L : ℕ} (hm : 1 ≤ m)
    (x : CommonAxisBandCoord m L hm → ℂ)
    (c : CommonAxisBandCoord m L hm)
    (P : MvPolynomial (BandParamCoord m L) ℂ) :
    MvPolynomial.eval x
        (MvPolynomial.pderiv c (commonAxisPolynomial hm P)) =
      MvPolynomial.eval (commonAxisBandInsert hm x)
        (MvPolynomial.pderiv c.1 P) := by
  rw [pderiv_commonAxisPolynomial, eval_commonAxisPolynomial]

/-- The canonical common-axis coordinate is the pinned canonical full
coordinate. -/
theorem commonAxisPolynomial_forwardBandCoordinatePolynomial_eq
    (m L : ℕ) (hm : 1 ≤ m) (hL : 2 ≤ L) (q : RetainedCumCoord L) :
    commonAxisPolynomial hm (forwardBandCoordinatePolynomial m L hL q) =
      forwardCommonAxisCoordinatePolynomial m L hm hL q := by
  apply MvPolynomial.funext
  intro x
  rw [eval_commonAxisPolynomial, eval_forwardBandCoordinatePolynomial]
  exact (Classical.choose_spec
    (forwardCommonAxisFiniteMap_isPolynomial m L hm hL q) x).symm

/-- Partial derivatives of the canonical common-axis coordinate can be
computed in the full coordinate family and then pinned. -/
theorem pderiv_forwardCommonAxisCoordinatePolynomial
    (m L : ℕ) (hm : 1 ≤ m) (hL : 2 ≤ L)
    (q : RetainedCumCoord L) (c : CommonAxisBandCoord m L hm) :
    MvPolynomial.pderiv c
        (forwardCommonAxisCoordinatePolynomial m L hm hL q) =
      commonAxisPolynomial hm
        (MvPolynomial.pderiv c.1
          (forwardBandCoordinatePolynomial m L hL q)) := by
  rw [← commonAxisPolynomial_forwardBandCoordinatePolynomial_eq,
    pderiv_commonAxisPolynomial]

/-- Evaluation transfer from a common-axis Jacobian entry to the full
Jacobian at the inserted parameter point. -/
theorem eval_pderiv_forwardCommonAxisCoordinatePolynomial
    (m L : ℕ) (hm : 1 ≤ m) (hL : 2 ≤ L)
    (q : RetainedCumCoord L) (c : CommonAxisBandCoord m L hm)
    (x : CommonAxisBandCoord m L hm → ℂ) :
    MvPolynomial.eval x
        (MvPolynomial.pderiv c
          (forwardCommonAxisCoordinatePolynomial m L hm hL q)) =
      MvPolynomial.eval (commonAxisBandInsert hm x)
        (MvPolynomial.pderiv c.1
          (forwardBandCoordinatePolynomial m L hL q)) := by
  rw [pderiv_forwardCommonAxisCoordinatePolynomial,
    eval_commonAxisPolynomial]

/-! ### A pinned witness and its finite nodes -/

/-- Common-axis witness: the deleted latent slope is zero after insertion;
the direct slope is one, all other latent slopes are `i+1`, and every retained
weight is one. -/
def commonAxisJacobianWitnessCoord (m : ℕ) (hm : 1 ≤ m) :
    CommonAxisBandCoord m (2 * m + 2) hm → ℂ
  | ⟨Sum.inl _, _⟩ => 1
  | ⟨Sum.inr (Sum.inl i), _⟩ => ((i.val + 1 : ℕ) : ℂ)
  | ⟨Sum.inr (Sum.inr _), _⟩ => 1

/-- The finite source permutation puts the pinned latent source first and the
direct source second. -/
def commonAxisNodeSource (m : ℕ) (hm : 1 ≤ m) (j : Fin (m + 1)) :
    Fin (m + 2) :=
  if h0 : j.val = 0 then ⟨1, by omega⟩
  else if h1 : j.val = 1 then ⟨0, by omega⟩
  else ⟨j.val, by omega⟩

/-- The permuted finite nodes are `0,1,...,m`. -/
def commonAxisNodeValue (m : ℕ) (j : Fin (m + 1)) : ℂ :=
  (j.val : ℂ)

theorem commonAxisNodeValue_injective (m : ℕ) :
    Function.Injective (commonAxisNodeValue m) := by
  intro i j h
  apply Fin.ext
  exact_mod_cast (show (i.val : ℂ) = j.val by simpa [commonAxisNodeValue] using h)

lemma commonAxisJacobianWitness_insert_direct (m : ℕ) (hm : 1 ≤ m) :
    commonAxisBandInsert hm (commonAxisJacobianWitnessCoord m hm)
        (Sum.inl ()) = 1 := by
  simp only [commonAxisBandInsert]
  rw [dif_neg]
  · rfl
  · intro h
    cases h

/-- Proves the stated mathematical property of common Axis Jacobian Witness insert latent. -/
lemma commonAxisJacobianWitness_insert_latent (m : ℕ) (hm : 1 ≤ m)
    (i : Fin m) :
    commonAxisBandInsert hm (commonAxisJacobianWitnessCoord m hm)
        (Sum.inr (Sum.inl i)) =
      if i = ⟨0, hm⟩ then 0 else ((i.val + 1 : ℕ) : ℂ) := by
  by_cases hi : i = ⟨0, hm⟩
  · subst i
    simp [commonAxisBandInsert]
  · simp only [commonAxisBandInsert]
    rw [dif_neg]
    · simp [hi, commonAxisJacobianWitnessCoord]
    · intro h
      apply hi
      exact Sum.inl.inj (Sum.inr.inj h)

/-- Proves the stated mathematical property of common Axis Jacobian Witness insert weight. -/
lemma commonAxisJacobianWitness_insert_weight (m : ℕ) (hm : 1 ≤ m)
    (j : Fin (m + 2)) (k : Fin (2 * m + 1)) :
    commonAxisBandInsert hm (commonAxisJacobianWitnessCoord m hm)
        (Sum.inr (Sum.inr (j, k))) = 1 := by
  simp only [commonAxisBandInsert]
  rw [dif_neg]
  · rfl
  · intro h
    cases Sum.inr.inj h

/-- Loading evaluation at the inserted common-axis witness. -/
theorem commonAxisJacobianWitness_loading (m : ℕ) (hm : 1 ≤ m)
    (j : Fin (m + 1)) :
    forwardLoading m
        (decodeBandParam
          (commonAxisBandInsert hm (commonAxisJacobianWitnessCoord m hm))).1
        (decodeBandParam
          (commonAxisBandInsert hm (commonAxisJacobianWitnessCoord m hm))).2.1
        (commonAxisNodeSource m hm j) =
      (1, commonAxisNodeValue m j) := by
  by_cases h0 : j.val = 0
  · have hm0 : m ≠ 0 := by omega
    simp [commonAxisNodeSource, h0, commonAxisNodeValue, forwardLoading,
      decodeBandParam, hm0]
    exact commonAxisJacobianWitness_insert_latent m hm ⟨0, hm⟩
  · by_cases h1 : j.val = 1
    · simp [commonAxisNodeSource, h0, h1, commonAxisNodeValue, forwardLoading,
        decodeBandParam]
      exact commonAxisJacobianWitness_insert_direct m hm
    · have hjpos : 0 < j.val := Nat.pos_of_ne_zero h0
      have hjlast : j.val ≠ m + 1 := by omega
      have hidx :
          (⟨j.val - 1, by omega⟩ : Fin m) ≠ ⟨0, hm⟩ := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
        omega
      simp [commonAxisNodeSource, h0, h1, commonAxisNodeValue, forwardLoading,
        decodeBandParam, hjlast]
      simp only [commonAxisBandInsert]
      rw [dif_neg]
      · simp [commonAxisJacobianWitnessCoord]
        norm_cast
        omega
      · intro h
        apply hidx
        exact Sum.inl.inj (Sum.inr.inj h)

/-- Proves the stated mathematical property of common Axis Jacobian Witness weight. -/
theorem commonAxisJacobianWitness_weight (m : ℕ) (hm : 1 ≤ m)
    (j : Fin (m + 2)) (r : ℕ) (hr : 2 ≤ r ∧ r ≤ 2 * m + 2) :
    (decodeBandParam
      (commonAxisBandInsert hm (commonAxisJacobianWitnessCoord m hm))).2.2 j r = 1 := by
  rw [show (decodeBandParam
      (commonAxisBandInsert hm (commonAxisJacobianWitnessCoord m hm))).2.2 j r =
      commonAxisBandInsert hm (commonAxisJacobianWitnessCoord m hm)
        (Sum.inr (Sum.inr (j, ⟨r - 2, by omega⟩))) by
    simp only [decodeBandParam]
    rw [dif_pos hr]]
  exact commonAxisJacobianWitness_insert_weight m hm _ _

/-- Proves the stated mathematical property of common Axis Jacobian Witness loading last. -/
lemma commonAxisJacobianWitness_loading_last (m : ℕ) (hm : 1 ≤ m) :
    forwardLoading m
        (decodeBandParam
          (commonAxisBandInsert hm (commonAxisJacobianWitnessCoord m hm))).1
        (decodeBandParam
          (commonAxisBandInsert hm (commonAxisJacobianWitnessCoord m hm))).2.1
        (Fin.last (m + 1)) = (0, 1) := by
  simp [forwardLoading, decodeBandParam, commonAxisBandInsert,
    commonAxisJacobianWitnessCoord, Fin.last]

/-! ### The pinned-simple confluent top block -/

/-- Proves the stated mathematical property of Common Axis Top Index. -/
abbrev CommonAxisTopIndex (m : ℕ) :=
  Fin (m + 1) ⊕ Fin m

/-- Defines the mathematical object called the common Axis Top Row. -/
def commonAxisTopRow (m : ℕ) (a : CommonAxisTopIndex m) :
    RetainedCumCoord (2 * m + 2) :=
  ⟨(⟨2 * m + 2, by omega⟩,
      ⟨pinnedExponent a, by
        have h := pinnedExponent_lt (n := m + 1) (by omega) a
        omega⟩),
    by change 2 ≤ 2 * m + 2; omega,
    by
      change pinnedExponent a ≤ 2 * m + 2
      have h := pinnedExponent_lt (n := m + 1) (by omega) a
      omega⟩

/-- The slope associated with the derivative node `i+1`: the first is the
direct slope; all later ones are their same-index latent slopes. -/
def commonAxisUnpinnedSlope (m : ℕ) (i : Fin m) : ForwardSlopeIndex m :=
  if h0 : i.val = 0 then Sum.inl () else Sum.inr i

lemma forwardSlopeSourceIndex_commonAxisUnpinnedSlope
    (m : ℕ) (hm : 1 ≤ m) (i : Fin m) :
    forwardSlopeSourceIndex m (commonAxisUnpinnedSlope m i) =
      commonAxisNodeSource m hm (pinnedSucc (n := m + 1) (by omega) i) := by
  apply Fin.ext
  by_cases h0 : i.val = 0
  · change (forwardSlopeSourceIndex m (commonAxisUnpinnedSlope m i)).val = _
    simp [commonAxisUnpinnedSlope, commonAxisNodeSource, pinnedSucc, h0,
      forwardSlopeSourceIndex]
  · change (forwardSlopeSourceIndex m (commonAxisUnpinnedSlope m i)).val = _
    simp [commonAxisUnpinnedSlope, commonAxisNodeSource, pinnedSucc, h0,
      forwardSlopeSourceIndex]

/-- Defines the mathematical object called the common Axis Top Column. -/
def commonAxisTopColumn (m : ℕ) (hm : 1 ≤ m) :
    CommonAxisTopIndex m → CommonAxisBandCoord m (2 * m + 2) hm
  | Sum.inl j =>
      ⟨Sum.inr (Sum.inr
          (commonAxisNodeSource m hm j, ⟨2 * m, by omega⟩)), by
        intro h
        cases Sum.inr.inj h⟩
  | Sum.inr i =>
      ⟨forwardSlopeBandCoord m (2 * m + 2) (commonAxisUnpinnedSlope m i), by
        by_cases h0 : i.val = 0
        · simp [commonAxisUnpinnedSlope, h0, forwardSlopeBandCoord]
        · intro h
          rw [commonAxisUnpinnedSlope, dif_neg h0] at h
          simp only [forwardSlopeBandCoord] at h
          apply h0
          have h' := Sum.inl.inj (Sum.inr.inj h)
          exact Fin.ext_iff.mp h'⟩

/-- Defines the Jacobian matrix, row, column, or indexing object called the canonical Common Axis Top Jacobian At Witness. -/
def canonicalCommonAxisTopJacobianAtWitness (m : ℕ) (hm : 1 ≤ m) :
    Matrix (CommonAxisTopIndex m) (CommonAxisTopIndex m) ℂ :=
  fun a b =>
    MvPolynomial.eval (commonAxisJacobianWitnessCoord m hm)
      (MvPolynomial.pderiv (commonAxisTopColumn m hm b)
        (forwardCommonAxisCoordinatePolynomial m (2 * m + 2) hm (by omega)
          (commonAxisTopRow m a)))

/-- Proves the stated equality or equivalence for canonical Common Axis Top Jacobian At Witness equality pinned. -/
theorem canonicalCommonAxisTopJacobianAtWitness_eq_pinned
    (m : ℕ) (hm : 1 ≤ m) :
    canonicalCommonAxisTopJacobianAtWitness m hm =
      pinnedConfluentVandermonde (n := m + 1) (by omega)
        (commonAxisNodeValue m) := by
  ext a b
  rcases b with j | i
  · simp only [canonicalCommonAxisTopJacobianAtWitness, commonAxisTopColumn]
    rw [eval_pderiv_forwardCommonAxisCoordinatePolynomial,
      pderiv_forwardBandCoordinatePolynomial_eq_explicit,
      eval_pderiv_explicitForwardBandCoordinatePolynomial_weight_general,
      if_pos (by rfl)]
    change
      (forwardLoading m
          (decodeBandParam
            (commonAxisBandInsert hm (commonAxisJacobianWitnessCoord m hm))).1
          (decodeBandParam
            (commonAxisBandInsert hm (commonAxisJacobianWitnessCoord m hm))).2.1
          (commonAxisNodeSource m hm j)).1 ^
            (2 * m + 2 - pinnedExponent a) *
        (forwardLoading m
          (decodeBandParam
            (commonAxisBandInsert hm (commonAxisJacobianWitnessCoord m hm))).1
          (decodeBandParam
            (commonAxisBandInsert hm (commonAxisJacobianWitnessCoord m hm))).2.1
          (commonAxisNodeSource m hm j)).2 ^ pinnedExponent a = _
    rw [commonAxisJacobianWitness_loading]
    simp [pinnedConfluentVandermonde]
  · simp only [canonicalCommonAxisTopJacobianAtWitness, commonAxisTopColumn]
    rw [eval_pderiv_forwardCommonAxisCoordinatePolynomial,
      pderiv_forwardBandCoordinatePolynomial_eq_explicit,
      eval_pderiv_explicitForwardBandCoordinatePolynomial_slope,
      forwardSlopeSourceIndex_commonAxisUnpinnedSlope]
    change
      (decodeBandParam
          (commonAxisBandInsert hm (commonAxisJacobianWitnessCoord m hm))).2.2
            (commonAxisNodeSource m hm
              (pinnedSucc (n := m + 1) (by omega) i)) (2 * m + 2) *
        (forwardLoading m
          (decodeBandParam
            (commonAxisBandInsert hm (commonAxisJacobianWitnessCoord m hm))).1
          (decodeBandParam
            (commonAxisBandInsert hm (commonAxisJacobianWitnessCoord m hm))).2.1
          (commonAxisNodeSource m hm
            (pinnedSucc (n := m + 1) (by omega) i))).1 ^
              (2 * m + 2 - pinnedExponent a) *
        ((pinnedExponent a : ℂ) *
          (forwardLoading m
            (decodeBandParam
              (commonAxisBandInsert hm (commonAxisJacobianWitnessCoord m hm))).1
            (decodeBandParam
              (commonAxisBandInsert hm (commonAxisJacobianWitnessCoord m hm))).2.1
            (commonAxisNodeSource m hm
              (pinnedSucc (n := m + 1) (by omega) i))).2 ^
                (pinnedExponent a - 1)) = _
    rw [commonAxisJacobianWitness_weight _ _ _ _ (by omega),
      commonAxisJacobianWitness_loading]
    simp [pinnedConfluentVandermonde]

/-- Proves that the quantity called the det canonical Common Axis Top Jacobian At Witness is nonzero. -/
theorem det_canonicalCommonAxisTopJacobianAtWitness_ne_zero
    (m : ℕ) (hm : 1 ≤ m) :
    (canonicalCommonAxisTopJacobianAtWitness m hm).det ≠ 0 := by
  rw [canonicalCommonAxisTopJacobianAtWitness_eq_pinned]
  exact det_pinnedConfluentVandermonde_ne_zero (by omega)
    (commonAxisNodeValue m) (commonAxisNodeValue_injective m)

/-! ### The point at infinity -/

/-- Proves the stated mathematical property of Common Axis Top Augmented Index. -/
abbrev CommonAxisTopAugmentedIndex (m : ℕ) :=
  CommonAxisTopIndex m ⊕ Unit

/-- Defines the mathematical object called the common Axis Top Augmented Row. -/
def commonAxisTopAugmentedRow (m : ℕ) :
    CommonAxisTopAugmentedIndex m → RetainedCumCoord (2 * m + 2)
  | Sum.inl a => commonAxisTopRow m a
  | Sum.inr _ =>
      ⟨(⟨2 * m + 2, by omega⟩, ⟨2 * m + 2, by omega⟩),
        by change 2 ≤ 2 * m + 2; omega, le_rfl⟩

/-- Defines the mathematical object called the common Axis Top Augmented Column. -/
def commonAxisTopAugmentedColumn (m : ℕ) (hm : 1 ≤ m) :
    CommonAxisTopAugmentedIndex m →
      CommonAxisBandCoord m (2 * m + 2) hm
  | Sum.inl b => commonAxisTopColumn m hm b
  | Sum.inr _ =>
      ⟨Sum.inr (Sum.inr (Fin.last (m + 1), ⟨2 * m, by omega⟩)), by
        intro h
        cases Sum.inr.inj h⟩

/-- Defines the Jacobian matrix, row, column, or indexing object called the canonical Common Axis Top Augmented Jacobian At Witness. -/
def canonicalCommonAxisTopAugmentedJacobianAtWitness
    (m : ℕ) (hm : 1 ≤ m) :
    Matrix (CommonAxisTopAugmentedIndex m)
      (CommonAxisTopAugmentedIndex m) ℂ :=
  fun a b =>
    MvPolynomial.eval (commonAxisJacobianWitnessCoord m hm)
      (MvPolynomial.pderiv (commonAxisTopAugmentedColumn m hm b)
        (forwardCommonAxisCoordinatePolynomial m (2 * m + 2) hm (by omega)
          (commonAxisTopAugmentedRow m a)))

private def commonAxisTopAugmentedLowerLeft (m : ℕ) (hm : 1 ≤ m) :
    Matrix Unit (CommonAxisTopIndex m) ℂ :=
  fun u b => canonicalCommonAxisTopAugmentedJacobianAtWitness m hm
    (Sum.inr u) (Sum.inl b)

/-- Proves the stated equality or equivalence for canonical Common Axis Top Augmented Jacobian At Witness eq. -/
theorem canonicalCommonAxisTopAugmentedJacobianAtWitness_eq
    (m : ℕ) (hm : 1 ≤ m) :
    canonicalCommonAxisTopAugmentedJacobianAtWitness m hm =
      Matrix.fromBlocks (canonicalCommonAxisTopJacobianAtWitness m hm) 0
        (commonAxisTopAugmentedLowerLeft m hm) 1 := by
  ext a b
  rcases a with a | u <;> rcases b with b | v
  · rfl
  · obtain rfl : v = () := Subsingleton.elim _ _
    simp only [canonicalCommonAxisTopAugmentedJacobianAtWitness,
      commonAxisTopAugmentedColumn, commonAxisTopAugmentedRow,
      Matrix.fromBlocks_apply₁₂, Pi.zero_apply]
    rw [eval_pderiv_forwardCommonAxisCoordinatePolynomial,
      pderiv_forwardBandCoordinatePolynomial_eq_explicit,
      eval_pderiv_explicitForwardBandCoordinatePolynomial_weight_general,
      if_pos (by rfl), commonAxisJacobianWitness_loading_last]
    change
      (0 : ℂ) ^ (2 * m + 2 - pinnedExponent a) *
        1 ^ pinnedExponent a = 0
    simp [show 2 * m + 2 - pinnedExponent a ≠ 0 by
      have h := pinnedExponent_lt (n := m + 1) (by omega) a
      omega]
  · rfl
  · obtain rfl : u = () := Subsingleton.elim _ _
    obtain rfl : v = () := Subsingleton.elim _ _
    simp only [canonicalCommonAxisTopAugmentedJacobianAtWitness,
      commonAxisTopAugmentedColumn, commonAxisTopAugmentedRow,
      Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
    rw [eval_pderiv_forwardCommonAxisCoordinatePolynomial,
      pderiv_forwardBandCoordinatePolynomial_eq_explicit,
      eval_pderiv_explicitForwardBandCoordinatePolynomial_weight_general,
      if_pos (by rfl), commonAxisJacobianWitness_loading_last]
    simp

/-- Proves that the quantity called the det canonical Common Axis Top Augmented Jacobian At Witness is nonzero. -/
theorem det_canonicalCommonAxisTopAugmentedJacobianAtWitness_ne_zero
    (m : ℕ) (hm : 1 ≤ m) :
    (canonicalCommonAxisTopAugmentedJacobianAtWitness m hm).det ≠ 0 := by
  rw [canonicalCommonAxisTopAugmentedJacobianAtWitness_eq,
    Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]
  exact det_canonicalCommonAxisTopJacobianAtWitness_ne_zero m hm

end

/-- The canonical top-order common-axis Jacobian at the chosen witness is unchanged when equal
model orders and admissibility conditions are substituted. -/
add_decl_doc canonicalCommonAxisTopJacobianAtWitness.congr_simp

/-- The designated source node on the common axis is unchanged when equal model orders,
admissibility conditions, and node labels are substituted. -/
add_decl_doc commonAxisNodeSource.congr_simp

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
