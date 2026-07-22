/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Full Jacobian minor for the forward exceptional-locus image
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ExceptionalImageDimensionUpper
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ExceptionalJacobianCoordinates
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ExceptionalCommonAxisOrdinary
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension

noncomputable section

private lemma eval_forward_weight_otherOrder
    (m : ℕ) (q : RetainedCumCoord (2 * m + 2))
    (j : Fin (m + 2)) (k : Fin (2 * m + 1))
    (hk : k.val ≠ q.1.1 - 2) :
    MvPolynomial.eval (forwardJacobianWitnessCoord m)
        (MvPolynomial.pderiv
          (Sum.inr (Sum.inr (j, k)) : BandParamCoord m (2 * m + 2))
          (forwardBandCoordinatePolynomial m (2 * m + 2) (by omega) q)) = 0 := by
  rw [pderiv_forwardBandCoordinatePolynomial_eq_explicit,
    pderiv_explicitForwardBandCoordinatePolynomial_weight_otherOrder
      m (2 * m + 2) (by omega) q j k hk]
  simp

private lemma high_order_sub_two (m k : ℕ) (hm : 1 ≤ m) :
    m + 1 + k - 2 = m - 1 + k := by
  omega

/-! The ordinary-order block combines orders `2,...,m` and
`m+1,...,2m+1`.  Only its lower-left block must vanish for the determinant
calculation; the upper-right block is kept explicitly. -/

/-- Proves the stated mathematical property of Forward Ordinary Jacobian Index. -/
abbrev ForwardOrdinaryJacobianIndex (m : ℕ) :=
  ForwardLowWeightIndex m ⊕ ForwardHighWeightIndex m

/-- Defines the Jacobian matrix, row, column, or indexing object called the forward Ordinary Jacobian Row. -/
def forwardOrdinaryJacobianRow (m : ℕ) (hm : 1 ≤ m) :
    ForwardOrdinaryJacobianIndex m → RetainedCumCoord (2 * m + 2)
  | Sum.inl a => forwardLowWeightRow m a
  | Sum.inr a => forwardHighWeightRow m hm a

/-- Defines the Jacobian matrix, row, column, or indexing object called the forward Ordinary Jacobian Column. -/
def forwardOrdinaryJacobianColumn (m : ℕ) :
    ForwardOrdinaryJacobianIndex m → BandParamCoord m (2 * m + 2)
  | Sum.inl b => forwardLowWeightColumn m b
  | Sum.inr b => forwardHighWeightColumn m b

/-- Defines the Jacobian matrix, row, column, or indexing object called the canonical Forward Ordinary Jacobian At Witness. -/
def canonicalForwardOrdinaryJacobianAtWitness (m : ℕ) (hm : 1 ≤ m) :
    Matrix (ForwardOrdinaryJacobianIndex m)
      (ForwardOrdinaryJacobianIndex m) ℂ :=
  fun a b =>
    MvPolynomial.eval (forwardJacobianWitnessCoord m)
      (MvPolynomial.pderiv (forwardOrdinaryJacobianColumn m b)
        (forwardBandCoordinatePolynomial m (2 * m + 2) (by omega)
          (forwardOrdinaryJacobianRow m hm a)))

private def forwardOrdinaryUpperRight (m : ℕ) (hm : 1 ≤ m) :
    Matrix (ForwardLowWeightIndex m) (ForwardHighWeightIndex m) ℂ :=
  fun a b => canonicalForwardOrdinaryJacobianAtWitness m hm
    (Sum.inl a) (Sum.inr b)

/-- Proves the stated equality or equivalence for canonical Forward Ordinary Jacobian At Witness eq. -/
theorem canonicalForwardOrdinaryJacobianAtWitness_eq
    (m : ℕ) (hm : 1 ≤ m) :
    canonicalForwardOrdinaryJacobianAtWitness m hm =
      Matrix.fromBlocks (canonicalForwardLowWeightJacobianAtWitness m)
        (forwardOrdinaryUpperRight m hm) 0
        (canonicalForwardHighWeightJacobianAtWitness m hm) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · rfl
  · rfl
  · rcases a with ⟨a, ka⟩
    rcases b with ⟨kb, b⟩
    rcases a with a | u
    all_goals
      simp only [canonicalForwardOrdinaryJacobianAtWitness,
        forwardOrdinaryJacobianColumn, forwardOrdinaryJacobianRow,
        forwardLowWeightColumn,
        Matrix.fromBlocks_apply₂₁, Pi.zero_apply]
      apply eval_forward_weight_otherOrder
      rw [forwardHighWeightRow_order]
      rw [high_order_sub_two m ka.val hm]
      intro heq
      have hval : kb.val = m - 1 + ka.val := by
        simpa using heq
      have := kb.isLt
      omega
  · rfl

/-- Proves that the quantity called the det canonical Forward Ordinary Jacobian At Witness is nonzero. -/
theorem det_canonicalForwardOrdinaryJacobianAtWitness_ne_zero
    (m : ℕ) (hm : 1 ≤ m) :
    (canonicalForwardOrdinaryJacobianAtWitness m hm).det ≠ 0 := by
  rw [canonicalForwardOrdinaryJacobianAtWitness_eq,
    Matrix.det_fromBlocks_zero₂₁]
  exact mul_ne_zero
    (det_canonicalForwardLowWeightJacobianAtWitness_ne_zero m)
    (det_canonicalForwardHighWeightJacobianAtWitness_ne_zero m hm)

/-! The top order contributes the confluent block.  Its derivatives with
respect to all ordinary-order weights vanish, yielding the global
block-triangular minor. -/

/-- Proves the stated mathematical property of Forward Full Jacobian Index. -/
abbrev ForwardFullJacobianIndex (m : ℕ) :=
  ForwardOrdinaryJacobianIndex m ⊕ ForwardTopAugmentedIndex m

/-- Defines the Jacobian matrix, row, column, or indexing object called the forward Full Jacobian Row. -/
def forwardFullJacobianRow (m : ℕ) (hm : 1 ≤ m) :
    ForwardFullJacobianIndex m → RetainedCumCoord (2 * m + 2)
  | Sum.inl a => forwardOrdinaryJacobianRow m hm a
  | Sum.inr a => forwardTopAugmentedRow m a

/-- Defines the Jacobian matrix, row, column, or indexing object called the forward Full Jacobian Column. -/
def forwardFullJacobianColumn (m : ℕ) :
    ForwardFullJacobianIndex m → BandParamCoord m (2 * m + 2)
  | Sum.inl b => forwardOrdinaryJacobianColumn m b
  | Sum.inr b => forwardTopAugmentedColumn m b

/-- Defines the Jacobian matrix, row, column, or indexing object called the canonical Forward Full Jacobian At Witness. -/
def canonicalForwardFullJacobianAtWitness (m : ℕ) (hm : 1 ≤ m) :
    Matrix (ForwardFullJacobianIndex m) (ForwardFullJacobianIndex m) ℂ :=
  fun a b =>
    MvPolynomial.eval (forwardJacobianWitnessCoord m)
      (MvPolynomial.pderiv (forwardFullJacobianColumn m b)
        (forwardBandCoordinatePolynomial m (2 * m + 2) (by omega)
          (forwardFullJacobianRow m hm a)))

private def forwardFullUpperRight (m : ℕ) (hm : 1 ≤ m) :
    Matrix (ForwardOrdinaryJacobianIndex m) (ForwardTopAugmentedIndex m) ℂ :=
  fun a b => canonicalForwardFullJacobianAtWitness m hm
    (Sum.inl a) (Sum.inr b)

/-- Proves the stated equality or equivalence for canonical Forward Full Jacobian At Witness eq. -/
theorem canonicalForwardFullJacobianAtWitness_eq
    (m : ℕ) (hm : 1 ≤ m) :
    canonicalForwardFullJacobianAtWitness m hm =
      Matrix.fromBlocks (canonicalForwardOrdinaryJacobianAtWitness m hm)
        (forwardFullUpperRight m hm) 0
        (canonicalForwardTopAugmentedJacobianAtWitness m) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · rfl
  · rfl
  · rcases b with b | b
    · rcases b with ⟨k, j⟩
      rcases a with a | u
      · simp only [canonicalForwardFullJacobianAtWitness,
          forwardFullJacobianColumn, forwardFullJacobianRow,
          forwardOrdinaryJacobianColumn, forwardLowWeightColumn,
          forwardTopAugmentedRow, forwardTopRow,
          Matrix.fromBlocks_apply₂₁, Pi.zero_apply]
        apply eval_forward_weight_otherOrder
        change k.val ≠ 2 * m
        have := doubledExponent_lt (n := m + 1) (by omega) a
        omega
      · simp only [canonicalForwardFullJacobianAtWitness,
          forwardFullJacobianColumn, forwardFullJacobianRow,
          forwardOrdinaryJacobianColumn, forwardLowWeightColumn,
          forwardTopAugmentedRow, Matrix.fromBlocks_apply₂₁, Pi.zero_apply]
        apply eval_forward_weight_otherOrder
        change k.val ≠ 2 * m
        omega
    · rcases b with ⟨j, k⟩
      rcases j with j | u <;> rcases a with a | v
      all_goals
        simp only [canonicalForwardFullJacobianAtWitness,
          forwardFullJacobianColumn, forwardFullJacobianRow,
          forwardOrdinaryJacobianColumn, forwardHighWeightColumn,
          forwardTopAugmentedRow, forwardTopRow,
          Matrix.fromBlocks_apply₂₁, Pi.zero_apply]
        apply eval_forward_weight_otherOrder
        change m - 1 + k.val ≠ 2 * m
        omega
  · rfl

/-- Proves that the quantity called the det canonical Forward Full Jacobian At Witness is nonzero. -/
theorem det_canonicalForwardFullJacobianAtWitness_ne_zero
    (m : ℕ) (hm : 1 ≤ m) :
    (canonicalForwardFullJacobianAtWitness m hm).det ≠ 0 := by
  rw [canonicalForwardFullJacobianAtWitness_eq,
    Matrix.det_fromBlocks_zero₂₁]
  exact mul_ne_zero
    (det_canonicalForwardOrdinaryJacobianAtWitness_ne_zero m hm)
    (det_canonicalForwardTopAugmentedJacobianAtWitness_ne_zero m)

/-- Proves the stated mathematical property of card forward Full Jacobian Index. -/
theorem card_forwardFullJacobianIndex (m : ℕ) (hm : 1 ≤ m) :
    Fintype.card (ForwardFullJacobianIndex m) =
      commonAxisExpectedDimension m + 1 := by
  rw [← card_forwardImageGenerator m hm]
  have hlow : Fintype.card (ForwardLowWeightIndex m) =
      Fintype.card (RetainedCumCoord m) :=
    Fintype.card_congr (retainedCumCoordEquivSigma m).symm
  simp only [ForwardFullJacobianIndex, ForwardOrdinaryJacobianIndex,
    ForwardLowWeightIndex, ForwardHighWeightIndex, ForwardHighWeightNode,
    ForwardTopAugmentedIndex, ForwardImageGenerator, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_unit, hlow]
  ring

/-- Defines the Jacobian matrix, row, column, or indexing object called the forward Full Jacobian Equiv Fin. -/
noncomputable def forwardFullJacobianEquivFin (m : ℕ) (hm : 1 ≤ m) :
    ForwardFullJacobianIndex m ≃ Fin (commonAxisExpectedDimension m + 1) :=
  Fintype.equivFinOfCardEq (card_forwardFullJacobianIndex m hm)

/-- Defines the Jacobian matrix, row, column, or indexing object called the forward Full Jacobian Fin Row. -/
def forwardFullJacobianFinRow (m : ℕ) (hm : 1 ≤ m) :
    Fin (commonAxisExpectedDimension m + 1) →
      RetainedCumCoord (2 * m + 2) :=
  fun i => forwardFullJacobianRow m hm
    ((forwardFullJacobianEquivFin m hm).symm i)

/-- Defines the Jacobian matrix, row, column, or indexing object called the forward Full Jacobian Fin Column. -/
def forwardFullJacobianFinColumn (m : ℕ) (hm : 1 ≤ m) :
    Fin (commonAxisExpectedDimension m + 1) →
      BandParamCoord m (2 * m + 2) :=
  fun i => forwardFullJacobianColumn m
    ((forwardFullJacobianEquivFin m hm).symm i)

/-- Proves that the quantity called the forward Full Polynomial Jacobian Minor is nonzero. -/
theorem forwardFullPolynomialJacobianMinor_ne_zero
    (m : ℕ) (hm : 1 ≤ m) :
    polynomialJacobianMinor
      (forwardBandCoordinatePolynomial m (2 * m + 2) (by omega))
      (forwardFullJacobianFinRow m hm)
      (forwardFullJacobianFinColumn m hm) ≠ 0 := by
  intro hz
  have hzEval := congrArg (MvPolynomial.eval (forwardJacobianWitnessCoord m)) hz
  rw [map_zero, polynomialJacobianMinor, RingHom.map_det] at hzEval
  change ((canonicalForwardFullJacobianAtWitness m hm).submatrix
      (forwardFullJacobianEquivFin m hm).symm
      (forwardFullJacobianEquivFin m hm).symm).det = 0 at hzEval
  rw [Matrix.det_submatrix_equiv_self] at hzEval
  exact det_canonicalForwardFullJacobianAtWitness_ne_zero m hm hzEval

/-- The full forward retained-band image has the exact dimension certified by
the global confluent/Vandermonde Jacobian minor and the independently proved
generator-envelope upper bound. -/
theorem restrict_forwardCumulantImageVariety_dimension_expected
    (m : ℕ) (hm : 1 ≤ m) :
    HasAffineZariskiDimension (commonAxisExpectedDimension m + 1)
      (restrictCumBand (2 * m + 2) ''
        cumulantImageVariety (forwardCumulantMap m (2 * m + 2))) := by
  apply restrict_forwardCumulantImageVariety_dimension_of_jacobian
    m (commonAxisExpectedDimension m + 1)
    (forwardFullJacobianFinRow m hm)
    (forwardFullJacobianFinColumn m hm)
    (forwardFullPolynomialJacobianMinor_ne_zero m hm)
  simpa only [Nat.cast_add, Nat.cast_one] using
    forwardBandCoordinateSubalgebra_trdeg_le_expected m hm

/-! ### The pinned common-axis minor -/

private def selectedCommonAxisLowWeightColumn (m : ℕ) (hm : 1 ≤ m) :
    ForwardLowWeightIndex m → CommonAxisBandCoord m (2 * m + 2) hm
  | ⟨k, j⟩ =>
      ⟨Sum.inr (Sum.inr
        (commonAxisNodeSource m hm ⟨j.val, by omega⟩,
          ⟨k.val, by omega⟩)), by
        intro h
        cases Sum.inr.inj h⟩

private def selectedCommonAxisHighWeightColumn (m : ℕ) (hm : 1 ≤ m) :
    ForwardHighWeightIndex m → CommonAxisBandCoord m (2 * m + 2) hm
  | (Sum.inl j, k) =>
      ⟨Sum.inr (Sum.inr
        (commonAxisNodeSource m hm j, ⟨m - 1 + k.val, by omega⟩)), by
        intro h
        cases Sum.inr.inj h⟩
  | (Sum.inr _, k) =>
      ⟨Sum.inr (Sum.inr
        (Fin.last (m + 1), ⟨m - 1 + k.val, by omega⟩)), by
        intro h
        cases Sum.inr.inj h⟩

private lemma eval_selected_commonAxis_weight_otherOrder
    (m : ℕ) (hm : 1 ≤ m) (q : RetainedCumCoord (2 * m + 2))
    (c : CommonAxisBandCoord m (2 * m + 2) hm)
    (j : Fin (m + 2)) (k : Fin (2 * m + 1))
    (hc : c.1 = Sum.inr (Sum.inr (j, k)))
    (hk : k.val ≠ q.1.1 - 2) :
    MvPolynomial.eval (commonAxisJacobianWitnessCoord m hm)
        (MvPolynomial.pderiv c
          (forwardCommonAxisCoordinatePolynomial m (2 * m + 2) hm
            (by omega) q)) = 0 := by
  rw [eval_pderiv_forwardCommonAxisCoordinatePolynomial, hc,
    forwardBandCoordinatePolynomial_eq_explicit]
  have hz :=
    pderiv_explicitForwardBandCoordinatePolynomial_weight_otherOrder
      m (2 * m + 2) (by omega) q j k hk
  have heval := congrArg
    (MvPolynomial.eval
      (commonAxisBandInsert hm (commonAxisJacobianWitnessCoord m hm))) hz
  simpa using heval

/-- Proves the stated mathematical property of Common Axis Ordinary Jacobian Index. -/
abbrev CommonAxisOrdinaryJacobianIndex (m : ℕ) :=
  ForwardLowWeightIndex m ⊕ ForwardHighWeightIndex m

private def commonAxisOrdinaryJacobianRow (m : ℕ) (hm : 1 ≤ m) :
    CommonAxisOrdinaryJacobianIndex m → RetainedCumCoord (2 * m + 2)
  | Sum.inl a => forwardLowWeightRow m a
  | Sum.inr a => forwardHighWeightRow m hm a

private def commonAxisOrdinaryJacobianColumn (m : ℕ) (hm : 1 ≤ m) :
    CommonAxisOrdinaryJacobianIndex m →
      CommonAxisBandCoord m (2 * m + 2) hm
  | Sum.inl b => selectedCommonAxisLowWeightColumn m hm b
  | Sum.inr b => selectedCommonAxisHighWeightColumn m hm b

private def canonicalCommonAxisOrdinaryJacobianAtWitness
    (m : ℕ) (hm : 1 ≤ m) :
    Matrix (CommonAxisOrdinaryJacobianIndex m)
      (CommonAxisOrdinaryJacobianIndex m) ℂ :=
  fun a b =>
    MvPolynomial.eval (commonAxisJacobianWitnessCoord m hm)
      (MvPolynomial.pderiv (commonAxisOrdinaryJacobianColumn m hm b)
        (forwardCommonAxisCoordinatePolynomial m (2 * m + 2) hm
          (by omega) (commonAxisOrdinaryJacobianRow m hm a)))

private def commonAxisOrdinaryUpperRight (m : ℕ) (hm : 1 ≤ m) :
    Matrix (ForwardLowWeightIndex m) (ForwardHighWeightIndex m) ℂ :=
  fun a b => canonicalCommonAxisOrdinaryJacobianAtWitness m hm
    (Sum.inl a) (Sum.inr b)

private theorem canonicalCommonAxisOrdinaryJacobianAtWitness_eq
    (m : ℕ) (hm : 1 ≤ m) :
    canonicalCommonAxisOrdinaryJacobianAtWitness m hm =
      Matrix.fromBlocks (canonicalCommonAxisLowWeightJacobianAtWitness m hm)
        (commonAxisOrdinaryUpperRight m hm) 0
        (canonicalCommonAxisHighWeightJacobianAtWitness m hm) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · rfl
  · rfl
  · rcases a with ⟨a, ka⟩
    rcases b with ⟨kb, b⟩
    rcases a with a | u
    all_goals
      simp only [canonicalCommonAxisOrdinaryJacobianAtWitness,
        commonAxisOrdinaryJacobianColumn, commonAxisOrdinaryJacobianRow,
        selectedCommonAxisLowWeightColumn,
        Matrix.fromBlocks_apply₂₁, Pi.zero_apply]
      apply eval_selected_commonAxis_weight_otherOrder
      · rfl
      · rw [forwardHighWeightRow_order]
        rw [high_order_sub_two m ka.val hm]
        intro heq
        have hval : kb.val = m - 1 + ka.val := by simpa using heq
        have := kb.isLt
        omega
  · rfl

private theorem det_canonicalCommonAxisOrdinaryJacobianAtWitness_ne_zero
    (m : ℕ) (hm : 1 ≤ m) :
    (canonicalCommonAxisOrdinaryJacobianAtWitness m hm).det ≠ 0 := by
  rw [canonicalCommonAxisOrdinaryJacobianAtWitness_eq,
    Matrix.det_fromBlocks_zero₂₁]
  exact mul_ne_zero
    (det_canonicalCommonAxisLowWeightJacobianAtWitness_ne_zero m hm)
    (det_canonicalCommonAxisHighWeightJacobianAtWitness_ne_zero m hm)

/-- Proves the stated mathematical property of Common Axis Full Jacobian Index. -/
abbrev CommonAxisFullJacobianIndex (m : ℕ) :=
  CommonAxisOrdinaryJacobianIndex m ⊕ CommonAxisTopAugmentedIndex m

/-- Defines the Jacobian matrix, row, column, or indexing object called the common Axis Full Jacobian Row. -/
def commonAxisFullJacobianRow (m : ℕ) (hm : 1 ≤ m) :
    CommonAxisFullJacobianIndex m → RetainedCumCoord (2 * m + 2)
  | Sum.inl a => commonAxisOrdinaryJacobianRow m hm a
  | Sum.inr a => commonAxisTopAugmentedRow m a

/-- Defines the Jacobian matrix, row, column, or indexing object called the common Axis Full Jacobian Column. -/
def commonAxisFullJacobianColumn (m : ℕ) (hm : 1 ≤ m) :
    CommonAxisFullJacobianIndex m →
      CommonAxisBandCoord m (2 * m + 2) hm
  | Sum.inl b => commonAxisOrdinaryJacobianColumn m hm b
  | Sum.inr b => commonAxisTopAugmentedColumn m hm b

/-- Defines the Jacobian matrix, row, column, or indexing object called the canonical Common Axis Full Jacobian At Witness. -/
def canonicalCommonAxisFullJacobianAtWitness (m : ℕ) (hm : 1 ≤ m) :
    Matrix (CommonAxisFullJacobianIndex m)
      (CommonAxisFullJacobianIndex m) ℂ :=
  fun a b =>
    MvPolynomial.eval (commonAxisJacobianWitnessCoord m hm)
      (MvPolynomial.pderiv (commonAxisFullJacobianColumn m hm b)
        (forwardCommonAxisCoordinatePolynomial m (2 * m + 2) hm
          (by omega) (commonAxisFullJacobianRow m hm a)))

private def commonAxisFullUpperRight (m : ℕ) (hm : 1 ≤ m) :
    Matrix (CommonAxisOrdinaryJacobianIndex m)
      (CommonAxisTopAugmentedIndex m) ℂ :=
  fun a b => canonicalCommonAxisFullJacobianAtWitness m hm
    (Sum.inl a) (Sum.inr b)

/-- Proves the stated equality or equivalence for canonical Common Axis Full Jacobian At Witness eq. -/
theorem canonicalCommonAxisFullJacobianAtWitness_eq
    (m : ℕ) (hm : 1 ≤ m) :
    canonicalCommonAxisFullJacobianAtWitness m hm =
      Matrix.fromBlocks (canonicalCommonAxisOrdinaryJacobianAtWitness m hm)
        (commonAxisFullUpperRight m hm) 0
        (canonicalCommonAxisTopAugmentedJacobianAtWitness m hm) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · rfl
  · rfl
  · rcases b with b | b
    · rcases b with ⟨k, j⟩
      rcases a with a | u
      · simp only [canonicalCommonAxisFullJacobianAtWitness,
          commonAxisFullJacobianColumn, commonAxisFullJacobianRow,
          commonAxisOrdinaryJacobianColumn, selectedCommonAxisLowWeightColumn,
          commonAxisTopAugmentedRow, commonAxisTopRow,
          Matrix.fromBlocks_apply₂₁, Pi.zero_apply]
        apply eval_selected_commonAxis_weight_otherOrder
        · rfl
        · change k.val ≠ 2 * m
          have h := pinnedExponent_lt (n := m + 1) (by omega) a
          omega
      · simp only [canonicalCommonAxisFullJacobianAtWitness,
          commonAxisFullJacobianColumn, commonAxisFullJacobianRow,
          commonAxisOrdinaryJacobianColumn, selectedCommonAxisLowWeightColumn,
          commonAxisTopAugmentedRow,
          Matrix.fromBlocks_apply₂₁, Pi.zero_apply]
        apply eval_selected_commonAxis_weight_otherOrder
        · rfl
        · change k.val ≠ 2 * m
          omega
    · rcases b with ⟨j, k⟩
      rcases j with j | u <;> rcases a with a | v
      all_goals
        simp only [canonicalCommonAxisFullJacobianAtWitness,
          commonAxisFullJacobianColumn, commonAxisFullJacobianRow,
          commonAxisOrdinaryJacobianColumn, selectedCommonAxisHighWeightColumn,
          commonAxisTopAugmentedRow, commonAxisTopRow,
          Matrix.fromBlocks_apply₂₁, Pi.zero_apply]
        apply eval_selected_commonAxis_weight_otherOrder
        · rfl
        · change m - 1 + k.val ≠ 2 * m
          omega
  · rfl

/-- Proves that the quantity called the det canonical Common Axis Full Jacobian At Witness is nonzero. -/
theorem det_canonicalCommonAxisFullJacobianAtWitness_ne_zero
    (m : ℕ) (hm : 1 ≤ m) :
    (canonicalCommonAxisFullJacobianAtWitness m hm).det ≠ 0 := by
  rw [canonicalCommonAxisFullJacobianAtWitness_eq,
    Matrix.det_fromBlocks_zero₂₁]
  exact mul_ne_zero
    (det_canonicalCommonAxisOrdinaryJacobianAtWitness_ne_zero m hm)
    (det_canonicalCommonAxisTopAugmentedJacobianAtWitness_ne_zero m hm)

/-- Proves the stated mathematical property of card common Axis Full Jacobian Index. -/
theorem card_commonAxisFullJacobianIndex (m : ℕ) (hm : 1 ≤ m) :
    Fintype.card (CommonAxisFullJacobianIndex m) =
      commonAxisExpectedDimension m := by
  have h := card_forwardFullJacobianIndex m hm
  simp only [CommonAxisFullJacobianIndex, CommonAxisOrdinaryJacobianIndex,
    CommonAxisTopAugmentedIndex, CommonAxisTopIndex,
    ForwardFullJacobianIndex, ForwardOrdinaryJacobianIndex,
    ForwardTopAugmentedIndex, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_unit] at h ⊢
  omega

/-- Defines the Jacobian matrix, row, column, or indexing object called the common Axis Full Jacobian Equiv Fin. -/
noncomputable def commonAxisFullJacobianEquivFin (m : ℕ) (hm : 1 ≤ m) :
    CommonAxisFullJacobianIndex m ≃ Fin (commonAxisExpectedDimension m) :=
  Fintype.equivFinOfCardEq (card_commonAxisFullJacobianIndex m hm)

/-- Defines the Jacobian matrix, row, column, or indexing object called the common Axis Full Jacobian Fin Row. -/
def commonAxisFullJacobianFinRow (m : ℕ) (hm : 1 ≤ m) :
    Fin (commonAxisExpectedDimension m) → RetainedCumCoord (2 * m + 2) :=
  fun i => commonAxisFullJacobianRow m hm
    ((commonAxisFullJacobianEquivFin m hm).symm i)

/-- Defines the Jacobian matrix, row, column, or indexing object called the common Axis Full Jacobian Fin Column. -/
def commonAxisFullJacobianFinColumn (m : ℕ) (hm : 1 ≤ m) :
    Fin (commonAxisExpectedDimension m) →
      CommonAxisBandCoord m (2 * m + 2) hm :=
  fun i => commonAxisFullJacobianColumn m hm
    ((commonAxisFullJacobianEquivFin m hm).symm i)

/-- Proves that the quantity called the forward Common Axis Polynomial Jacobian Minor is nonzero. -/
theorem forwardCommonAxisPolynomialJacobianMinor_ne_zero
    (m : ℕ) (hm : 1 ≤ m) :
    polynomialJacobianMinor
      (forwardCommonAxisCoordinatePolynomial m (2 * m + 2) hm (by omega))
      (commonAxisFullJacobianFinRow m hm)
      (commonAxisFullJacobianFinColumn m hm) ≠ 0 := by
  intro hz
  have hzEval := congrArg
    (MvPolynomial.eval (commonAxisJacobianWitnessCoord m hm)) hz
  rw [map_zero, polynomialJacobianMinor, RingHom.map_det] at hzEval
  change ((canonicalCommonAxisFullJacobianAtWitness m hm).submatrix
      (commonAxisFullJacobianEquivFin m hm).symm
      (commonAxisFullJacobianEquivFin m hm).symm).det = 0 at hzEval
  rw [Matrix.det_submatrix_equiv_self] at hzEval
  exact det_canonicalCommonAxisFullJacobianAtWitness_ne_zero m hm hzEval

/-- The common-axis retained-band image has the exact dimension certified by
the pinned confluent-Vandermonde minor and the generator-envelope upper bound. -/
theorem restrict_forwardCommonAxisImageClosure_dimension_expected
    (m : ℕ) (hm : 1 ≤ m) :
    HasAffineZariskiDimension (commonAxisExpectedDimension m)
      (restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm) := by
  apply restrict_forwardCommonAxisImageClosure_dimension_of_jacobian m hm
    (commonAxisFullJacobianFinRow m hm)
    (commonAxisFullJacobianFinColumn m hm)
    (forwardCommonAxisPolynomialJacobianMinor_ne_zero m hm)
  exact forwardCommonAxisCoordinateSubalgebra_trdeg_le_expected m hm

end

/-- The canonical common-axis high-weight Jacobian at the chosen witness is unchanged when equal
model orders and admissibility conditions are substituted. -/
add_decl_doc canonicalCommonAxisHighWeightJacobianAtWitness.congr_simp

/-- The canonical common-axis low-weight Jacobian at the chosen witness is unchanged when equal
model orders and admissibility conditions are substituted. -/
add_decl_doc canonicalCommonAxisLowWeightJacobianAtWitness.congr_simp

/-- The augmented top-order common-axis Jacobian at the chosen witness is unchanged when equal
model orders and admissibility conditions are substituted. -/
add_decl_doc canonicalCommonAxisTopAugmentedJacobianAtWitness.congr_simp

/-- The canonical forward high-weight Jacobian at the chosen witness is unchanged when equal
model orders and admissibility conditions are substituted. -/
add_decl_doc canonicalForwardHighWeightJacobianAtWitness.congr_simp

/-- The canonical forward ordinary-order Jacobian at the chosen witness is unchanged when equal
model orders and admissibility conditions are substituted. -/
add_decl_doc canonicalForwardOrdinaryJacobianAtWitness.congr_simp

/-- The row selector for the full common-axis Jacobian is unchanged when equal model orders and
row indices are substituted. -/
add_decl_doc commonAxisFullJacobianRow.congr_simp

/-- The row selector for the full forward Jacobian is unchanged when equal model orders and row
indices are substituted. -/
add_decl_doc forwardFullJacobianRow.congr_simp

/-- The row selector for the ordinary forward Jacobian is unchanged when equal model orders and
row indices are substituted. -/
add_decl_doc forwardOrdinaryJacobianRow.congr_simp

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
