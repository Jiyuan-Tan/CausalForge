/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Common-axis ordinary-order Jacobian blocks
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ExceptionalCommonAxisJacobianTop
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

noncomputable section

private def commonAxisLowWeightColumn (m : ℕ) (hm : 1 ≤ m) :
    ForwardLowWeightIndex m → CommonAxisBandCoord m (2 * m + 2) hm
  | ⟨k, j⟩ =>
      ⟨Sum.inr (Sum.inr
        (commonAxisNodeSource m hm ⟨j.val, by
          have := j.isLt
          have := k.isLt
          omega⟩, ⟨k.val, by omega⟩)), by
        intro h
        cases Sum.inr.inj h⟩

private def commonAxisHighWeightColumn (m : ℕ) (hm : 1 ≤ m) :
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

private lemma eval_commonAxis_weight_otherOrder
    (m : ℕ) (hm : 1 ≤ m) (q : RetainedCumCoord (2 * m + 2))
    (c : CommonAxisBandCoord m (2 * m + 2) hm)
    (j : Fin (m + 2)) (k : Fin (2 * m + 1))
    (hc : c.1 = Sum.inr (Sum.inr (j, k)))
    (hk : k.val ≠ q.1.1 - 2) :
    MvPolynomial.eval (commonAxisJacobianWitnessCoord m hm)
        (MvPolynomial.pderiv c
          (forwardCommonAxisCoordinatePolynomial m (2 * m + 2) hm
            (by omega) q)) = 0 := by
  rw [eval_pderiv_forwardCommonAxisCoordinatePolynomial]
  rw [hc, forwardBandCoordinatePolynomial_eq_explicit]
  have hz :=
    pderiv_explicitForwardBandCoordinatePolynomial_weight_otherOrder
      m (2 * m + 2) (by omega) q j k hk
  have heval := congrArg
    (MvPolynomial.eval
      (commonAxisBandInsert hm (commonAxisJacobianWitnessCoord m hm))) hz
  simpa using heval

/-- Defines the Jacobian matrix, row, column, or indexing object called the canonical Common Axis Low Weight Jacobian At Witness. -/
def canonicalCommonAxisLowWeightJacobianAtWitness (m : ℕ) (hm : 1 ≤ m) :
    Matrix (ForwardLowWeightIndex m) (ForwardLowWeightIndex m) ℂ :=
  fun a b =>
    MvPolynomial.eval (commonAxisJacobianWitnessCoord m hm)
      (MvPolynomial.pderiv (commonAxisLowWeightColumn m hm b)
        (forwardCommonAxisCoordinatePolynomial m (2 * m + 2) hm
          (by omega) (forwardLowWeightRow m a)))

private def commonAxisLowVandermondeBlock (k : Fin (m - 1)) :
    Matrix (Fin (k.val + 3)) (Fin (k.val + 3)) ℂ :=
  (Matrix.vandermonde (fun j => (j.val : ℂ))).transpose

/-- Proves the stated equality or equivalence for canonical Common Axis Low Weight Jacobian At Witness eq. -/
theorem canonicalCommonAxisLowWeightJacobianAtWitness_eq
    (m : ℕ) (hm : 1 ≤ m) :
    canonicalCommonAxisLowWeightJacobianAtWitness m hm =
      Matrix.blockDiagonal' (commonAxisLowVandermondeBlock (m := m)) := by
  ext a b
  rcases a with ⟨ka, a⟩
  rcases b with ⟨kb, b⟩
  by_cases h : ka = kb
  · subst kb
    rw [Matrix.blockDiagonal'_apply_eq]
    simp only [canonicalCommonAxisLowWeightJacobianAtWitness,
      commonAxisLowWeightColumn, forwardLowWeightRow]
    rw [eval_pderiv_forwardCommonAxisCoordinatePolynomial,
      pderiv_forwardBandCoordinatePolynomial_eq_explicit,
      eval_pderiv_explicitForwardBandCoordinatePolynomial_weight_general,
      if_pos (by rfl)]
    change
      (forwardLoading m
        (decodeBandParam (commonAxisBandInsert hm
          (commonAxisJacobianWitnessCoord m hm))).1
        (decodeBandParam (commonAxisBandInsert hm
          (commonAxisJacobianWitnessCoord m hm))).2.1
        (commonAxisNodeSource m hm ⟨b.val, _⟩)).1 ^ (ka.val + 2 - a.val) *
      (forwardLoading m
        (decodeBandParam (commonAxisBandInsert hm
          (commonAxisJacobianWitnessCoord m hm))).1
        (decodeBandParam (commonAxisBandInsert hm
          (commonAxisJacobianWitnessCoord m hm))).2.1
        (commonAxisNodeSource m hm ⟨b.val, _⟩)).2 ^ a.val = _
    rw [commonAxisJacobianWitness_loading]
    simp [commonAxisNodeValue, commonAxisLowVandermondeBlock,
      Matrix.vandermonde]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
    simp only [canonicalCommonAxisLowWeightJacobianAtWitness]
    apply eval_commonAxis_weight_otherOrder
      m hm (forwardLowWeightRow m ⟨ka, a⟩)
      (commonAxisLowWeightColumn m hm ⟨kb, b⟩)
      (commonAxisNodeSource m hm ⟨b.val, by
        have := b.isLt; have := kb.isLt; omega⟩)
      ⟨kb.val, by omega⟩
    · rfl
    · intro heq
      apply h
      apply Fin.ext
      simpa using heq.symm

/-- Proves that the quantity called the det canonical Common Axis Low Weight Jacobian At Witness is nonzero. -/
theorem det_canonicalCommonAxisLowWeightJacobianAtWitness_ne_zero
    (m : ℕ) (hm : 1 ≤ m) :
    (canonicalCommonAxisLowWeightJacobianAtWitness m hm).det ≠ 0 := by
  rw [canonicalCommonAxisLowWeightJacobianAtWitness_eq]
  have hblocks : IsUnit (commonAxisLowVandermondeBlock (m := m)) := by
    rw [Pi.isUnit_iff]
    intro k
    rw [Matrix.isUnit_iff_isUnit_det]
    rw [commonAxisLowVandermondeBlock, Matrix.det_transpose]
    exact (Matrix.det_vandermonde_ne_zero_iff.mpr (by
      intro i j hij
      apply Fin.ext
      change ((i.val : ℕ) : ℂ) = ((j.val : ℕ) : ℂ) at hij
      exact_mod_cast hij)).isUnit
  have hmatrix : IsUnit (Matrix.blockDiagonal'
      (commonAxisLowVandermondeBlock (m := m))) :=
    hblocks.map (Matrix.blockDiagonal'RingHom
      (fun k : Fin (m - 1) => Fin (k.val + 3)) ℂ)
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hmatrix).ne_zero

/-- Defines the Jacobian matrix, row, column, or indexing object called the canonical Common Axis High Weight Jacobian At Witness. -/
def canonicalCommonAxisHighWeightJacobianAtWitness (m : ℕ) (hm : 1 ≤ m) :
    Matrix (ForwardHighWeightIndex m) (ForwardHighWeightIndex m) ℂ :=
  fun a b =>
    MvPolynomial.eval (commonAxisJacobianWitnessCoord m hm)
      (MvPolynomial.pderiv (commonAxisHighWeightColumn m hm b)
        (forwardCommonAxisCoordinatePolynomial m (2 * m + 2) hm
          (by omega) (forwardHighWeightRow m hm a)))

private def commonAxisHighWeightBlock (m : ℕ) (k : Fin (m + 1)) :
    Matrix (ForwardHighWeightNode m) (ForwardHighWeightNode m) ℂ :=
  Matrix.fromBlocks
    (Matrix.vandermonde (fun j : Fin (m + 1) => (j.val : ℂ))).transpose
    0
    (fun _ j => (j.val : ℂ) ^ (m + 1 + k.val))
    1

private theorem det_commonAxisHighWeightBlock_ne_zero
    (m : ℕ) (k : Fin (m + 1)) :
    (commonAxisHighWeightBlock m k).det ≠ 0 := by
  rw [commonAxisHighWeightBlock, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_transpose, Matrix.det_one, mul_one]
  exact Matrix.det_vandermonde_ne_zero_iff.mpr (by
    intro i j hij
    apply Fin.ext
    change ((i.val : ℕ) : ℂ) = ((j.val : ℕ) : ℂ) at hij
    exact_mod_cast hij)

private lemma commonAxis_high_order_sub_two (m k : ℕ) (hm : 1 ≤ m) :
    m + 1 + k - 2 = m - 1 + k := by
  omega

/-- Proves the stated equality or equivalence for canonical Common Axis High Weight Jacobian At Witness eq. -/
theorem canonicalCommonAxisHighWeightJacobianAtWitness_eq
    (m : ℕ) (hm : 1 ≤ m) :
    canonicalCommonAxisHighWeightJacobianAtWitness m hm =
      Matrix.blockDiagonal (commonAxisHighWeightBlock m) := by
  ext a b
  rcases a with ⟨a, ka⟩
  rcases b with ⟨b, kb⟩
  by_cases h : ka = kb
  · subst kb
    rw [Matrix.blockDiagonal_apply_eq]
    rcases a with a | u <;> rcases b with b | v
    · simp only [canonicalCommonAxisHighWeightJacobianAtWitness,
        commonAxisHighWeightColumn, forwardHighWeightRow,
        commonAxisHighWeightBlock, Matrix.fromBlocks_apply₁₁]
      rw [eval_pderiv_forwardCommonAxisCoordinatePolynomial,
        pderiv_forwardBandCoordinatePolynomial_eq_explicit,
        eval_pderiv_explicitForwardBandCoordinatePolynomial_weight_general,
        if_pos (by
          change m - 1 + ka.val = m + 1 + ka.val - 2
          omega)]
      change
        (forwardLoading m
          (decodeBandParam (commonAxisBandInsert hm
            (commonAxisJacobianWitnessCoord m hm))).1
          (decodeBandParam (commonAxisBandInsert hm
            (commonAxisJacobianWitnessCoord m hm))).2.1
          (commonAxisNodeSource m hm b)).1 ^
            ((forwardHighWeightRow m hm (Sum.inl a, ka)).1.1.val - a.val) *
        (forwardLoading m
          (decodeBandParam (commonAxisBandInsert hm
            (commonAxisJacobianWitnessCoord m hm))).1
          (decodeBandParam (commonAxisBandInsert hm
            (commonAxisJacobianWitnessCoord m hm))).2.1
          (commonAxisNodeSource m hm b)).2 ^ a.val = _
      rw [commonAxisJacobianWitness_loading, forwardHighWeightRow_order]
      simp [commonAxisNodeValue, Matrix.vandermonde]
    · simp only [canonicalCommonAxisHighWeightJacobianAtWitness,
        commonAxisHighWeightColumn, forwardHighWeightRow,
        commonAxisHighWeightBlock, Matrix.fromBlocks_apply₁₂, Pi.zero_apply]
      rw [eval_pderiv_forwardCommonAxisCoordinatePolynomial,
        pderiv_forwardBandCoordinatePolynomial_eq_explicit,
        eval_pderiv_explicitForwardBandCoordinatePolynomial_weight_general,
        if_pos (by
          change m - 1 + ka.val = m + 1 + ka.val - 2
          omega)]
      change
        (forwardLoading m
          (decodeBandParam (commonAxisBandInsert hm
            (commonAxisJacobianWitnessCoord m hm))).1
          (decodeBandParam (commonAxisBandInsert hm
            (commonAxisJacobianWitnessCoord m hm))).2.1
          (Fin.last (m + 1))).1 ^
            ((forwardHighWeightRow m hm (Sum.inl a, ka)).1.1.val - a.val) *
        (forwardLoading m
          (decodeBandParam (commonAxisBandInsert hm
            (commonAxisJacobianWitnessCoord m hm))).1
          (decodeBandParam (commonAxisBandInsert hm
            (commonAxisJacobianWitnessCoord m hm))).2.1
          (Fin.last (m + 1))).2 ^ a.val = _
      rw [commonAxisJacobianWitness_loading_last, forwardHighWeightRow_order]
      simp [show m + 1 + ka.val - a.val ≠ 0 by
        have := a.isLt; omega]
    · obtain rfl : u = () := Subsingleton.elim _ _
      simp only [canonicalCommonAxisHighWeightJacobianAtWitness,
        commonAxisHighWeightColumn, forwardHighWeightRow,
        commonAxisHighWeightBlock, Matrix.fromBlocks_apply₂₁]
      rw [eval_pderiv_forwardCommonAxisCoordinatePolynomial,
        pderiv_forwardBandCoordinatePolynomial_eq_explicit,
        eval_pderiv_explicitForwardBandCoordinatePolynomial_weight_general,
        if_pos (by
          change m - 1 + ka.val = m + 1 + ka.val - 2
          omega)]
      change
        (forwardLoading m
          (decodeBandParam (commonAxisBandInsert hm
            (commonAxisJacobianWitnessCoord m hm))).1
          (decodeBandParam (commonAxisBandInsert hm
            (commonAxisJacobianWitnessCoord m hm))).2.1
          (commonAxisNodeSource m hm b)).1 ^
            ((forwardHighWeightRow m hm (Sum.inr (), ka)).1.1.val -
              (forwardHighWeightRow m hm (Sum.inr (), ka)).1.2.val) *
        (forwardLoading m
          (decodeBandParam (commonAxisBandInsert hm
            (commonAxisJacobianWitnessCoord m hm))).1
          (decodeBandParam (commonAxisBandInsert hm
            (commonAxisJacobianWitnessCoord m hm))).2.1
          (commonAxisNodeSource m hm b)).2 ^
            (forwardHighWeightRow m hm (Sum.inr (), ka)).1.2.val = _
      rw [commonAxisJacobianWitness_loading, forwardHighWeightRow_order]
      simp [commonAxisNodeValue]
      rfl
    · simp only [canonicalCommonAxisHighWeightJacobianAtWitness,
        commonAxisHighWeightColumn, forwardHighWeightRow,
        commonAxisHighWeightBlock, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
      rw [eval_pderiv_forwardCommonAxisCoordinatePolynomial,
        pderiv_forwardBandCoordinatePolynomial_eq_explicit,
        eval_pderiv_explicitForwardBandCoordinatePolynomial_weight_general,
        if_pos (by
          change m - 1 + ka.val = m + 1 + ka.val - 2
          omega),
        commonAxisJacobianWitness_loading_last]
      simp
  · rw [Matrix.blockDiagonal_apply_ne _ _ _ h]
    rcases a with a | u <;> rcases b with b | v
    all_goals
      simp only [canonicalCommonAxisHighWeightJacobianAtWitness]
      apply eval_commonAxis_weight_otherOrder
      · rfl
      · intro heq
        apply h
        apply Fin.ext
        change m - 1 + kb.val = m + 1 + ka.val - 2 at heq
        omega

/-- Proves that the quantity called the det canonical Common Axis High Weight Jacobian At Witness is nonzero. -/
theorem det_canonicalCommonAxisHighWeightJacobianAtWitness_ne_zero
    (m : ℕ) (hm : 1 ≤ m) :
    (canonicalCommonAxisHighWeightJacobianAtWitness m hm).det ≠ 0 := by
  rw [canonicalCommonAxisHighWeightJacobianAtWitness_eq,
    Matrix.det_blockDiagonal]
  exact Finset.prod_ne_zero_iff.mpr fun k _ =>
    det_commonAxisHighWeightBlock_ne_zero m k

end

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
