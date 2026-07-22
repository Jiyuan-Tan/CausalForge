/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.SymRedMatrix
import Mathlib.Data.Real.StarOrdered

/-! # PSD of block-symmetric elliptope points

The block-symmetric matrix `X(u,v)` has the orthogonal eigendecomposition

    `X(u,v) = x • (1 − P₁ − P_s) + y • P_s + z • P₁`,

with `x = 1−u`, `y = 1+(m−1)u−mv`, `z = 1+(m−1)u+mv`, where `P₁ = J/2m` (projection
onto `span 1`) and `P_s = s sᵀ/2m` (projection onto `span s`).  Each of `P₁`, `P_s`,
`1 − P₁ − P_s` is PSD, so nonnegative spectral coordinates force `X(u,v)` PSD.  This
supplies the inclusion `E_m^blk ⊆ {PSD, diag 1}` used by the `sInf` reductions. -/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators
open Causalean.Experimentation.DesignBased

/-- The quadratic form of `X(u,v)` on a vector `w`:
`wᵀ X(u,v) w = x·(Q − P²/2m − D²/2m) + y·(D²/2m) + z·(P²/2m)` with
`Q = ∑ wᵢ²`, `P = ∑ wᵢ`, `D = ∑ sᵢ wᵢ`. -/
lemma onesProj_posSemidef (m : ℕ) : (onesProj m).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact Matrix.IsHermitian.ext fun i j => by simp [onesProj]
  · intro x
    by_cases hm0 : m = 0
    · subst m
      simp [dotProduct]
    · have hquad :
          dotProduct x ((onesProj m).mulVec x)
            = (1 / (2 * (m : ℝ))) * (∑ i, x i) ^ 2 := by
        simp [dotProduct, Matrix.mulVec, onesProj, Finset.mul_sum, Finset.sum_mul,
          sq, mul_assoc, mul_left_comm, mul_comm]
      simpa [hquad] using mul_nonneg (by positivity) (sq_nonneg (∑ i, x i))

/-- `signProj = s sᵀ / 2m` is PSD. -/
lemma signProj_posSemidef (m : ℕ) : (signProj m).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact Matrix.IsHermitian.ext fun i j => by
      simp [signProj, mul_comm, mul_left_comm, mul_assoc]
  · intro x
    by_cases hm0 : m = 0
    · subst m
      simp [dotProduct]
    · have hquad :
        dotProduct x ((signProj m).mulVec x)
            = (1 / (2 * (m : ℝ))) * (∑ i, signVec m i * x i) ^ 2 := by
        simp [dotProduct, Matrix.mulVec, signProj, Finset.mul_sum, Finset.sum_mul,
          sq, mul_assoc, mul_left_comm, mul_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      simpa [hquad] using
        mul_nonneg (by positivity) (sq_nonneg (∑ i, signVec m i * x i))

/-- The complementary projection `1 − P₁ − P_s` is PSD. -/
lemma projComplement_posSemidef (m : ℕ) (hm : 2 ≤ m) :
    ((1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) - onesProj m - signProj m).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact ((Matrix.isHermitian_one.sub (onesProj_posSemidef m).1).sub
      (signProj_posSemidef m).1)
  · intro x
    change 0 ≤ dotProduct x
      (((1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) - onesProj m - signProj m).mulVec x)
    let A : ℝ := ∑ i ∈ blockAFin m, x i
    let B : ℝ := ∑ i ∈ blockBFin m, x i
    let QA : ℝ := ∑ i ∈ blockAFin m, x i ^ 2
    let QB : ℝ := ∑ i ∈ blockBFin m, x i ^ 2
    have hmposR : (0 : ℝ) < (m : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
    have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmposR
    have hP1 :
        dotProduct x ((onesProj m).mulVec x)
          = (1 / (2 * (m : ℝ))) * (∑ i, x i) ^ 2 := by
      simp [dotProduct, Matrix.mulVec, onesProj, Finset.mul_sum, Finset.sum_mul,
        sq, mul_assoc, mul_left_comm, mul_comm]
    have hPs :
        dotProduct x ((signProj m).mulVec x)
          = (1 / (2 * (m : ℝ))) * (∑ i, signVec m i * x i) ^ 2 := by
      simp [dotProduct, Matrix.mulVec, signProj, Finset.mul_sum, Finset.sum_mul,
        sq, mul_assoc, mul_left_comm, mul_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hSelf : dotProduct x x = ∑ i, x i ^ 2 := by
      simp [dotProduct, pow_two]
    have hsumx : (∑ i, x i) = A + B := by
      dsimp [A, B, blockAFin, blockBFin]
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun i : Fin (2 * m) => i.val < m) (f := fun i => x i)]
    have hsumq : (∑ i, x i ^ 2) = QA + QB := by
      dsimp [QA, QB, blockAFin, blockBFin]
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun i : Fin (2 * m) => i.val < m) (f := fun i => x i ^ 2)]
    have hsumd : (∑ i, signVec m i * x i) = A - B := by
      have hA : (∑ i ∈ blockAFin m, signVec m i * x i) = A := by
        dsimp [A]
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i.val < m := by simpa [blockAFin] using hi
        simp [signVec, hi']
      have hB : (∑ i ∈ blockBFin m, signVec m i * x i) = -B := by
        dsimp [B]
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : ¬ i.val < m := by simpa [blockBFin] using hi
        simp [signVec, hi']
      calc
        (∑ i, signVec m i * x i)
            = (∑ i ∈ blockAFin m, signVec m i * x i)
              + (∑ i ∈ blockBFin m, signVec m i * x i) := by
                dsimp [blockAFin, blockBFin]
                rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
                  (p := fun i : Fin (2 * m) => i.val < m)
                  (f := fun i => signVec m i * x i)]
        _ = A - B := by
          rw [hA, hB]
          ring
    have hquad :
        dotProduct x
          (((1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) - onesProj m - signProj m).mulVec x)
          =
        (QA + QB) - (1 / (2 * (m : ℝ))) * (A + B) ^ 2
          - (1 / (2 * (m : ℝ))) * (A - B) ^ 2 := by
      rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
      rw [dotProduct_sub, dotProduct_sub, hSelf, hP1, hPs, hsumx, hsumd, hsumq]
    have hAcs : A ^ 2 ≤ (m : ℝ) * QA := by
      dsimp [A, QA]
      simpa [card_blockAFin] using
        (sq_sum_le_card_mul_sum_sq (s := blockAFin m) (f := fun i => x i))
    have hBcs : B ^ 2 ≤ (m : ℝ) * QB := by
      dsimp [B, QB]
      simpa [card_blockBFin] using
        (sq_sum_le_card_mul_sum_sq (s := blockBFin m) (f := fun i => x i))
    have hmain :
        0 ≤ (QA + QB) - (1 / (2 * (m : ℝ))) * (A + B) ^ 2
          - (1 / (2 * (m : ℝ))) * (A - B) ^ 2 := by
      have hle : (A ^ 2 + B ^ 2) / (m : ℝ) ≤ QA + QB := by
        rw [div_le_iff₀ hmposR]
        nlinarith [hAcs, hBcs]
      have halg :
          (1 / (2 * (m : ℝ))) * (A + B) ^ 2
            + (1 / (2 * (m : ℝ))) * (A - B) ^ 2
          = (A ^ 2 + B ^ 2) / (m : ℝ) := by
        field_simp [hm0]
        ring
      nlinarith
    simpa [hquad] using hmain

/-- **Spectral decomposition** of the block-symmetric matrix. -/
lemma blockSymMatrix_decomp (m : ℕ) (u v : ℝ) :
    blockSymMatrix m u v
      = (1 - u) • ((1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) - onesProj m - signProj m)
        + (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v) • signProj m
        + (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) • onesProj m := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · ext i
    exact Fin.elim0 i
  · have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hmpos)
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : i.val < m
      · simp [blockSymMatrix, onesProj, signProj, signVec, hi, hm0, smul_eq_mul]
        field_simp [hm0]
        ring
      · simp [blockSymMatrix, onesProj, signProj, signVec, hi, hm0, smul_eq_mul]
        field_simp [hm0]
        ring
    · by_cases hi : i.val < m <;> by_cases hj : j.val < m
      · simp [blockSymMatrix, onesProj, signProj, signVec, Matrix.one_apply, hij, hi, hj,
          hm0, smul_eq_mul]
        field_simp [hm0]
        ring
      · simp [blockSymMatrix, onesProj, signProj, signVec, Matrix.one_apply, hij, hi, hj,
          hm0, smul_eq_mul]
        field_simp [hm0]
        ring
      · simp [blockSymMatrix, onesProj, signProj, signVec, Matrix.one_apply, hij, hi, hj,
          hm0, smul_eq_mul]
        field_simp [hm0]
        ring
      · simp [blockSymMatrix, onesProj, signProj, signVec, Matrix.one_apply, hij, hi, hj,
          hm0, smul_eq_mul]
        field_simp [hm0]
        ring

/-- **PSD from nonnegative spectral coordinates.** -/
lemma blockSymMatrix_posSemidef (m : ℕ) (u v : ℝ) (hm : 2 ≤ m)
    (hx : 0 ≤ 1 - u)
    (hy : 0 ≤ 1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
    (hz : 0 ≤ 1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) :
    (blockSymMatrix m u v).PosSemidef := by
  rw [blockSymMatrix_decomp]
  exact (((projComplement_posSemidef m hm).smul hx).add
    ((signProj_posSemidef m).smul hy)).add ((onesProj_posSemidef m).smul hz)

/-- Block-symmetric elliptope points are PSD with unit diagonal:
`E_m^blk ⊆ {X : PSD ∧ diag 1}`. -/
lemma blockElliptope_subset_elliptope (m : ℕ) (a b : ℝ) :
    blockElliptope m a b
      ⊆ { X : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ | X.PosSemidef ∧ ∀ i, X i i = 1 } := by
  intro X hX
  obtain ⟨u, v, rfl, hmem⟩ := hX
  exact ⟨blockSymMatrix_posSemidef m u v hmem.homophily.1 hmem.psd_x hmem.psd_y hmem.psd_z,
    fun i => by simp [blockSymMatrix]⟩

end CausalSmith.Experimentation.DesignPm1
