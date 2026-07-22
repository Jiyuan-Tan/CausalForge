/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.SpectralCoordinates
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Matrix-side symmetry reduction (block-constant averaging, no group action)

The objective matrices `L_m`, `L_m^†`, `J_n` are all **block-constant**: their
entries depend only on the pair type (diagonal / within-community / cross-community).
For a block-constant `M` and a symmetric `X`,

    `Tr(M X) = d·∑ᵢ Xᵢᵢ + w·Ssame(X) + c·Scross(X)`,

where `Ssame`/`Scross` are the within/cross off-diagonal entry sums.  Setting
`u = Ssame(X)/Nsame`, `v = Scross(X)/Ncross` (the block averages) makes the block
sums of `X(u,v)` match those of `X`, so **every trace term is exactly preserved**,
while the Frobenius term drops by Cauchy–Schwarz (`(∑x)² ≤ N·∑x²`).  PSD unit-diagonal
`X` further forces `X(u,v) ∈ E_m^blk` via the quadratic forms `1ᵀX1 ≥ 0`, `sᵀXs ≥ 0`,
`(eᵢ−eⱼ)ᵀX(eᵢ−eⱼ) ≥ 0`.  Hence orbit-averaging never worsens the objective — with no
group machinery. -/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators
open Causalean.Experimentation.DesignBased

/-- Block-constant matrix `G(d,w,c)`: entry `d` on the diagonal, `w` within a
community, `c` across communities.  `blockSymMatrix m u v = blockConstMat m 1 u v`. -/
def blockConstMat (m : ℕ) (d w c : ℝ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  Matrix.of fun i j =>
    if i = j then d else if (decide (i.val < m) = decide (j.val < m)) then w else c

/-- The within-community off-diagonal ordered pairs. -/
def sameOffPairs (m : ℕ) : Finset (Fin (2 * m) × Fin (2 * m)) :=
  Finset.univ.filter fun p => p.1 ≠ p.2 ∧ decide (p.1.val < m) = decide (p.2.val < m)

/-- The cross-community ordered pairs. -/
def crossPairs (m : ℕ) : Finset (Fin (2 * m) × Fin (2 * m)) :=
  Finset.univ.filter fun p => decide (p.1.val < m) ≠ decide (p.2.val < m)

/-- The within-community entry sum `∑_{same, i≠j} Xᵢⱼ`. -/
def Ssame (m : ℕ) (X : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) : ℝ :=
  ∑ p ∈ sameOffPairs m, X p.1 p.2

/-- The cross-community entry sum `∑_{cross} Xᵢⱼ`. -/
def Scross (m : ℕ) (X : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) : ℝ :=
  ∑ p ∈ crossPairs m, X p.1 p.2

/-- Number of within-community off-diagonal ordered pairs `= 2m(m−1)`. -/
def NsameR (m : ℕ) : ℝ := 2 * (m : ℝ) * ((m : ℝ) - 1)

/-- Number of cross-community ordered pairs `= 2m²`. -/
def NcrossR (m : ℕ) : ℝ := 2 * (m : ℝ) * (m : ℝ)

/-- The block average `u` of `X`. -/
noncomputable def uOf (m : ℕ) (X : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) : ℝ :=
  Ssame m X / NsameR m

/-- The block average `v` of `X`. -/
noncomputable def vOf (m : ℕ) (X : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) : ℝ :=
  Scross m X / NcrossR m

/-- `blockSymMatrix` is the `d = 1` block-constant matrix. -/
lemma blockSymMatrix_eq_blockConst (m : ℕ) (u v : ℝ) :
    blockSymMatrix m u v = blockConstMat m 1 u v := rfl

/-- A block-constant matrix is symmetric. -/
lemma blockConstMat_symm (m : ℕ) (d w c : ℝ) (i j : Fin (2 * m)) :
    blockConstMat m d w c i j = blockConstMat m d w c j i := by
  by_cases hi : i.val < m <;> by_cases hj : j.val < m <;> by_cases hij : i = j <;>
    simp [blockConstMat, hi, hj, hij, eq_comm]

/-- `|sameOffPairs m| = 2m(m−1)`. -/
lemma card_sameOffPairs (m : ℕ) : (sameOffPairs m).card = 2 * m * (m - 1) := by
  have hpair := block_pair_sum m (0 : ℝ) 1 0
  have hpair' : (∑ i : Fin (2 * m), ∑ j : Fin (2 * m),
      if i = j then (0 : ℝ) else if i.val < m ↔ j.val < m then 1 else 0)
      = 2 * (m : ℝ) * ((m : ℝ) - 1) := by
    simpa using hpair
  have hsum : (∑ i : Fin (2 * m), ∑ j : Fin (2 * m),
      (if i ≠ j ∧ decide (i.val < m) = decide (j.val < m) then (1 : ℝ) else 0))
      = 2 * (m : ℝ) * ((m : ℝ) - 1) := by
    rw [← hpair']
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j <;> by_cases hsame : i.val < m ↔ j.val < m <;>
      simp [hij, hsame]
  have hreal : ((sameOffPairs m).card : ℝ) = 2 * (m : ℝ) * ((m : ℝ) - 1) := by
    have hcard : ((sameOffPairs m).card : ℝ) = ∑ p ∈ sameOffPairs m, (1 : ℝ) := by simp
    rw [hcard, sameOffPairs, Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
    simpa [decide_eq_decide, eq_comm] using hsum
  apply Nat.cast_injective (R := ℝ)
  rw [hreal]
  cases m <;> simp

/-- `|crossPairs m| = 2m²`. -/
lemma card_crossPairs (m : ℕ) : (crossPairs m).card = 2 * m * m := by
  have hpair := block_pair_sum m (0 : ℝ) 0 1
  have hpair' : (∑ i : Fin (2 * m), ∑ j : Fin (2 * m),
      if i = j then (0 : ℝ) else if i.val < m ↔ j.val < m then 0 else 1)
      = 2 * (m : ℝ) * (m : ℝ) := by
    simpa using hpair
  have hsum : (∑ i : Fin (2 * m), ∑ j : Fin (2 * m),
      (if decide (i.val < m) ≠ decide (j.val < m) then (1 : ℝ) else 0))
      = 2 * (m : ℝ) * (m : ℝ) := by
    rw [← hpair']
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j <;> by_cases hsame : i.val < m ↔ j.val < m <;>
      simp [hij, hsame]
  have hreal : ((crossPairs m).card : ℝ) = 2 * (m : ℝ) * (m : ℝ) := by
    have hcard : ((crossPairs m).card : ℝ) = ∑ p ∈ crossPairs m, (1 : ℝ) := by simp
    rw [hcard, crossPairs, Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
    simpa [decide_eq_decide, eq_comm] using hsum
  apply Nat.cast_injective (R := ℝ)
  rw [hreal]
  norm_num

/-- **Master trace decomposition.** For block-constant `M = G(d,w,c)` and symmetric
`X`, the trace splits into the diagonal, within, and cross sums. -/
lemma trace_blockConstMat_mul (m : ℕ) (d w c : ℝ)
    (X : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) (hSymm : ∀ i j, X i j = X j i) :
    Matrix.trace (blockConstMat m d w c * X)
      = d * (∑ i, X i i) + w * Ssame m X + c * Scross m X := by
  have htrace : Matrix.trace (blockConstMat m d w c * X)
      = ∑ i : Fin (2 * m), ∑ j : Fin (2 * m),
        (if i = j then d else if decide (i.val < m) = decide (j.val < m) then w else c) *
          X i j := by
    simp [Matrix.trace, Matrix.mul_apply, blockConstMat]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hSymm j i]
  have hdiag : (∑ i : Fin (2 * m), ∑ j : Fin (2 * m), if i = j then d * X i j else 0)
      = d * (∑ i, X i i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have hij : i ≠ j := fun h => hji h.symm
      simp [hij]
    · intro hi
      simp at hi
  have hsame : (∑ i : Fin (2 * m), ∑ j : Fin (2 * m),
      if i ≠ j ∧ decide (i.val < m) = decide (j.val < m) then w * X i j else 0)
      = w * Ssame m X := by
    unfold Ssame sameOffPairs
    rw [Finset.mul_sum]
    rw [Finset.sum_filter]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have hcross : (∑ i : Fin (2 * m), ∑ j : Fin (2 * m),
      if decide (i.val < m) ≠ decide (j.val < m) then c * X i j else 0)
      = c * Scross m X := by
    unfold Scross crossPairs
    rw [Finset.mul_sum]
    rw [Finset.sum_filter]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [htrace]
  calc
    (∑ i : Fin (2 * m), ∑ j : Fin (2 * m),
        (if i = j then d else if decide (i.val < m) = decide (j.val < m) then w else c) *
          X i j)
        = (∑ i : Fin (2 * m), ∑ j : Fin (2 * m), if i = j then d * X i j else 0)
          + (∑ i : Fin (2 * m), ∑ j : Fin (2 * m),
              if i ≠ j ∧ decide (i.val < m) = decide (j.val < m) then w * X i j else 0)
          + (∑ i : Fin (2 * m), ∑ j : Fin (2 * m),
              if decide (i.val < m) ≠ decide (j.val < m) then c * X i j else 0) := by
            simp_rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            by_cases hij : i = j <;>
              by_cases hsame : decide (i.val < m) = decide (j.val < m) <;>
              simp [hij, hsame]
    _ = d * (∑ i, X i i) + w * Ssame m X + c * Scross m X := by
          rw [hdiag, hsame, hcross]

/-- `Ssame` of a block-symmetric matrix `X(u',v')` is `Nsame · u'`. -/
lemma Ssame_blockSym (m : ℕ) (u v : ℝ) :
    Ssame m (blockSymMatrix m u v) = NsameR m * u := by
  unfold Ssame
  calc
    (∑ p ∈ sameOffPairs m, blockSymMatrix m u v p.1 p.2)
        = ∑ p ∈ sameOffPairs m, u := by
          apply Finset.sum_congr rfl
          intro p hp
          simp only [sameOffPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          have hsame : p.1.val < m ↔ p.2.val < m := by
            simpa [decide_eq_decide] using hp.2
          simp [blockSymMatrix, hp.1, hsame]
    _ = NsameR m * u := by
          rw [Finset.sum_const, nsmul_eq_mul, card_sameOffPairs]
          unfold NsameR
          cases m <;> simp

/-- `Scross` of a block-symmetric matrix `X(u',v')` is `Ncross · v'`. -/
lemma Scross_blockSym (m : ℕ) (u v : ℝ) :
    Scross m (blockSymMatrix m u v) = NcrossR m * v := by
  unfold Scross
  calc
    (∑ p ∈ crossPairs m, blockSymMatrix m u v p.1 p.2)
        = ∑ p ∈ crossPairs m, v := by
          apply Finset.sum_congr rfl
          intro p hp
          simp only [crossPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          have hne : p.1 ≠ p.2 := by
            intro h
            exact hp (by simp [h])
          have hcross : ¬ (p.1.val < m ↔ p.2.val < m) := by
            intro hsame
            exact hp (by simp [hsame])
          simp [blockSymMatrix, hne, hcross]
    _ = NcrossR m * v := by
          rw [Finset.sum_const, nsmul_eq_mul, card_crossPairs]
          unfold NcrossR
          norm_num

/-- Diagonal sum of a unit-diagonal matrix is `2m`. -/
lemma diagSum_of_diag_one (m : ℕ) (X : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
    (hdiag : ∀ i, X i i = 1) : (∑ i, X i i) = 2 * (m : ℝ) := by
  simp [hdiag]

/-- **Trace preservation.** For block-constant `M` and symmetric unit-diagonal `X`,
symmetrizing to the block averages preserves the trace `Tr(M X)`. -/
lemma trace_symmetrize (m : ℕ) (d w c : ℝ)
    (X : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) (hSymm : ∀ i j, X i j = X j i)
    (hdiag : ∀ i, X i i = 1) (hm : 2 ≤ m) :
    Matrix.trace (blockConstMat m d w c * X)
      = Matrix.trace (blockConstMat m d w c * blockSymMatrix m (uOf m X) (vOf m X)) := by
  have hblockSymm : ∀ i j,
      blockSymMatrix m (uOf m X) (vOf m X) i j =
        blockSymMatrix m (uOf m X) (vOf m X) j i := by
    intro i j
    simpa [blockSymMatrix_eq_blockConst] using blockConstMat_symm m 1 (uOf m X) (vOf m X) i j
  have hblockDiag : ∀ i, blockSymMatrix m (uOf m X) (vOf m X) i i = 1 := by
    intro i
    simp [blockSymMatrix]
  have hNsame : NsameR m ≠ 0 := by
    unfold NsameR
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
    have hmgt1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hm)
    exact ne_of_gt (mul_pos (mul_pos (by norm_num) hmpos) (by linarith))
  have hNcross : NcrossR m ≠ 0 := by
    unfold NcrossR
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
    positivity
  rw [trace_blockConstMat_mul m d w c X hSymm,
    trace_blockConstMat_mul m d w c (blockSymMatrix m (uOf m X) (vOf m X)) hblockSymm]
  rw [diagSum_of_diag_one m X hdiag, diagSum_of_diag_one m _ hblockDiag]
  rw [Ssame_blockSym, Scross_blockSym]
  unfold uOf vOf
  field_simp [hNsame, hNcross]

/-- `twoBlockLaplacian` is block-constant. -/
lemma twoBlockLaplacian_isBlockConst (m : ℕ) (a b : ℝ) (hm : 2 ≤ m) :
    ∃ d w c, twoBlockLaplacian m a b = blockConstMat m d w c := by
  let deg : ℝ := ((m : ℝ) - 1) * (a / (m : ℝ)) + (m : ℝ) * (b / (m : ℝ))
  have hcast_m_sub_one : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have hm1 : 1 ≤ m := by omega
    rw [Nat.cast_sub hm1]
    norm_num
  have hDegree : ∀ i : Fin (2 * m),
      (∑ j : Fin (2 * m), twoBlockGraph m a b i j) = deg := by
    intro i
    let A := blockAFin m
    let B := blockBFin m
    by_cases hi : i.val < m
    · have hsplit : (∑ j : Fin (2 * m), twoBlockGraph m a b i j)
          = (∑ j ∈ A, twoBlockGraph m a b i j)
            + (∑ j ∈ B, twoBlockGraph m a b i j) := by
        dsimp [A, B, blockAFin, blockBFin]
        rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
          (p := fun j : Fin (2 * m) => j.val < m)
          (f := fun j => twoBlockGraph m a b i j)]
      rw [hsplit]
      have hA : (∑ j ∈ A, twoBlockGraph m a b i j)
          = ((m - 1 : ℕ) : ℝ) * (a / (m : ℝ)) := by
        have hiA : i ∈ A := by simpa [A, blockAFin] using hi
        have hAcard : A.card = m := by dsimp [A]; exact card_blockAFin m
        calc
          (∑ j ∈ A, twoBlockGraph m a b i j)
              = ∑ j ∈ A, if i = j then 0 else a / (m : ℝ) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  have hj' : j.val < m := by simpa [A, blockAFin] using hj
                  by_cases hij : i = j <;> simp [twoBlockGraph, hij, hi, hj']
          _ = 0 + ((A.card - 1 : ℕ) : ℝ) * (a / (m : ℝ)) :=
              sum_if_eq_else_self_real A 0 (a / (m : ℝ)) hiA
          _ = ((m - 1 : ℕ) : ℝ) * (a / (m : ℝ)) := by
              rw [hAcard]
              ring
      have hB : (∑ j ∈ B, twoBlockGraph m a b i j)
          = (m : ℝ) * (b / (m : ℝ)) := by
        have hBcard : B.card = m := by dsimp [B]; exact card_blockBFin m
        calc
          (∑ j ∈ B, twoBlockGraph m a b i j)
              = ∑ j ∈ B, b / (m : ℝ) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  have hj' : ¬ j.val < m := by simpa [B, blockBFin] using hj
                  have hne : i ≠ j := by
                    intro h
                    exact hj' (by simpa [h] using hi)
                  have hnot : ¬ (i.val < m ↔ j.val < m) := by
                    intro hiff
                    exact hj' (hiff.mp hi)
                  simp [twoBlockGraph, hne, hnot]
          _ = (m : ℝ) * (b / (m : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul, hBcard]
      rw [hA, hB, hcast_m_sub_one]
    · have hsplit : (∑ j : Fin (2 * m), twoBlockGraph m a b i j)
          = (∑ j ∈ A, twoBlockGraph m a b i j)
            + (∑ j ∈ B, twoBlockGraph m a b i j) := by
        dsimp [A, B, blockAFin, blockBFin]
        rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
          (p := fun j : Fin (2 * m) => j.val < m)
          (f := fun j => twoBlockGraph m a b i j)]
      rw [hsplit]
      have hA : (∑ j ∈ A, twoBlockGraph m a b i j)
          = (m : ℝ) * (b / (m : ℝ)) := by
        have hAcard : A.card = m := by dsimp [A]; exact card_blockAFin m
        calc
          (∑ j ∈ A, twoBlockGraph m a b i j)
              = ∑ j ∈ A, b / (m : ℝ) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  have hj' : j.val < m := by simpa [A, blockAFin] using hj
                  have hne : i ≠ j := by
                    intro h
                    exact hi (by simpa [h] using hj')
                  have hnot : ¬ (i.val < m ↔ j.val < m) := by
                    intro hiff
                    exact hi (hiff.mpr hj')
                  simp [twoBlockGraph, hne, hnot]
          _ = (m : ℝ) * (b / (m : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul, hAcard]
      have hB : (∑ j ∈ B, twoBlockGraph m a b i j)
          = ((m - 1 : ℕ) : ℝ) * (a / (m : ℝ)) := by
        have hiB : i ∈ B := by simpa [B, blockBFin] using hi
        have hBcard : B.card = m := by dsimp [B]; exact card_blockBFin m
        calc
          (∑ j ∈ B, twoBlockGraph m a b i j)
              = ∑ j ∈ B, if i = j then 0 else a / (m : ℝ) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  have hj' : ¬ j.val < m := by simpa [B, blockBFin] using hj
                  by_cases hij : i = j <;> simp [twoBlockGraph, hij, hi, hj']
          _ = 0 + ((B.card - 1 : ℕ) : ℝ) * (a / (m : ℝ)) :=
              sum_if_eq_else_self_real B 0 (a / (m : ℝ)) hiB
          _ = ((m - 1 : ℕ) : ℝ) * (a / (m : ℝ)) := by
              rw [hBcard]
              ring
      rw [hA, hB, hcast_m_sub_one]
      ring
  refine ⟨deg, -(a / (m : ℝ)), -(b / (m : ℝ)), ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    simp [twoBlockLaplacian, blockConstMat, hDegree]
  · by_cases hsame : i.val < m ↔ j.val < m
    · have hsameDec : decide (i.val < m) = decide (j.val < m) := by
        simp [decide_eq_decide, hsame]
      simp [twoBlockLaplacian, twoBlockGraph, blockConstMat, hij, hsame, hsameDec]
    · have hsameDec : decide (i.val < m) ≠ decide (j.val < m) := by
        intro h
        exact hsame (by simpa [decide_eq_decide] using h)
      simp [twoBlockLaplacian, twoBlockGraph, blockConstMat, hij, hsame, hsameDec]

/-- `twoBlockLaplacianPinv` is block-constant. -/
lemma twoBlockLaplacianPinv_isBlockConst (m : ℕ) (a b : ℝ) (hm : 2 ≤ m) :
    ∃ d w c, twoBlockLaplacianPinv m a b = blockConstMat m d w c := by
  refine ⟨(1 / (a + b)) * (1 - 1 / (2 * (m : ℝ)) - 1 / (2 * (m : ℝ)))
      + (1 / (2 * b)) * (1 / (2 * (m : ℝ))),
    (1 / (a + b)) * (0 - 1 / (2 * (m : ℝ)) - 1 / (2 * (m : ℝ)))
      + (1 / (2 * b)) * (1 / (2 * (m : ℝ))),
    (1 / (a + b)) * (0 - 1 / (2 * (m : ℝ)) - (-1 / (2 * (m : ℝ))))
      + (1 / (2 * b)) * (-1 / (2 * (m : ℝ))), ?_⟩
  ext i j
  by_cases hi : i.val < m <;> by_cases hj : j.val < m <;> by_cases hij : i = j <;>
    simp [twoBlockLaplacianPinv, blockConstMat, onesProj, signProj, signVec,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hi, hj, hij]

/-- `allOnesMatrix` is block-constant `G(1,1,1)`. -/
lemma allOnesMatrix_isBlockConst (m : ℕ) :
    allOnesMatrix m = blockConstMat m 1 1 1 := by
  ext i j
  by_cases hij : i = j <;> by_cases hsame : decide (i.val < m) = decide (j.val < m) <;>
    simp [allOnesMatrix, blockConstMat, hij, hsame]

/-- **Frobenius drop.** Symmetrizing weakly decreases the Frobenius norm. -/
lemma frobeniusNorm_symmetrize_le (m : ℕ) (hm : 2 ≤ m)
    (X : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) (hSymm : ∀ i j, X i j = X j i)
    (hdiag : ∀ i, X i i = 1) :
    frobeniusNorm (blockSymMatrix m (uOf m X) (vOf m X)) ≤ frobeniusNorm X := by
  let X2 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ := Matrix.of fun i j => (X i j) ^ 2
  have hX2symm : ∀ i j, X2 i j = X2 j i := by
    intro i j
    simp [X2, hSymm i j]
  have hradX : (∑ i : Fin (2 * m), ∑ j : Fin (2 * m), (X i j) ^ 2)
      = 2 * (m : ℝ) + Ssame m X2 + Scross m X2 := by
    have ht := trace_blockConstMat_mul m 1 1 1 X2 hX2symm
    have hleft : Matrix.trace (blockConstMat m 1 1 1 * X2)
        = ∑ i : Fin (2 * m), ∑ j : Fin (2 * m), X2 i j := by
      simp [Matrix.trace, Matrix.mul_apply, blockConstMat]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hX2symm j i]
    have hdiag2 : (∑ i : Fin (2 * m), X2 i i) = 2 * (m : ℝ) := by
      simp [X2, hdiag]
    rw [hleft] at ht
    rw [hdiag2] at ht
    simpa [X2, one_mul] using ht
  have hradY : (∑ i : Fin (2 * m), ∑ j : Fin (2 * m),
        (blockSymMatrix m (uOf m X) (vOf m X) i j) ^ 2)
      = 2 * (m : ℝ) + NsameR m * (uOf m X) ^ 2 + NcrossR m * (vOf m X) ^ 2 := by
    simp [blockSymMatrix]
    have h' := block_pair_sum m (1 : ℝ) ((uOf m X) ^ 2) ((vOf m X) ^ 2)
    rw [h']
    unfold NsameR NcrossR
    ring
  have hNsamePos : 0 < NsameR m := by
    unfold NsameR
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
    have hmgt1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hm)
    exact mul_pos (mul_pos (by norm_num) hmpos) (by linarith)
  have hNcrossPos : 0 < NcrossR m := by
    unfold NcrossR
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
    exact mul_pos (mul_pos (by norm_num) hmpos) hmpos
  have hcardSameR : ((sameOffPairs m).card : ℝ) = NsameR m := by
    rw [card_sameOffPairs]
    unfold NsameR
    cases m <;> simp
  have hcardCrossR : ((crossPairs m).card : ℝ) = NcrossR m := by
    rw [card_crossPairs]
    unfold NcrossR
    norm_num
  have hsameAvg : NsameR m * (uOf m X) ^ 2 ≤ Ssame m X2 := by
    have hc := sq_sum_le_card_mul_sum_sq (s := sameOffPairs m) (f := fun p => X p.1 p.2)
    have hc' : (Ssame m X) ^ 2 ≤ NsameR m * Ssame m X2 := by
      simpa [Ssame, X2, hcardSameR] using hc
    unfold uOf
    have hNne : NsameR m ≠ 0 := ne_of_gt hNsamePos
    rw [show NsameR m * (Ssame m X / NsameR m) ^ 2 = (Ssame m X) ^ 2 / NsameR m by
      field_simp [hNne]]
    exact (div_le_iff₀ hNsamePos).mpr (by simpa [mul_comm] using hc')
  have hcrossAvg : NcrossR m * (vOf m X) ^ 2 ≤ Scross m X2 := by
    have hc := sq_sum_le_card_mul_sum_sq (s := crossPairs m) (f := fun p => X p.1 p.2)
    have hc' : (Scross m X) ^ 2 ≤ NcrossR m * Scross m X2 := by
      simpa [Scross, X2, hcardCrossR] using hc
    unfold vOf
    have hNne : NcrossR m ≠ 0 := ne_of_gt hNcrossPos
    rw [show NcrossR m * (Scross m X / NcrossR m) ^ 2 = (Scross m X) ^ 2 / NcrossR m by
      field_simp [hNne]]
    exact (div_le_iff₀ hNcrossPos).mpr (by simpa [mul_comm] using hc')
  unfold frobeniusNorm
  apply Real.sqrt_le_sqrt
  rw [hradY, hradX]
  nlinarith [hsameAvg, hcrossAvg]

/-- **Unified objective comparison.** If `Y` matches `X` on the block sums and has no
larger Frobenius norm, then `Y` has no larger objective.  Both the matrix-side and the
design-side symmetrizations feed through this lemma. -/
lemma designObjective_le_of_blockSums (m : ℕ) (a b r kappa : ℝ)
    (hHom : TwoBlockHomophily m a b) (hk : 0 ≤ kappa)
    (X Y : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
    (hXsym : ∀ i j, X i j = X j i) (hYsym : ∀ i j, Y i j = Y j i)
    (hXdiag : ∀ i, X i i = 1) (hYdiag : ∀ i, Y i i = 1)
    (hSs : Ssame m Y = Ssame m X) (hSc : Scross m Y = Scross m X)
    (hFrob : frobeniusNorm Y ≤ frobeniusNorm X) :
    designObjective m a b r kappa Y ≤ designObjective m a b r kappa X := by
  have hm : 2 ≤ m := hHom.1
  have hTraceEq_of_block : ∀ M : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ,
      (∃ d w c, M = blockConstMat m d w c) →
      Matrix.trace (M * Y) = Matrix.trace (M * X) := by
    intro M hM
    rcases hM with ⟨d, w, c, rfl⟩
    rw [trace_blockConstMat_mul m d w c Y hYsym, trace_blockConstMat_mul m d w c X hXsym]
    rw [diagSum_of_diag_one m Y hYdiag, diagSum_of_diag_one m X hXdiag, hSs, hSc]
  have hL := hTraceEq_of_block (twoBlockLaplacian m a b) (twoBlockLaplacian_isBlockConst m a b hm)
  have hPinv :=
    hTraceEq_of_block (twoBlockLaplacianPinv m a b) (twoBlockLaplacianPinv_isBlockConst m a b hm)
  have hJ := hTraceEq_of_block (allOnesMatrix m) ⟨1, 1, 1, allOnesMatrix_isBlockConst m⟩
  have hF : kappa * frobeniusNorm Y ≤ kappa * frobeniusNorm X :=
    mul_le_mul_of_nonneg_left hFrob hk
  unfold designObjective
  rw [hL, hPinv, hJ]
  nlinarith

/-- Off-diagonal entries of a PSD unit-diagonal matrix are bounded by `1`. -/
lemma abs_entry_le_one (m : ℕ) (X : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
    (hpsd : X.PosSemidef) (hdiag : ∀ i, X i i = 1) (i j : Fin (2 * m)) :
    |X i j| ≤ 1 := by
  by_cases hij : i = j
  · subst j
    simp [hdiag]
  · have hsym : X j i = X i j := by
      have h := hpsd.1.apply i j
      simpa using h
    let vm : Fin (2 * m) → ℝ := Pi.single i 1 - Pi.single j 1
    have hmnonneg := hpsd.dotProduct_mulVec_nonneg vm
    have hmnonneg' : 0 ≤ vm ⬝ᵥ X.mulVec vm := by
      simpa using hmnonneg
    have hmcalc : vm ⬝ᵥ X.mulVec vm = 2 - 2 * X i j := by
      classical
      calc
        vm ⬝ᵥ X.mulVec vm = X i i - X i j - X j i + X j j := by
          simp only [vm]
          rw [Matrix.mulVec_sub]
          rw [dotProduct_sub, sub_dotProduct]
          simp [Matrix.mulVec_single, single_dotProduct]
          ring
        _ = 2 - 2 * X i j := by
          simp [hdiag, hsym]
          ring
    have hle : X i j ≤ 1 := by
      nlinarith [hmnonneg', hmcalc]
    let vp : Fin (2 * m) → ℝ := Pi.single i 1 + Pi.single j 1
    have hpnonneg := hpsd.dotProduct_mulVec_nonneg vp
    have hpnonneg' : 0 ≤ vp ⬝ᵥ X.mulVec vp := by
      simpa using hpnonneg
    have hpcalc : vp ⬝ᵥ X.mulVec vp = 2 + 2 * X i j := by
      classical
      calc
        vp ⬝ᵥ X.mulVec vp = X i i + X i j + X j i + X j j := by
          simp only [vp]
          rw [Matrix.mulVec_add]
          rw [dotProduct_add, add_dotProduct]
          simp [Matrix.mulVec_single, single_dotProduct]
          ring
        _ = 2 + 2 * X i j := by
          simp [hdiag, hsym]
          ring
    have hge : -1 ≤ X i j := by
      nlinarith [hpnonneg', hpcalc]
    exact abs_le.mpr ⟨hge, hle⟩

/-- **Objective bounded below on the elliptope.** -/
lemma designObjective_bddBelow (m : ℕ) (a b r kappa : ℝ)
    (hHom : TwoBlockHomophily m a b) (hk : 0 ≤ kappa) :
    BddBelow (designObjective m a b r kappa ''
      { X : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ | X.PosSemidef ∧ ∀ i, X i i = 1 }) := by
  have hm : 2 ≤ m := hHom.1
  rcases twoBlockLaplacian_isBlockConst m a b hm with ⟨dL, wL, cL, hLmat⟩
  rcases twoBlockLaplacianPinv_isBlockConst m a b hm with ⟨dP, wP, cP, hPmat⟩
  let BL : ℝ := |dL| * (2 * (m : ℝ)) + |wL| * NsameR m + |cL| * NcrossR m
  let BP : ℝ := |dP| * (2 * (m : ℝ)) + |wP| * NsameR m + |cP| * NcrossR m
  let BJ : ℝ := (1 : ℝ) * (2 * (m : ℝ)) + (1 : ℝ) * NsameR m + (1 : ℝ) * NcrossR m
  refine ⟨-(BL + |r| * BP + BJ), ?_⟩
  rintro y ⟨X, hX, rfl⟩
  rcases hX with ⟨hpsd, hdiag⟩
  have hSymm : ∀ i j, X i j = X j i := by
    intro i j
    have h := hpsd.1.apply j i
    simpa using h
  have hcardSameR : ((sameOffPairs m).card : ℝ) = NsameR m := by
    rw [card_sameOffPairs]
    unfold NsameR
    cases m <;> simp
  have hcardCrossR : ((crossPairs m).card : ℝ) = NcrossR m := by
    rw [card_crossPairs]
    unfold NcrossR
    norm_num
  have hAbsSame : |Ssame m X| ≤ NsameR m := by
    calc
      |Ssame m X| = |∑ p ∈ sameOffPairs m, X p.1 p.2| := rfl
      _ ≤ ∑ p ∈ sameOffPairs m, |X p.1 p.2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ sameOffPairs m, (1 : ℝ) := by
        gcongr with p hp
        exact abs_entry_le_one m X hpsd hdiag p.1 p.2
      _ = NsameR m := by
        rw [Finset.sum_const, nsmul_eq_mul, hcardSameR]
        ring
  have hAbsCross : |Scross m X| ≤ NcrossR m := by
    calc
      |Scross m X| = |∑ p ∈ crossPairs m, X p.1 p.2| := rfl
      _ ≤ ∑ p ∈ crossPairs m, |X p.1 p.2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ crossPairs m, (1 : ℝ) := by
        gcongr with p hp
        exact abs_entry_le_one m X hpsd hdiag p.1 p.2
      _ = NcrossR m := by
        rw [Finset.sum_const, nsmul_eq_mul, hcardCrossR]
        ring
  have hTraceAbs : ∀ d w c : ℝ,
      |Matrix.trace (blockConstMat m d w c * X)| ≤
        |d| * (2 * (m : ℝ)) + |w| * NsameR m + |c| * NcrossR m := by
    intro d w c
    rw [trace_blockConstMat_mul m d w c X hSymm, diagSum_of_diag_one m X hdiag]
    calc
      |d * (2 * (m : ℝ)) + w * Ssame m X + c * Scross m X|
          ≤ |d * (2 * (m : ℝ))| + |w * Ssame m X| + |c * Scross m X| := by
            calc
              |d * (2 * (m : ℝ)) + w * Ssame m X + c * Scross m X|
                  ≤ |d * (2 * (m : ℝ)) + w * Ssame m X| + |c * Scross m X| :=
                    abs_add_le _ _
              _ ≤ |d * (2 * (m : ℝ))| + |w * Ssame m X| + |c * Scross m X| := by
                    nlinarith [abs_add_le (d * (2 * (m : ℝ))) (w * Ssame m X)]
      _ = |d| * |2 * (m : ℝ)| + |w| * |Ssame m X| + |c| * |Scross m X| := by
            rw [abs_mul (d) (2 * (m : ℝ)), abs_mul (w) (Ssame m X),
              abs_mul (c) (Scross m X)]
      _ ≤ |d| * (2 * (m : ℝ)) + |w| * NsameR m + |c| * NcrossR m := by
        have htwononneg : 0 ≤ 2 * (m : ℝ) := by positivity
        rw [abs_of_nonneg htwononneg]
        gcongr
  have hLAbs : |Matrix.trace (twoBlockLaplacian m a b * X)| ≤ BL := by
    rw [hLmat]
    exact hTraceAbs dL wL cL
  have hPAbs : |Matrix.trace (twoBlockLaplacianPinv m a b * X)| ≤ BP := by
    rw [hPmat]
    exact hTraceAbs dP wP cP
  have hJAbs : |Matrix.trace (allOnesMatrix m * X)| ≤ BJ := by
    rw [allOnesMatrix_isBlockConst]
    simpa [BJ] using hTraceAbs 1 1 1
  have hLlower : -BL ≤ Matrix.trace (twoBlockLaplacian m a b * X) := (abs_le.mp hLAbs).1
  have hPlower : -(|r| * BP) ≤ r * Matrix.trace (twoBlockLaplacianPinv m a b * X) := by
    have hmulAbs : |r * Matrix.trace (twoBlockLaplacianPinv m a b * X)| ≤ |r| * BP := by
      rw [abs_mul]
      gcongr
    exact (abs_le.mp hmulAbs).1
  have hJlower : -BJ ≤ Matrix.trace (allOnesMatrix m * X) := (abs_le.mp hJAbs).1
  have hFrobNonneg : 0 ≤ kappa * frobeniusNorm X := by
    unfold frobeniusNorm
    exact mul_nonneg hk (Real.sqrt_nonneg _)
  unfold designObjective
  nlinarith

/-- **Generic `sInf` reduction.** If `T ⊆ S`, `T` is nonempty, `f '' S` is bounded
below, and every point of `S` is dominated by some point of `T`, then the two infima
of `f` over `S` and `T` coincide. -/
lemma sInf_image_reduce {α : Type*} (f : α → ℝ) (S T : Set α)
    (hTS : T ⊆ S) (hTne : T.Nonempty) (hbdd : BddBelow (f '' S))
    (hreduce : ∀ x ∈ S, ∃ y ∈ T, f y ≤ f x) :
    sInf (f '' S) = sInf (f '' T) := by
  have hSne : S.Nonempty := hTne.mono hTS
  have hTbdd : BddBelow (f '' T) := hbdd.mono (Set.image_mono hTS)
  apply le_antisymm
  · exact csInf_le_csInf hbdd (hTne.image f) (Set.image_mono hTS)
  · refine le_csInf (hSne.image f) ?_
    intro z hz
    rcases hz with ⟨x, hxS, rfl⟩
    rcases hreduce x hxS with ⟨y, hyT, hle⟩
    exact le_trans (csInf_le hTbdd ⟨y, hyT, rfl⟩) hle

/-- **Membership.** The block averages of a PSD unit-diagonal `X` land in `E_m^blk`. -/
lemma blockElliptopeMem_symmetrize (m : ℕ) (a b : ℝ)
    (hHom : TwoBlockHomophily m a b)
    (X : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) (hpsd : X.PosSemidef)
    (hdiag : ∀ i, X i i = 1) :
    BlockElliptopeMem m a b (uOf m X) (vOf m X) := by
  have hm : 2 ≤ m := hHom.1
  have hSymm : ∀ i j, X i j = X j i := by
    intro i j
    have h := hpsd.1.apply j i
    simpa using h
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
  have htwompos : 0 < 2 * (m : ℝ) := by positivity
  have hNsamePos : 0 < NsameR m := by
    unfold NsameR
    have hmgt1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hm)
    exact mul_pos (mul_pos (by norm_num) hmpos) (by linarith)
  have hNcrossPos : 0 < NcrossR m := by
    unfold NcrossR
    exact mul_pos (mul_pos (by norm_num) hmpos) hmpos
  have hcardSameR : ((sameOffPairs m).card : ℝ) = NsameR m := by
    rw [card_sameOffPairs]
    unfold NsameR
    cases m <;> simp
  have hNsame_u : NsameR m * uOf m X = Ssame m X := by
    unfold uOf
    field_simp [ne_of_gt hNsamePos]
  have hNcross_v : NcrossR m * vOf m X = Scross m X := by
    unfold vOf
    field_simp [ne_of_gt hNcrossPos]
  refine ⟨hHom, ?_, ?_, ?_⟩
  · have hentry : ∀ p ∈ sameOffPairs m, X p.1 p.2 ≤ 1 := by
      intro p hp
      exact (abs_le.mp (abs_entry_le_one m X hpsd hdiag p.1 p.2)).2
    have hSle : Ssame m X ≤ NsameR m := by
      calc
        Ssame m X = ∑ p ∈ sameOffPairs m, X p.1 p.2 := rfl
        _ ≤ ∑ p ∈ sameOffPairs m, (1 : ℝ) := by
          gcongr with p hp
          exact hentry p hp
        _ = NsameR m := by
          rw [Finset.sum_const, nsmul_eq_mul, hcardSameR]
          ring
    have hu : uOf m X ≤ 1 := by
      unfold uOf
      exact (div_le_iff₀ hNsamePos).mpr (by simpa using hSle)
    linarith
  · let sv : Fin (2 * m) → ℝ := signVec m
    have hnonneg := hpsd.dotProduct_mulVec_nonneg sv
    have hnonneg' : 0 ≤ sv ⬝ᵥ X.mulVec sv := by
      simpa using hnonneg
    have hquad : sv ⬝ᵥ X.mulVec sv
        = 2 * (m : ℝ) + Ssame m X - Scross m X := by
      have htrace := trace_blockConstMat_mul m 1 1 (-1) X hSymm
      have hleft : Matrix.trace (blockConstMat m 1 1 (-1) * X)
          = sv ⬝ᵥ X.mulVec sv := by
        simp [Matrix.trace, Matrix.mul_apply, dotProduct, Matrix.mulVec,
          blockConstMat, sv, signVec]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i.val < m
        · simp [hi]
          apply Finset.sum_congr rfl
          intro j _
          rw [hSymm j i]
          by_cases hij : i = j
          · subst j
            simp [hi]
          · by_cases hj : j.val < m <;> simp [hi, hj, hij]
        · simp [hi]
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro j _
          rw [hSymm j i]
          by_cases hij : i = j
          · subst j
            simp [hi]
          · by_cases hj : j.val < m <;> simp [hi, hj, hij]
      have hdiagSum := diagSum_of_diag_one m X hdiag
      rw [hleft] at htrace
      rw [hdiagSum] at htrace
      linarith
    have hyprod : 0 ≤ 2 * (m : ℝ) *
        (1 + ((m : ℝ) - 1) * uOf m X - (m : ℝ) * vOf m X) := by
      rw [show 2 * (m : ℝ) * (1 + ((m : ℝ) - 1) * uOf m X - (m : ℝ) * vOf m X)
          = 2 * (m : ℝ) + NsameR m * uOf m X - NcrossR m * vOf m X by
            unfold NsameR NcrossR
            ring]
      rw [hNsame_u, hNcross_v]
      simpa [hquad] using hnonneg'
    have hyprod' : 0 ≤
        (1 + ((m : ℝ) - 1) * uOf m X - (m : ℝ) * vOf m X) * (2 * (m : ℝ)) := by
      simpa [mul_comm] using hyprod
    exact nonneg_of_mul_nonneg_left hyprod' htwompos
  · let ov : Fin (2 * m) → ℝ := fun _ => 1
    have hnonneg := hpsd.dotProduct_mulVec_nonneg ov
    have hnonneg' : 0 ≤ ov ⬝ᵥ X.mulVec ov := by
      simpa using hnonneg
    have hquad : ov ⬝ᵥ X.mulVec ov
        = 2 * (m : ℝ) + Ssame m X + Scross m X := by
      have htrace := trace_blockConstMat_mul m 1 1 1 X hSymm
      have hleft : Matrix.trace (blockConstMat m 1 1 1 * X)
          = ov ⬝ᵥ X.mulVec ov := by
        simp [Matrix.trace, Matrix.mul_apply, dotProduct, Matrix.mulVec,
          blockConstMat, ov]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hSymm j i]
      have hdiagSum := diagSum_of_diag_one m X hdiag
      rw [hleft] at htrace
      rw [hdiagSum] at htrace
      linarith
    have hzprod : 0 ≤ 2 * (m : ℝ) *
        (1 + ((m : ℝ) - 1) * uOf m X + (m : ℝ) * vOf m X) := by
      rw [show 2 * (m : ℝ) * (1 + ((m : ℝ) - 1) * uOf m X + (m : ℝ) * vOf m X)
          = 2 * (m : ℝ) + NsameR m * uOf m X + NcrossR m * vOf m X by
            unfold NsameR NcrossR
            ring]
      rw [hNsame_u, hNcross_v]
      simpa [hquad] using hnonneg'
    have hzprod' : 0 ≤
        (1 + ((m : ℝ) - 1) * uOf m X + (m : ℝ) * vOf m X) * (2 * (m : ℝ)) := by
      simpa [mul_comm] using hzprod
    exact nonneg_of_mul_nonneg_left hzprod' htwompos

/-- **Matrix-side symmetry reduction (master export).** For PSD unit-diagonal `X`,
the block-average point `X(uOf X, vOf X)` is an elliptope point with weakly smaller
objective. -/
lemma symmetrize_objective_le (m : ℕ) (a b r kappa : ℝ)
    (hHom : TwoBlockHomophily m a b) (hk : 0 ≤ kappa)
    (X : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) (hpsd : X.PosSemidef)
    (hdiag : ∀ i, X i i = 1) :
    BlockElliptopeMem m a b (uOf m X) (vOf m X) ∧
    designObjective m a b r kappa (blockSymMatrix m (uOf m X) (vOf m X))
      ≤ designObjective m a b r kappa X := by
  have hm : 2 ≤ m := hHom.1
  have hSymm : ∀ i j, X i j = X j i := by
    intro i j
    have h := hpsd.1.apply j i
    simpa using h
  have hblockSymm : ∀ i j,
      blockSymMatrix m (uOf m X) (vOf m X) i j =
        blockSymMatrix m (uOf m X) (vOf m X) j i := by
    intro i j
    simpa [blockSymMatrix_eq_blockConst] using blockConstMat_symm m 1 (uOf m X) (vOf m X) i j
  have hblockDiag : ∀ i, blockSymMatrix m (uOf m X) (vOf m X) i i = 1 := by
    intro i
    simp [blockSymMatrix]
  have hNsamePos : 0 < NsameR m := by
    unfold NsameR
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
    have hmgt1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hm)
    exact mul_pos (mul_pos (by norm_num) hmpos) (by linarith)
  have hNcrossPos : 0 < NcrossR m := by
    unfold NcrossR
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
    exact mul_pos (mul_pos (by norm_num) hmpos) hmpos
  have hSs : Ssame m (blockSymMatrix m (uOf m X) (vOf m X)) = Ssame m X := by
    rw [Ssame_blockSym]
    unfold uOf
    field_simp [ne_of_gt hNsamePos]
  have hSc : Scross m (blockSymMatrix m (uOf m X) (vOf m X)) = Scross m X := by
    rw [Scross_blockSym]
    unfold vOf
    field_simp [ne_of_gt hNcrossPos]
  exact ⟨blockElliptopeMem_symmetrize m a b hHom X hpsd hdiag,
    designObjective_le_of_blockSums m a b r kappa hHom hk X
      (blockSymMatrix m (uOf m X) (vOf m X)) hSymm hblockSymm hdiag hblockDiag
      hSs hSc (frobeniusNorm_symmetrize_le m hm X hSymm hdiag)⟩

end CausalSmith.Experimentation.DesignPm1
