/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.BlockPairSums
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.SpectralMembership
/-! # Block spectral coordinates

The four-way orthogonal eigendecomposition of `ℝⁿ` (`span 1_n`, `span s_m`, the
within-`A` and within-`B` contrast subspaces) reads off the eigenvalues of `X(u,v)`
as `x = 1−u`, `y = 1+(m−1)u−mv`, `z = 1+(m−1)u+mv`, converts elliptope membership
into the reduced triangle, and gives the closed-form objective `φ`. -/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators

/-- The cut covariance is the block-symmetric point `X(1,−1)`, with spectral
coordinates `(0, 2m, 0)`. -/
lemma cutCovariance_eq_blockSym (m : ℕ) :
    cutCovariance m = blockSymMatrix m 1 (-1) := by
  ext i j
  by_cases hi : i.val < m <;> by_cases hj : j.val < m <;>
    by_cases hij : i = j <;>
    simp [cutCovariance, blockSymMatrix, signVec, hi, hj, hij]

/-- The identity `I_n` is the block-symmetric point `X(0,0)`, with spectral
coordinates `(1, 1, 1)`. -/
lemma identity_eq_blockSym (m : ℕ) :
    (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) = blockSymMatrix m 0 0 := by
  ext i j
  by_cases hij : i = j <;> simp [blockSymMatrix, Matrix.one_apply, hij]

-- @node: lem:block-spectral-coordinates
/-- `X(u,v)` lies in `E_m^blk` iff its spectral coordinates lie in the reduced
triangle `T_m`, and the design objective equals the reduced form `φ` with
`c_x = q((a+b)+r/(a+b))`, `c_y = 2b + r/(2b)`, `c_z = 2m` and `q = 2(m−1)`.
The last two conjuncts record the corner coordinate readings the note states:
`X_cut = X(1,−1)` has spectral coordinates `(0, 2m, 0)` and `I_n = X(0,0)` has
spectral coordinates `(1, 1, 1)`. -/
lemma block_spectral_coordinates (m : ℕ) (a b r kappa u v : ℝ)
    (hHom : TwoBlockHomophily m a b) :
    (blockSymMatrix m u v ∈ blockElliptope m a b ↔
      InReducedTriangle m (1 - u) (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
        (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v)) ∧
    designObjective m a b r kappa (blockSymMatrix m u v)
      = reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
          (1 - u) (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
          (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) ∧
    (cutCovariance m = blockSymMatrix m 1 (-1) ∧
      ((1 : ℝ) - 1, 1 + ((m : ℝ) - 1) * 1 - (m : ℝ) * (-1),
          1 + ((m : ℝ) - 1) * 1 + (m : ℝ) * (-1))
        = ((0 : ℝ), 2 * (m : ℝ), (0 : ℝ))) ∧
    ((1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) = blockSymMatrix m 0 0 ∧
      ((1 : ℝ) - 0, 1 + ((m : ℝ) - 1) * 0 - (m : ℝ) * 0,
          1 + ((m : ℝ) - 1) * 0 + (m : ℝ) * 0)
        = ((1 : ℝ), (1 : ℝ), (1 : ℝ))) := by
  have hm2 : 2 ≤ m := hHom.1
  have hmposR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm2)
  have hm0R : (m : ℝ) ≠ 0 := ne_of_gt hmposR
  have hm20R : 2 * (m : ℝ) ≠ 0 := by positivity
  have hcast_m_sub_one : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have hm1 : 1 ≤ m := by omega
    rw [Nat.cast_sub hm1]
    norm_num
  constructor
  · exact blockSymMatrix_mem_blockElliptope_iff_reducedTriangle m a b u v hHom
  · constructor
    · have hJ : Matrix.trace (allOnesMatrix m * blockSymMatrix m u v)
          = 2 * (m : ℝ) * (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) := by
        simp [Matrix.trace, allOnesMatrix, blockSymMatrix, Matrix.mul_apply]
        have h' : (∑ x : Fin (2 * m), ∑ x_1 : Fin (2 * m),
            if x_1 = x then (1 : ℝ) else if (x_1.val < m ↔ x.val < m) then u else v)
            = 2 * (m : ℝ) * 1 + 2 * (m : ℝ) * ((m : ℝ) - 1) * u +
              2 * (m : ℝ) * (m : ℝ) * v := by
          simpa [eq_comm, iff_comm] using block_pair_sum m (1 : ℝ) u v
        rw [h']
        ring
      have hFrob : frobeniusNorm (blockSymMatrix m u v)
          = Real.sqrt (qParam m * (1 - u) ^ 2
              + (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v) ^ 2
              + (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) ^ 2) := by
        unfold frobeniusNorm
        congr 1
        simp [blockSymMatrix]
        have h' : (∑ x : Fin (2 * m), ∑ x_1 : Fin (2 * m),
            if x = x_1 then (1 : ℝ)
            else if (x.val < m ↔ x_1.val < m) then u ^ 2 else v ^ 2)
            = 2 * (m : ℝ) * 1 + 2 * (m : ℝ) * ((m : ℝ) - 1) * (u ^ 2) +
              2 * (m : ℝ) * (m : ℝ) * (v ^ 2) := by
          simpa using block_pair_sum m (1 : ℝ) (u ^ 2) (v ^ 2)
        rw [h']
        unfold qParam
        ring
      have hTraceX : Matrix.trace (blockSymMatrix m u v) = 2 * (m : ℝ) := by
        simp [Matrix.trace, blockSymMatrix]
      have hOnesProj : Matrix.trace (onesProj m * blockSymMatrix m u v)
          = 1 + ((m : ℝ) - 1) * u + (m : ℝ) * v := by
        simp [Matrix.trace, Matrix.mul_apply, onesProj, blockSymMatrix]
        rw [← Finset.mul_sum]
        have h' : (∑ x : Fin (2 * m), ∑ x_1 : Fin (2 * m),
            if x_1 = x then (2 : ℝ)⁻¹
            else if x_1.val < m ↔ x.val < m then 2⁻¹ * u else 2⁻¹ * v)
            = 2 * (m : ℝ) * 2⁻¹
              + 2 * (m : ℝ) * ((m : ℝ) - 1) * (2⁻¹ * u)
              + 2 * (m : ℝ) * (m : ℝ) * (2⁻¹ * v) := by
          simpa [eq_comm, iff_comm] using
            block_pair_sum m ((2 : ℝ)⁻¹) (2⁻¹ * u) (2⁻¹ * v)
        rw [h']
        field_simp [hm0R]
      have hSign : Matrix.trace (signProj m * blockSymMatrix m u v)
          = 1 + ((m : ℝ) - 1) * u - (m : ℝ) * v := by
        simp [Matrix.trace, Matrix.mul_apply, signProj, blockSymMatrix]
        calc
          (∑ x : Fin (2 * m), ∑ x_1 : Fin (2 * m),
              if x_1 = x then signVec m x * signVec m x_1 / (2 * (m : ℝ))
              else if x_1.val < m ↔ x.val < m then
                signVec m x * signVec m x_1 / (2 * (m : ℝ)) * u
              else signVec m x * signVec m x_1 / (2 * (m : ℝ)) * v)
              = (2 * (m : ℝ))⁻¹ *
                  (∑ x : Fin (2 * m), ∑ x_1 : Fin (2 * m),
                    signVec m x * signVec m x_1 *
                      (if x_1 = x then (1 : ℝ)
                       else if x_1.val < m ↔ x.val < m then u else v)) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro x _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro x_1 _
                by_cases hdiag : x_1 = x <;>
                  by_cases hsame : x_1.val < m ↔ x.val < m <;>
                  simp [hdiag, hsame] <;> ring_nf
          _ = 1 + ((m : ℝ) - 1) * u - (m : ℝ) * v := by
                have h' : (∑ x : Fin (2 * m), ∑ x_1 : Fin (2 * m),
                    signVec m x * signVec m x_1 *
                      (if x_1 = x then (1 : ℝ)
                       else if x_1.val < m ↔ x.val < m then u else v))
                    = 2 * (m : ℝ) * 1 + 2 * (m : ℝ) * ((m : ℝ) - 1) * u -
                      2 * (m : ℝ) * (m : ℝ) * v := by
                  simpa [eq_comm, iff_comm, mul_assoc, mul_left_comm, mul_comm] using
                    block_signed_pair_sum m (1 : ℝ) u v
                rw [h']
                field_simp [hm20R]
      have hPinv : Matrix.trace (twoBlockLaplacianPinv m a b * blockSymMatrix m u v)
          = qParam m * (1 - u) / (a + b)
            + (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v) / (2 * b) := by
        rw [twoBlockLaplacianPinv]
        simp [Matrix.add_mul, Matrix.sub_mul, Matrix.trace_add, Matrix.trace_sub,
          Matrix.trace_smul]
        rw [hTraceX, hOnesProj, hSign]
        unfold qParam
        ring
      have hL : Matrix.trace (twoBlockLaplacian m a b * blockSymMatrix m u v)
          = qParam m * (a + b) * (1 - u)
            + 2 * b * (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v) := by
        let deg : ℝ := ((m : ℝ) - 1) * (a / (m : ℝ)) + (m : ℝ) * (b / (m : ℝ))
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
        have hTraceRaw : Matrix.trace (twoBlockLaplacian m a b * blockSymMatrix m u v)
            = ∑ i : Fin (2 * m), ∑ j : Fin (2 * m),
              if i = j then deg else if (i.val < m ↔ j.val < m)
                then -(a / (m : ℝ) * u) else -(b / (m : ℝ) * v) := by
          simp [Matrix.trace, Matrix.mul_apply, twoBlockLaplacian]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          by_cases hij : j = i
          · subst j
            rw [if_pos rfl, if_pos rfl, hDegree]
            have hdiagX : blockSymMatrix m u v i i = 1 := by simp [blockSymMatrix]
            rw [hdiagX]
            ring
          · have hji : i ≠ j := fun h => hij h.symm
            by_cases hsame : i.val < m ↔ j.val < m
            · have hsame' : j.val < m ↔ i.val < m := hsame.symm
              have hW : twoBlockGraph m a b i j = a / (m : ℝ) := by
                simp [twoBlockGraph, hji, hsame]
              have hX : blockSymMatrix m u v j i = u := by
                simp [blockSymMatrix, hij, hsame']
              rw [hW, hX]
              simp [hji, hsame]
            · have hsame' : ¬ (j.val < m ↔ i.val < m) := by
                intro h
                exact hsame h.symm
              have hW : twoBlockGraph m a b i j = b / (m : ℝ) := by
                simp [twoBlockGraph, hji, hsame]
              have hX : blockSymMatrix m u v j i = v := by
                simp [blockSymMatrix, hij, hsame']
              rw [hW, hX]
              simp [hji, hsame]
        rw [hTraceRaw]
        have hpair := block_pair_sum m deg (-(a / (m : ℝ) * u)) (-(b / (m : ℝ) * v))
        rw [hpair]
        unfold deg qParam
        field_simp [hm0R]
        ring
      unfold designObjective reducedObjective cX cY cZ
      rw [hL, hPinv, hFrob, hJ]
      ring
    · constructor
      · exact ⟨cutCovariance_eq_blockSym m, by
          norm_num; exact ⟨rfl, by ring⟩⟩
      · exact ⟨identity_eq_blockSym m, by ring_nf⟩

end CausalSmith.Experimentation.DesignPm1
