/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Basic

/-! # ±1 reduced-slice characterization: the forward (necessity) direction

If a `±1` design `D` realizes the block-symmetric second moment `X(u,v)` (i.e.
`E_D[Z Zᵀ] = X(u,v)`), then its reduced spectral coordinates
`x = 1−u`, `y = 1+(m−1)u−mv`, `z = 1+(m−1)u+mv` are nonnegative (PSD of a Gram
matrix) and satisfy the parity bound `y + z ≥ d_m` (`0` for even `m`, `2/m` for
odd `m`).  The whole argument is elementary second-moment algebra: reading the
matrix entries `1` (diagonal), `u` (within-block), `v` (across-block), the block
sums `S_A = ∑_{i∈A} Z_i`, `S_B = ∑_{i∈B} Z_i` satisfy
`E[S_A²] = E[S_B²] = m + m(m−1)u`, `E[S_A S_B] = m² v`, whence
`E[(S_A−S_B)²] = 2m·y ≥ 0`, `E[(S_A+S_B)²] = 2m·z ≥ 0`, and for odd `m` the
parity `S_A, S_B` odd forces `E[S_A²], E[S_B²] ≥ 1`, so `y+z = (E[S_A²]+E[S_B²])/m ≥ 2/m`.
-/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators
open Causalean.Experimentation.DesignBased

/-- Community `A_m = {i : i.val < m}` as a `Finset`. -/
def blockAFin (m : ℕ) : Finset (Fin (2 * m)) :=
  Finset.univ.filter (fun i : Fin (2 * m) => i.val < m)

/-- Community `B_m = {i : ¬ i.val < m}` as a `Finset`. -/
def blockBFin (m : ℕ) : Finset (Fin (2 * m)) :=
  Finset.univ.filter (fun i : Fin (2 * m) => ¬ i.val < m)

/-- The real community sum `S_A(z) = ∑_{i ∈ A_m} Z_i`. -/
noncomputable def sumAr (m : ℕ) (z : Fin (2 * m) → Bool) : ℝ :=
  ∑ i ∈ blockAFin m, signOf m z i

/-- The real community sum `S_B(z) = ∑_{i ∈ B_m} Z_i`. -/
noncomputable def sumBr (m : ℕ) (z : Fin (2 * m) → Bool) : ℝ :=
  ∑ i ∈ blockBFin m, signOf m z i

/-- Each `±1` sign squares to `1`. -/
lemma signOf_sq (m : ℕ) (z : Fin (2 * m) → Bool) (i : Fin (2 * m)) :
    signOf m z i * signOf m z i = 1 := by
  unfold signOf; split <;> ring

/-- `|A_m| = m`. -/
lemma card_blockAFin (m : ℕ) : (blockAFin m).card = m := by
  unfold blockAFin
  refine Finset.card_eq_of_bijective
    (fun i hi => (⟨i, by omega⟩ : Fin (2 * m))) ?surj ?mem ?inj
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact ⟨a.val, ha, Fin.ext rfl⟩
  · intro i hi
    simp [hi]
  · intro i j hi hj h
    exact congrArg Fin.val h

/-- `|B_m| = m`. -/
lemma card_blockBFin (m : ℕ) : (blockBFin m).card = m := by
  unfold blockBFin
  refine Finset.card_eq_of_bijective
    (fun i hi => (⟨m + i, by omega⟩ : Fin (2 * m))) ?surj ?mem ?inj
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    refine ⟨a.val - m, by omega, ?_⟩
    apply Fin.ext
    simp
    omega
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro i j hi hj h
    have := congrArg Fin.val h
    simp at this
    omega

/-- The design second-moment entries read off from `X(u,v)`: the `(i,j)` entry is
`1` on the diagonal, `u` within a block, `v` across blocks. -/
lemma secondMoment_entry (m : ℕ) (u v : ℝ)
    (D : FiniteDesign (Fin (2 * m) → Bool))
    (hD : assignmentSecondMoment m D = blockSymMatrix m u v)
    (i j : Fin (2 * m)) :
    D.E (fun z => signOf m z i * signOf m z j) = blockSymMatrix m u v i j := by
  have := congrFun (congrFun hD i) j
  simpa [assignmentSecondMoment] using this

private lemma blockSymMatrix_AA (m : ℕ) (u v : ℝ) {i j : Fin (2 * m)}
    (hi : i ∈ blockAFin m) (hj : j ∈ blockAFin m) :
    blockSymMatrix m u v i j = if i = j then 1 else u := by
  have hi' : i.val < m := by simpa [blockAFin] using hi
  have hj' : j.val < m := by simpa [blockAFin] using hj
  by_cases hij : i = j
  · simp [blockSymMatrix, hij]
  · simp [blockSymMatrix, hij, hi', hj']

private lemma blockSymMatrix_BB (m : ℕ) (u v : ℝ) {i j : Fin (2 * m)}
    (hi : i ∈ blockBFin m) (hj : j ∈ blockBFin m) :
    blockSymMatrix m u v i j = if i = j then 1 else u := by
  have hi' : ¬ i.val < m := by simpa [blockBFin] using hi
  have hj' : ¬ j.val < m := by simpa [blockBFin] using hj
  by_cases hij : i = j
  · simp [blockSymMatrix, hij]
  · simp [blockSymMatrix, hij, hi', hj']

private lemma blockSymMatrix_AB (m : ℕ) (u v : ℝ) {i j : Fin (2 * m)}
    (hi : i ∈ blockAFin m) (hj : j ∈ blockBFin m) :
    blockSymMatrix m u v i j = v := by
  have hi' : i.val < m := by simpa [blockAFin] using hi
  have hj' : ¬ j.val < m := by simpa [blockBFin] using hj
  have hij : i ≠ j := by
    intro h
    exact hj' (by simpa [h] using hi')
  simp [blockSymMatrix, hij, hi', hj']

private lemma sum_if_eq_else_self {α : Type*} [DecidableEq α] (s : Finset α) (a b : ℝ)
    {i : α} (hi : i ∈ s) :
    (∑ j ∈ s, (if i = j then a else b)) = a + ((s.card - 1 : ℕ) : ℝ) * b := by
  rw [← Finset.sum_erase_add s (fun j => if i = j then a else b) hi]
  have herase : (∑ x ∈ s.erase i, (if i = x then a else b)) = ∑ x ∈ s.erase i, b := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxne : i ≠ x := by
      have hx' := (Finset.mem_erase.mp hx).1
      exact fun h => hx' h.symm
    simp [hxne]
  rw [herase]
  rw [Finset.sum_const, Finset.card_erase_of_mem hi, nsmul_eq_mul]
  simp
  ring

private lemma sum_sum_if_eq_else {α : Type*} [DecidableEq α] (s : Finset α) (a b : ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, (if i = j then a else b))
      = (s.card : ℝ) * a + (s.card : ℝ) * ((s.card - 1 : ℕ) : ℝ) * b := by
  calc
    (∑ i ∈ s, ∑ j ∈ s, (if i = j then a else b))
        = ∑ i ∈ s, (a + ((s.card - 1 : ℕ) : ℝ) * b) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact sum_if_eq_else_self s a b hi
    _ = (s.card : ℝ) * a + (s.card : ℝ) * ((s.card - 1 : ℕ) : ℝ) * b := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring

/-- `E[S_A²] = m + m(m−1) u` (and identically `E[S_B²]`). -/
lemma E_sumAr_sq (m : ℕ) (u v : ℝ)
    (D : FiniteDesign (Fin (2 * m) → Bool))
    (hD : assignmentSecondMoment m D = blockSymMatrix m u v) :
    D.E (fun z => sumAr m z * sumAr m z) = (m : ℝ) + (m : ℝ) * ((m : ℝ) - 1) * u := by
  let A := blockAFin m
  have hE :
      D.E (fun z => sumAr m z * sumAr m z)
        = ∑ i ∈ A, ∑ j ∈ A, D.E (fun z => signOf m z i * signOf m z j) := by
    calc
      D.E (fun z => sumAr m z * sumAr m z)
          = D.E (fun z => ∑ i ∈ A, ∑ j ∈ A, signOf m z i * signOf m z j) := by
              apply D.E_congr
              intro z
              simp [sumAr, A, Finset.sum_mul_sum]
      _ = ∑ i ∈ A, D.E (fun z => ∑ j ∈ A, signOf m z i * signOf m z j) := by
              rw [D.E_sum]
      _ = ∑ i ∈ A, ∑ j ∈ A, D.E (fun z => signOf m z i * signOf m z j) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [D.E_sum]
  calc
    D.E (fun z => sumAr m z * sumAr m z)
        = ∑ i ∈ A, ∑ j ∈ A, (if i = j then (1 : ℝ) else u) := by
            rw [hE]
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            rw [secondMoment_entry m u v D hD, blockSymMatrix_AA m u v hi hj]
    _ = (A.card : ℝ) * 1 + (A.card : ℝ) * ((A.card - 1 : ℕ) : ℝ) * u := by
            exact sum_sum_if_eq_else A 1 u
    _ = (m : ℝ) + (m : ℝ) * ((m : ℝ) - 1) * u := by
            subst A
            rw [card_blockAFin]
            cases m <;> simp

lemma E_sumBr_sq (m : ℕ) (u v : ℝ)
    (D : FiniteDesign (Fin (2 * m) → Bool))
    (hD : assignmentSecondMoment m D = blockSymMatrix m u v) :
    D.E (fun z => sumBr m z * sumBr m z) = (m : ℝ) + (m : ℝ) * ((m : ℝ) - 1) * u := by
  let B := blockBFin m
  have hE :
      D.E (fun z => sumBr m z * sumBr m z)
        = ∑ i ∈ B, ∑ j ∈ B, D.E (fun z => signOf m z i * signOf m z j) := by
    calc
      D.E (fun z => sumBr m z * sumBr m z)
          = D.E (fun z => ∑ i ∈ B, ∑ j ∈ B, signOf m z i * signOf m z j) := by
              apply D.E_congr
              intro z
              simp [sumBr, B, Finset.sum_mul_sum]
      _ = ∑ i ∈ B, D.E (fun z => ∑ j ∈ B, signOf m z i * signOf m z j) := by
              rw [D.E_sum]
      _ = ∑ i ∈ B, ∑ j ∈ B, D.E (fun z => signOf m z i * signOf m z j) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [D.E_sum]
  calc
    D.E (fun z => sumBr m z * sumBr m z)
        = ∑ i ∈ B, ∑ j ∈ B, (if i = j then (1 : ℝ) else u) := by
            rw [hE]
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            rw [secondMoment_entry m u v D hD, blockSymMatrix_BB m u v hi hj]
    _ = (B.card : ℝ) * 1 + (B.card : ℝ) * ((B.card - 1 : ℕ) : ℝ) * u := by
            exact sum_sum_if_eq_else B 1 u
    _ = (m : ℝ) + (m : ℝ) * ((m : ℝ) - 1) * u := by
            subst B
            rw [card_blockBFin]
            cases m <;> simp

/-- `E[S_A S_B] = m² v`. -/
lemma E_sumAr_sumBr (m : ℕ) (u v : ℝ)
    (D : FiniteDesign (Fin (2 * m) → Bool))
    (hD : assignmentSecondMoment m D = blockSymMatrix m u v) :
    D.E (fun z => sumAr m z * sumBr m z) = (m : ℝ) ^ 2 * v := by
  let A := blockAFin m
  let B := blockBFin m
  have hE :
      D.E (fun z => sumAr m z * sumBr m z)
        = ∑ i ∈ A, ∑ j ∈ B, D.E (fun z => signOf m z i * signOf m z j) := by
    calc
      D.E (fun z => sumAr m z * sumBr m z)
          = D.E (fun z => ∑ i ∈ A, ∑ j ∈ B, signOf m z i * signOf m z j) := by
              apply D.E_congr
              intro z
              simp [sumAr, sumBr, A, B, Finset.sum_mul_sum]
      _ = ∑ i ∈ A, D.E (fun z => ∑ j ∈ B, signOf m z i * signOf m z j) := by
              rw [D.E_sum]
      _ = ∑ i ∈ A, ∑ j ∈ B, D.E (fun z => signOf m z i * signOf m z j) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [D.E_sum]
  calc
    D.E (fun z => sumAr m z * sumBr m z)
        = ∑ i ∈ A, ∑ j ∈ B, v := by
            rw [hE]
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            rw [secondMoment_entry m u v D hD, blockSymMatrix_AB m u v hi hj]
    _ = (m : ℝ) ^ 2 * v := by
            subst A
            subst B
            simp [Finset.sum_const, nsmul_eq_mul, card_blockAFin, card_blockBFin]
            ring

/-- The within-block second moment `u ≤ 1` (from `E[(Z_i − Z_j)²] ≥ 0` for a
within-block pair, available since `m ≥ 2`). -/
lemma u_le_one (m : ℕ) (hm : 2 ≤ m) (u v : ℝ)
    (D : FiniteDesign (Fin (2 * m) → Bool))
    (hD : assignmentSecondMoment m D = blockSymMatrix m u v) :
    u ≤ 1 := by
  let i0 : Fin (2 * m) := ⟨0, by omega⟩
  let j0 : Fin (2 * m) := ⟨1, by omega⟩
  have hi0 : i0 ∈ blockAFin m := by
    simp [blockAFin, i0]
    omega
  have hj0 : j0 ∈ blockAFin m := by
    simp [blockAFin, j0]
    omega
  have hne : i0 ≠ j0 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, j0] at this
  have hcross :
      D.E (fun z => signOf m z i0 * signOf m z j0) = u := by
    rw [secondMoment_entry m u v D hD, blockSymMatrix_AA m u v hi0 hj0]
    simp [hne]
  have hsqi : D.E (fun z => signOf m z i0 * signOf m z i0) = 1 := by
    calc
      D.E (fun z => signOf m z i0 * signOf m z i0)
          = D.E (fun _ => (1 : ℝ)) := by
              apply D.E_congr
              intro z
              exact signOf_sq m z i0
      _ = 1 := by rw [D.E_const]
  have hsqj : D.E (fun z => signOf m z j0 * signOf m z j0) = 1 := by
    calc
      D.E (fun z => signOf m z j0 * signOf m z j0)
          = D.E (fun _ => (1 : ℝ)) := by
              apply D.E_congr
              intro z
              exact signOf_sq m z j0
      _ = 1 := by rw [D.E_const]
  have hnonneg :
      0 ≤ D.E (fun z => (signOf m z i0 - signOf m z j0)
        * (signOf m z i0 - signOf m z j0)) := by
    apply D.E_nonneg
    intro z
    nlinarith [sq_nonneg (signOf m z i0 - signOf m z j0)]
  have hE :
      D.E (fun z => (signOf m z i0 - signOf m z j0)
        * (signOf m z i0 - signOf m z j0)) = 2 - 2 * u := by
    calc
      D.E (fun z => (signOf m z i0 - signOf m z j0)
        * (signOf m z i0 - signOf m z j0))
          = D.E (fun z =>
              (signOf m z i0 * signOf m z i0 + signOf m z j0 * signOf m z j0)
                - 2 * (signOf m z i0 * signOf m z j0)) := by
              apply D.E_congr
              intro z
              ring
      _ = D.E (fun z => signOf m z i0 * signOf m z i0
              + signOf m z j0 * signOf m z j0)
            - D.E (fun z => 2 * (signOf m z i0 * signOf m z j0)) := by
              rw [D.E_sub]
      _ = (D.E (fun z => signOf m z i0 * signOf m z i0)
              + D.E (fun z => signOf m z j0 * signOf m z j0))
            - 2 * D.E (fun z => signOf m z i0 * signOf m z j0) := by
              rw [D.E_add, D.E_const_mul]
      _ = 2 - 2 * u := by
              rw [hsqi, hsqj, hcross]
              ring
  nlinarith

private lemma nat_odd_cast_int {n : ℕ} (h : Odd n) : Odd (n : ℤ) := by
  rcases h with ⟨k, hk⟩
  use (k : ℤ)
  omega

private lemma odd_int_sum_pm_one_of_odd_card {α : Type*} (s : Finset α) (f : α → ℤ)
    (hf : ∀ i ∈ s, f i = 1 ∨ f i = -1) (hodd : Odd s.card) :
    Odd (∑ i ∈ s, f i) := by
  have heach : ∀ i ∈ s, Even (f i - 1) := by
    intro i hi
    rcases hf i hi with h | h <;> simp [h]
  have hdiff0 : Even (∑ i ∈ s, (f i - 1)) := Finset.even_sum _ heach
  have hsum : (∑ i ∈ s, (f i - 1)) = (∑ i ∈ s, f i) - (s.card : ℤ) := by
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_const]
  have hdiff : Even ((∑ i ∈ s, f i) - (s.card : ℤ)) := by
    simpa [hsum] using hdiff0
  have hiff : Even (∑ i ∈ s, f i) ↔ Even (s.card : ℤ) := Int.even_sub.mp hdiff
  rw [← Int.not_even_iff_odd]
  intro hEven
  exact (Int.not_even_iff_odd.mpr (nat_odd_cast_int hodd)) (hiff.mp hEven)

private lemma one_le_sq_of_odd_int {n : ℤ} (hn : Odd n) :
    (1 : ℝ) ≤ (n : ℝ) * (n : ℝ) := by
  have hne : n ≠ 0 := by
    intro h
    subst n
    norm_num at hn
  have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hne
  have hle : 1 ≤ n.natAbs := hpos
  have hsq_nat : 1 ≤ n.natAbs * n.natAbs := by nlinarith
  have hsq_int : (1 : ℤ) ≤ n * n := by
    rw [← (Int.natAbs_mul_self (a := n))]
    exact_mod_cast hsq_nat
  exact_mod_cast hsq_int

private lemma sumAr_eq_blockSumA_cast (m : ℕ) (z : Fin (2 * m) → Bool) :
    sumAr m z = (blockSumA m z : ℝ) := by
  simp [sumAr, blockSumA, blockAFin, signOf]

private lemma sumBr_eq_blockSumB_cast (m : ℕ) (z : Fin (2 * m) → Bool) :
    sumBr m z = (blockSumB m z : ℝ) := by
  simp [sumBr, blockSumB, blockBFin, signOf]

/-- For odd `m`, the integer block sum `S_A` is odd for every assignment. -/
lemma blockSumA_odd (m : ℕ) (hOdd : Odd m) (z : Fin (2 * m) → Bool) :
    Odd (blockSumA m z) := by
  unfold blockSumA
  apply odd_int_sum_pm_one_of_odd_card
  · intro i hi
    by_cases hz : z i <;> simp [hz]
  · change Odd (blockAFin m).card
    simpa [card_blockAFin] using hOdd

private lemma blockSumB_odd (m : ℕ) (hOdd : Odd m) (z : Fin (2 * m) → Bool) :
    Odd (blockSumB m z) := by
  unfold blockSumB
  apply odd_int_sum_pm_one_of_odd_card
  · intro i hi
    by_cases hz : z i <;> simp [hz]
  · change Odd (blockBFin m).card
    simpa [card_blockBFin] using hOdd

/-- For odd `m`, `E[S_A²] ≥ 1`. -/
lemma one_le_E_sumAr_sq (m : ℕ) (hOdd : Odd m)
    (D : FiniteDesign (Fin (2 * m) → Bool)) :
    (1 : ℝ) ≤ D.E (fun z => sumAr m z * sumAr m z) := by
  have hnonneg : 0 ≤ D.E (fun z => sumAr m z * sumAr m z - 1) := by
    apply D.E_nonneg
    intro z
    have hsquare : (1 : ℝ) ≤ (blockSumA m z : ℝ) * (blockSumA m z : ℝ) :=
      one_le_sq_of_odd_int (blockSumA_odd m hOdd z)
    have hcast := sumAr_eq_blockSumA_cast m z
    rw [hcast]
    nlinarith
  have hsub :
      D.E (fun z => sumAr m z * sumAr m z - 1)
        = D.E (fun z => sumAr m z * sumAr m z) - 1 := by
    rw [D.E_sub, D.E_const]
  nlinarith

lemma one_le_E_sumBr_sq (m : ℕ) (hOdd : Odd m)
    (D : FiniteDesign (Fin (2 * m) → Bool)) :
    (1 : ℝ) ≤ D.E (fun z => sumBr m z * sumBr m z) := by
  have hnonneg : 0 ≤ D.E (fun z => sumBr m z * sumBr m z - 1) := by
    apply D.E_nonneg
    intro z
    have hsquare : (1 : ℝ) ≤ (blockSumB m z : ℝ) * (blockSumB m z : ℝ) :=
      one_le_sq_of_odd_int (blockSumB_odd m hOdd z)
    have hcast := sumBr_eq_blockSumB_cast m z
    rw [hcast]
    nlinarith
  have hsub :
      D.E (fun z => sumBr m z * sumBr m z - 1)
        = D.E (fun z => sumBr m z * sumBr m z) - 1 := by
    rw [D.E_sub, D.E_const]
  nlinarith

/-- **Forward (necessity) direction.** A design realizing `X(u,v)` has reduced
spectral coordinates in the parity-truncated triangle. -/
lemma pm_slice_forward (m : ℕ) (hm : 2 ≤ m) (u v : ℝ)
    (D : FiniteDesign (Fin (2 * m) → Bool))
    (hD : assignmentSecondMoment m D = blockSymMatrix m u v) :
    InReducedTriangle m (1 - u) (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
        (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) ∧
      parityThreshold m ≤ (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
        + (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) := by
  let A2 := fun z => sumAr m z * sumAr m z
  let B2 := fun z => sumBr m z * sumBr m z
  let AB := fun z => sumAr m z * sumBr m z
  let y : ℝ := 1 + ((m : ℝ) - 1) * u - (m : ℝ) * v
  let zc : ℝ := 1 + ((m : ℝ) - 1) * u + (m : ℝ) * v
  have hmpos_nat : 0 < m := by omega
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hmpos_nat
  have hA2 := E_sumAr_sq m u v D hD
  have hB2 := E_sumBr_sq m u v D hD
  have hAB := E_sumAr_sumBr m u v D hD
  have hminus_nonneg :
      0 ≤ D.E (fun w => (sumAr m w - sumBr m w) * (sumAr m w - sumBr m w)) := by
    apply D.E_nonneg
    intro w
    nlinarith [sq_nonneg (sumAr m w - sumBr m w)]
  have hplus_nonneg :
      0 ≤ D.E (fun w => (sumAr m w + sumBr m w) * (sumAr m w + sumBr m w)) := by
    apply D.E_nonneg
    intro w
    nlinarith [sq_nonneg (sumAr m w + sumBr m w)]
  have hminusE :
      D.E (fun w => (sumAr m w - sumBr m w) * (sumAr m w - sumBr m w))
        = 2 * (m : ℝ) * y := by
    calc
      D.E (fun w => (sumAr m w - sumBr m w) * (sumAr m w - sumBr m w))
          = D.E (fun w => (A2 w + B2 w) - 2 * AB w) := by
              apply D.E_congr
              intro w
              simp [A2, B2, AB]
              ring
      _ = D.E (fun w => A2 w + B2 w) - D.E (fun w => 2 * AB w) := by
              rw [D.E_sub]
      _ = (D.E A2 + D.E B2) - 2 * D.E AB := by
              rw [D.E_add, D.E_const_mul]
      _ = 2 * (m : ℝ) * y := by
              subst A2
              subst B2
              subst AB
              subst y
              rw [hA2, hB2, hAB]
              ring
  have hplusE :
      D.E (fun w => (sumAr m w + sumBr m w) * (sumAr m w + sumBr m w))
        = 2 * (m : ℝ) * zc := by
    calc
      D.E (fun w => (sumAr m w + sumBr m w) * (sumAr m w + sumBr m w))
          = D.E (fun w => (A2 w + B2 w) + 2 * AB w) := by
              apply D.E_congr
              intro w
              simp [A2, B2, AB]
              ring
      _ = D.E (fun w => A2 w + B2 w) + D.E (fun w => 2 * AB w) := by
              rw [D.E_add]
      _ = (D.E A2 + D.E B2) + 2 * D.E AB := by
              rw [D.E_add, D.E_const_mul]
      _ = 2 * (m : ℝ) * zc := by
              subst A2
              subst B2
              subst AB
              subst zc
              rw [hA2, hB2, hAB]
              ring
  have hx_nonneg : 0 ≤ 1 - u := by
    have hu := u_le_one m hm u v D hD
    nlinarith
  have hy_nonneg : 0 ≤ y := by
    nlinarith [hminus_nonneg, hminusE, hmpos]
  have hz_nonneg : 0 ≤ zc := by
    nlinarith [hplus_nonneg, hplusE, hmpos]
  constructor
  · subst y
    subst zc
    unfold InReducedTriangle
    refine ⟨hx_nonneg, ?_, ?_, ?_⟩
    · simpa using hy_nonneg
    · simpa using hz_nonneg
    · simp [qParam]
      ring
  · by_cases hEven : Even m
    · simp [parityThreshold, hEven]
      nlinarith [hy_nonneg, hz_nonneg]
    · have hOdd : Odd m := Nat.not_even_iff_odd.mp hEven
      have hA_ge := one_le_E_sumAr_sq m hOdd D
      have hB_ge := one_le_E_sumBr_sq m hOdd D
      have hsum_moment : D.E A2 + D.E B2 = (m : ℝ) * (y + zc) := by
        subst A2
        subst B2
        subst y
        subst zc
        rw [hA2, hB2]
        ring
      have hprod : (2 : ℝ) ≤ (m : ℝ) * (y + zc) := by
        nlinarith
      have hdiv : (2 : ℝ) / (m : ℝ) ≤ y + zc := by
        rw [div_le_iff₀ hmpos]
        nlinarith
      simp [parityThreshold, hEven]
      subst y
      subst zc
      simpa using hdiv

end CausalSmith.Experimentation.DesignPm1
