/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.ParitySliceForward

/-! # Pair counts for the balanced two-block partition

Finite pair-count identities over `A_m` and `B_m`, used by the spectral-coordinate
trace and Frobenius calculations.
-/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators

-- @node: sum_if_eq_else_self_real
/-- Sum a two-valued function over a finite set when one distinguished point takes
the diagonal value. -/
lemma sum_if_eq_else_self_real {α : Type*} [DecidableEq α] (s : Finset α) (a b : ℝ)
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

-- @node: block_pair_sum
/-- Pair count over the two equal blocks: diagonal pairs contribute `d`,
same-community off-diagonal pairs contribute `s`, and cross-community pairs
contribute `c`. -/
lemma block_pair_sum (m : ℕ) (d s c : ℝ) :
    (∑ i : Fin (2 * m), ∑ j : Fin (2 * m),
      if i = j then d else if (i.val < m ↔ j.val < m) then s else c)
      = 2 * (m : ℝ) * d + 2 * (m : ℝ) * ((m : ℝ) - 1) * s +
        2 * (m : ℝ) * (m : ℝ) * c := by
  let A := blockAFin m
  let B := blockBFin m
  have hsplit_outer :
      (∑ i : Fin (2 * m), ∑ j : Fin (2 * m),
        if i = j then d else if (i.val < m ↔ j.val < m) then s else c)
      = (∑ i ∈ A, ∑ j : Fin (2 * m),
          if i = j then d else if (i.val < m ↔ j.val < m) then s else c)
        + (∑ i ∈ B, ∑ j : Fin (2 * m),
          if i = j then d else if (i.val < m ↔ j.val < m) then s else c) := by
    dsimp [A, B, blockAFin, blockBFin]
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun i : Fin (2 * m) => i.val < m)
      (f := fun i => ∑ j : Fin (2 * m),
        if i = j then d else if (i.val < m ↔ j.val < m) then s else c)]
  have hinnerA : ∀ i ∈ A,
      (∑ j : Fin (2 * m), if i = j then d else if (i.val < m ↔ j.val < m) then s else c)
        = d + ((m - 1 : ℕ) : ℝ) * s + (m : ℝ) * c := by
    intro i hi
    have hi' : i.val < m := by simpa [A, blockAFin] using hi
    have hsplit_inner :
        (∑ j : Fin (2 * m), if i = j then d else if (i.val < m ↔ j.val < m) then s else c)
        = (∑ j ∈ A, if i = j then d else if (i.val < m ↔ j.val < m) then s else c)
          + (∑ j ∈ B, if i = j then d else if (i.val < m ↔ j.val < m) then s else c) := by
      dsimp [A, B, blockAFin, blockBFin]
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun j : Fin (2 * m) => j.val < m)
        (f := fun j => if i = j then d else if (i.val < m ↔ j.val < m) then s else c)]
    rw [hsplit_inner]
    have hAA : (∑ j ∈ A, if i = j then d else if (i.val < m ↔ j.val < m) then s else c)
        = d + ((m - 1 : ℕ) : ℝ) * s := by
      have hAcard : A.card = m := by dsimp [A]; exact card_blockAFin m
      calc
        (∑ j ∈ A, if i = j then d else if (i.val < m ↔ j.val < m) then s else c)
            = ∑ j ∈ A, if i = j then d else s := by
                apply Finset.sum_congr rfl
                intro j hj
                have hj' : j.val < m := by simpa [A, blockAFin] using hj
                by_cases hij : i = j <;> simp [hij, hi', hj']
        _ = d + ((A.card - 1 : ℕ) : ℝ) * s := sum_if_eq_else_self_real A d s hi
        _ = d + ((m - 1 : ℕ) : ℝ) * s := by rw [hAcard]
    have hAB : (∑ j ∈ B, if i = j then d else if (i.val < m ↔ j.val < m) then s else c)
        = (m : ℝ) * c := by
      have hBcard : B.card = m := by dsimp [B]; exact card_blockBFin m
      calc
        (∑ j ∈ B, if i = j then d else if (i.val < m ↔ j.val < m) then s else c)
            = ∑ j ∈ B, c := by
                apply Finset.sum_congr rfl
                intro j hj
                have hj' : ¬ j.val < m := by simpa [B, blockBFin] using hj
                have hne : i ≠ j := by
                  intro h
                  exact hj' (by simpa [h] using hi')
                have hnot : ¬ (i.val < m ↔ j.val < m) := by
                  intro hiff
                  exact hj' (hiff.mp hi')
                simp [hne, hnot]
        _ = (m : ℝ) * c := by rw [Finset.sum_const, nsmul_eq_mul, hBcard]
    rw [hAA, hAB]
  have hinnerB : ∀ i ∈ B,
      (∑ j : Fin (2 * m), if i = j then d else if (i.val < m ↔ j.val < m) then s else c)
        = d + ((m - 1 : ℕ) : ℝ) * s + (m : ℝ) * c := by
    intro i hi
    have hi' : ¬ i.val < m := by simpa [B, blockBFin] using hi
    have hsplit_inner :
        (∑ j : Fin (2 * m), if i = j then d else if (i.val < m ↔ j.val < m) then s else c)
        = (∑ j ∈ A, if i = j then d else if (i.val < m ↔ j.val < m) then s else c)
          + (∑ j ∈ B, if i = j then d else if (i.val < m ↔ j.val < m) then s else c) := by
      dsimp [A, B, blockAFin, blockBFin]
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun j : Fin (2 * m) => j.val < m)
        (f := fun j => if i = j then d else if (i.val < m ↔ j.val < m) then s else c)]
    rw [hsplit_inner]
    have hBA : (∑ j ∈ A, if i = j then d else if (i.val < m ↔ j.val < m) then s else c)
        = (m : ℝ) * c := by
      have hAcard : A.card = m := by dsimp [A]; exact card_blockAFin m
      calc
        (∑ j ∈ A, if i = j then d else if (i.val < m ↔ j.val < m) then s else c)
            = ∑ j ∈ A, c := by
                apply Finset.sum_congr rfl
                intro j hj
                have hj' : j.val < m := by simpa [A, blockAFin] using hj
                have hne : i ≠ j := by
                  intro h
                  exact hi' (by simpa [h] using hj')
                have hnot : ¬ (i.val < m ↔ j.val < m) := by
                  intro hiff
                  exact hi' (hiff.mpr hj')
                simp [hne, hnot]
        _ = (m : ℝ) * c := by rw [Finset.sum_const, nsmul_eq_mul, hAcard]
    have hBB : (∑ j ∈ B, if i = j then d else if (i.val < m ↔ j.val < m) then s else c)
        = d + ((m - 1 : ℕ) : ℝ) * s := by
      have hBcard : B.card = m := by dsimp [B]; exact card_blockBFin m
      calc
        (∑ j ∈ B, if i = j then d else if (i.val < m ↔ j.val < m) then s else c)
            = ∑ j ∈ B, if i = j then d else s := by
                apply Finset.sum_congr rfl
                intro j hj
                have hj' : ¬ j.val < m := by simpa [B, blockBFin] using hj
                by_cases hij : i = j <;> simp [hij, hi', hj']
        _ = d + ((B.card - 1 : ℕ) : ℝ) * s := sum_if_eq_else_self_real B d s hi
        _ = d + ((m - 1 : ℕ) : ℝ) * s := by rw [hBcard]
    rw [hBA, hBB]
    ring
  rw [hsplit_outer]
  calc
    (∑ i ∈ A, ∑ j : Fin (2 * m),
        if i = j then d else if (i.val < m ↔ j.val < m) then s else c)
      + (∑ i ∈ B, ∑ j : Fin (2 * m),
        if i = j then d else if (i.val < m ↔ j.val < m) then s else c)
        = (∑ i ∈ A, (d + ((m - 1 : ℕ) : ℝ) * s + (m : ℝ) * c))
          + (∑ i ∈ B, (d + ((m - 1 : ℕ) : ℝ) * s + (m : ℝ) * c)) := by
            congr 1
            · apply Finset.sum_congr rfl
              exact hinnerA
            · apply Finset.sum_congr rfl
              exact hinnerB
    _ = 2 * (m : ℝ) * d + 2 * (m : ℝ) * ((m : ℝ) - 1) * s +
        2 * (m : ℝ) * (m : ℝ) * c := by
          dsimp [A, B]
          rw [Finset.sum_const, Finset.sum_const, card_blockAFin, card_blockBFin]
          simp [nsmul_eq_mul]
          cases m with
          | zero => ring
          | succ n =>
              have hsub : (n + 1 - 1 : ℕ) = n := by omega
              simp [hsub]
              ring

-- @node: block_signed_pair_sum
/-- The same pair count with a community-sign multiplier. Same-community pairs
have sign product `+1`, and cross-community pairs have sign product `-1`. -/
lemma block_signed_pair_sum (m : ℕ) (d s c : ℝ) :
    (∑ i : Fin (2 * m), ∑ j : Fin (2 * m),
      signVec m i * signVec m j *
        (if i = j then d else if (i.val < m ↔ j.val < m) then s else c))
      = 2 * (m : ℝ) * d + 2 * (m : ℝ) * ((m : ℝ) - 1) * s -
        2 * (m : ℝ) * (m : ℝ) * c := by
  have hpoint : ∀ i j : Fin (2 * m),
      signVec m i * signVec m j *
          (if i = j then d else if (i.val < m ↔ j.val < m) then s else c)
        = if i = j then d else if (i.val < m ↔ j.val < m) then s else -c := by
    intro i j
    by_cases hi : i.val < m <;> by_cases hj : j.val < m <;> by_cases hij : i = j <;>
      simp [signVec, hi, hj, hij]
  calc
    (∑ i : Fin (2 * m), ∑ j : Fin (2 * m),
      signVec m i * signVec m j *
        (if i = j then d else if (i.val < m ↔ j.val < m) then s else c))
        = ∑ i : Fin (2 * m), ∑ j : Fin (2 * m),
            if i = j then d else if (i.val < m ↔ j.val < m) then s else -c := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact hpoint i j
    _ = 2 * (m : ℝ) * d + 2 * (m : ℝ) * ((m : ℝ) - 1) * s -
        2 * (m : ℝ) * (m : ℝ) * c := by
          have h := block_pair_sum m d s (-c)
          nlinarith [h]

end CausalSmith.Experimentation.DesignPm1
