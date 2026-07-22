/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.ParitySliceVertices

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

/-! # Odd-`m` parity vertex designs and the quadrilateral backward direction

For odd `m` the spread origin `(0,0)` is not implementable (parity forces
`S_A, S_B` odd, hence `y+z ≥ 2/m`).  The feasible region is the quadrilateral with
the two extra parity vertices

* `pcutVDesign`  — `X(−1/m, −1/m²)`, reduced `(2/m, 0)` (block sums `(±1, ∓1)`);
* `pallVDesign`  — `X(−1/m,  1/m²)`, reduced `(0, 2/m)` (block sums `(±1, ±1)`).

An arbitrary quadrilateral point is the convex combination of the four vertices
`cut, all, pcut, pall` with the outer/inner-edge weights `λμ, λ(1−μ), (1−λ)μ,
(1−λ)(1−μ)`, `μ = y/(y+z)`, `λ = ((y+z)−2/m)/(2m−2/m)`. -/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators
open Causalean.Experimentation.DesignBased

/-! ## Parity supports and witnesses (odd `m`) -/

/-- The `(±1, ∓1)` block-sum support (`pcut`). -/
def pcutSupport (m : ℕ) : Finset (Fin (2 * m) → Bool) :=
  Finset.univ.filter (fun z =>
    (blockSumA m z = 1 ∧ blockSumB m z = -1) ∨ (blockSumA m z = -1 ∧ blockSumB m z = 1))

/-- The `(±1, ±1)` block-sum support (`pall`). -/
def pallSupport (m : ℕ) : Finset (Fin (2 * m) → Bool) :=
  Finset.univ.filter (fun z =>
    (blockSumA m z = 1 ∧ blockSumB m z = 1) ∨ (blockSumA m z = -1 ∧ blockSumB m z = -1))

/-- An assignment with `S_A = 1, S_B = -1` (odd `m`): `(m+1)/2` `true` on block `A`,
`(m-1)/2` `true` on block `B`. -/
def pcutWitness (m : ℕ) : Fin (2 * m) → Bool :=
  fun i => decide (i.val < (m + 1) / 2 ∨ (m ≤ i.val ∧ i.val < m + (m - 1) / 2))

/-- An assignment with `S_A = 1, S_B = 1` (odd `m`). -/
def pallWitness (m : ℕ) : Fin (2 * m) → Bool :=
  fun i => decide (i.val < (m + 1) / 2 ∨ (m ≤ i.val ∧ i.val < m + (m + 1) / 2))

private lemma card_fin_lt_parity (m t : ℕ) (ht : t ≤ 2 * m) :
    (Finset.univ.filter (fun i : Fin (2 * m) => i.val < t)).card = t := by
  refine Finset.card_eq_of_bijective
    (fun i hi => (⟨i, by omega⟩ : Fin (2 * m))) ?surj ?mem ?inj
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact ⟨a.val, ha, Fin.ext rfl⟩
  · intro i hi
    simp [hi]
  · intro i j hi hj h
    exact congrArg Fin.val h

private lemma card_fin_interval_from_m_parity (m t : ℕ) (ht : t ≤ m) :
    (Finset.univ.filter (fun i : Fin (2 * m) => m ≤ i.val ∧ i.val < m + t)).card
      = t := by
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

private lemma half_up_le_of_odd (m : ℕ) (hOdd : Odd m) : (m + 1) / 2 ≤ m := by
  rcases hOdd with ⟨k, rfl⟩
  omega

private lemma half_down_le (m : ℕ) : (m - 1) / 2 ≤ m := by
  omega

private lemma pcutA_true_filter (m : ℕ) (hOdd : Odd m) :
    (blockAFin m).filter (fun i => pcutWitness m i) =
      Finset.univ.filter (fun i : Fin (2 * m) => i.val < (m + 1) / 2) := by
  ext i
  simp only [Finset.mem_filter, blockAFin, Finset.mem_univ, true_and, pcutWitness]
  constructor
  · intro h
    rcases h with ⟨hA, hs⟩
    have hs' :
        i.val < (m + 1) / 2 ∨ (m ≤ i.val ∧ i.val < m + (m - 1) / 2) :=
      of_decide_eq_true hs
    rcases hs' with hs' | hs'
    · exact hs'
    · omega
  · intro h
    constructor
    · have hle := half_up_le_of_odd m hOdd
      omega
    · exact decide_eq_true (Or.inl h)

private lemma pcutB_true_filter (m : ℕ) (hOdd : Odd m) :
    (blockBFin m).filter (fun i => pcutWitness m i) =
      Finset.univ.filter (fun i : Fin (2 * m) => m ≤ i.val ∧ i.val < m + (m - 1) / 2) := by
  ext i
  simp only [Finset.mem_filter, blockBFin, Finset.mem_univ, true_and, pcutWitness]
  constructor
  · intro h
    rcases h with ⟨hB, hs⟩
    have hs' :
        i.val < (m + 1) / 2 ∨ (m ≤ i.val ∧ i.val < m + (m - 1) / 2) :=
      of_decide_eq_true hs
    rcases hs' with hs' | hs'
    · have hle := half_up_le_of_odd m hOdd
      omega
    · exact hs'
  · intro h
    constructor
    · omega
    · exact decide_eq_true (Or.inr h)

private lemma pallA_true_filter (m : ℕ) (hOdd : Odd m) :
    (blockAFin m).filter (fun i => pallWitness m i) =
      Finset.univ.filter (fun i : Fin (2 * m) => i.val < (m + 1) / 2) := by
  ext i
  simp only [Finset.mem_filter, blockAFin, Finset.mem_univ, true_and, pallWitness]
  constructor
  · intro h
    rcases h with ⟨hA, hs⟩
    have hs' :
        i.val < (m + 1) / 2 ∨ (m ≤ i.val ∧ i.val < m + (m + 1) / 2) :=
      of_decide_eq_true hs
    rcases hs' with hs' | hs'
    · exact hs'
    · omega
  · intro h
    constructor
    · have hle := half_up_le_of_odd m hOdd
      omega
    · exact decide_eq_true (Or.inl h)

private lemma pallB_true_filter (m : ℕ) :
    (blockBFin m).filter (fun i => pallWitness m i) =
      Finset.univ.filter (fun i : Fin (2 * m) => m ≤ i.val ∧ i.val < m + (m + 1) / 2) := by
  ext i
  simp only [Finset.mem_filter, blockBFin, Finset.mem_univ, true_and, pallWitness]
  constructor
  · intro h
    rcases h with ⟨hB, hs⟩
    have hs' :
        i.val < (m + 1) / 2 ∨ (m ≤ i.val ∧ i.val < m + (m + 1) / 2) :=
      of_decide_eq_true hs
    rcases hs' with hs' | hs'
    · omega
    · exact hs'
  · intro h
    constructor
    · omega
    · exact decide_eq_true (Or.inr h)

private lemma blockSumA_pcutWitness (m : ℕ) (hOdd : Odd m) :
    blockSumA m (pcutWitness m) = 1 := by
  change (∑ i ∈ blockAFin m, (if pcutWitness m i = true then (1 : ℤ) else -1)) = 1
  have hTrueCardBool :
      ((blockAFin m).filter (fun i => pcutWitness m i)).card = (m + 1) / 2 := by
    rw [pcutA_true_filter m hOdd]
    apply card_fin_lt_parity
    omega
  have hTrueCard : ((blockAFin m).filter (fun i => pcutWitness m i = true)).card
      = (m + 1) / 2 := by
    simpa using hTrueCardBool
  have hFalseCard : ((blockAFin m).filter (fun i => pcutWitness m i = false)).card
      = (m - 1) / 2 := by
    have hsum := Finset.card_filter_add_card_filter_not (s := blockAFin m)
      (p := fun i => pcutWitness m i = true)
    rw [hTrueCard, card_blockAFin] at hsum
    have hfalseNot :
        ((blockAFin m).filter (fun i => ¬ pcutWitness m i = true)).card = (m - 1) / 2 := by
      rcases hOdd with ⟨k, rfl⟩
      omega
    simpa [Bool.not_eq_true] using hfalseNot
  rw [← Finset.sum_filter_add_sum_filter_not (s := blockAFin m)
    (p := fun i => pcutWitness m i = true)
    (f := fun i => if pcutWitness m i = true then (1 : ℤ) else -1)]
  have hT : (∑ x ∈ blockAFin m with pcutWitness m x = true,
      if pcutWitness m x = true then (1 : ℤ) else -1) = ((m + 1) / 2 : ℤ) := by
    calc
      (∑ x ∈ blockAFin m with pcutWitness m x = true,
          if pcutWitness m x = true then (1 : ℤ) else -1)
          = ∑ x ∈ blockAFin m with pcutWitness m x = true, (1 : ℤ) := by
              apply Finset.sum_congr rfl
              intro x hx
              simp only [Finset.mem_filter] at hx
              simp [hx.2]
      _ = ((m + 1) / 2 : ℤ) := by
              simp [hTrueCard]
  have hF : (∑ x ∈ blockAFin m with ¬pcutWitness m x = true,
      if pcutWitness m x = true then (1 : ℤ) else -1) = -((m - 1) / 2 : ℤ) := by
    calc
      (∑ x ∈ blockAFin m with ¬pcutWitness m x = true,
          if pcutWitness m x = true then (1 : ℤ) else -1)
          = ∑ x ∈ blockAFin m with ¬pcutWitness m x = true, (-1 : ℤ) := by
              apply Finset.sum_congr rfl
              intro x hx
              simp only [Finset.mem_filter] at hx
              simp [hx.2]
      _ = -((m - 1) / 2 : ℤ) := by
              simp [Bool.not_eq_true, hFalseCard]
              rcases hOdd with ⟨k, rfl⟩
              norm_num
  rw [hT, hF]
  rcases hOdd with ⟨k, rfl⟩
  omega

private lemma blockSumB_pcutWitness (m : ℕ) (hOdd : Odd m) :
    blockSumB m (pcutWitness m) = -1 := by
  change (∑ i ∈ blockBFin m, (if pcutWitness m i = true then (1 : ℤ) else -1)) = -1
  have hTrueCardBool :
      ((blockBFin m).filter (fun i => pcutWitness m i)).card = (m - 1) / 2 := by
    rw [pcutB_true_filter m hOdd]
    apply card_fin_interval_from_m_parity
    exact half_down_le m
  have hTrueCard : ((blockBFin m).filter (fun i => pcutWitness m i = true)).card
      = (m - 1) / 2 := by
    simpa using hTrueCardBool
  have hFalseCard : ((blockBFin m).filter (fun i => pcutWitness m i = false)).card
      = (m + 1) / 2 := by
    have hsum := Finset.card_filter_add_card_filter_not (s := blockBFin m)
      (p := fun i => pcutWitness m i = true)
    rw [hTrueCard, card_blockBFin] at hsum
    have hfalseNot :
        ((blockBFin m).filter (fun i => ¬ pcutWitness m i = true)).card = (m + 1) / 2 := by
      rcases hOdd with ⟨k, rfl⟩
      omega
    simpa [Bool.not_eq_true] using hfalseNot
  rw [← Finset.sum_filter_add_sum_filter_not (s := blockBFin m)
    (p := fun i => pcutWitness m i = true)
    (f := fun i => if pcutWitness m i = true then (1 : ℤ) else -1)]
  have hT : (∑ x ∈ blockBFin m with pcutWitness m x = true,
      if pcutWitness m x = true then (1 : ℤ) else -1) = ((m - 1) / 2 : ℤ) := by
    calc
      (∑ x ∈ blockBFin m with pcutWitness m x = true,
          if pcutWitness m x = true then (1 : ℤ) else -1)
          = ∑ x ∈ blockBFin m with pcutWitness m x = true, (1 : ℤ) := by
              apply Finset.sum_congr rfl
              intro x hx
              simp only [Finset.mem_filter] at hx
              simp [hx.2]
      _ = ((m - 1) / 2 : ℤ) := by
              simp [hTrueCard]
              rcases hOdd with ⟨k, rfl⟩
              norm_num
  have hF : (∑ x ∈ blockBFin m with ¬pcutWitness m x = true,
      if pcutWitness m x = true then (1 : ℤ) else -1) = -((m + 1) / 2 : ℤ) := by
    calc
      (∑ x ∈ blockBFin m with ¬pcutWitness m x = true,
          if pcutWitness m x = true then (1 : ℤ) else -1)
          = ∑ x ∈ blockBFin m with ¬pcutWitness m x = true, (-1 : ℤ) := by
              apply Finset.sum_congr rfl
              intro x hx
              simp only [Finset.mem_filter] at hx
              simp [hx.2]
      _ = -((m + 1) / 2 : ℤ) := by
              simp [Bool.not_eq_true, hFalseCard]
  rw [hT, hF]
  rcases hOdd with ⟨k, rfl⟩
  omega

private lemma blockSumA_pallWitness (m : ℕ) (hOdd : Odd m) :
    blockSumA m (pallWitness m) = 1 := by
  change (∑ i ∈ blockAFin m, (if pallWitness m i = true then (1 : ℤ) else -1)) = 1
  have hTrueCardBool :
      ((blockAFin m).filter (fun i => pallWitness m i)).card = (m + 1) / 2 := by
    rw [pallA_true_filter m hOdd]
    apply card_fin_lt_parity
    omega
  have hTrueCard : ((blockAFin m).filter (fun i => pallWitness m i = true)).card
      = (m + 1) / 2 := by
    simpa using hTrueCardBool
  have hFalseCard : ((blockAFin m).filter (fun i => pallWitness m i = false)).card
      = (m - 1) / 2 := by
    have hsum := Finset.card_filter_add_card_filter_not (s := blockAFin m)
      (p := fun i => pallWitness m i = true)
    rw [hTrueCard, card_blockAFin] at hsum
    have hfalseNot :
        ((blockAFin m).filter (fun i => ¬ pallWitness m i = true)).card = (m - 1) / 2 := by
      rcases hOdd with ⟨k, rfl⟩
      omega
    simpa [Bool.not_eq_true] using hfalseNot
  rw [← Finset.sum_filter_add_sum_filter_not (s := blockAFin m)
    (p := fun i => pallWitness m i = true)
    (f := fun i => if pallWitness m i = true then (1 : ℤ) else -1)]
  have hT : (∑ x ∈ blockAFin m with pallWitness m x = true,
      if pallWitness m x = true then (1 : ℤ) else -1) = ((m + 1) / 2 : ℤ) := by
    calc
      (∑ x ∈ blockAFin m with pallWitness m x = true,
          if pallWitness m x = true then (1 : ℤ) else -1)
          = ∑ x ∈ blockAFin m with pallWitness m x = true, (1 : ℤ) := by
              apply Finset.sum_congr rfl
              intro x hx
              simp only [Finset.mem_filter] at hx
              simp [hx.2]
      _ = ((m + 1) / 2 : ℤ) := by
              simp [hTrueCard]
  have hF : (∑ x ∈ blockAFin m with ¬pallWitness m x = true,
      if pallWitness m x = true then (1 : ℤ) else -1) = -((m - 1) / 2 : ℤ) := by
    calc
      (∑ x ∈ blockAFin m with ¬pallWitness m x = true,
          if pallWitness m x = true then (1 : ℤ) else -1)
          = ∑ x ∈ blockAFin m with ¬pallWitness m x = true, (-1 : ℤ) := by
              apply Finset.sum_congr rfl
              intro x hx
              simp only [Finset.mem_filter] at hx
              simp [hx.2]
      _ = -((m - 1) / 2 : ℤ) := by
              simp [Bool.not_eq_true, hFalseCard]
              rcases hOdd with ⟨k, rfl⟩
              norm_num
  rw [hT, hF]
  rcases hOdd with ⟨k, rfl⟩
  omega

private lemma blockSumB_pallWitness (m : ℕ) (hOdd : Odd m) :
    blockSumB m (pallWitness m) = 1 := by
  change (∑ i ∈ blockBFin m, (if pallWitness m i = true then (1 : ℤ) else -1)) = 1
  have hTrueCardBool :
      ((blockBFin m).filter (fun i => pallWitness m i)).card = (m + 1) / 2 := by
    rw [pallB_true_filter m]
    apply card_fin_interval_from_m_parity
    exact half_up_le_of_odd m hOdd
  have hTrueCard : ((blockBFin m).filter (fun i => pallWitness m i = true)).card
      = (m + 1) / 2 := by
    simpa using hTrueCardBool
  have hFalseCard : ((blockBFin m).filter (fun i => pallWitness m i = false)).card
      = (m - 1) / 2 := by
    have hsum := Finset.card_filter_add_card_filter_not (s := blockBFin m)
      (p := fun i => pallWitness m i = true)
    rw [hTrueCard, card_blockBFin] at hsum
    have hfalseNot :
        ((blockBFin m).filter (fun i => ¬ pallWitness m i = true)).card = (m - 1) / 2 := by
      rcases hOdd with ⟨k, rfl⟩
      omega
    simpa [Bool.not_eq_true] using hfalseNot
  rw [← Finset.sum_filter_add_sum_filter_not (s := blockBFin m)
    (p := fun i => pallWitness m i = true)
    (f := fun i => if pallWitness m i = true then (1 : ℤ) else -1)]
  have hT : (∑ x ∈ blockBFin m with pallWitness m x = true,
      if pallWitness m x = true then (1 : ℤ) else -1) = ((m + 1) / 2 : ℤ) := by
    calc
      (∑ x ∈ blockBFin m with pallWitness m x = true,
          if pallWitness m x = true then (1 : ℤ) else -1)
          = ∑ x ∈ blockBFin m with pallWitness m x = true, (1 : ℤ) := by
              apply Finset.sum_congr rfl
              intro x hx
              simp only [Finset.mem_filter] at hx
              simp [hx.2]
      _ = ((m + 1) / 2 : ℤ) := by
              simp [hTrueCard]
  have hF : (∑ x ∈ blockBFin m with ¬pallWitness m x = true,
      if pallWitness m x = true then (1 : ℤ) else -1) = -((m - 1) / 2 : ℤ) := by
    calc
      (∑ x ∈ blockBFin m with ¬pallWitness m x = true,
          if pallWitness m x = true then (1 : ℤ) else -1)
          = ∑ x ∈ blockBFin m with ¬pallWitness m x = true, (-1 : ℤ) := by
              apply Finset.sum_congr rfl
              intro x hx
              simp only [Finset.mem_filter] at hx
              simp [hx.2]
      _ = -((m - 1) / 2 : ℤ) := by
              simp [Bool.not_eq_true, hFalseCard]
              rcases hOdd with ⟨k, rfl⟩
              norm_num
  rw [hT, hF]
  rcases hOdd with ⟨k, rfl⟩
  omega

lemma pcutSupport_nonempty (m : ℕ) (hOdd : Odd m) : (pcutSupport m).Nonempty := by
  refine ⟨pcutWitness m, ?_⟩
  simp [pcutSupport, blockSumA_pcutWitness m hOdd, blockSumB_pcutWitness m hOdd]

lemma pallSupport_nonempty (m : ℕ) (hOdd : Odd m) : (pallSupport m).Nonempty := by
  refine ⟨pallWitness m, ?_⟩
  simp [pallSupport, blockSumA_pallWitness m hOdd, blockSumB_pallWitness m hOdd]

/-- The `pcut` parity design. -/
noncomputable def pcutVDesign (m : ℕ) (hOdd : Odd m) : FiniteDesign (Fin (2 * m) → Bool) :=
  uniformOnDesign m (pcutSupport m) (pcutSupport_nonempty m hOdd)

/-- The `pall` parity design. -/
noncomputable def pallVDesign (m : ℕ) (hOdd : Odd m) : FiniteDesign (Fin (2 * m) → Bool) :=
  uniformOnDesign m (pallSupport m) (pallSupport_nonempty m hOdd)

lemma pcutVDesign_mem (m : ℕ) (hOdd : Odd m) :
    pcutVDesign m hOdd ∈ blockExchangeableDesignClass m := by
  unfold pcutVDesign
  apply uniformOnDesign_mem
  · intro z
    simp only [pcutSupport, Finset.mem_filter, Finset.mem_univ, true_and, blockSumA_neg,
      blockSumB_neg]
    constructor
    · intro hz
      rcases hz with ⟨hA, hB⟩ | ⟨hA, hB⟩
      · right
        constructor <;> omega
      · left
        constructor <;> omega
    · intro hz
      rcases hz with ⟨hA, hB⟩ | ⟨hA, hB⟩
      · right
        constructor <;> omega
      · left
        constructor <;> omega
  · intro σ hσ z
    rcases blockSum_reindex m σ hσ z with h | h
    · simp [pcutSupport, h.1, h.2]
    · simp only [pcutSupport, Finset.mem_filter, Finset.mem_univ, true_and, h.1, h.2]
      constructor
      · intro hz
        rcases hz with ⟨hB, hA⟩ | ⟨hB, hA⟩
        · right
          exact ⟨hA, hB⟩
        · left
          exact ⟨hA, hB⟩
      · intro hz
        rcases hz with ⟨hA, hB⟩ | ⟨hA, hB⟩
        · right
          exact ⟨hB, hA⟩
        · left
          exact ⟨hB, hA⟩

lemma pallVDesign_mem (m : ℕ) (hOdd : Odd m) :
    pallVDesign m hOdd ∈ blockExchangeableDesignClass m := by
  unfold pallVDesign
  apply uniformOnDesign_mem
  · intro z
    simp only [pallSupport, Finset.mem_filter, Finset.mem_univ, true_and, blockSumA_neg,
      blockSumB_neg]
    constructor
    · intro hz
      rcases hz with ⟨hA, hB⟩ | ⟨hA, hB⟩
      · right
        constructor <;> omega
      · left
        constructor <;> omega
    · intro hz
      rcases hz with ⟨hA, hB⟩ | ⟨hA, hB⟩
      · right
        constructor <;> omega
      · left
        constructor <;> omega
  · intro σ hσ z
    rcases blockSum_reindex m σ hσ z with h | h
    · simp [pallSupport, h.1, h.2]
    · simp [pallSupport, h.1, h.2, and_comm]

private lemma sumAr_eq_blockSumA_cast_parity (m : ℕ) (z : Fin (2 * m) → Bool) :
    sumAr m z = (blockSumA m z : ℝ) := by
  simp [sumAr, blockSumA, blockAFin, signOf]

private lemma sumBr_eq_blockSumB_cast_parity (m : ℕ) (z : Fin (2 * m) → Bool) :
    sumBr m z = (blockSumB m z : ℝ) := by
  simp [sumBr, blockSumB, blockBFin, signOf]

private lemma uniformOnDesign_E_eq_const (m : ℕ) (S : Finset (Fin (2 * m) → Bool))
    (hS : S.Nonempty) (f : (Fin (2 * m) → Bool) → ℝ) (c : ℝ)
    (hf : ∀ z, z ∈ S → f z = c) :
    (uniformOnDesign m S hS).E f = c := by
  calc
    (uniformOnDesign m S hS).E f = (uniformOnDesign m S hS).E (fun _ => c) := by
      rw [FiniteDesign.E, FiniteDesign.E]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z ∈ S
      · simp [uniformOnDesign, hz, hf z hz]
      · simp [uniformOnDesign, hz]
    _ = c := by
      rw [(uniformOnDesign m S hS).E_const c]

/-- On `pcutSupport`, `S_A² = 1`, so `E[S_A²] = 1`. -/
lemma pcutVDesign_sumAr_sq (m : ℕ) (hOdd : Odd m) :
    (pcutVDesign m hOdd).E (fun z => sumAr m z * sumAr m z) = 1 := by
  unfold pcutVDesign
  apply uniformOnDesign_E_eq_const
  intro z hz
  have hzmem :
      (blockSumA m z = 1 ∧ blockSumB m z = -1) ∨
        (blockSumA m z = -1 ∧ blockSumB m z = 1) := by
    simpa [pcutSupport] using hz
  rw [sumAr_eq_blockSumA_cast_parity]
  rcases hzmem with h | h <;> rw [h.1] <;> norm_num

/-- On `pcutSupport`, `S_A S_B = -1`. -/
lemma pcutVDesign_sumAr_sumBr (m : ℕ) (hOdd : Odd m) :
    (pcutVDesign m hOdd).E (fun z => sumAr m z * sumBr m z) = -1 := by
  unfold pcutVDesign
  apply uniformOnDesign_E_eq_const
  intro z hz
  have hzmem :
      (blockSumA m z = 1 ∧ blockSumB m z = -1) ∨
        (blockSumA m z = -1 ∧ blockSumB m z = 1) := by
    simpa [pcutSupport] using hz
  rw [sumAr_eq_blockSumA_cast_parity, sumBr_eq_blockSumB_cast_parity]
  rcases hzmem with h | h <;> rw [h.1, h.2] <;> norm_num

lemma pallVDesign_sumAr_sq (m : ℕ) (hOdd : Odd m) :
    (pallVDesign m hOdd).E (fun z => sumAr m z * sumAr m z) = 1 := by
  unfold pallVDesign
  apply uniformOnDesign_E_eq_const
  intro z hz
  have hzmem :
      (blockSumA m z = 1 ∧ blockSumB m z = 1) ∨
        (blockSumA m z = -1 ∧ blockSumB m z = -1) := by
    simpa [pallSupport] using hz
  rw [sumAr_eq_blockSumA_cast_parity]
  rcases hzmem with h | h <;> rw [h.1] <;> norm_num

lemma pallVDesign_sumAr_sumBr (m : ℕ) (hOdd : Odd m) :
    (pallVDesign m hOdd).E (fun z => sumAr m z * sumBr m z) = 1 := by
  unfold pallVDesign
  apply uniformOnDesign_E_eq_const
  intro z hz
  have hzmem :
      (blockSumA m z = 1 ∧ blockSumB m z = 1) ∨
        (blockSumA m z = -1 ∧ blockSumB m z = -1) := by
    simpa [pallSupport] using hz
  rw [sumAr_eq_blockSumA_cast_parity, sumBr_eq_blockSumB_cast_parity]
  rcases hzmem with h | h <;> rw [h.1, h.2] <;> norm_num

lemma pcutVDesign_secondMoment (m : ℕ) (hm : 2 ≤ m) (hOdd : Odd m) :
    assignmentSecondMoment m (pcutVDesign m hOdd)
      = blockSymMatrix m (-1 / (m : ℝ)) (-1 / (m : ℝ) ^ 2) := by
  rcases secondMoment_blockSym_of_exchangeable m hm (pcutVDesign m hOdd)
      (pcutVDesign_mem m hOdd) with ⟨u, v, hUV⟩
  have hEqU : (m : ℝ) + (m : ℝ) * ((m : ℝ) - 1) * u = 1 := by
    rw [← E_sumAr_sq m u v (pcutVDesign m hOdd) hUV, pcutVDesign_sumAr_sq]
  have hEqV : (m : ℝ) ^ 2 * v = -1 := by
    rw [← E_sumAr_sumBr m u v (pcutVDesign m hOdd) hUV,
      pcutVDesign_sumAr_sumBr]
  have hmposR : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm)
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmposR
  have hmgt1 : (1 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hm)
  have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
  have huProd : ((m : ℝ) - 1) * ((m : ℝ) * u + 1) = 0 := by
    nlinarith [hEqU]
  have hlin : (m : ℝ) * u + 1 = 0 := (mul_eq_zero.mp huProd).resolve_left hm1
  have hu : u = -1 / (m : ℝ) := by
    field_simp [hm0]
    linarith
  have hv : v = -1 / (m : ℝ) ^ 2 := by
    have hm2 : (m : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hm0
    field_simp [hm2]
    nlinarith
  rw [hUV, hu, hv]

lemma pallVDesign_secondMoment (m : ℕ) (hm : 2 ≤ m) (hOdd : Odd m) :
    assignmentSecondMoment m (pallVDesign m hOdd)
      = blockSymMatrix m (-1 / (m : ℝ)) (1 / (m : ℝ) ^ 2) := by
  rcases secondMoment_blockSym_of_exchangeable m hm (pallVDesign m hOdd)
      (pallVDesign_mem m hOdd) with ⟨u, v, hUV⟩
  have hEqU : (m : ℝ) + (m : ℝ) * ((m : ℝ) - 1) * u = 1 := by
    rw [← E_sumAr_sq m u v (pallVDesign m hOdd) hUV, pallVDesign_sumAr_sq]
  have hEqV : (m : ℝ) ^ 2 * v = 1 := by
    rw [← E_sumAr_sumBr m u v (pallVDesign m hOdd) hUV,
      pallVDesign_sumAr_sumBr]
  have hmposR : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm)
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmposR
  have hmgt1 : (1 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hm)
  have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
  have huProd : ((m : ℝ) - 1) * ((m : ℝ) * u + 1) = 0 := by
    nlinarith [hEqU]
  have hlin : (m : ℝ) * u + 1 = 0 := (mul_eq_zero.mp huProd).resolve_left hm1
  have hu : u = -1 / (m : ℝ) := by
    field_simp [hm0]
    linarith
  have hv : v = 1 / (m : ℝ) ^ 2 := by
    have hm2 : (m : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hm0
    field_simp [hm2]
    nlinarith
  rw [hUV, hu, hv]

private lemma parity_lam_inner_eq (m : ℕ) (hm : 2 ≤ m) (s : ℝ) :
    ((s - 2 / (m : ℝ)) / (2 * (m : ℝ) - 2 / (m : ℝ))) +
        (1 - ((s - 2 / (m : ℝ)) / (2 * (m : ℝ) - 2 / (m : ℝ)))) /
          (m : ℝ) ^ 2
      = s / (2 * (m : ℝ)) := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hsq : (m : ℝ) ^ 2 - 1 ≠ 0 := by
    nlinarith [hmR]
  have hden : 2 * (m : ℝ) - 2 / (m : ℝ) ≠ 0 := by
    intro h
    have hmul := congrArg (fun t : ℝ => t * (m : ℝ)) h
    field_simp [hm0] at hmul
    nlinarith [hsq]
  field_simp [hm0, hden, hsq]
  ring

private lemma parity_lam_outer_eq_u (m : ℕ) (hm : 2 ≤ m) (u s : ℝ)
    (htrace : 2 * ((m : ℝ) - 1) * (1 - u) + s = 2 * (m : ℝ)) :
    ((s - 2 / (m : ℝ)) / (2 * (m : ℝ) - 2 / (m : ℝ))) +
        (1 - ((s - 2 / (m : ℝ)) / (2 * (m : ℝ) - 2 / (m : ℝ)))) *
          (-1 / (m : ℝ))
      = u := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hsq : (m : ℝ) ^ 2 - 1 ≠ 0 := by
    nlinarith [hmR]
  have hden : 2 * (m : ℝ) - 2 / (m : ℝ) ≠ 0 := by
    intro h
    have hmul := congrArg (fun t : ℝ => t * (m : ℝ)) h
    field_simp [hm0] at hmul
    nlinarith [hsq]
  field_simp [hm0, hden, hsq]
  nlinarith [htrace]

private lemma parity_mu_diff (y z s : ℝ) (hs0 : s ≠ 0) (hs : s = y + z) :
    1 - 2 * (y / s) = (z - y) / s := by
  field_simp [hs0]
  nlinarith [hs]

private lemma parity_v_eq_z_sub_y (m : ℕ) (hm : 2 ≤ m) (u v y z : ℝ)
    (hydef : y = 1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
    (hzdef : z = 1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) :
    v = (z - y) / (2 * (m : ℝ)) := by
  have hm0 : (m : ℝ) ≠ 0 := by
    have hmpos : 0 < (m : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm)
    exact ne_of_gt hmpos
  have hzy : z - y = 2 * (m : ℝ) * v := by
    nlinarith [hydef, hzdef]
  field_simp [hm0]
  nlinarith [hzy]

/-- Backward direction, odd `m`: the 4-vertex quadrilateral mixture. -/
lemma pm_slice_backward_odd (m : ℕ) (hm : 2 ≤ m) (hOdd : Odd m) (u v : ℝ)
    (htri : InReducedTriangle m (1 - u) (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
        (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v))
    (hpar : parityThreshold m ≤ (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
        + (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v)) :
    blockSymMatrix m u v ∈ implementableCovarianceClass m := by
  obtain ⟨hx, hy, hz, htrace⟩ := htri
  set x : ℝ := 1 - u with hxdef
  set y : ℝ := 1 + ((m : ℝ) - 1) * u - (m : ℝ) * v with hydef
  set z : ℝ := 1 + ((m : ℝ) - 1) * u + (m : ℝ) * v with hzdef
  set s : ℝ := y + z with hsdef
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0pos : 0 < (m : ℝ) := by linarith
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hm0pos
  have hm1pos : 0 < (m : ℝ) - 1 := by linarith
  have hden_pos : 0 < 2 * (m : ℝ) - 2 / (m : ℝ) := by
    field_simp [hm0]
    nlinarith [hmR]
  have hnotEven : ¬ Even m := Nat.not_even_iff_odd.mpr hOdd
  have hpar_s : 2 / (m : ℝ) ≤ s := by
    simpa [parityThreshold, hnotEven, hsdef, hydef, hzdef] using hpar
  have hs_pos : 0 < s := by
    have htwo : 0 < 2 / (m : ℝ) := by positivity
    linarith
  have hs_le : s ≤ 2 * (m : ℝ) := by
    have hqp_nonneg : 0 ≤ qParam m * x := by
      apply mul_nonneg
      · simp [qParam]
        linarith
      · exact hx
    nlinarith [htrace, hsdef, hqp_nonneg]
  let mu : ℝ := y / s
  let lam : ℝ := (s - 2 / (m : ℝ)) / (2 * (m : ℝ) - 2 / (m : ℝ))
  let w : Fin 4 → ℝ := ![lam * mu, lam * (1 - mu), (1 - lam) * mu,
    (1 - lam) * (1 - mu)]
  let Ds : Fin 4 → FiniteDesign (Fin (2 * m) → Bool) :=
    ![cutVDesign m, allVDesign m, pcutVDesign m hOdd, pallVDesign m hOdd]
  let uu : Fin 4 → ℝ := ![1, 1, -1 / (m : ℝ), -1 / (m : ℝ)]
  let vv : Fin 4 → ℝ := ![-1, 1, -1 / (m : ℝ) ^ 2, 1 / (m : ℝ) ^ 2]
  have hmu0 : 0 ≤ mu := by
    exact div_nonneg hy (le_of_lt hs_pos)
  have hmu1 : mu ≤ 1 := by
    dsimp [mu]
    field_simp [hs_pos.ne']
    nlinarith [hsdef, hz]
  have h1mu0 : 0 ≤ 1 - mu := by linarith
  have hlam0 : 0 ≤ lam := by
    dsimp [lam]
    exact div_nonneg (sub_nonneg.mpr hpar_s) (le_of_lt hden_pos)
  have hlam1 : lam ≤ 1 := by
    dsimp [lam]
    rw [div_le_one hden_pos]
    nlinarith [hpar_s, hs_le]
  have h1lam0 : 0 ≤ 1 - lam := by linarith
  have hw0 : ∀ i, 0 ≤ w i := by
    intro i
    fin_cases i <;> simp only [w, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    · exact mul_nonneg hlam0 hmu0
    · exact mul_nonneg hlam0 h1mu0
    · exact mul_nonneg h1lam0 hmu0
    · exact mul_nonneg h1lam0 h1mu0
  have hw1 : ∑ i, w i = 1 := by
    simp only [w, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    ring
  refine ⟨mixtureDesign m w Ds hw0 hw1, mixtureDesign_mem m w Ds hw0 hw1 ?_, ?_⟩
  · intro i
    fin_cases i <;> simp only [Ds, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    · exact cutVDesign_mem m
    · exact allVDesign_mem m
    · exact pcutVDesign_mem m hOdd
    · exact pallVDesign_mem m hOdd
  · have hSM := mixtureDesign_secondMoment m w Ds hw0 hw1 uu vv ?_
    · rw [hSM]
      congr 1
      · simp only [w, uu, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
        have htrace' : 2 * ((m : ℝ) - 1) * (1 - u) + s = 2 * (m : ℝ) := by
          simp [qParam] at htrace
          nlinarith [htrace, hsdef, hxdef]
        have hlam_u : lam + (1 - lam) * (-1 / (m : ℝ)) = u := by
          exact parity_lam_outer_eq_u m hm u s htrace'
        rw [← hlam_u]
        ring
      · simp only [w, vv, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
        have hcollapse :
            lam * mu * (-1) + lam * (1 - mu) * 1 +
                (1 - lam) * mu * (-1 / (m : ℝ) ^ 2) +
              (1 - lam) * (1 - mu) * (1 / (m : ℝ) ^ 2)
            = (1 - 2 * mu) * (lam + (1 - lam) / (m : ℝ) ^ 2) := by
          ring
        rw [hcollapse]
        have hmu_diff : 1 - 2 * mu = (z - y) / s := by
          exact parity_mu_diff y z s hs_pos.ne' hsdef
        have hlamid : lam + (1 - lam) / (m : ℝ) ^ 2 = s / (2 * (m : ℝ)) := by
          exact parity_lam_inner_eq m hm s
        have hv_yz : v = (z - y) / (2 * (m : ℝ)) := by
          exact parity_v_eq_z_sub_y m hm u v y z hydef hzdef
        calc
          v = (z - y) / (2 * (m : ℝ)) := hv_yz
          _ = ((z - y) / s) * (s / (2 * (m : ℝ))) := by
            field_simp [hm0, hs_pos.ne']
          _ = (1 - 2 * mu) * (lam + (1 - lam) / (m : ℝ) ^ 2) := by
            rw [← hmu_diff, ← hlamid]
    · intro i
      fin_cases i <;> simp only [Ds, uu, vv, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
      · exact cutVDesign_secondMoment m
      · exact allVDesign_secondMoment m
      · exact pcutVDesign_secondMoment m hm hOdd
      · exact pallVDesign_secondMoment m hm hOdd

end CausalSmith.Experimentation.DesignPm1
