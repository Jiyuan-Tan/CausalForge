/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.ParitySliceMixture

set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

/-! # Vertex designs for the backward direction

Explicit block-exchangeable designs realizing the triangle vertices:

* `cutVDesign`  — `X(1,−1)`,  reduced `(0, 2m, 0)` (uniform on `{s_m, −s_m}`);
* `allVDesign`  — `X(1, 1)`,  reduced `(0, 0, 2m)` (uniform on `{1, −1}` assignments);
* `spreadVDesign` (even `m`) — `X(−1/(m−1), 0)`, reduced `(2m/q, 0, 0)` (uniform on
  the balanced-in-each-block assignments, second moment via block symmetry and the
  deterministic block sums `S_A = S_B = 0`).

The block-sum transport lemmas (`blockSumA` under negation and block automorphism)
supply the support-invariance the class membership needs. -/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators
open Causalean.Experimentation.DesignBased

/-! ## Block-sum transport -/

/-- Negating an assignment negates each community sum. -/
lemma blockSumA_neg (m : ℕ) (z : Fin (2 * m) → Bool) :
    blockSumA m (fun i => ! z i) = - blockSumA m z := by
  unfold blockSumA
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : z i <;> simp [h]

/-- Negating an assignment negates the community-`B` sign sum, the mirror of
`blockSumA_neg`. Together the two make every sign-symmetric support closed under
global negation, which is what the balanced-design membership proofs need. -/
lemma blockSumB_neg (m : ℕ) (z : Fin (2 * m) → Bool) :
    blockSumB m (fun i => ! z i) = - blockSumB m z := by
  unfold blockSumB
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : z i <;> simp [h]

private lemma blockSumA_eq_total (m : ℕ) (z : Fin (2 * m) → Bool) :
    blockSumA m z =
      ∑ i : Fin (2 * m), if i.val < m then (if z i then (1 : ℤ) else -1) else 0 := by
  unfold blockSumA
  rw [Finset.sum_filter]

private lemma blockSumB_eq_total (m : ℕ) (z : Fin (2 * m) → Bool) :
    blockSumB m z =
      ∑ i : Fin (2 * m), if ¬ i.val < m then (if z i then (1 : ℤ) else -1) else 0 := by
  unfold blockSumB
  rw [Finset.sum_filter]

private lemma blockSumA_reindex_pres (m : ℕ) (σ : Equiv.Perm (Fin (2 * m)))
    (hpres : ∀ i, ((σ i).val < m ↔ i.val < m)) (z : Fin (2 * m) → Bool) :
    blockSumA m (reindexBy m σ z) = blockSumA m z := by
  rw [blockSumA_eq_total, blockSumA_eq_total]
  have hsum := σ.sum_comp Finset.univ
    (fun i : Fin (2 * m) => if i.val < m then (if z i then (1 : ℤ) else -1) else 0)
    (by intro x hx; simp)
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsum
  exact if_congr (by simp [hpres i]) rfl rfl

private lemma blockSumB_reindex_pres (m : ℕ) (σ : Equiv.Perm (Fin (2 * m)))
    (hpres : ∀ i, ((σ i).val < m ↔ i.val < m)) (z : Fin (2 * m) → Bool) :
    blockSumB m (reindexBy m σ z) = blockSumB m z := by
  rw [blockSumB_eq_total, blockSumB_eq_total]
  have hsum := σ.sum_comp Finset.univ
    (fun i : Fin (2 * m) => if ¬ i.val < m then (if z i then (1 : ℤ) else -1) else 0)
    (by intro x hx; simp)
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsum
  exact if_congr (by simp [hpres i]) rfl rfl

private lemma blockSumA_reindex_swap (m : ℕ) (σ : Equiv.Perm (Fin (2 * m)))
    (hswap : ∀ i, ((σ i).val < m ↔ ¬ i.val < m)) (z : Fin (2 * m) → Bool) :
    blockSumA m (reindexBy m σ z) = blockSumB m z := by
  rw [blockSumA_eq_total, blockSumB_eq_total]
  have hsum := σ.sum_comp Finset.univ
    (fun i : Fin (2 * m) => if ¬ i.val < m then (if z i then (1 : ℤ) else -1) else 0)
    (by intro x hx; simp)
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsum
  exact if_congr (by simp [hswap i]) rfl rfl

private lemma blockSumB_reindex_swap (m : ℕ) (σ : Equiv.Perm (Fin (2 * m)))
    (hswap : ∀ i, ((σ i).val < m ↔ ¬ i.val < m)) (z : Fin (2 * m) → Bool) :
    blockSumB m (reindexBy m σ z) = blockSumA m z := by
  rw [blockSumB_eq_total, blockSumA_eq_total]
  have hsum := σ.sum_comp Finset.univ
    (fun i : Fin (2 * m) => if i.val < m then (if z i then (1 : ℤ) else -1) else 0)
    (by intro x hx; simp)
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsum
  exact if_congr (by simp [hswap i]) rfl rfl

/-- Under a block-automorphism `σ`, the pair of community sums of `reindexBy σ z`
is either `(S_A, S_B)` (block-preserving) or `(S_B, S_A)` (block-swapping). -/
lemma blockSum_reindex (m : ℕ) (σ : Equiv.Perm (Fin (2 * m))) (hσ : IsBlockAuto m σ)
    (z : Fin (2 * m) → Bool) :
    (blockSumA m (reindexBy m σ z) = blockSumA m z ∧
        blockSumB m (reindexBy m σ z) = blockSumB m z) ∨
    (blockSumA m (reindexBy m σ z) = blockSumB m z ∧
        blockSumB m (reindexBy m σ z) = blockSumA m z) := by
  rcases hσ with hpres | hswap
  · left
    exact ⟨blockSumA_reindex_pres m σ hpres z, blockSumB_reindex_pres m σ hpres z⟩
  · right
    exact ⟨blockSumA_reindex_swap m σ hswap z, blockSumB_reindex_swap m σ hswap z⟩

/-! ## Two-point (cut / all) designs -/

/-- Expectation under the uniform law on a two-element support `{z₁, z₂}`. -/
lemma uniformOnDesign_two_E (m : ℕ) (z₁ z₂ : Fin (2 * m) → Bool) (hne : z₁ ≠ z₂)
    (f : (Fin (2 * m) → Bool) → ℝ) :
    (uniformOnDesign m {z₁, z₂} ⟨z₁, by simp⟩).E f = (f z₁ + f z₂) / 2 := by
  rw [FiniteDesign.E]
  have hcard : ({z₁, z₂} : Finset (Fin (2 * m) → Bool)).card = 2 := by
    simp [hne]
  simp only [uniformOnDesign]
  rw [hcard]
  calc
    (∑ x, (if x ∈ ({z₁, z₂} : Finset (Fin (2 * m) → Bool)) then (2 : ℝ)⁻¹ else 0)
        * f x)
        = ∑ x, ((if x = z₁ then (2 : ℝ)⁻¹ * f x else 0) +
            (if x = z₂ then (2 : ℝ)⁻¹ * f x else 0)) := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases h1 : x = z₁
            · simp [h1, hne]
            · by_cases h2 : x = z₂
              · simp [h2, hne.symm]
              · simp [h1, h2]
    _ = (∑ x, if x = z₁ then (2 : ℝ)⁻¹ * f x else 0) +
          (∑ x, if x = z₂ then (2 : ℝ)⁻¹ * f x else 0) := by
            rw [Finset.sum_add_distrib]
    _ = (f z₁ + f z₂) / 2 := by
            simp [Finset.sum_ite_eq']
            ring

/-- The cut vertex design `½δ_{s_m} + ½δ_{−s_m}`. -/
noncomputable def cutVDesign (m : ℕ) : FiniteDesign (Fin (2 * m) → Bool) :=
  uniformOnDesign m {cutPlus m, cutMinus m} ⟨cutPlus m, by simp⟩

/-- The all-ones vertex design `½δ_{1} + ½δ_{−1}`. -/
noncomputable def allVDesign (m : ℕ) : FiniteDesign (Fin (2 * m) → Bool) :=
  uniformOnDesign m {(fun _ => true), (fun _ => false)} ⟨fun _ => true, by simp⟩

private lemma neg_cutPlus (m : ℕ) : (fun i => ! cutPlus m i) = cutMinus m := by
  funext i
  unfold cutPlus cutMinus
  by_cases h : i.val < m <;> simp [h]

private lemma neg_cutMinus (m : ℕ) : (fun i => ! cutMinus m i) = cutPlus m := by
  funext i
  unfold cutPlus cutMinus
  by_cases h : i.val < m <;> simp [h]

private lemma reindex_cutPlus_pres (m : ℕ) (σ : Equiv.Perm (Fin (2 * m)))
    (hpres : ∀ i, ((σ i).val < m ↔ i.val < m)) :
    reindexBy m σ (cutPlus m) = cutPlus m := by
  funext i
  simp [reindexBy, cutPlus, hpres i]

private lemma reindex_cutMinus_pres (m : ℕ) (σ : Equiv.Perm (Fin (2 * m)))
    (hpres : ∀ i, ((σ i).val < m ↔ i.val < m)) :
    reindexBy m σ (cutMinus m) = cutMinus m := by
  funext i
  simp [reindexBy, cutMinus, hpres i]

private lemma reindex_cutPlus_swap (m : ℕ) (σ : Equiv.Perm (Fin (2 * m)))
    (hswap : ∀ i, ((σ i).val < m ↔ ¬ i.val < m)) :
    reindexBy m σ (cutPlus m) = cutMinus m := by
  funext i
  simp [reindexBy, cutPlus, cutMinus, hswap i]

private lemma reindex_cutMinus_swap (m : ℕ) (σ : Equiv.Perm (Fin (2 * m)))
    (hswap : ∀ i, ((σ i).val < m ↔ ¬ i.val < m)) :
    reindexBy m σ (cutMinus m) = cutPlus m := by
  funext i
  simp [reindexBy, cutPlus, cutMinus, hswap i]

private lemma reindexBy_injective (m : ℕ) (σ : Equiv.Perm (Fin (2 * m))) :
    Function.Injective (reindexBy m σ) := by
  intro z₁ z₂ h
  funext i
  have h' := congrFun h (σ.symm i)
  simpa [reindexBy] using h'

private lemma reindex_const_true (m : ℕ) (σ : Equiv.Perm (Fin (2 * m))) :
    reindexBy m σ (fun _ => true) = (fun _ => true) := by
  funext i
  rfl

private lemma reindex_const_false (m : ℕ) (σ : Equiv.Perm (Fin (2 * m))) :
    reindexBy m σ (fun _ => false) = (fun _ => false) := by
  funext i
  rfl

/-- The cut vertex design — a fair coin between "treat community `A`, control community
`B`" and its reverse — belongs to the block-exchangeable design class: its two-point
support is closed under global sign flip and under every two-block automorphism
(relabelling units inside a community fixes each of the two assignments, swapping the
communities exchanges them). -/
lemma cutVDesign_mem (m : ℕ) : cutVDesign m ∈ blockExchangeableDesignClass m := by
  unfold cutVDesign
  apply uniformOnDesign_mem
  · intro z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hz
      rcases hz with hz | hz
      · right
        funext i
        have hpoint := congrFun hz i
        change z i = decide (¬ i.val < m)
        change (!(z i)) = decide (i.val < m) at hpoint
        by_cases h : i.val < m <;> simp [h] at hpoint ⊢ <;> exact hpoint
      · left
        funext i
        have hpoint := congrFun hz i
        change z i = decide (i.val < m)
        change (!(z i)) = decide (¬ i.val < m) at hpoint
        by_cases h : i.val < m <;> simp [h] at hpoint ⊢ <;> exact hpoint
    · intro hz
      rcases hz with rfl | rfl
      · right
        exact neg_cutPlus m
      · left
        exact neg_cutMinus m
  · intro σ hσ z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hσ with hpres | hswap
    · constructor
      · intro hz
        rcases hz with hz | hz
        · left
          apply reindexBy_injective m σ
          rw [hz, reindex_cutPlus_pres m σ hpres]
        · right
          apply reindexBy_injective m σ
          rw [hz, reindex_cutMinus_pres m σ hpres]
      · intro hz
        rcases hz with rfl | rfl
        · left
          exact reindex_cutPlus_pres m σ hpres
        · right
          exact reindex_cutMinus_pres m σ hpres
    · constructor
      · intro hz
        rcases hz with hz | hz
        · right
          apply reindexBy_injective m σ
          rw [hz, reindex_cutMinus_swap m σ hswap]
        · left
          apply reindexBy_injective m σ
          rw [hz, reindex_cutPlus_swap m σ hswap]
      · intro hz
        rcases hz with rfl | rfl
        · right
          exact reindex_cutPlus_swap m σ hswap
        · left
          exact reindex_cutMinus_swap m σ hswap

/-- The all-ones vertex design — a fair coin between "treat everyone" and "control
everyone" — belongs to the block-exchangeable design class: its two-point support is
closed under global sign flip, and both constant assignments are fixed by every
permutation of the units, hence by every two-block automorphism. -/
lemma allVDesign_mem (m : ℕ) : allVDesign m ∈ blockExchangeableDesignClass m := by
  unfold allVDesign
  apply uniformOnDesign_mem
  · intro z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hz
      rcases hz with hz | hz
      · right
        funext i
        have := congrFun hz i
        simpa using congrArg Bool.not this
      · left
        funext i
        have := congrFun hz i
        simpa using congrArg Bool.not this
    · intro hz
      rcases hz with rfl | rfl <;> simp
  · intro σ _ z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hz
      rcases hz with hz | hz
      · left
        apply reindexBy_injective m σ
        rw [hz, reindex_const_true m σ]
      · right
        apply reindexBy_injective m σ
        rw [hz, reindex_const_false m σ]
    · intro hz
      rcases hz with rfl | rfl
      · left
        exact reindex_const_true m σ
      · right
        exact reindex_const_false m σ

/-- The cut vertex design has assignment second moment `X(1,−1)`: two units in the same
community always receive the same sign, and two units in opposite communities always
receive opposite signs. In the reduced spectral coordinates this is the triangle vertex
`(0, 2m, 0)`. -/
lemma cutVDesign_secondMoment (m : ℕ) :
    assignmentSecondMoment m (cutVDesign m) = blockSymMatrix m 1 (-1) := by
  by_cases hm0 : m = 0
  · subst m
    ext i j
    exact Fin.elim0 i
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hne : cutPlus m ≠ cutMinus m := by
      intro h
      let k : Fin (2 * m) := ⟨0, by omega⟩
      have hk := congrFun h k
      simp [cutPlus, cutMinus, k, hmpos] at hk
    ext i j
    simp only [assignmentSecondMoment, Matrix.of_apply]
    unfold cutVDesign
    rw [uniformOnDesign_two_E m (cutPlus m) (cutMinus m) hne]
    by_cases hij : i = j
    · subst j
      by_cases hi : i.val < m
      · have hnle : ¬ m ≤ i.val := by omega
        simp [signOf, cutPlus, cutMinus, blockSymMatrix, hi, hnle]
      · have hle : m ≤ i.val := by omega
        simp [signOf, cutPlus, cutMinus, blockSymMatrix, hi, hle]
    · by_cases hi : i.val < m <;> by_cases hj : j.val < m
      · simp [signOf, cutPlus, cutMinus, blockSymMatrix, hij, hi, hj]
      · have hji : m ≤ j.val := by omega
        simp [signOf, cutPlus, cutMinus, blockSymMatrix, hij, hi, hj, hji]
      · have hii : m ≤ i.val := by omega
        simp [signOf, cutPlus, cutMinus, blockSymMatrix, hij, hi, hj, hii]
      · have hii : m ≤ i.val := by omega
        have hji : m ≤ j.val := by omega
        simp [signOf, cutPlus, cutMinus, blockSymMatrix, hij, hi, hj, hii, hji]

/-- The all-ones vertex design has assignment second moment `X(1,1)`: every pair of units
always receives the same sign, whether or not they share a community. In the reduced
spectral coordinates this is the triangle vertex `(0, 0, 2m)`. -/
lemma allVDesign_secondMoment (m : ℕ) :
    assignmentSecondMoment m (allVDesign m) = blockSymMatrix m 1 1 := by
  by_cases hm0 : m = 0
  · subst m
    ext i j
    exact Fin.elim0 i
  · have hne : (fun _ : Fin (2 * m) => true) ≠ (fun _ => false) := by
      intro h
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      let k : Fin (2 * m) := ⟨0, by omega⟩
      have hk := congrFun h k
      simp at hk
    ext i j
    unfold allVDesign
    simp only [assignmentSecondMoment, Matrix.of_apply]
    rw [uniformOnDesign_two_E m (fun _ : Fin (2 * m) => true) (fun _ => false) hne]
    simp [signOf, blockSymMatrix]

/-! ## Spread design (even `m`) -/

/-- The balanced-in-each-block support `{z : S_A(z) = 0 ∧ S_B(z) = 0}`. -/
def spreadSupport (m : ℕ) : Finset (Fin (2 * m) → Bool) :=
  Finset.univ.filter (fun z => blockSumA m z = 0 ∧ blockSumB m z = 0)

/-- For even `m`, an explicit balanced-in-each-block assignment (`true` on the first
half of each block). -/
def spreadWitness (m : ℕ) : Fin (2 * m) → Bool :=
  fun i => decide (i.val < m / 2 ∨ (m ≤ i.val ∧ i.val < m + m / 2))

private lemma card_fin_lt (m t : ℕ) (ht : t ≤ 2 * m) :
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

private lemma card_fin_interval_from_m (m t : ℕ) (ht : t ≤ m) :
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

private lemma spreadA_true_filter (m : ℕ) :
    (blockAFin m).filter (fun i => spreadWitness m i) =
      Finset.univ.filter (fun i : Fin (2 * m) => i.val < m / 2) := by
  ext i
  simp only [Finset.mem_filter, blockAFin, Finset.mem_univ, true_and, spreadWitness,
    decide_eq_true_eq]
  omega

private lemma spreadB_true_filter (m : ℕ) :
    (blockBFin m).filter (fun i => spreadWitness m i) =
      Finset.univ.filter (fun i : Fin (2 * m) => m ≤ i.val ∧ i.val < m + m / 2) := by
  ext i
  simp only [Finset.mem_filter, blockBFin, Finset.mem_univ, true_and, spreadWitness,
    decide_eq_true_eq]
  omega

private lemma blockSumA_spreadWitness (m : ℕ) (hEven : Even m) :
    blockSumA m (spreadWitness m) = 0 := by
  change (∑ i ∈ blockAFin m, (if spreadWitness m i = true then (1 : ℤ) else -1)) = 0
  have hTrueCardBool : ((blockAFin m).filter (fun i => spreadWitness m i)).card = m / 2 := by
    rw [spreadA_true_filter]
    apply card_fin_lt
    omega
  have hTrueCard : ((blockAFin m).filter (fun i => spreadWitness m i = true)).card
      = m / 2 := by
    simpa using hTrueCardBool
  have hFalseCard : ((blockAFin m).filter (fun i => spreadWitness m i = false)).card
      = m / 2 := by
    have hsum := Finset.card_filter_add_card_filter_not (s := blockAFin m)
      (p := fun i => spreadWitness m i = true)
    rw [hTrueCard, card_blockAFin] at hsum
    have hfalseNot :
        ((blockAFin m).filter (fun i => ¬ spreadWitness m i = true)).card = m / 2 := by
      rcases hEven with ⟨k, rfl⟩
      omega
    simpa [Bool.not_eq_true] using hfalseNot
  rw [← Finset.sum_filter_add_sum_filter_not (s := blockAFin m)
    (p := fun i => spreadWitness m i = true)
    (f := fun i => if spreadWitness m i = true then (1 : ℤ) else -1)]
  have hT : (∑ x ∈ blockAFin m with spreadWitness m x = true,
      if spreadWitness m x = true then (1 : ℤ) else -1) = (m / 2 : ℤ) := by
    calc
      (∑ x ∈ blockAFin m with spreadWitness m x = true,
          if spreadWitness m x = true then (1 : ℤ) else -1)
          = ∑ x ∈ blockAFin m with spreadWitness m x = true, (1 : ℤ) := by
              apply Finset.sum_congr rfl
              intro x hx
              simp only [Finset.mem_filter] at hx
              simp [hx.2]
      _ = (m / 2 : ℤ) := by
              simp [hTrueCard]
  have hF : (∑ x ∈ blockAFin m with ¬spreadWitness m x = true,
      if spreadWitness m x = true then (1 : ℤ) else -1) = -(m / 2 : ℤ) := by
    calc
      (∑ x ∈ blockAFin m with ¬spreadWitness m x = true,
          if spreadWitness m x = true then (1 : ℤ) else -1)
          = ∑ x ∈ blockAFin m with ¬spreadWitness m x = true, (-1 : ℤ) := by
              apply Finset.sum_congr rfl
              intro x hx
              simp only [Finset.mem_filter] at hx
              simp [hx.2]
      _ = -(m / 2 : ℤ) := by
              simp [Bool.not_eq_true, hFalseCard]
  rw [hT, hF]
  ring

private lemma blockSumB_spreadWitness (m : ℕ) (hEven : Even m) :
    blockSumB m (spreadWitness m) = 0 := by
  change (∑ i ∈ blockBFin m, (if spreadWitness m i = true then (1 : ℤ) else -1)) = 0
  have hTrueCardBool : ((blockBFin m).filter (fun i => spreadWitness m i)).card = m / 2 := by
    rw [spreadB_true_filter]
    apply card_fin_interval_from_m
    omega
  have hTrueCard : ((blockBFin m).filter (fun i => spreadWitness m i = true)).card
      = m / 2 := by
    simpa using hTrueCardBool
  have hFalseCard : ((blockBFin m).filter (fun i => spreadWitness m i = false)).card
      = m / 2 := by
    have hsum := Finset.card_filter_add_card_filter_not (s := blockBFin m)
      (p := fun i => spreadWitness m i = true)
    rw [hTrueCard, card_blockBFin] at hsum
    have hfalseNot :
        ((blockBFin m).filter (fun i => ¬ spreadWitness m i = true)).card = m / 2 := by
      rcases hEven with ⟨k, rfl⟩
      omega
    simpa [Bool.not_eq_true] using hfalseNot
  rw [← Finset.sum_filter_add_sum_filter_not (s := blockBFin m)
    (p := fun i => spreadWitness m i = true)
    (f := fun i => if spreadWitness m i = true then (1 : ℤ) else -1)]
  have hT : (∑ x ∈ blockBFin m with spreadWitness m x = true,
      if spreadWitness m x = true then (1 : ℤ) else -1) = (m / 2 : ℤ) := by
    calc
      (∑ x ∈ blockBFin m with spreadWitness m x = true,
          if spreadWitness m x = true then (1 : ℤ) else -1)
          = ∑ x ∈ blockBFin m with spreadWitness m x = true, (1 : ℤ) := by
              apply Finset.sum_congr rfl
              intro x hx
              simp only [Finset.mem_filter] at hx
              simp [hx.2]
      _ = (m / 2 : ℤ) := by
              simp [hTrueCard]
  have hF : (∑ x ∈ blockBFin m with ¬spreadWitness m x = true,
      if spreadWitness m x = true then (1 : ℤ) else -1) = -(m / 2 : ℤ) := by
    calc
      (∑ x ∈ blockBFin m with ¬spreadWitness m x = true,
          if spreadWitness m x = true then (1 : ℤ) else -1)
          = ∑ x ∈ blockBFin m with ¬spreadWitness m x = true, (-1 : ℤ) := by
              apply Finset.sum_congr rfl
              intro x hx
              simp only [Finset.mem_filter] at hx
              simp [hx.2]
      _ = -(m / 2 : ℤ) := by
              simp [Bool.not_eq_true, hFalseCard]
  rw [hT, hF]
  ring

/-- For even `m`, the explicit half-and-half assignment (treat the first half of each
community, control the second half) really is balanced in each block: both community sign
sums are zero. -/
lemma spreadWitness_mem (m : ℕ) (hEven : Even m) :
    spreadWitness m ∈ spreadSupport m := by
  simp [spreadSupport, blockSumA_spreadWitness m hEven, blockSumB_spreadWitness m hEven]

/-- For even `m` at least one assignment has both community sign sums equal to zero, so
the balanced-in-each-block support is nonempty and the uniform law on it is well defined.
Evenness is essential: for odd `m` each community sum is an odd integer and this support
is empty. -/
lemma spreadSupport_nonempty (m : ℕ) (hEven : Even m) : (spreadSupport m).Nonempty :=
  ⟨spreadWitness m, spreadWitness_mem m hEven⟩

/-- The spread vertex design (even `m`). -/
noncomputable def spreadVDesign (m : ℕ) (hEven : Even m) :
    FiniteDesign (Fin (2 * m) → Bool) :=
  uniformOnDesign m (spreadSupport m) (spreadSupport_nonempty m hEven)

/-- For even `m`, the spread vertex design — uniform over the assignments that are exactly
balanced inside each community — belongs to the block-exchangeable design class. Negating
an assignment and relabelling units by a two-block automorphism both leave the pair of
community sign sums at `(0,0)`, so the support is invariant. -/
lemma spreadVDesign_mem (m : ℕ) (hEven : Even m) :
    spreadVDesign m hEven ∈ blockExchangeableDesignClass m := by
  unfold spreadVDesign
  apply uniformOnDesign_mem
  · intro z
    simp [spreadSupport, blockSumA_neg, blockSumB_neg]
  · intro σ hσ z
    rcases blockSum_reindex m σ hσ z with h | h
    · simp [spreadSupport, h.1, h.2]
    · simp [spreadSupport, h.1, h.2, and_comm]

private lemma sumAr_eq_blockSumA_cast (m : ℕ) (z : Fin (2 * m) → Bool) :
    sumAr m z = (blockSumA m z : ℝ) := by
  simp [sumAr, blockSumA, blockAFin, signOf]

private lemma sumBr_eq_blockSumB_cast (m : ℕ) (z : Fin (2 * m) → Bool) :
    sumBr m z = (blockSumB m z : ℝ) := by
  simp [sumBr, blockSumB, blockBFin, signOf]

/-- On the spread support the real community sums vanish, so `E[S_A²]=E[S_A S_B]=0`. -/
lemma spreadVDesign_sumAr_zero (m : ℕ) (hEven : Even m) :
    (spreadVDesign m hEven).E (fun z => sumAr m z * sumAr m z) = 0 := by
  unfold spreadVDesign
  rw [FiniteDesign.E]
  apply Finset.sum_eq_zero
  intro z _
  by_cases hz : z ∈ spreadSupport m
  · have hzmem : blockSumA m z = 0 ∧ blockSumB m z = 0 := by
      simpa [spreadSupport] using hz
    have hsum : sumAr m z = 0 := by
      rw [sumAr_eq_blockSumA_cast, hzmem.1]
      norm_num
    simp [uniformOnDesign, hz, hsum]
  · simp [uniformOnDesign, hz]

/-- Under the spread vertex design the two community sign sums have zero cross moment,
since every assignment in its support has both sums equal to zero pointwise. With the
companion `spreadVDesign_sumAr_zero` this pins the design's reduced coordinates. -/
lemma spreadVDesign_sumAr_sumBr_zero (m : ℕ) (hEven : Even m) :
    (spreadVDesign m hEven).E (fun z => sumAr m z * sumBr m z) = 0 := by
  unfold spreadVDesign
  rw [FiniteDesign.E]
  apply Finset.sum_eq_zero
  intro z _
  by_cases hz : z ∈ spreadSupport m
  · have hzmem : blockSumA m z = 0 ∧ blockSumB m z = 0 := by
      simpa [spreadSupport] using hz
    have hsum : sumAr m z = 0 := by
      rw [sumAr_eq_blockSumA_cast, hzmem.1]
      norm_num
    simp [uniformOnDesign, hz, hsum]
  · simp [uniformOnDesign, hz]

/-- For even `m ≥ 2` the spread vertex design has assignment second moment
`X(−1/(m−1), 0)`: units in different communities are uncorrelated, and units in the same
community carry the small negative correlation `−1/(m−1)` forced by the community sign sum
being identically zero. These are the reduced coordinates `(2m/q, 0, 0)` — the spread
vertex of the triangle — so for even `m` the spread covariance is implementable. -/
lemma spreadVDesign_secondMoment (m : ℕ) (hm : 2 ≤ m) (hEven : Even m) :
    assignmentSecondMoment m (spreadVDesign m hEven)
      = blockSymMatrix m (-1 / ((m : ℝ) - 1)) 0 := by
  rcases secondMoment_blockSym_of_exchangeable m hm (spreadVDesign m hEven)
      (spreadVDesign_mem m hEven) with ⟨u, v, hUV⟩
  have hEqU : (m : ℝ) + (m : ℝ) * ((m : ℝ) - 1) * u = 0 := by
    rw [← E_sumAr_sq m u v (spreadVDesign m hEven) hUV, spreadVDesign_sumAr_zero]
  have hEqV : (m : ℝ) ^ 2 * v = 0 := by
    rw [← E_sumAr_sumBr m u v (spreadVDesign m hEven) hUV,
      spreadVDesign_sumAr_sumBr_zero]
  have hmposR : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm)
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmposR
  have hmgt1 : (1 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hm)
  have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
  have huProd : ((m : ℝ) - 1) * u = -1 := by
    have hfac : (m : ℝ) * (1 + ((m : ℝ) - 1) * u) = 0 := by
      nlinarith [hEqU]
    have hlin : 1 + ((m : ℝ) - 1) * u = 0 := (mul_eq_zero.mp hfac).resolve_left hm0
    linarith
  have hu : u = -1 / ((m : ℝ) - 1) := by
    field_simp [hm1]
    nlinarith
  have hv : v = 0 := by
    have hm2 : (m : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hm0
    exact (mul_eq_zero.mp hEqV).resolve_left hm2
  rw [hUV, hu, hv]

end CausalSmith.Experimentation.DesignPm1
