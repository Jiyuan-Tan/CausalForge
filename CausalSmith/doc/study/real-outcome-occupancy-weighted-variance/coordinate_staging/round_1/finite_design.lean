/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Sample.OccupancyWeightedMean.Basic
import Causalean.Stat.Sample.OccupancyWeightedMean.BinomialDesign

/-!
# Finite enumeration for occupancy-weighted design factors

This module assembles groupwise inverse-arm bounds into an algebraic comparison
between the expected occupancy design variance factor and reciprocal usable
occupancy. Zero-mass group fibers vanish before any conditional arm probability
is formed.
-/

namespace Causalean.Stat

open scoped BigOperators

section FiniteDesign

variable {n : Nat} {κ : Type*} [Fintype κ] [DecidableEq κ]

private def fdArmCount (x : Fin n → κ) (b : Fin n → Bool)
    (a : Bool) (k : κ) : Nat :=
  (Finset.univ.filter fun i => x i = k ∧ b i = a).card

private def fdGroupCount (x : Fin n → κ) (k : κ) : Nat :=
  (Finset.univ.filter fun i => x i = k).card

private def fdUsable (x : Fin n → κ) (b : Fin n → Bool) (k : κ) : Prop :=
  0 < fdArmCount x b false k ∧ 0 < fdArmCount x b true k

private noncomputable def fdTotal (x : Fin n → κ) (b : Fin n → Bool) : Nat :=
  by
    classical
    exact ∑ k, if fdUsable x b k then fdGroupCount x k else 0

private noncomputable def fdInverse (x : Fin n → κ) (b : Fin n → Bool) : Real :=
  if 0 < fdTotal x b then (fdTotal x b : Real)⁻¹ else 0

private noncomputable def fdVariance (x : Fin n → κ) (b : Fin n → Bool) : Real :=
  by
    classical
    exact if 0 < fdTotal x b then
      (fdTotal x b : Real)⁻¹ ^ 2 *
        ∑ k, if fdUsable x b k then
          (fdGroupCount x k : Real) ^ 2 *
            ((fdArmCount x b true k : Real)⁻¹ +
              (fdArmCount x b false k : Real)⁻¹)
        else 0
    else 0

private def fdWeight (p : κ → Real) (x : Fin n → κ) (b : Fin n → Bool) : Real :=
  ∏ i, if b i then p (x i) else 1 - p (x i)

private lemma fdArmCount_false_add_true (x : Fin n → κ) (b : Fin n → Bool) (k : κ) :
    fdArmCount x b false k + fdArmCount x b true k = fdGroupCount x k := by
  classical
  unfold fdArmCount fdGroupCount
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      cases hb : b i
      · exact Or.inl ⟨h, by simp [hb]⟩
      · exact Or.inr ⟨h, by simp [hb]⟩
  · simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hf ht
    simp_all

private lemma fdUsable_iff_true_count (x : Fin n → κ) (b : Fin n → Bool) (k : κ) :
    fdUsable x b k ↔
      0 < fdArmCount x b true k ∧ fdArmCount x b true k < fdGroupCount x k := by
  have hsplit := fdArmCount_false_add_true x b k
  unfold fdUsable
  omega

private noncomputable def fdOtherTotal (x : Fin n → κ) (b : Fin n → Bool) (k : κ) : Nat :=
  by
    classical
    exact ∑ l, if l ≠ k ∧ fdUsable x b l then fdGroupCount x l else 0

private lemma fdTotal_eq_other_add (x : Fin n → κ) (b : Fin n → Bool) (k : κ)
    (hk : fdUsable x b k) :
    fdTotal x b = fdOtherTotal x b k + fdGroupCount x k := by
  classical
  unfold fdTotal fdOtherTotal
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
  simp only [hk, if_true]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
  simp only [ne_eq, not_true_eq_false, false_and, if_false, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  have hlk : l ≠ k := Finset.ne_of_mem_erase hl
  simp [hlk]

private noncomputable def fdLocalVariance
    (x : Fin n → κ) (b : Fin n → Bool) (k : κ) : Real :=
  by
    classical
    exact if fdUsable x b k then
      (fdGroupCount x k : Real) ^ 2 *
        (((fdOtherTotal x b k + fdGroupCount x k : Nat) : Real)⁻¹ ^ 2) *
        ((fdArmCount x b true k : Real)⁻¹ +
          (fdArmCount x b false k : Real)⁻¹)
    else 0

private noncomputable def fdLocalShare
    (x : Fin n → κ) (b : Fin n → Bool) (k : κ) : Real :=
  by
    classical
    exact if fdUsable x b k then
      (fdGroupCount x k : Real) *
        (((fdOtherTotal x b k + fdGroupCount x k : Nat) : Real)⁻¹ ^ 2)
    else 0

private lemma fdVariance_eq_sum_local (x : Fin n → κ) (b : Fin n → Bool) :
    fdVariance x b = ∑ k, fdLocalVariance x b k := by
  classical
  by_cases hR : 0 < fdTotal x b
  · rw [fdVariance, if_pos hR]
    apply Eq.symm
    calc
      (∑ k, fdLocalVariance x b k) =
          ∑ k, (fdTotal x b : Real)⁻¹ ^ 2 *
            (if fdUsable x b k then
              (fdGroupCount x k : Real) ^ 2 *
                ((fdArmCount x b true k : Real)⁻¹ +
                  (fdArmCount x b false k : Real)⁻¹)
            else 0) := by
        apply Finset.sum_congr rfl
        intro k hkfin
        by_cases hk : fdUsable x b k
        · rw [fdLocalVariance, if_pos hk, fdTotal_eq_other_add x b k hk]
          simp [hk]
          ring
        · simp [fdLocalVariance, hk]
      _ = _ := by rw [Finset.mul_sum]
  · have hnusable (k : κ) : ¬ fdUsable x b k := by
      intro hk
      have hmpos : 0 < fdGroupCount x k := by
        have hk' := hk
        unfold fdUsable at hk'
        rw [← fdArmCount_false_add_true x b k]
        exact Nat.add_pos_left hk'.1 _
      have hle : fdGroupCount x k ≤ fdTotal x b := by
        unfold fdTotal
        have h := Finset.single_le_sum
          (s := (Finset.univ : Finset κ))
          (f := fun l => if fdUsable x b l then fdGroupCount x l else 0)
          (fun l _ => Nat.zero_le _) (Finset.mem_univ k)
        simpa [hk] using h
      omega
    simp [fdVariance, hR, fdLocalVariance, hnusable]

private lemma fdInverse_eq_sum_localShare (x : Fin n → κ) (b : Fin n → Bool) :
    fdInverse x b = ∑ k, fdLocalShare x b k := by
  classical
  by_cases hR : 0 < fdTotal x b
  · rw [fdInverse, if_pos hR]
    have hRreal : (0 : Real) < fdTotal x b := by exact_mod_cast hR
    calc
      (fdTotal x b : Real)⁻¹ =
          (fdTotal x b : Real)⁻¹ ^ 2 * (fdTotal x b : Real) := by
        field_simp
      _ = (fdTotal x b : Real)⁻¹ ^ 2 *
          ∑ k, if fdUsable x b k then (fdGroupCount x k : Real) else 0 := by
        congr 1
        simp [fdTotal]
      _ = ∑ k, fdLocalShare x b k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hkfin
        by_cases hk : fdUsable x b k
        · rw [fdLocalShare, if_pos hk, fdTotal_eq_other_add x b k hk]
          simp [hk]
          ring
        · simp [fdLocalShare, hk]
  · have hnusable (k : κ) : ¬ fdUsable x b k := by
      intro hk
      have hmpos : 0 < fdGroupCount x k := by
        have hk' := hk
        unfold fdUsable at hk'
        rw [← fdArmCount_false_add_true x b k]
        exact Nat.add_pos_left hk'.1 _
      have hle : fdGroupCount x k ≤ fdTotal x b := by
        unfold fdTotal
        have h := Finset.single_le_sum
          (s := (Finset.univ : Finset κ))
          (f := fun l => if fdUsable x b l then fdGroupCount x l else 0)
          (fun l _ => Nat.zero_le _) (Finset.mem_univ k)
        simpa [hk] using h
      omega
    simp [fdInverse, hR, fdLocalShare, hnusable]

private def fdSplit (x : Fin n → κ) (k : κ) :
    (Fin n → Bool) ≃
      (({i : Fin n // x i = k} → Bool) × ({i : Fin n // x i ≠ k} → Bool)) where
  toFun b := (fun i => b i, fun i => b i)
  invFun bc := fun i => if h : x i = k then bc.1 ⟨i, h⟩ else bc.2 ⟨i, h⟩
  left_inv b := by
    funext i
    by_cases h : x i = k <;> simp [h]
  right_inv bc := by
    apply Prod.ext
    · funext i
      simp [i.2]
    · funext i
      simp [i.2]

private lemma fdGroupCount_eq_card (x : Fin n → κ) (k : κ) :
    fdGroupCount x k = Fintype.card {i : Fin n // x i = k} := by
  classical
  unfold fdGroupCount
  rw [Fintype.card_subtype]

private lemma fdArmCount_split_true (x : Fin n → κ) (k : κ)
    (u : {i : Fin n // x i = k} → Bool)
    (v : {i : Fin n // x i ≠ k} → Bool) :
    fdArmCount x ((fdSplit x k).symm (u, v)) true k =
      (Finset.univ.filter fun i => u i = true).card := by
  classical
  unfold fdArmCount
  rw [show (Finset.univ.filter fun i => x i = k ∧ (fdSplit x k).symm (u, v) i = true) =
      Finset.univ.filter fun i => (fdSplit x k).symm (u, v) i = true ∧ x i = k by
    ext i
    simp [and_comm]]
  rw [← Finset.filter_filter]
  rw [← Finset.card_subtype (p := fun i : Fin n => x i = k)
    (s := Finset.univ.filter fun i => (fdSplit x k).symm (u, v) i = true)]
  congr 1
  ext i
  simp [fdSplit, i.2]

private lemma fdArmCount_split_false (x : Fin n → κ) (k : κ)
    (u : {i : Fin n // x i = k} → Bool)
    (v : {i : Fin n // x i ≠ k} → Bool) :
    fdArmCount x ((fdSplit x k).symm (u, v)) false k =
      Fintype.card {i : Fin n // x i = k} -
        (Finset.univ.filter fun i => u i = true).card := by
  have hsplit := fdArmCount_false_add_true x ((fdSplit x k).symm (u, v)) k
  rw [fdArmCount_split_true, fdGroupCount_eq_card] at hsplit
  omega

private lemma fdUsable_split (x : Fin n → κ) (k : κ)
    (u : {i : Fin n // x i = k} → Bool)
    (v : {i : Fin n // x i ≠ k} → Bool) :
    fdUsable x ((fdSplit x k).symm (u, v)) k ↔
      0 < (Finset.univ.filter fun i => u i = true).card ∧
        (Finset.univ.filter fun i => u i = true).card <
          Fintype.card {i : Fin n // x i = k} := by
  rw [fdUsable_iff_true_count, fdArmCount_split_true, fdGroupCount_eq_card]

private lemma fdArmCount_split_ne (x : Fin n → κ) (k l : κ) (hlk : l ≠ k)
    (u u' : {i : Fin n // x i = k} → Bool)
    (v : {i : Fin n // x i ≠ k} → Bool) (a : Bool) :
    fdArmCount x ((fdSplit x k).symm (u, v)) a l =
      fdArmCount x ((fdSplit x k).symm (u', v)) a l := by
  classical
  unfold fdArmCount
  congr 1
  ext i
  by_cases hil : x i = l
  · have hik : x i ≠ k := by intro h; apply hlk; exact hil.symm.trans h
    simp [fdSplit, hil, hik, hlk]
  · simp [hil]

private lemma fdOtherTotal_split (x : Fin n → κ) (k : κ)
    (u u' : {i : Fin n // x i = k} → Bool)
    (v : {i : Fin n // x i ≠ k} → Bool) :
    fdOtherTotal x ((fdSplit x k).symm (u, v)) k =
      fdOtherTotal x ((fdSplit x k).symm (u', v)) k := by
  classical
  unfold fdOtherTotal
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hlk : l = k
  · simp [hlk]
  · have hf := fdArmCount_split_ne x k l hlk u u' v false
    have ht := fdArmCount_split_ne x k l hlk u u' v true
    have hu : fdUsable x ((fdSplit x k).symm (u, v)) l ↔
        fdUsable x ((fdSplit x k).symm (u', v)) l := by
      unfold fdUsable
      rw [hf, ht]
    simp [hlk, hu]

private lemma fdWeight_split (p : κ → Real) (x : Fin n → κ) (k : κ)
    (u : {i : Fin n // x i = k} → Bool)
    (v : {i : Fin n // x i ≠ k} → Bool) :
    fdWeight p x ((fdSplit x k).symm (u, v)) =
      (∏ i, if v i then p (x i) else 1 - p (x i)) *
        ∏ i, if u i then p k else 1 - p k := by
  classical
  unfold fdWeight
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : Fin n => x i = k)]
  rw [mul_comm]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    simp [fdSplit, i.2]
  · apply Finset.prod_congr rfl
    intro i hi
    simp [fdSplit, i.2]

private lemma fdLocalVariance_split (x : Fin n → κ) (k : κ)
    (u : {i : Fin n // x i = k} → Bool)
    (v : {i : Fin n // x i ≠ k} → Bool) :
    fdLocalVariance x ((fdSplit x k).symm (u, v)) k =
      (Fintype.card {i : Fin n // x i = k} : Real) ^ 2 *
        (((fdOtherTotal x ((fdSplit x k).symm (fun _ => false, v)) k +
          Fintype.card {i : Fin n // x i = k} : Nat) : Real)⁻¹ ^ 2) *
        inverseTwoCounts (Fintype.card {i : Fin n // x i = k})
          (Finset.univ.filter fun i => u i = true).card := by
  classical
  rw [fdLocalVariance, fdUsable_split, fdGroupCount_eq_card,
    fdArmCount_split_true, fdArmCount_split_false,
    fdOtherTotal_split x k u (fun _ => false) v]
  unfold inverseTwoCounts
  split <;> simp_all

private lemma fdLocalShare_split (x : Fin n → κ) (k : κ)
    (u : {i : Fin n // x i = k} → Bool)
    (v : {i : Fin n // x i ≠ k} → Bool) :
    fdLocalShare x ((fdSplit x k).symm (u, v)) k =
      (Fintype.card {i : Fin n // x i = k} : Real) *
        (((fdOtherTotal x ((fdSplit x k).symm (fun _ => false, v)) k +
          Fintype.card {i : Fin n // x i = k} : Nat) : Real)⁻¹ ^ 2) *
        interiorIndicator (Fintype.card {i : Fin n // x i = k})
          (Finset.univ.filter fun i => u i = true).card := by
  classical
  rw [fdLocalShare, fdUsable_split, fdGroupCount_eq_card,
    fdOtherTotal_split x k u (fun _ => false) v]
  unfold interiorIndicator
  split <;> simp_all

private lemma sum_fdWeight_localVariance_le
    (p : κ → Real) (x : Fin n → κ) (k : κ) (epsilon : Real)
    (hepsilon : 0 < epsilon)
    (hlo : ∀ l, epsilon ≤ p l) (hhi : ∀ l, p l ≤ 1 - epsilon) :
    (∑ b : Fin n → Bool, fdWeight p x b * fdLocalVariance x b k) ≤
      (4 / (epsilon ^ 2 * (1 - epsilon))) *
        ∑ b : Fin n → Bool, fdWeight p x b * fdLocalShare x b k := by
  classical
  rw [Fintype.sum_equiv (fdSplit x k)
    (fun b => fdWeight p x b * fdLocalVariance x b k)
    (fun uv => fdWeight p x ((fdSplit x k).symm uv) *
      fdLocalVariance x ((fdSplit x k).symm uv) k)
    (fun b => by simp), Fintype.sum_prod_type_right]
  rw [Fintype.sum_equiv (fdSplit x k)
    (fun b => fdWeight p x b * fdLocalShare x b k)
    (fun uv => fdWeight p x ((fdSplit x k).symm uv) *
      fdLocalShare x ((fdSplit x k).symm uv) k)
    (fun b => by simp), Fintype.sum_prod_type_right]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  let q : Real := ∏ i, if v i then p (x i) else 1 - p (x i)
  let r : Nat := fdOtherTotal x ((fdSplit x k).symm (fun _ => false, v)) k
  have hq : 0 ≤ q := by
    dsimp [q]
    apply Finset.prod_nonneg
    intro i hi
    split
    · exact (hepsilon.trans_le (hlo (x i))).le
    · linarith [hhi (x i)]
  have hlocal := sum_bernoulli_local_variance_le_share
    (ι := {i : Fin n // x i = k}) r (p k) epsilon
    hepsilon (hlo k) (hhi k)
  calc
    (∑ u : {i : Fin n // x i = k} → Bool,
        fdWeight p x ((fdSplit x k).symm (u, v)) *
        fdLocalVariance x ((fdSplit x k).symm (u, v)) k) =
        q * ∑ u : {i : Fin n // x i = k} → Bool,
          (∏ i, if u i then p k else 1 - p k) *
          ((Fintype.card {i : Fin n // x i = k} : Real) ^ 2 *
            (((r + Fintype.card {i : Fin n // x i = k} : Nat) : Real)⁻¹ ^ 2) *
            inverseTwoCounts (Fintype.card {i : Fin n // x i = k})
              (Finset.univ.filter fun i => u i = true).card) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      rw [fdWeight_split, fdLocalVariance_split]
      dsimp [q, r]
      ring
    _ ≤ q * ((4 / (epsilon ^ 2 * (1 - epsilon))) *
        ∑ u : {i : Fin n // x i = k} → Bool,
          (∏ i, if u i then p k else 1 - p k) *
          ((Fintype.card {i : Fin n // x i = k} : Real) *
            (((r + Fintype.card {i : Fin n // x i = k} : Nat) : Real)⁻¹ ^ 2) *
            interiorIndicator (Fintype.card {i : Fin n // x i = k})
              (Finset.univ.filter fun i => u i = true).card)) := by
      exact mul_le_mul_of_nonneg_left hlocal hq
    _ = (4 / (epsilon ^ 2 * (1 - epsilon))) *
        ∑ u : {i : Fin n // x i = k} → Bool,
          fdWeight p x ((fdSplit x k).symm (u, v)) *
          fdLocalShare x ((fdSplit x k).symm (u, v)) k := by
      have hsum :
          (∑ u : {i : Fin n // x i = k} → Bool,
            fdWeight p x ((fdSplit x k).symm (u, v)) *
              fdLocalShare x ((fdSplit x k).symm (u, v)) k) =
            q * ∑ u : {i : Fin n // x i = k} → Bool,
              (∏ i, if u i then p k else 1 - p k) *
                ((Fintype.card {i : Fin n // x i = k} : Real) *
                  (((r + Fintype.card {i : Fin n // x i = k} : Nat) : Real)⁻¹ ^ 2) *
                  interiorIndicator (Fintype.card {i : Fin n // x i = k})
                    (Finset.univ.filter fun i => u i = true).card) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        rw [fdWeight_split, fdLocalShare_split]
        dsimp [q, r]
        ring
      rw [hsum]
      ring

/-- If [the overlap margin is positive](hyp:hepsilon) and [every group's arm
probability lies between the margin and one minus the margin](hyp:hlo,hhi),
[the finite arm-weighted design variance is bounded by a margin-dependent
multiple of reciprocal usable occupancy](goal). -/
private lemma sum_fdWeight_variance_le_inverse
    (p : κ → Real) (x : Fin n → κ) (epsilon : Real)
    (hepsilon : 0 < epsilon)
    (hlo : ∀ k, epsilon ≤ p k) (hhi : ∀ k, p k ≤ 1 - epsilon) :
    (∑ b : Fin n → Bool, fdWeight p x b * fdVariance x b) ≤
      (4 / (epsilon ^ 2 * (1 - epsilon))) *
        ∑ b : Fin n → Bool, fdWeight p x b * fdInverse x b := by
  classical
  calc
    (∑ b : Fin n → Bool, fdWeight p x b * fdVariance x b) =
        ∑ k, ∑ b : Fin n → Bool, fdWeight p x b * fdLocalVariance x b k := by
      simp_rw [fdVariance_eq_sum_local, Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ ∑ k, (4 / (epsilon ^ 2 * (1 - epsilon))) *
        ∑ b : Fin n → Bool, fdWeight p x b * fdLocalShare x b k := by
      apply Finset.sum_le_sum
      intro k hk
      exact sum_fdWeight_localVariance_le p x k epsilon hepsilon hlo hhi
    _ = (4 / (epsilon ^ 2 * (1 - epsilon))) *
        ∑ b : Fin n → Bool, fdWeight p x b * fdInverse x b := by
      rw [Finset.mul_sum]
      simp_rw [fdInverse_eq_sum_localShare, Finset.mul_sum]
      rw [Finset.sum_comm]

private def fdDesignSplit :
    (Fin n → κ × Bool) ≃ ((Fin n → κ) × (Fin n → Bool)) where
  toFun d := (fun i => (d i).1, fun i => (d i).2)
  invFun xb := fun i => (xb.1 i, xb.2 i)
  left_inv d := by funext i; exact Prod.eta (d i)
  right_inv xb := rfl

private lemma canonical_groupArmCount_eq (x : Fin n → κ) (b : Fin n → Bool)
    (a : Bool) (k : κ) :
    groupArmCount Prod.fst Prod.snd (fun i => (x i, b i)) a k =
      fdArmCount x b a k := by
  rfl

private lemma canonical_groupCount_eq (x : Fin n → κ) (b : Fin n → Bool) (k : κ) :
    groupCount Prod.fst Prod.snd (fun i => (x i, b i)) k = fdGroupCount x k := by
  rw [groupCount, canonical_groupArmCount_eq, canonical_groupArmCount_eq,
    ← fdArmCount_false_add_true]

private lemma canonical_usable_eq (x : Fin n → κ) (b : Fin n → Bool) (k : κ) :
    usableGroup Prod.fst Prod.snd (fun i => (x i, b i)) k ↔ fdUsable x b k := by
  rfl

private lemma canonical_total_eq (x : Fin n → κ) (b : Fin n → Bool) :
    usableGroupTotal Prod.fst Prod.snd (fun i => (x i, b i)) = fdTotal x b := by
  classical
  unfold usableGroupTotal fdTotal
  apply Finset.sum_congr rfl
  intro k hk
  rw [canonical_groupCount_eq]
  rfl

private lemma canonical_variance_eq (x : Fin n → κ) (b : Fin n → Bool) :
    occupancyDesignVarianceFactor Prod.fst Prod.snd (fun i => (x i, b i)) =
      fdVariance x b := by
  classical
  unfold occupancyDesignVarianceFactor fdVariance
  rw [canonical_total_eq]
  by_cases hR : 0 < fdTotal x b
  · simp only [hR, if_true]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [canonical_groupCount_eq, canonical_groupArmCount_eq,
      canonical_groupArmCount_eq]
    rfl
  · simp [hR]

private lemma canonical_inverse_eq (x : Fin n → κ) (b : Fin n → Bool) :
    inverseUsableGroupTotal Prod.fst Prod.snd (fun i => (x i, b i)) = fdInverse x b := by
  unfold inverseUsableGroupTotal fdInverse
  rw [canonical_total_eq]

/-- If [all joint group/arm masses are nonnegative](hyp:hq), [their two arm
masses sum to the group mass](hyp:hsum), [the overlap margin is positive and at
most one half](hyp:hepsilon,hepsilon_half), and [each positive-mass group gives
both arms at least the overlap share](hyp:hoverlap), [the joint-design average
of the occupancy variance factor is bounded by a margin-dependent multiple of
average reciprocal usable occupancy](goal). Zero-mass groups contribute zero
before any conditional arm probability is formed. -/
lemma sum_jointWeight_variance_le_inverse
    (q : κ → Bool → Real) (g : κ → Real) (epsilon : Real)
    (hq : ∀ k a, 0 ≤ q k a)
    (hsum : ∀ k, q k false + q k true = g k)
    (hepsilon : 0 < epsilon)
    (hepsilon_half : epsilon ≤ (1 / 2 : Real))
    (hoverlap : ∀ k, 0 < g k → ∀ a, epsilon * g k ≤ q k a) :
    (∑ d : Fin n → κ × Bool, (∏ i, q (d i).1 (d i).2) *
      occupancyDesignVarianceFactor Prod.fst Prod.snd d) ≤
      (4 / (epsilon ^ 2 * (1 - epsilon))) *
        ∑ d : Fin n → κ × Bool, (∏ i, q (d i).1 (d i).2) *
          inverseUsableGroupTotal Prod.fst Prod.snd d := by
  classical
  rw [Fintype.sum_equiv fdDesignSplit
    (fun d => (∏ i, q (d i).1 (d i).2) *
      occupancyDesignVarianceFactor Prod.fst Prod.snd d)
    (fun xb => (∏ i, q (xb.1 i) (xb.2 i)) * fdVariance xb.1 xb.2)
    (fun d => by
      rw [canonical_variance_eq]
      rfl), Fintype.sum_prod_type]
  rw [Fintype.sum_equiv fdDesignSplit
    (fun d => (∏ i, q (d i).1 (d i).2) *
      inverseUsableGroupTotal Prod.fst Prod.snd d)
    (fun xb => (∏ i, q (xb.1 i) (xb.2 i)) * fdInverse xb.1 xb.2)
    (fun d => by
      rw [canonical_inverse_eq]
      rfl), Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  by_cases hpos : ∀ i, 0 < g (x i)
  · let p : κ → Real := fun k => if 0 < g k then q k true / g k else epsilon
    let G : Real := ∏ i, g (x i)
    have hg0 (k : κ) : 0 ≤ g k := by
      rw [← hsum k]
      exact add_nonneg (hq k false) (hq k true)
    have hp_lo (k : κ) : epsilon ≤ p k := by
      by_cases hg : 0 < g k
      · dsimp [p]
        rw [if_pos hg]
        apply (le_div_iff₀ hg).2
        exact hoverlap k hg true
      · simp [p, hg]
    have hp_hi (k : κ) : p k ≤ 1 - epsilon := by
      by_cases hg : 0 < g k
      · dsimp [p]
        rw [if_pos hg]
        apply (div_le_iff₀ hg).2
        have hf := hoverlap k hg false
        calc
          q k true ≤ g k - epsilon * g k := by linarith [hsum k]
          _ = (1 - epsilon) * g k := by ring
      · simp [p, hg]
        linarith
    have hG : 0 ≤ G := by
      dsimp [G]
      exact Finset.prod_nonneg fun i _ => hg0 (x i)
    have hfactor (b : Fin n → Bool) :
        (∏ i, q (x i) (b i)) = G * fdWeight p x b := by
      dsimp [G, fdWeight]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      have hg := hpos i
      by_cases hb : b i
      · simp [hb, p, hg]
        field_simp
      · simp [hb, p, hg]
        have hs := hsum (x i)
        field_simp
        linarith
    have hcond := sum_fdWeight_variance_le_inverse p x epsilon hepsilon hp_lo hp_hi
    calc
      (∑ b, (∏ i, q (x i) (b i)) * fdVariance x b) =
          G * ∑ b, fdWeight p x b * fdVariance x b := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [hfactor]
        ring
      _ ≤ G * ((4 / (epsilon ^ 2 * (1 - epsilon))) *
          ∑ b, fdWeight p x b * fdInverse x b) :=
        mul_le_mul_of_nonneg_left hcond hG
      _ = (4 / (epsilon ^ 2 * (1 - epsilon))) *
          ∑ b, (∏ i, q (x i) (b i)) * fdInverse x b := by
        rw [show (∑ b, (∏ i, q (x i) (b i)) * fdInverse x b) =
            G * ∑ b, fdWeight p x b * fdInverse x b by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          rw [hfactor]
          ring]
        ring
  · push Not at hpos
    obtain ⟨i, hi⟩ := hpos
    have hg0 : 0 ≤ g (x i) := by
      rw [← hsum (x i)]
      exact add_nonneg (hq (x i) false) (hq (x i) true)
    have hgzero : g (x i) = 0 := le_antisymm hi hg0
    have hqzero (a : Bool) : q (x i) a = 0 := by
      have hs := hsum (x i)
      have hfalse := hq (x i) false
      have htrue := hq (x i) true
      rw [hgzero] at hs
      cases a <;> nlinarith
    have hweight (b : Fin n → Bool) : (∏ j, q (x j) (b j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (hqzero (b i))
    simp [hweight]

end FiniteDesign

end Causalean.Stat
