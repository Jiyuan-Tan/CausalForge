/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Complete randomization (fixed number of treated units)

**Complete randomization** treats exactly `n₁` of the `N` units, choosing the treated set uniformly
among all size-`n₁` subsets of the population.  Unlike the Bernoulli design, the number treated is
fixed, so unit treatments are negatively dependent.  This file records the design — the uniform law
on `{S : Finset U // S.card = n₁}` — and its **inclusion probabilities**: a unit is treated with
first-order probability `n₁ / N`, and two distinct units are jointly treated with second-order
probability `n₁(n₁−1) / (N(N−1))`.  These are the design facts the Horvitz–Thompson and
difference-in-means estimators' bias and variance are built from.
-/

import Causalean.Experimentation.DesignBased.DesignCore
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Powerset

/-!
# Complete randomization designs

This file defines the fixed-treated-count randomization design `completeRandomization`, the uniform
law on treated subsets of size `n₁`. It also proves the design-space count
`completeRandomization_card`, the first-order inclusion probability
`completeRandomization_incl`, and the second-order inclusion probability
`completeRandomization_incl_pair` for two distinct units. These are the finite-population facts used
by Horvitz-Thompson and difference-in-means bias and variance calculations under complete
randomization.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The number of possible treated sets in complete randomization is the binomial coefficient
`(Fintype.card U).choose n₁`. -/
lemma completeRandomization_card (n₁ : ℕ) :
    Fintype.card {S : Finset U // S.card = n₁} = (Fintype.card U).choose n₁ := by
  rw [Fintype.card_subtype]
  rw [← Finset.card_univ]
  rw [← Finset.card_powersetCard n₁ (Finset.univ : Finset U)]
  congr
  ext S
  simp [Finset.mem_powersetCard]

/-- The **complete-randomization design**: the uniform law on size-`n₁` subsets of the population,
i.e. exactly `n₁` of the `N = card U` units are treated, with every such treated set equally likely.
Requires `n₁ ≤ N` so that the design space is nonempty. -/
noncomputable def completeRandomization (n₁ : ℕ) (hn : n₁ ≤ Fintype.card U) :
    FiniteDesign {S : Finset U // S.card = n₁} where
  p := fun _ => 1 / (Fintype.card {S : Finset U // S.card = n₁} : ℝ)
  p_nonneg := fun _ => one_div_nonneg.mpr (Nat.cast_nonneg _)
  p_sum := by
    -- ∑ over the C(N,n₁) equally-likely treated sets of 1/C(N,n₁) = 1; needs C(N,n₁) > 0 (from hn).
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard_nat : Fintype.card {S : Finset U // S.card = n₁} ≠ 0 := by
      rw [completeRandomization_card]
      exact Nat.choose_ne_zero hn
    have hcard_real : (Fintype.card {S : Finset U // S.card = n₁} : ℝ) ≠ 0 := by
      exact_mod_cast hcard_nat
    field_simp [hcard_real]

private lemma card_powersetCard_filter_mem_succ (i : U) (k : ℕ) :
    (((Finset.univ : Finset U).powersetCard (k + 1)).filter (fun S => i ∈ S)).card =
      ((Finset.univ.erase i).powersetCard k).card := by
  have hps0 := Finset.powersetCard_succ_insert
    (notMem_erase i (Finset.univ : Finset U)) k
  have hps : (Finset.univ : Finset U).powersetCard (k + 1) =
      (Finset.univ.erase i).powersetCard (k + 1) ∪
        ((Finset.univ.erase i).powersetCard k).image (insert i) := by
    simpa [Nat.succ_eq_add_one,
      show insert i (Finset.univ.erase i) = (Finset.univ : Finset U) by simp] using hps0
  rw [hps, Finset.filter_union]
  have hleft :
      (((Finset.univ.erase i).powersetCard (k + 1)).filter (fun S => i ∈ S)) = ∅ := by
    apply Finset.filter_false_of_mem
    intro S hSpow hi
    exact (Finset.notMem_erase i (Finset.univ : Finset U))
      ((Finset.mem_powersetCard.mp hSpow).1 hi)
  have hright :
      ((((Finset.univ.erase i).powersetCard k).image (insert i)).filter
          (fun S => i ∈ S)) =
        ((Finset.univ.erase i).powersetCard k).image (insert i) := by
    ext S
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.1
    · intro hS
      refine ⟨hS, ?_⟩
      rcases Finset.mem_image.mp hS with ⟨T, _hT, rfl⟩
      exact Finset.mem_insert_self _ _
  rw [hleft, hright, Finset.empty_union]
  exact Finset.card_image_of_injOn (by
    intro A hA B hB hEq
    exact insert_erase_invOn.2.injOn (by
      intro hi
      exact (Finset.notMem_erase i (Finset.univ : Finset U))
        ((Finset.mem_powersetCard.mp hA).1 hi)) (by
      intro hi
      exact (Finset.notMem_erase i (Finset.univ : Finset U))
        ((Finset.mem_powersetCard.mp hB).1 hi)) hEq)

private lemma card_design_mem_succ (i : U) (k : ℕ) :
    Fintype.card {S : {S : Finset U // S.card = k + 1} // i ∈ S.val} =
      (Fintype.card U - 1).choose k := by
  let e : {S : {S : Finset U // S.card = k + 1} // i ∈ S.val} ≃
      {S : Finset U // S.card = k + 1 ∧ i ∈ S} :=
    { toFun := fun S => ⟨S.val.val, S.val.property, S.property⟩
      invFun := fun S => ⟨⟨S.val, S.property.1⟩, S.property.2⟩
      left_inv := by intro S; cases S; rfl
      right_inv := by intro S; cases S; rfl }
  rw [Fintype.card_congr e]
  rw [Fintype.card_subtype]
  have hfilter : ((Finset.univ : Finset (Finset U)).filter
      (fun S => S.card = k + 1 ∧ i ∈ S)) =
      (((Finset.univ : Finset U).powersetCard (k + 1)).filter (fun S => i ∈ S)) := by
    ext S
    simp [Finset.mem_powersetCard, and_comm]
  rw [hfilter, card_powersetCard_filter_mem_succ]
  rw [Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ]

private lemma card_powersetCard_filter_mem_pair (i j : U) (hij : i ≠ j) (k : ℕ) :
    (((Finset.univ : Finset U).powersetCard (k + 2)).filter
        (fun S => i ∈ S ∧ j ∈ S)).card =
      (((Finset.univ.erase i).erase j).powersetCard k).card := by
  let e : {S : Finset U // S ∈ ((Finset.univ : Finset U).powersetCard (k + 2)) ∧
        i ∈ S ∧ j ∈ S} ≃
      {T : Finset U // T.card = k ∧ T ⊆ (Finset.univ.erase i).erase j} :=
    { toFun := fun S => by
        refine ⟨(S.val.erase i).erase j, ?_⟩
        rcases S.property with ⟨hSpow, hi, hj⟩
        constructor
        · have hcardS : S.val.card = k + 2 := (Finset.mem_powersetCard.mp hSpow).2
          have hcard_erase_i : (S.val.erase i).card = k + 1 := by
            rw [Finset.card_erase_of_mem hi, hcardS]
            omega
          have hj_erase_i : j ∈ S.val.erase i := by simp [hj, hij.symm]
          rw [Finset.card_erase_of_mem hj_erase_i, hcard_erase_i]
          omega
        · intro x hx
          simp only [Finset.mem_erase] at hx
          rcases hx with ⟨hxj, hxi, _hxS⟩
          simp [hxj, hxi]
      invFun := fun T => by
        refine ⟨insert i (insert j T.val), ?_⟩
        rcases T.property with ⟨hTcard, hTsub⟩
        have hiT : i ∉ T.val := by
          intro hi
          have := hTsub hi
          simp at this
        have hjT : j ∉ T.val := by
          intro hj
          have := hTsub hj
          simp at this
        have hi_insert_j : i ∉ insert j T.val := by
          simp [hiT, hij]
        constructor
        · rw [Finset.mem_powersetCard]
          constructor
          · simp
          · rw [Finset.card_insert_of_notMem hi_insert_j,
              Finset.card_insert_of_notMem hjT, hTcard]
        · constructor
          · simp
          · simp
      left_inv := by
        intro S
        ext x
        rcases S.property with ⟨_hSpow, hi, hj⟩
        by_cases hxi : x = i
        · subst x
          simp [hi]
        · by_cases hxj : x = j
          · subst x
            simp [hj]
          · simp [hxi, hxj]
      right_inv := by
        intro T
        ext x
        rcases T.property with ⟨_hTcard, hTsub⟩
        have hiT : i ∉ T.val := by
          intro hi
          have := hTsub hi
          simp at this
        have hjT : j ∉ T.val := by
          intro hj
          have := hTsub hj
          simp at this
        by_cases hxi : x = i
        · subst x
          simp [hiT]
        · by_cases hxj : x = j
          · subst x
            simp [hjT]
          · simp [hxi, hxj] }
  have hleft :
      Fintype.card {S : Finset U // S ∈ ((Finset.univ : Finset U).powersetCard (k + 2)) ∧
          i ∈ S ∧ j ∈ S} =
        (((Finset.univ : Finset U).powersetCard (k + 2)).filter
          (fun S => i ∈ S ∧ j ∈ S)).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext S
    simp [Finset.mem_powersetCard]
  have hright :
      Fintype.card {T : Finset U // T.card = k ∧ T ⊆ (Finset.univ.erase i).erase j} =
        (((Finset.univ.erase i).erase j).powersetCard k).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext T
    simp [Finset.mem_powersetCard, and_comm]
  rw [← hleft, ← hright]
  exact Fintype.card_congr e

private lemma card_design_mem_pair (i j : U) (hij : i ≠ j) (k : ℕ) :
    Fintype.card {S : {S : Finset U // S.card = k + 2} // i ∈ S.val ∧ j ∈ S.val} =
      (Fintype.card U - 2).choose k := by
  let e : {S : {S : Finset U // S.card = k + 2} // i ∈ S.val ∧ j ∈ S.val} ≃
      {S : Finset U // S.card = k + 2 ∧ i ∈ S ∧ j ∈ S} :=
    { toFun := fun S => ⟨S.val.val, S.val.property, S.property⟩
      invFun := fun S => ⟨⟨S.val, S.property.1⟩, S.property.2⟩
      left_inv := by intro S; cases S; rfl
      right_inv := by intro S; cases S; rfl }
  rw [Fintype.card_congr e]
  rw [Fintype.card_subtype]
  have hfilter : ((Finset.univ : Finset (Finset U)).filter
      (fun S => S.card = k + 2 ∧ i ∈ S ∧ j ∈ S)) =
      (((Finset.univ : Finset U).powersetCard (k + 2)).filter
        (fun S => i ∈ S ∧ j ∈ S)) := by
    ext S
    simp [Finset.mem_powersetCard]
  rw [hfilter, card_powersetCard_filter_mem_pair i j hij k]
  rw [Finset.card_powersetCard]
  have hcard : ((Finset.univ.erase i).erase j).card = Fintype.card U - 2 := by
    rw [Finset.card_erase_of_mem
        (by simp [hij.symm] : j ∈ (Finset.univ : Finset U).erase i),
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    omega
  rw [hcard]

/-- **First-order inclusion probability.** Under complete randomization, a unit is treated with
probability `n₁ / N`. -/
lemma completeRandomization_incl (n₁ : ℕ) (hn : n₁ ≤ Fintype.card U) (i : U) :
    (completeRandomization n₁ hn).Pr (fun S => i ∈ S.val) = (n₁ : ℝ) / (Fintype.card U : ℝ) := by
  -- Pr = (#{size-n₁ sets containing i}) / C(N,n₁) = C(N−1,n₁−1)/C(N,n₁) = n₁/N.
  -- Key counting: size-n₁ subsets containing i ↔ size-(n₁−1) subsets of U∖{i}; and the choose
  -- identity n₁ · C(N,n₁) = N · C(N−1,n₁−1) (`Nat.succ_mul_choose_eq` family).
  cases n₁ with
  | zero =>
      unfold FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind completeRandomization
      simp
  | succ k =>
      unfold FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind completeRandomization
      rw [← Finset.mul_sum]
      have hsum :
          (∑ S : {S : Finset U // S.card = k + 1},
              if i ∈ S.val then (1 : ℝ) else 0) =
            (Fintype.card {S : {S : Finset U // S.card = k + 1} // i ∈ S.val} : ℝ) := by
        rw [Fintype.card_subtype]
        simpa using (Finset.sum_boole (R := ℝ)
          (fun S : {S : Finset U // S.card = k + 1} => i ∈ S.val) Finset.univ)
      rw [hsum, card_design_mem_succ]
      rw [completeRandomization_card]
      have hNpos : 0 < Fintype.card U := Fintype.card_pos_iff.mpr ⟨i⟩
      have hchoose_nat : Fintype.card U * (Fintype.card U - 1).choose k =
          (Fintype.card U).choose (k + 1) * (k + 1) := by
        have h := Nat.add_one_mul_choose_eq (Fintype.card U - 1) k
        rwa [Nat.sub_add_cancel (Nat.succ_le_of_lt hNpos)] at h
      have hchoose_real :
          (Fintype.card U : ℝ) * ((Fintype.card U - 1).choose k : ℝ) =
            ((Fintype.card U).choose (k + 1) : ℝ) * ((k : ℝ) + 1) := by
        exact_mod_cast hchoose_nat
      have hden_real : ((Fintype.card U).choose (k + 1) : ℝ) ≠ 0 := by
        exact_mod_cast Nat.choose_ne_zero hn
      have hN_real : (Fintype.card U : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hNpos)
      field_simp [hden_real, hN_real]
      rw [mul_comm]
      simpa using hchoose_real

/-- **Second-order inclusion probability.** Under complete randomization, two distinct units are
jointly treated with probability `n₁(n₁−1) / (N(N−1))`. -/
lemma completeRandomization_incl_pair (n₁ : ℕ) (hn : n₁ ≤ Fintype.card U) {i j : U} (h : i ≠ j) :
    (completeRandomization n₁ hn).Pr (fun S => i ∈ S.val ∧ j ∈ S.val)
      = ((n₁ : ℝ) * ((n₁ : ℝ) - 1)) / ((Fintype.card U : ℝ) * ((Fintype.card U : ℝ) - 1)) := by
  -- Pr = C(N−2,n₁−2)/C(N,n₁); size-n₁ subsets containing both i,j ↔ size-(n₁−2) subsets of U∖{i,j}.
  cases n₁ with
  | zero =>
      unfold FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind completeRandomization
      simp
  | succ m =>
      cases m with
      | zero =>
          unfold FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind completeRandomization
          have hfalse : ∀ S : {S : Finset U // S.card = 1},
              ¬(i ∈ S.val ∧ j ∈ S.val) := by
            intro S hmem
            have hpair_sub : ({i, j} : Finset U) ⊆ S.val := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl
              · exact hmem.1
              · exact hmem.2
            have hpair_card : ({i, j} : Finset U).card = 2 := by
              simp [h]
            have hle : 2 ≤ S.val.card := by
              rw [← hpair_card]
              exact Finset.card_le_card hpair_sub
            omega
          simp [hfalse]
      | succ k =>
          unfold FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind completeRandomization
          rw [← Finset.mul_sum]
          have hsum :
              (∑ S : {S : Finset U // S.card = k + 2},
                  if i ∈ S.val ∧ j ∈ S.val then (1 : ℝ) else 0) =
                (Fintype.card {S : {S : Finset U // S.card = k + 2} //
                    i ∈ S.val ∧ j ∈ S.val} : ℝ) := by
            rw [Fintype.card_subtype]
            simpa using (Finset.sum_boole (R := ℝ)
              (fun S : {S : Finset U // S.card = k + 2} => i ∈ S.val ∧ j ∈ S.val)
              Finset.univ)
          rw [hsum, card_design_mem_pair i j h k]
          rw [completeRandomization_card]
          have hpair_sub : ({i, j} : Finset U) ⊆ (Finset.univ : Finset U) := by
            intro x _hx
            exact Finset.mem_univ x
          have hpair_card : ({i, j} : Finset U).card = 2 := by
            simp [h]
          have hN2 : 2 ≤ Fintype.card U := by
            rw [← Finset.card_univ, ← hpair_card]
            exact Finset.card_le_card hpair_sub
          have hNpos : 0 < Fintype.card U := by omega
          have h1 : (Fintype.card U - 1) * (Fintype.card U - 2).choose k =
              (Fintype.card U - 1).choose (k + 1) * (k + 1) := by
            have hchoose := Nat.add_one_mul_choose_eq (Fintype.card U - 2) k
            have hsub : Fintype.card U - 2 + 1 = Fintype.card U - 1 := by omega
            rwa [hsub] at hchoose
          have h2 : Fintype.card U * (Fintype.card U - 1).choose (k + 1) =
              (Fintype.card U).choose (k + 2) * (k + 2) := by
            have hchoose := Nat.add_one_mul_choose_eq (Fintype.card U - 1) (k + 1)
            rwa [Nat.sub_add_cancel (Nat.succ_le_of_lt hNpos)] at hchoose
          have hchoose_nat : Fintype.card U * (Fintype.card U - 1) *
                (Fintype.card U - 2).choose k =
              (Fintype.card U).choose (k + 2) * ((k + 2) * (k + 1)) := by
            calc
              Fintype.card U * (Fintype.card U - 1) *
                    (Fintype.card U - 2).choose k =
                  Fintype.card U * ((Fintype.card U - 1) *
                    (Fintype.card U - 2).choose k) := by ring
              _ = Fintype.card U * ((Fintype.card U - 1).choose (k + 1) *
                    (k + 1)) := by rw [h1]
              _ = (Fintype.card U * (Fintype.card U - 1).choose (k + 1)) *
                    (k + 1) := by ring
              _ = ((Fintype.card U).choose (k + 2) * (k + 2)) *
                    (k + 1) := by rw [h2]
              _ = (Fintype.card U).choose (k + 2) *
                    ((k + 2) * (k + 1)) := by ring
          have hchoose_real0 :
              (Fintype.card U : ℝ) * ((Fintype.card U - 1 : ℕ) : ℝ) *
                  ((Fintype.card U - 2).choose k : ℝ) =
                ((Fintype.card U).choose (k + 2) : ℝ) *
                  (((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)) := by
            exact_mod_cast hchoose_nat
          have hchoose_real :
              (Fintype.card U : ℝ) * ((Fintype.card U : ℝ) - 1) *
                  ((Fintype.card U - 2).choose k : ℝ) =
                ((Fintype.card U).choose (k + 2) : ℝ) *
                  (((k : ℝ) + 2) * ((k : ℝ) + 1)) := by
            simpa [Nat.cast_sub (by omega : 1 ≤ Fintype.card U)] using hchoose_real0
          have hden_real : (((Fintype.card U).choose (k + 2) : ℝ) ≠ 0) := by
            exact_mod_cast Nat.choose_ne_zero hn
          have hN_real : (Fintype.card U : ℝ) ≠ 0 := by
            exact_mod_cast (ne_of_gt hNpos)
          have hNm1_real : (Fintype.card U : ℝ) - 1 ≠ 0 := by
            have hNgt1 : (1 : ℝ) < Fintype.card U := by
              exact_mod_cast (by omega : 1 < Fintype.card U)
            exact ne_of_gt (sub_pos.mpr hNgt1)
          field_simp [hden_real, hN_real, hNm1_real]
          ring_nf at hchoose_real ⊢
          rw [hchoose_real]
          norm_num [Nat.cast_add, Nat.cast_ofNat]
          ring

end DesignBased
end Experimentation
end Causalean
