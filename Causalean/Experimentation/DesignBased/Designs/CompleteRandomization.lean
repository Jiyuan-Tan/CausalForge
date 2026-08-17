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
lemma completeRandomization_card {V : Type*} [Fintype V] (n₁ : ℕ) :
    Fintype.card {S : Finset V // S.card = n₁} = (Fintype.card V).choose n₁ := by
  classical
  rw [Fintype.card_subtype]
  rw [← Finset.card_univ]
  rw [← Finset.card_powersetCard n₁ (Finset.univ : Finset V)]
  congr
  ext S
  simp [Finset.mem_powersetCard]

/-- The **complete-randomization design**: the uniform law on size-`n₁` subsets of the population,
i.e. exactly `n₁` of the `N = card U` units are treated, with every such treated set equally likely.
Requires `n₁ ≤ N` so that the design space is nonempty. -/
noncomputable def completeRandomization {V : Type*} [Fintype V] (n₁ : ℕ)
    (hn : n₁ ≤ Fintype.card V) : FiniteDesign {S : Finset V // S.card = n₁} := by
  classical
  exact {
    p := fun _ => 1 / (Fintype.card {S : Finset V // S.card = n₁} : ℝ)
    p_nonneg := fun _ => one_div_nonneg.mpr (Nat.cast_nonneg _)
    p_sum := by
      -- The equally likely treated sets have total mass one; `hn` makes their count positive.
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hcard_nat : Fintype.card {S : Finset V // S.card = n₁} ≠ 0 := by
        rw [completeRandomization_card]
        exact Nat.choose_ne_zero hn
      have hcard_real : (Fintype.card {S : Finset V // S.card = n₁} : ℝ) ≠ 0 := by
        exact_mod_cast hcard_nat
      field_simp [hcard_real] }

/-- Among subsets containing a specified unit and of size `k + 1`,
there are exactly as many as there are size-`k` subsets after that unit is removed. -/
lemma card_powersetCard_filter_mem_succ {α : Type*} [DecidableEq α] (s : Finset α) (i : α)
    (hi : i ∈ s) (k : ℕ) :
    ((s.powersetCard (k + 1)).filter (fun t => i ∈ t)).card =
      ((s.erase i).powersetCard k).card := by
  have hps0 := Finset.powersetCard_succ_insert
    (notMem_erase i s) k
  have hps : s.powersetCard (k + 1) =
      (s.erase i).powersetCard (k + 1) ∪ ((s.erase i).powersetCard k).image (insert i) := by
    simpa [Nat.succ_eq_add_one,
      show insert i (s.erase i) = s by exact Finset.insert_erase hi] using hps0
  rw [hps, Finset.filter_union]
  have hleft :
      (((s.erase i).powersetCard (k + 1)).filter (fun S => i ∈ S)) = ∅ := by
    apply Finset.filter_false_of_mem
    intro S hSpow hi
    exact (Finset.notMem_erase i s)
      ((Finset.mem_powersetCard.mp hSpow).1 hi)
  have hright :
      ((((s.erase i).powersetCard k).image (insert i)).filter
          (fun S => i ∈ S)) =
        ((s.erase i).powersetCard k).image (insert i) := by
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
      exact (Finset.notMem_erase i s)
        ((Finset.mem_powersetCard.mp hA).1 hi)) (by
      intro hi
      exact (Finset.notMem_erase i s)
        ((Finset.mem_powersetCard.mp hB).1 hi)) hEq)

/-- The number of subsets of a finite population with `k + 1` units that contain one specified
unit equals the number of ways to choose `k` units from the remaining population. -/
lemma card_design_mem_succ (i : U) (k : ℕ) :
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
  rw [hfilter, card_powersetCard_filter_mem_succ (Finset.univ : Finset U) i (Finset.mem_univ i)]
  rw [Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ]

/-- Among the fixed-size subsets of a finite set that contain two distinct specified elements,
the count equals the number of subsets of the remaining set after those two elements are removed.
This is the finite-population counting identity behind pairwise inclusion probabilities. -/
lemma card_powersetCard_filter_mem_pair {α : Type*} [DecidableEq α] (s : Finset α) (i j : α)
    (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) (k : ℕ) :
    ((s.powersetCard (k + 2)).filter (fun t => i ∈ t ∧ j ∈ t)).card =
      (((s.erase i).erase j).powersetCard k).card := by
  refine Finset.card_bij' (fun t _ => (t.erase i).erase j) (fun t _ => insert i (insert j t))
    ?_ ?_ ?_ ?_
  · intro t ht
    rcases Finset.mem_filter.mp ht with ⟨htpow, hti, htj⟩
    rw [Finset.mem_powersetCard]
    constructor
    · intro x hx
      rcases Finset.mem_erase.mp hx with ⟨hxj, hx⟩
      rcases Finset.mem_erase.mp hx with ⟨hxi, hxt⟩
      exact Finset.mem_erase.mpr ⟨hxj, Finset.mem_erase.mpr ⟨hxi,
        (Finset.mem_powersetCard.mp htpow).1 hxt⟩⟩
    · have htcard : t.card = k + 2 := (Finset.mem_powersetCard.mp htpow).2
      have hterase_i : (t.erase i).card = k + 1 := by
        rw [Finset.card_erase_of_mem hti, htcard]
        omega
      have htj_erase_i : j ∈ t.erase i := by simp [htj, hij.symm]
      rw [Finset.card_erase_of_mem htj_erase_i, hterase_i]
      omega
  · intro t ht
    rcases Finset.mem_powersetCard.mp ht with ⟨htsub, htcard⟩
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_powersetCard]
      constructor
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hi
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hj
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp (htsub hx)).2).2
      · have hti : i ∉ t := by
          intro hti
          have := htsub hti
          simp at this
        have htj : j ∉ t := by
          intro htj
          have := htsub htj
          simp at this
        have hti_insert_j : i ∉ insert j t := by simp [hti, hij]
        rw [Finset.card_insert_of_notMem hti_insert_j,
          Finset.card_insert_of_notMem htj, htcard]
    · simp
  · intro t ht
    rcases Finset.mem_filter.mp ht with ⟨_htpow, hti, htj⟩
    ext x
    by_cases hxi : x = i
    · subst x
      simp [hti]
    · by_cases hxj : x = j
      · subst x
        simp [htj]
      · simp [hxi, hxj]
  · intro t ht
    have hti : i ∉ t := by
      intro hti
      have := (Finset.mem_powersetCard.mp ht).1 hti
      simp at this
    have htj : j ∉ t := by
      intro htj
      have := (Finset.mem_powersetCard.mp ht).1 htj
      simp at this
    ext x
    by_cases hxi : x = i
    · subst x
      simp [hti]
    · by_cases hxj : x = j
      · subst x
        simp [htj]
      · simp [hxi, hxj]

/-- The number of subsets of a finite population with `k + 2` units that contain two distinct
specified units equals the number of ways to choose `k` units from the remaining population. -/
lemma card_design_mem_pair (i j : U) (hij : i ≠ j) (k : ℕ) :
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
  rw [hfilter, card_powersetCard_filter_mem_pair (Finset.univ : Finset U) i j
    (Finset.mem_univ i) (Finset.mem_univ j) hij k]
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
        exact Finset.sum_boole (R := ℝ)
          (fun S : {S : Finset U // S.card = k + 1} => i ∈ S.val) Finset.univ
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

/-- **Second-order inclusion probability.** Under complete randomization treating exactly `n₁`
of the `N` units, where [the treated count `n₁` does not exceed the population size `N`](hyp:hn),
[two distinct units](hyp:h) are [jointly treated with probability `n₁(n₁−1) / (N(N−1))`](goal). -/
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
            exact Finset.sum_boole (R := ℝ)
              (fun S : {S : Finset U // S.card = k + 2} => i ∈ S.val ∧ j ∈ S.val)
              Finset.univ
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
