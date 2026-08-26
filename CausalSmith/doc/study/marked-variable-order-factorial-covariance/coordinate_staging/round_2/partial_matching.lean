/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset

/-!
# Finite partial matchings

This module packages a partial matching between two finite coordinate sets as
an equivalence between selected subsets.  It provides the fixed-cardinality
families used to classify collisions between two ordered injective tuples.
-/

namespace Causalean.Stat

open scoped BigOperators

/-- A partial matching between ordered coordinate sets of sizes `r` and `s`
selects a subset from each side and pairs the selected coordinates bijectively. -/
structure PartialMatching (r s : ℕ) where
  /-- The selected coordinates on the left. -/
  left : Finset (Fin r)
  /-- The selected coordinates on the right. -/
  right : Finset (Fin s)
  /-- The one-to-one pairing between the selected coordinate sets. -/
  equiv : (left : Set (Fin r)) ≃ (right : Set (Fin s))

namespace PartialMatching

variable {r s : ℕ}

/-- The size of a partial matching is its number of paired coordinates. -/
def size (M : PartialMatching r s) : ℕ := M.left.card

/-- Given [a partial matching](hyp:M), [its selected right subset has the same
number of coordinates as the matching](goal). -/
theorem right_card (M : PartialMatching r s) : M.right.card = M.size := by
  simpa [size] using (Fintype.card_congr M.equiv).symm

/-- The empty partial matching between two coordinate sets pairs no coordinates. -/
def empty (r s : ℕ) : PartialMatching r s where
  left := ∅
  right := ∅
  equiv :=
    { toFun := fun x => False.elim (by simpa using x.property)
      invFun := fun x => False.elim (by simpa using x.property)
      left_inv := fun x => False.elim (by simpa using x.property)
      right_inv := fun x => False.elim (by simpa using x.property) }

/-- For [coordinate-set sizes `r` and `s`](hyp:r,s), [the empty partial matching
has no pairs](goal). -/
@[simp] theorem empty_size (r s : ℕ) : (empty r s).size = 0 := by
  simp [size, empty]

/-- [A partial matching](hyp:M) [with no pairs](hyp:hM) [is the empty partial
matching](goal). -/
theorem eq_empty_of_size_eq_zero (M : PartialMatching r s) (hM : M.size = 0) :
    M = empty r s := by
  have hleft : M.left = ∅ := Finset.card_eq_zero.mp (by simpa [size] using hM)
  have hright : M.right = ∅ := Finset.card_eq_zero.mp (by simpa [right_card] using hM)
  cases M with
  | mk left right equiv =>
      simp only at hleft hright
      subst left
      subst right
      congr
      apply Equiv.ext
      intro x
      exact False.elim (by simpa using x.property)

/-- The merged coordinate set retains every left coordinate and only the
unmatched right coordinates. -/
abbrev MergedIndex (M : PartialMatching r s) :=
  Fin r ⊕ {j : Fin s // j ∉ M.right}

/-- A left coordinate occupies its own position in the merged coordinate set. -/
def leftInjection (M : PartialMatching r s) (i : Fin r) : M.MergedIndex :=
  Sum.inl i

/-- A right coordinate shares the position of its matched left coordinate, or
occupies a separate position when it is unmatched. -/
noncomputable def rightInjection (M : PartialMatching r s) (j : Fin s) : M.MergedIndex := by
  classical
  by_cases hj : j ∈ M.right
  · exact Sum.inl (M.equiv.symm ⟨j, hj⟩).1
  · exact Sum.inr ⟨j, hj⟩

/-- For [a partial matching between coordinate sets of sizes `r` and `s`](hyp:M),
[the merged coordinate set contains `r + s` minus the matching size coordinates](goal). -/
theorem mergedIndex_card (M : PartialMatching r s) :
    Fintype.card M.MergedIndex = r + s - M.size := by
  rw [Fintype.card_sum]
  simp only [Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_coe,
    right_card]
  have hs : M.size ≤ s := by
    rw [← M.right_card]
    simpa using M.right.card_le_univ
  omega

end PartialMatching

/-- Partial matchings are represented exactly by a selected subset on each side
together with a bijection between those subsets. -/
def partialMatchingEquivSigma (r s : ℕ) :
    PartialMatching r s ≃
      Σ left : Finset (Fin r), Σ right : Finset (Fin s),
        (left : Set (Fin r)) ≃ (right : Set (Fin s)) where
  toFun M := ⟨M.left, M.right, M.equiv⟩
  invFun M := ⟨M.1, M.2.1, M.2.2⟩
  left_inv M := by cases M; rfl
  right_inv M := by cases M; rfl

/-- The equivalences between two finite sets form a finite collection. -/
noncomputable local instance equivFintype {α β : Type*} [Fintype α] [Fintype β] :
    Fintype (α ≃ β) := by
  classical
  let e : (α ≃ β) ≃ {f : α → β // Function.Bijective f} :=
    { toFun := fun f => ⟨f, f.bijective⟩
      invFun := fun f => Equiv.ofBijective f.1 f.2
      left_inv := fun f => Equiv.ext (fun x => rfl)
      right_inv := fun f => Subtype.ext (funext (fun x => rfl)) }
  exact Fintype.ofEquiv {f : α → β // Function.Bijective f} e.symm

/-- The finite subsets of a finite set form a finite collection. -/
noncomputable local instance finsetFintype {α : Type*} [Fintype α] :
    Fintype (Finset α) where
  elems := Finset.univ.powerset
  complete := by simp

/-- The collection of partial matchings between two finite coordinate sets is finite. -/
noncomputable instance partialMatchingFintype (r s : ℕ) : Fintype (PartialMatching r s) := by
  classical
  exact Fintype.ofEquiv _ (partialMatchingEquivSigma r s).symm

/-- The fixed-size matching family consists of all partial matchings with exactly
the prescribed number of pairs. -/
noncomputable def partialMatchingsOfSize (r s h : ℕ) : Finset (PartialMatching r s) := by
  classical
  exact Finset.univ.filter (fun M => M.size = h)

/-- [A partial matching](hyp:M) [belongs to the family with `h` pairs exactly
when its matching size is `h`](goal). -/
@[simp] theorem mem_partialMatchingsOfSize {r s h : ℕ} (M : PartialMatching r s) :
    M ∈ partialMatchingsOfSize r s h ↔ M.size = h := by
  simp [partialMatchingsOfSize]

/-- For [coordinate-set sizes `r` and `s` and matching size `h`](hyp:r,s,h),
[the number of partial matchings is the product of the two subset counts and
the number of permutations of `h` objects](goal). -/
theorem card_partialMatchingsOfSize (r s h : ℕ) :
    (partialMatchingsOfSize r s h).card =
      Nat.choose r h * Nat.choose s h * h.factorial := by
  /- Count the left and right `h`-subsets, then identify equivalences between
  two `h`-element subtypes with permutations of `Fin h`. -/
  classical
  let e : {M : PartialMatching r s // M.size = h} ≃
      Σ left : {L : Finset (Fin r) // L.card = h},
        Σ right : {R : Finset (Fin s) // R.card = h},
          (left.1 : Set (Fin r)) ≃ (right.1 : Set (Fin s)) :=
    { toFun := fun M =>
        ⟨⟨M.1.left, M.2⟩,
          ⟨⟨M.1.right, by simpa [M.2] using M.1.right_card⟩, M.1.equiv⟩⟩
      invFun := fun M =>
        ⟨⟨M.1.1, M.2.1.1, M.2.2⟩, M.1.2⟩
      left_inv := by
        rintro ⟨⟨left, right, equiv⟩, hsize⟩
        rfl
      right_inv := by
        rintro ⟨⟨left, hleft⟩, ⟨⟨right, hright⟩, equiv⟩⟩
        rfl }
  rw [← Fintype.card_of_subtype (partialMatchingsOfSize r s h)
    (fun M => mem_partialMatchingsOfSize M)]
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp_rw [Fintype.card_sigma]
  have hequiv : ∀ (left : {L : Finset (Fin r) // L.card = h})
      (right : {R : Finset (Fin s) // R.card = h}),
      Fintype.card ((left.1 : Set (Fin r)) ≃ (right.1 : Set (Fin s))) = h.factorial := by
    intro left right
    have hcard : Fintype.card (left.1 : Set (Fin r)) =
        Fintype.card (right.1 : Set (Fin s)) := by
      simp [left.2, right.2]
    let f := Classical.choice (Fintype.card_eq.mp hcard)
    exact (@Fintype.card_congr
      ((left.1 : Set (Fin r)) ≃ (right.1 : Set (Fin s)))
      ((left.1 : Set (Fin r)) ≃ (right.1 : Set (Fin s)))
      equivFintype Equiv.instFintype (Equiv.refl _)).trans (by
        simpa [left.2] using Fintype.card_equiv f)
  simp_rw [hequiv]
  simp [Fintype.card_finset_len, Nat.mul_assoc]

/-- [A partial matching](hyp:M) [has at most the smaller coordinate-set size
many pairs](goal). -/
theorem PartialMatching.size_le_min (M : PartialMatching r s) :
    M.size ≤ min r s := by
  apply le_min
  · simpa [PartialMatching.size] using M.left.card_le_univ
  · simpa [PartialMatching.right_card] using M.right.card_le_univ

/-- Given [a quantity assigned to each partial matching](hyp:F), [summing it over
all matchings equals summing first by matching size through the smaller
coordinate-set size](goal). -/
theorem sum_partialMatchingsOfSize {α : Type*} [AddCommMonoid α]
    (F : PartialMatching r s → α) :
    (∑ M : PartialMatching r s, F M) =
      ∑ h ∈ Finset.range (min r s + 1), ∑ M ∈ partialMatchingsOfSize r s h, F M := by
  /- Partition `Finset.univ` by `M.size`; `size_le_min` supplies the range bound. -/
  classical
  simp only [partialMatchingsOfSize, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M _
  rw [Finset.sum_eq_single M.size]
  · simp
  · intro h hh hne
    simp [hne.symm]
  · exact fun hnotmem => False.elim
      (hnotmem (Finset.mem_range.mpr (Nat.lt_succ_of_le M.size_le_min)))

end Causalean.Stat
