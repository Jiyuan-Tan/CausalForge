/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.UStatistic.OrderM.PartialMatching
import Causalean.Stat.UStatistic.OrderM.Variance

/-!
# Mixed-order partial-matching expansion

This module classifies pairs of injective tuples by their cross-tuple collision
matching.  It gives pointwise product and product-law expectation expansions,
then exposes the size-zero normalization correction in the centered identity.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-- The merged product kernel evaluates matched left and right factors on the
same observation and unmatched factors on separate observations. -/
noncomputable def mergedProductKernel {r s : ℕ} (f : Fin r → X → ℝ)
    (g : Fin s → X → ℝ) (M : PartialMatching r s) :
    (M.MergedIndex → X) → ℝ :=
  fun z =>
    (∏ i : Fin r, f i (z (M.leftInjection i))) *
      ∏ j : Fin s, g j (z (M.rightInjection j))

/-- The merged product moment is the expectation of a merged product kernel
under independent copies indexed by its merged coordinates. -/
noncomputable def mergedProductMoment {r s : ℕ} (P : Measure X)
    (f : Fin r → X → ℝ) (g : Fin s → X → ℝ) (M : PartialMatching r s) : ℝ :=
  ∫ z, mergedProductKernel f g M z ∂(Measure.pi fun _ : M.MergedIndex => P)

/-- The normalization of a partial matching is the falling factorial for its
number of distinct observations divided by the two marginal falling factorials. -/
noncomputable def matchingNormalization (n : ℕ) {r s : ℕ}
    (M : PartialMatching r s) : ℝ :=
  (n.descFactorial (r + s - M.size) : ℝ) /
    ((n.descFactorial r : ℝ) * (n.descFactorial s : ℝ))

private noncomputable def matchingRight {r s n : ℕ}
    (t : Fin r ↪ Fin n) (q : Fin s ↪ Fin n) (i : Fin r)
    (hi : ∃ j, t i = q j) : Fin s :=
  Classical.choose hi

private theorem matchingRight_spec {r s n : ℕ}
    (t : Fin r ↪ Fin n) (q : Fin s ↪ Fin n) (i : Fin r)
    (hi : ∃ j, t i = q j) :
    t i = q (matchingRight t q i hi) :=
  Classical.choose_spec hi

private noncomputable def matchingLeft {r s n : ℕ}
    (t : Fin r ↪ Fin n) (q : Fin s ↪ Fin n) (j : Fin s)
    (hj : ∃ i, t i = q j) : Fin r :=
  Classical.choose hj

private theorem matchingLeft_spec {r s n : ℕ}
    (t : Fin r ↪ Fin n) (q : Fin s ↪ Fin n) (j : Fin s)
    (hj : ∃ i, t i = q j) :
    t (matchingLeft t q j hj) = q j :=
  Classical.choose_spec hj

/-- The collision relation of two injective tuples, packaged as a partial matching. -/
private noncomputable def collisionMatching {r s n : ℕ}
    (t : Fin r ↪ Fin n) (q : Fin s ↪ Fin n) : PartialMatching r s := by
  classical
  let L := Finset.univ.filter (fun i => ∃ j, t i = q j)
  let R := Finset.univ.filter (fun j => ∃ i, t i = q j)
  let toFun : {i : Fin r // i ∈ L} → {j : Fin s // j ∈ R} := fun i => by
    have hi : ∃ j, t i.1 = q j := (Finset.mem_filter.mp i.2).2
    refine ⟨matchingRight t q i.1 hi, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨i.1, matchingRight_spec t q i.1 hi⟩
  let invFun : {j : Fin s // j ∈ R} → {i : Fin r // i ∈ L} := fun j => by
    have hj : ∃ i, t i = q j.1 := (Finset.mem_filter.mp j.2).2
    refine ⟨matchingLeft t q j.1 hj, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨j.1, matchingLeft_spec t q j.1 hj⟩
  exact
    { left := L
      right := R
      equiv :=
        { toFun := toFun
          invFun := invFun
          left_inv := by
            intro i
            apply Subtype.ext
            apply t.injective
            have hi : ∃ j, t i.1 = q j := (Finset.mem_filter.mp i.2).2
            have hto : t i.1 = q (toFun i).1 := by
              simpa [toFun] using matchingRight_spec t q i.1 hi
            have hj : ∃ i', t i' = q (toFun i).1 :=
              (Finset.mem_filter.mp (toFun i).2).2
            have hinv : t (invFun (toFun i)).1 = q (toFun i).1 := by
              simpa [invFun] using matchingLeft_spec t q (toFun i).1 hj
            exact hinv.trans hto.symm
          right_inv := by
            intro j
            apply Subtype.ext
            apply q.injective
            have hj : ∃ i, t i = q j.1 := (Finset.mem_filter.mp j.2).2
            have hinv : t (invFun j).1 = q j.1 := by
              simpa [invFun] using matchingLeft_spec t q j.1 hj
            have hi : ∃ j', t (invFun j).1 = q j' :=
              (Finset.mem_filter.mp (invFun j).2).2
            have hto : t (invFun j).1 = q (toFun (invFun j)).1 := by
              simpa [toFun] using matchingRight_spec t q (invFun j).1 hi
            exact hto.symm.trans hinv } }

private theorem leftInjection_injective {r s : ℕ} (M : PartialMatching r s) :
    Function.Injective M.leftInjection := by
  intro i i' h
  simpa [PartialMatching.leftInjection] using h

private theorem rightInjection_injective {r s : ℕ} (M : PartialMatching r s) :
    Function.Injective M.rightInjection := by
  classical
  intro j j' h
  by_cases hj : j ∈ M.right <;> by_cases hj' : j' ∈ M.right
  · simp only [PartialMatching.rightInjection, hj, hj', dite_true] at h
    have he : M.equiv.symm ⟨j, hj⟩ = M.equiv.symm ⟨j', hj'⟩ := by
      apply Subtype.ext
      exact Sum.inl.inj h
    exact congrArg Subtype.val (M.equiv.symm.injective he)
  · simp [PartialMatching.rightInjection, hj, hj'] at h
  · simp [PartialMatching.rightInjection, hj, hj'] at h
  · simp only [PartialMatching.rightInjection, hj, hj', dite_false] at h
    exact congrArg Subtype.val (Sum.inr.inj h)

private theorem exists_rightInjection_eq_leftInjection_iff {r s : ℕ}
    (M : PartialMatching r s) (i : Fin r) :
    (∃ j, M.leftInjection i = M.rightInjection j) ↔ i ∈ M.left := by
  classical
  constructor
  · rintro ⟨j, h⟩
    by_cases hj : j ∈ M.right
    · simp only [PartialMatching.leftInjection, PartialMatching.rightInjection, hj,
        dite_true] at h
      have hi : (M.equiv.symm ⟨j, hj⟩).1 = i := Sum.inl.inj h.symm
      simpa [← hi] using (M.equiv.symm ⟨j, hj⟩).2
    · simp [PartialMatching.leftInjection, PartialMatching.rightInjection, hj] at h
  · intro hi
    let j : Fin s := (M.equiv ⟨i, hi⟩).1
    have hj : j ∈ M.right := (M.equiv ⟨i, hi⟩).2
    refine ⟨j, ?_⟩
    simp only [PartialMatching.leftInjection, PartialMatching.rightInjection, hj, dite_true]
    congr
    simpa [j]

private theorem exists_leftInjection_eq_rightInjection_iff {r s : ℕ}
    (M : PartialMatching r s) (j : Fin s) :
    (∃ i, M.leftInjection i = M.rightInjection j) ↔ j ∈ M.right := by
  classical
  constructor
  · rintro ⟨i, h⟩
    by_cases hj : j ∈ M.right
    · exact hj
    · simp [PartialMatching.leftInjection, PartialMatching.rightInjection, hj] at h
  · intro hj
    refine ⟨(M.equiv.symm ⟨j, hj⟩).1, ?_⟩
    simp [PartialMatching.leftInjection, PartialMatching.rightInjection, hj]

private noncomputable def mergeTuple {r s n : ℕ}
    (t : Fin r ↪ Fin n) (q : Fin s ↪ Fin n) :
    (collisionMatching t q).MergedIndex ↪ Fin n where
  toFun x := match x with
    | Sum.inl i => t i
    | Sum.inr j => q j.1
  inj' := by
    intro x y hxy
    cases x with
    | inl i =>
        cases y with
        | inl i' =>
            exact congrArg Sum.inl (t.injective hxy)
        | inr j =>
            exfalso
            have hj : ∃ i', t i' = q j.1 := ⟨i, hxy⟩
            exact j.2 (by
              change j.1 ∈ (collisionMatching t q).right
              simpa [collisionMatching] using hj)
    | inr j =>
        cases y with
        | inl i =>
            exfalso
            have hj : ∃ i', t i' = q j.1 := ⟨i, hxy.symm⟩
            exact j.2 (by
              change j.1 ∈ (collisionMatching t q).right
              simpa [collisionMatching] using hj)
        | inr j' =>
            congr 1
            apply Subtype.ext
            exact q.injective hxy

private noncomputable def unmergeTuple {r s n : ℕ}
    (p : Σ M : PartialMatching r s, M.MergedIndex ↪ Fin n) :
    (Fin r ↪ Fin n) × (Fin s ↪ Fin n) :=
  (⟨fun i => p.2 (p.1.leftInjection i),
      p.2.injective.comp (leftInjection_injective p.1)⟩,
    ⟨fun j => p.2 (p.1.rightInjection j),
      p.2.injective.comp (rightInjection_injective p.1)⟩)

private theorem collisionMatching_unmerge {r s n : ℕ}
    (M : PartialMatching r s) (u : M.MergedIndex ↪ Fin n) :
    collisionMatching (unmergeTuple ⟨M, u⟩).1 (unmergeTuple ⟨M, u⟩).2 = M := by
  classical
  cases M with
  | mk L R e =>
      let M : PartialMatching r s := ⟨L, R, e⟩
      let t : Fin r ↪ Fin n :=
        ⟨fun i => u (M.leftInjection i),
          u.injective.comp (leftInjection_injective M)⟩
      let q : Fin s ↪ Fin n :=
        ⟨fun j => u (M.rightInjection j),
          u.injective.comp (rightInjection_injective M)⟩
      change collisionMatching t q = M
      have hL : Finset.univ.filter (fun i => ∃ j, t i = q j) = L := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨j, hij⟩
          exact (exists_rightInjection_eq_leftInjection_iff
            M i).mp ⟨j, u.injective hij⟩
        · intro hi
          obtain ⟨j, hij⟩ := (exists_rightInjection_eq_leftInjection_iff
            M i).mpr hi
          exact ⟨j, congrArg u hij⟩
      have hR : Finset.univ.filter (fun j => ∃ i, t i = q j) = R := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨i, hij⟩
          exact (exists_leftInjection_eq_rightInjection_iff
            M j).mp ⟨i, u.injective hij⟩
        · intro hj
          obtain ⟨i, hij⟩ := (exists_leftInjection_eq_rightInjection_iff
            M j).mpr hj
          exact ⟨i, congrArg u hij⟩
      have hmatched : ∀ i : {i : Fin r // i ∈ L}, t i.1 = q (e i).1 := by
        intro i
        dsimp only [t, q]
        exact congrArg u (by
          simp [M, PartialMatching.leftInjection, PartialMatching.rightInjection])
      clear_value t q
      clear u
      cases hL
      cases hR
      unfold collisionMatching
      dsimp only [M]
      congr 1
      apply Equiv.ext
      intro i
      apply Subtype.ext
      apply q.injective
      exact (matchingRight_spec t q i.1 (by simpa using i.2)).symm.trans (hmatched i)

@[simp] private theorem mergeTuple_left {r s n : ℕ}
    (t : Fin r ↪ Fin n) (q : Fin s ↪ Fin n) (i : Fin r) :
    mergeTuple t q ((collisionMatching t q).leftInjection i) = t i := rfl

@[simp] private theorem mergeTuple_right {r s n : ℕ}
    (t : Fin r ↪ Fin n) (q : Fin s ↪ Fin n) (j : Fin s) :
    mergeTuple t q ((collisionMatching t q).rightInjection j) = q j := by
  classical
  by_cases hj : ∃ i, t i = q j
  · have hjmem : j ∈ (collisionMatching t q).right := by
      simpa [collisionMatching] using hj
    simp only [PartialMatching.rightInjection, hjmem, dite_true, mergeTuple]
    change t (matchingLeft t q j _) = q j
    exact matchingLeft_spec t q j hj
  · have hjmem : j ∉ (collisionMatching t q).right := by
      simpa [collisionMatching] using hj
    simp only [PartialMatching.rightInjection, hjmem, dite_false, mergeTuple]
    rfl

private theorem unmerge_merge {r s n : ℕ} (t : Fin r ↪ Fin n) (q : Fin s ↪ Fin n) :
    unmergeTuple ⟨collisionMatching t q, mergeTuple t q⟩ = (t, q) := by
  dsimp only [unmergeTuple]
  apply Prod.ext
  · ext i
    exact congrArg Fin.val (mergeTuple_left t q i)
  · ext j
    exact congrArg Fin.val (mergeTuple_right t q j)

private theorem unmergeTuple_injective {r s n : ℕ} :
    Function.Injective
      (unmergeTuple : (Σ M : PartialMatching r s, M.MergedIndex ↪ Fin n) →
        (Fin r ↪ Fin n) × (Fin s ↪ Fin n)) := by
  rintro ⟨M, u⟩ ⟨N, v⟩ h
  have hMN : M = N := by
    calc
      M = collisionMatching (unmergeTuple ⟨M, u⟩).1
          (unmergeTuple ⟨M, u⟩).2 := (collisionMatching_unmerge M u).symm
      _ = collisionMatching (unmergeTuple ⟨N, v⟩).1
          (unmergeTuple ⟨N, v⟩).2 := by rw [h]
      _ = N := collisionMatching_unmerge N v
  cases hMN
  congr 1
  ext x
  cases x with
  | inl i =>
      have hi := congrArg (fun p => p.1 i) h
      exact congrArg Fin.val hi
  | inr j =>
      have hj := congrArg (fun p => p.2 j.1) h
      exact congrArg Fin.val (by
        simpa [unmergeTuple, PartialMatching.rightInjection, j.2] using hj)

private noncomputable def tuplePairEquivMergedTuple (r s n : ℕ) :
    ((Fin r ↪ Fin n) × (Fin s ↪ Fin n)) ≃
      (Σ M : PartialMatching r s, M.MergedIndex ↪ Fin n) :=
  (Equiv.ofBijective unmergeTuple
    ⟨unmergeTuple_injective, fun p =>
      ⟨⟨collisionMatching p.1 p.2, mergeTuple p.1 p.2⟩,
        unmerge_merge p.1 p.2⟩⟩).symm

private theorem sum_finiteInjectiveTuples_eq_sum_embedding
    {ι : Type*} [Fintype ι] (n : ℕ) (F : (ι → Fin n) → ℝ) :
    (∑ t ∈ finiteInjectiveTuples ι n, F t) =
      ∑ t : ι ↪ Fin n, F t := by
  classical
  rw [Finset.sum_subtype (p := Function.Injective) (finiteInjectiveTuples ι n)
    (fun t => by simp [finiteInjectiveTuples]) F]
  let e : {t : ι → Fin n // Function.Injective t} ≃ (ι ↪ Fin n) :=
    { toFun := fun t => ⟨t.1, t.2⟩
      invFun := fun t => ⟨t, t.injective⟩
      left_inv := fun t => by cases t; rfl
      right_inv := fun t => by cases t; rfl }
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

private theorem mergedProductKernel_unmerge {r s n : ℕ}
    (f : Fin r → X → ℝ) (g : Fin s → X → ℝ)
    (p : Σ M : PartialMatching r s, M.MergedIndex ↪ Fin n)
    (Y : Fin n → X) :
    mergedProductKernel f g p.1 (fun x => Y (p.2 x)) =
      orderedProductKernel f (fun i => Y ((unmergeTuple p).1 i)) *
        orderedProductKernel g (fun j => Y ((unmergeTuple p).2 j)) := by
  rfl

private theorem unnormalized_product_sum_expansion
    (S : Causalean.Stat.IIDSample Ω X μ P) {r s n : ℕ}
    (f : Fin r → X → ℝ) (g : Fin s → X → ℝ) (ω : Ω) :
    (∑ t ∈ finiteInjectiveTuples (Fin r) n,
        orderedProductKernel f (fun i => S.Z (t i : ℕ) ω)) *
      (∑ q ∈ finiteInjectiveTuples (Fin s) n,
        orderedProductKernel g (fun j => S.Z (q j : ℕ) ω)) =
      ∑ M : PartialMatching r s,
        ∑ u ∈ finiteInjectiveTuples M.MergedIndex n,
          mergedProductKernel f g M (fun x => S.Z (u x : ℕ) ω) := by
  classical
  rw [sum_finiteInjectiveTuples_eq_sum_embedding,
    sum_finiteInjectiveTuples_eq_sum_embedding]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Fintype.sum_prod_type (fun p : (Fin r ↪ Fin n) × (Fin s ↪ Fin n) =>
    orderedProductKernel f (fun i => S.Z (p.1 i : ℕ) ω) *
      orderedProductKernel g (fun j => S.Z (p.2 j : ℕ) ω))]
  rw [Fintype.sum_equiv (tuplePairEquivMergedTuple r s n)
    (fun p => orderedProductKernel f (fun i => S.Z (p.1 i : ℕ) ω) *
      orderedProductKernel g (fun j => S.Z (p.2 j : ℕ) ω))
    (fun p => mergedProductKernel f g p.1 (fun x => S.Z (p.2 x : ℕ) ω))]
  · rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro M _
    change (∑ u : M.MergedIndex ↪ Fin n,
      mergedProductKernel f g M (fun x => S.Z (u x : ℕ) ω)) = _
    exact (sum_finiteInjectiveTuples_eq_sum_embedding n
      (fun u : M.MergedIndex → Fin n =>
        mergedProductKernel f g M (fun x => S.Z (u x : ℕ) ω))).symm
  · intro p
    have hp := (tuplePairEquivMergedTuple r s n).symm_apply_apply p
    change unmergeTuple ((tuplePairEquivMergedTuple r s n) p) = p at hp
    let Y : Fin n → X := fun k => S.Z (k : ℕ) ω
    change orderedProductKernel f (fun i => Y (p.1 i)) *
        orderedProductKernel g (fun j => Y (p.2 j)) =
      mergedProductKernel f g ((tuplePairEquivMergedTuple r s n) p).1
        (fun x => Y (((tuplePairEquivMergedTuple r s n) p).2 x))
    rw [mergedProductKernel_unmerge, hp]

private theorem matchingNormalization_mul_normalizedFiniteKernelStatistic
    (S : Causalean.Stat.IIDSample Ω X μ P) {r s n : ℕ}
    (hrn : r ≤ n) (hsn : s ≤ n) (M : PartialMatching r s)
    (k : (M.MergedIndex → X) → ℝ) (ω : Ω) :
    matchingNormalization n M * normalizedFiniteKernelStatistic S k n ω =
      ((n.descFactorial r : ℝ)⁻¹ * (n.descFactorial s : ℝ)⁻¹) *
        ∑ u ∈ finiteInjectiveTuples M.MergedIndex n,
          k (fun x => S.Z (u x : ℕ) ω) := by
  classical
  by_cases hc : Fintype.card M.MergedIndex ≤ n
  · have hr : (n.descFactorial r : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_pos.mpr hrn).ne'
    have hs : (n.descFactorial s : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_pos.mpr hsn).ne'
    have hm : (n.descFactorial (Fintype.card M.MergedIndex) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_pos.mpr hc).ne'
    unfold matchingNormalization normalizedFiniteKernelStatistic
    rw [← M.mergedIndex_card]
    field_simp
  · have hempty : finiteInjectiveTuples M.MergedIndex n = ∅ := by
      apply (Finset.not_nonempty_iff_eq_empty).mp
      rintro ⟨u, hu⟩
      have huinj : Function.Injective u := (Finset.mem_filter.mp hu).2
      exact hc (by simpa using Fintype.card_le_of_injective u huinj)
    simp [normalizedFiniteKernelStatistic, hempty]

/-- Given [sample size `n`, statistic orders `r` and `s`, and overlap size `h`](hyp:n,r,s,h),
[a partial matching](hyp:M) [belonging to the size-`h` family](hyp:hM), [its
normalization has the falling factorial of length `r + s - h` in the numerator](goal). -/
theorem matchingNormalization_of_mem {n r s h : ℕ} {M : PartialMatching r s}
    (hM : M ∈ partialMatchingsOfSize r s h) :
    matchingNormalization n M =
      (n.descFactorial (r + s - h) : ℝ) /
        ((n.descFactorial r : ℝ) * (n.descFactorial s : ℝ)) := by
  rw [matchingNormalization]
  rw [(mem_partialMatchingsOfSize M).mp hM]

/-- For [an i.i.d. sample](hyp:S), [statistic orders and a sample size](hyp:r,s,n),
if [the first order does not exceed the sample size](hyp:hrn) and [the second
order does not exceed the sample size](hyp:hsn), then [the pointwise product of
the statistics built from two coordinate-function families](hyp:f,g) [equals
the sum of normalized merged-kernel statistics over all partial matchings,
grouped by overlap size](goal). -/
theorem normalizedOrderedProductStatistic_mul_expansion
    (S : Causalean.Stat.IIDSample Ω X μ P) {r s n : ℕ}
    (hrn : r ≤ n) (hsn : s ≤ n) (f : Fin r → X → ℝ) (g : Fin s → X → ℝ) :
    (fun ω => normalizedOrderedProductStatistic S f n ω *
      normalizedOrderedProductStatistic S g n ω) =
    fun ω => ∑ h ∈ Finset.range (min r s + 1),
      ∑ M ∈ partialMatchingsOfSize r s h,
        matchingNormalization n M *
          normalizedFiniteKernelStatistic S (mergedProductKernel f g M) n ω := by
  /- Expand both tuple sums.  Send a pair `(t,q)` to the matching of coordinates
  satisfying `t i = q j`; injectivity makes this a partial bijection.  The
  induced map on `MergedIndex` is injective, and this construction is a
  bijection with `(M,u)` where `u` is an injective merged assignment. -/
  classical
  funext ω
  rw [← sum_partialMatchingsOfSize]
  simp_rw [matchingNormalization_mul_normalizedFiniteKernelStatistic S hrn hsn]
  rw [← Finset.mul_sum]
  rw [← unnormalized_product_sum_expansion S f g ω]
  unfold normalizedOrderedProductStatistic normalizedFiniteKernelStatistic
  simp only [Fintype.card_fin]
  ring

private theorem integrable_normalizedFiniteKernelStatistic
    (S : Causalean.Stat.IIDSample Ω X μ P) {ι : Type*} [Fintype ι]
    {k : (ι → X) → ℝ} {n : ℕ} (hkmeas : Measurable k)
    (hkint : Integrable k (Measure.pi fun _ : ι => P)) :
    Integrable (normalizedFiniteKernelStatistic S k n) μ := by
  classical
  have hterm : ∀ t ∈ finiteInjectiveTuples ι n,
      Integrable (fun ω => k (fun i => S.Z (t i : ℕ) ω)) μ := by
    intro t ht
    have htinj : Function.Injective t := (Finset.mem_filter.mp ht).2
    have hmap : Integrable k
        (μ.map (fun ω : Ω => fun i : ι => S.Z (t i : ℕ) ω)) := by
      rw [S.map_fintype_tuple_eq htinj]
      exact hkint
    exact (integrable_map_measure hkmeas.aestronglyMeasurable
      (measurable_pi_lambda _ (fun i : ι => S.meas (t i : ℕ))).aemeasurable).mp hmap
  exact (integrable_finset_sum _ (fun t ht => hterm t ht)).const_mul _

private theorem matchingNormalization_eq_zero_of_card_gt {n r s : ℕ}
    (M : PartialMatching r s) (hcard : ¬Fintype.card M.MergedIndex ≤ n) :
    matchingNormalization n M = 0 := by
  have hz : n.descFactorial (Fintype.card M.MergedIndex) = 0 := by
    apply Nat.eq_zero_of_not_pos
    simpa only [Nat.descFactorial_pos] using hcard
  unfold matchingNormalization
  rw [← M.mergedIndex_card, hz]
  norm_num

/-- For [an i.i.d. sample](hyp:S), [statistic orders and a sample size](hyp:r,s,n),
if [the first order](hyp:hrn) and [the second order](hyp:hsn) do not exceed the
sample size, then for [two coordinate-function families](hyp:f,g), when [every
merged kernel is measurable](hyp:hmeas) and [integrable under its product
law](hyp:hint), [the expected product of their normalized statistics is the
partial-matching sum of merged product-law moments](goal). -/
theorem integral_normalizedOrderedProductStatistic_mul
    (S : Causalean.Stat.IIDSample Ω X μ P) {r s n : ℕ}
    (hrn : r ≤ n) (hsn : s ≤ n) (f : Fin r → X → ℝ) (g : Fin s → X → ℝ)
    (hmeas : ∀ M : PartialMatching r s, Measurable (mergedProductKernel f g M))
    (hint : ∀ M : PartialMatching r s,
      Integrable (mergedProductKernel f g M)
        (Measure.pi fun _ : M.MergedIndex => P)) :
    ∫ ω, normalizedOrderedProductStatistic S f n ω *
        normalizedOrderedProductStatistic S g n ω ∂μ =
      ∑ h ∈ Finset.range (min r s + 1),
        ∑ M ∈ partialMatchingsOfSize r s h,
          matchingNormalization n M * mergedProductMoment P f g M := by
  classical
  rw [normalizedOrderedProductStatistic_mul_expansion S hrn hsn f g]
  have hterm : ∀ h ∈ Finset.range (min r s + 1),
      Integrable (fun ω => ∑ M ∈ partialMatchingsOfSize r s h,
        matchingNormalization n M *
          normalizedFiniteKernelStatistic S (mergedProductKernel f g M) n ω) μ := by
    intro h hh
    apply integrable_finset_sum
    intro M hM
    by_cases hc : Fintype.card M.MergedIndex ≤ n
    · exact (integrable_normalizedFiniteKernelStatistic S (hmeas M) (hint M)).const_mul _
    · rw [matchingNormalization_eq_zero_of_card_gt M hc]
      simp
  rw [integral_finset_sum _ hterm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro M hM
    rw [integral_const_mul]
    by_cases hc : Fintype.card M.MergedIndex ≤ n
    · rw [integral_normalizedFiniteKernelStatistic S hc (hmeas M) (hint M)]
      rfl
    · rw [matchingNormalization_eq_zero_of_card_gt M hc]
      simp
  · intro M hM
    by_cases hc : Fintype.card M.MergedIndex ≤ n
    · exact (integrable_normalizedFiniteKernelStatistic S (hmeas M) (hint M)).const_mul _
    · rw [matchingNormalization_eq_zero_of_card_gt M hc]
      simp

/-- The ordered-product mean is the expectation of a coordinatewise product
under independent draws from the population law. -/
noncomputable def orderedProductMean {r : ℕ} (P : Measure X)
    (f : Fin r → X → ℝ) : ℝ :=
  ∫ z, orderedProductKernel f z ∂(Measure.pi fun _ : Fin r => P)

/-- The centered cross moment subtracts the product of two means from the mean
of their product. -/
noncomputable def centeredCrossMoment (μ : Measure Ω) (A B : Ω → ℝ) : ℝ :=
  (∫ ω, A ω * B ω ∂μ) - (∫ ω, A ω ∂μ) * (∫ ω, B ω ∂μ)

/-- Under a probability law, for [two coordinate-function families of
orders `r` and `s`](hyp:r,s,f,g), if [the first product kernel is measurable](hyp:hmeasF),
[the second product kernel is measurable](hyp:hmeasG), [the first product
kernel is integrable](hyp:hintF), and [the second product kernel is
integrable](hyp:hintG), [the empty matching's merged moment factors into the
two separate product-law means](goal). -/
theorem mergedProductMoment_empty [IsProbabilityMeasure P] {r s : ℕ}
    (f : Fin r → X → ℝ) (g : Fin s → X → ℝ)
    (hmeasF : Measurable (orderedProductKernel f))
    (hmeasG : Measurable (orderedProductKernel g))
    (hintF : Integrable (orderedProductKernel f) (Measure.pi fun _ : Fin r => P))
    (hintG : Integrable (orderedProductKernel g) (Measure.pi fun _ : Fin s => P)) :
    mergedProductMoment P f g (PartialMatching.empty r s) =
      orderedProductMean P f * orderedProductMean P g := by
  classical
  let J := {j : Fin s // j ∉ (PartialMatching.empty r s).right}
  let e : J ≃ Fin s := Equiv.subtypeUnivEquiv (by
    intro j
    simp [J, PartialMatching.empty])
  let split := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Fin r ⊕ J => X)
  let reindex := MeasurableEquiv.piCongrLeft (fun _ : Fin s => X) e
  have hsplit := measurePreserving_sumPiEquivProdPi
    (fun _ : Fin r ⊕ J => P)
  have hreindex : Measure.map reindex (Measure.pi fun _ : J => P) =
      Measure.pi fun _ : Fin s => P := by
    simpa [reindex] using
      (Measure.pi_map_piCongrLeft e (fun _ : Fin s => P))
  let gJ : (J → X) → ℝ := fun z => ∏ j : Fin s, g j (z (e.symm j))
  have hgJ : ∫ z, gJ z ∂(Measure.pi fun _ : J => P) = orderedProductMean P g := by
    unfold orderedProductMean
    rw [← hreindex, integral_map_equiv]
    rfl
  unfold mergedProductMoment
  change (∫ z, mergedProductKernel f g (PartialMatching.empty r s) z
      ∂(Measure.pi fun _ : Fin r ⊕ J => P)) = _
  calc
    _ = ∫ z : (Fin r → X) × (J → X),
        orderedProductKernel f z.1 * gJ z.2
        ∂((Measure.pi fun _ : Fin r => P).prod (Measure.pi fun _ : J => P)) := by
      rw [← hsplit.map_eq, integral_map_equiv]
      rfl
    _ = _ := by
      rw [integral_prod_mul, hgJ]
      rfl

/-- Under a probability population law, for [an i.i.d. sample](hyp:S),
[statistic orders and a sample size](hyp:r,s,n), if [the first order](hyp:hrn)
and [the second order](hyp:hsn) do not exceed the sample size, then for [two
coordinate-function families](hyp:f,g), when [their product kernels are
measurable](hyp:hmeasF,hmeasG), [their product kernels are integrable](hyp:hintF,hintG),
[every merged kernel is measurable](hyp:hmeas), and [every merged kernel is
integrable](hyp:hint), [their centered cross moment equals an explicit disjoint
normalization correction plus the merged moments from every positive-size
partial matching](goal). -/
theorem centeredCrossMoment_normalizedOrderedProductStatistic
    [IsProbabilityMeasure P]
    (S : Causalean.Stat.IIDSample Ω X μ P) {r s n : ℕ}
    (hrn : r ≤ n) (hsn : s ≤ n) (f : Fin r → X → ℝ) (g : Fin s → X → ℝ)
    (hmeasF : Measurable (orderedProductKernel f))
    (hmeasG : Measurable (orderedProductKernel g))
    (hintF : Integrable (orderedProductKernel f) (Measure.pi fun _ : Fin r => P))
    (hintG : Integrable (orderedProductKernel g) (Measure.pi fun _ : Fin s => P))
    (hmeas : ∀ M : PartialMatching r s, Measurable (mergedProductKernel f g M))
    (hint : ∀ M : PartialMatching r s,
      Integrable (mergedProductKernel f g M)
        (Measure.pi fun _ : M.MergedIndex => P)) :
    centeredCrossMoment μ (normalizedOrderedProductStatistic S f n)
        (normalizedOrderedProductStatistic S g n) =
      (matchingNormalization n (PartialMatching.empty r s) - 1) *
          orderedProductMean P f * orderedProductMean P g +
        ∑ h ∈ (Finset.range (min r s + 1)).filter (fun h => 0 < h),
          ∑ M ∈ partialMatchingsOfSize r s h,
            matchingNormalization n M * mergedProductMoment P f g M := by
  /- Combine the product-moment expansion with unbiasedness of each marginal.
  Use `eq_empty_of_size_eq_zero` and `mergedProductMoment_empty` to rewrite the
  unique size-zero term, then partition the remaining sizes by `0 < h`. -/
  classical
  have hfmean : ∫ ω, normalizedOrderedProductStatistic S f n ω ∂μ =
      orderedProductMean P f := by
    unfold normalizedOrderedProductStatistic orderedProductMean
    exact integral_normalizedFiniteKernelStatistic S (by simpa using hrn) hmeasF hintF
  have hgmean : ∫ ω, normalizedOrderedProductStatistic S g n ω ∂μ =
      orderedProductMean P g := by
    unfold normalizedOrderedProductStatistic orderedProductMean
    exact integral_normalizedFiniteKernelStatistic S (by simpa using hsn) hmeasG hintG
  let F : ℕ → ℝ := fun h =>
    ∑ M ∈ partialMatchingsOfSize r s h,
      matchingNormalization n M * mergedProductMoment P f g M
  have hzero : F 0 = matchingNormalization n (PartialMatching.empty r s) *
      (orderedProductMean P f * orderedProductMean P g) := by
    dsimp only [F]
    rw [Finset.sum_eq_single (PartialMatching.empty r s)]
    · rw [mergedProductMoment_empty f g hmeasF hmeasG hintF hintG]
    · intro M hM hne
      exact False.elim (hne (PartialMatching.eq_empty_of_size_eq_zero M
        ((mem_partialMatchingsOfSize M).mp hM)))
    · intro hnot
      exact False.elim (hnot (by simp))
  let H := Finset.range (min r s + 1)
  have hnonpos : H.filter (fun h => ¬0 < h) = {0} := by
    ext h
    simp [H]
  have hsplit : (∑ h ∈ H, F h) = F 0 +
      ∑ h ∈ H.filter (fun h => 0 < h), F h := by
    have hpart := Finset.sum_filter_add_sum_filter_not H (fun h => 0 < h) F
    rw [hnonpos] at hpart
    simpa [add_comm] using hpart.symm
  unfold centeredCrossMoment
  rw [integral_normalizedOrderedProductStatistic_mul S hrn hsn f g hmeas hint,
    hfmean, hgmean]
  change (∑ h ∈ H, F h) - orderedProductMean P f * orderedProductMean P g = _
  rw [hsplit, hzero]
  ring

end Causalean.Stat
