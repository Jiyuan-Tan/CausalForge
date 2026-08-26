/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Sample.FiniteStratumMarkedRatioMse.Basic
import Mathlib.Probability.ProductMeasure

/-!
# Missing-arm moments for finite-stratum samples

This module computes the first, second, and cross moments of category
occupancy on an empty empirical arm.  It also packages an exponentially
damped aggregate envelope and its boundary-safe deterministic lower-mass
relaxation.
-/

namespace Causalean.Stat.FiniteStratumMarkedRatioMse

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Omega kappa : Type*} [MeasurableSpace Omega]
  [Fintype kappa] [DecidableEq kappa]
  [MeasurableSpace kappa] [MeasurableSingletonClass kappa]

private lemma prod_one_distinguished {I : Type*} [Fintype I] [DecidableEq I]
    (i : I) (x y : ℝ≥0∞) :
    (∏ j : I, if j = i then x else y) =
      x * y ^ (Fintype.card I - 1) := by
  rw [Fintype.prod_eq_mul_prod_compl i]
  simp only [if_pos]
  have hprod : (∏ j ∈ ({i}ᶜ : Finset I), if j = i then x else y) =
      y ^ (Fintype.card I - 1) := by
    rw [show (∏ j ∈ ({i}ᶜ : Finset I), if j = i then x else y) =
        ∏ _j ∈ ({i}ᶜ : Finset I), y by
      apply Finset.prod_congr rfl
      intro j hj
      simp only [Finset.mem_compl, Finset.mem_singleton] at hj
      simp [hj]]
    rw [Finset.prod_const]
    congr 1
    rw [Finset.card_compl]
    simp
  rw [hprod]

private lemma prod_two_distinguished {I : Type*} [Fintype I] [DecidableEq I]
    (i j : I) (x y z : ℝ≥0∞) (hij : i ≠ j) :
    (∏ l : I, if l = i then x else if l = j then y else z) =
      x * y * z ^ (Fintype.card I - 2) := by
  rw [Fintype.prod_eq_mul_prod_compl i]
  simp only [if_pos]
  have hjmem : j ∈ ({i}ᶜ : Finset I) := by simp [hij.symm]
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem hjmem]
  simp only [hij.symm, if_false, if_pos]
  have hprod :
      (∏ l ∈ ({i}ᶜ : Finset I) \ {j},
          if l = i then x else if l = j then y else z) =
        z ^ (Fintype.card I - 2) := by
    rw [show (∏ l ∈ ({i}ᶜ : Finset I) \ {j},
        if l = i then x else if l = j then y else z) =
        ∏ _l ∈ (({i}ᶜ : Finset I) \ {j}), z by
      apply Finset.prod_congr rfl
      intro l hl
      simp only [Finset.mem_sdiff, Finset.mem_compl, Finset.mem_singleton] at hl
      simp [hl.1, hl.2]]
    rw [Finset.prod_const]
    congr 1
    have hcard : (({i}ᶜ : Finset I).erase j).card =
        Fintype.card I - 2 := by
      rw [Finset.card_erase_of_mem hjmem, Finset.card_compl]
      simp only [Finset.card_singleton]
      omega
    simpa only [Finset.sdiff_singleton_eq_erase] using hcard
  rw [hprod]
  ring

private def oneSelectedAvoidSetEvent {m : Nat} (i : Fin m)
    (S R : Set Omega) : Set (Fin m → Omega) :=
  {z | z i ∈ S ∧ ∀ j, z j ∉ R}

private def twoSelectedAvoidSetsEvent {m : Nat} (i j : Fin m)
    (S T R : Set Omega) : Set (Fin m → Omega) :=
  {z | z i ∈ S ∧ z j ∈ T ∧ ∀ l, z l ∉ R}

private lemma oneSelectedAvoidSetEvent_eq_pi {m : Nat} (i : Fin m)
    (S R : Set Omega) (hSR : Disjoint S R) :
    oneSelectedAvoidSetEvent i S R =
      Set.univ.pi (fun j => if j = i then S else Rᶜ) := by
  ext z
  simp only [oneSelectedAvoidSetEvent, Set.mem_setOf_eq, Set.mem_pi,
    Set.mem_univ, forall_true_left]
  constructor
  · rintro ⟨hzi, hav⟩ j
    by_cases hji : j = i
    · simpa [hji] using hzi
    · simp [hji, hav j]
  · intro h
    have hi := h i
    simp only [if_pos] at hi
    refine ⟨hi, ?_⟩
    intro j hjR
    have hj := h j
    by_cases hji : j = i
    · subst j
      exact Set.disjoint_left.1 hSR hi hjR
    · simpa [hji, hjR] using hj

private lemma twoSelectedAvoidSetsEvent_eq_pi {m : Nat} (i j : Fin m)
    (S T R : Set Omega) (hij : i ≠ j) (hSR : Disjoint S R)
    (hTR : Disjoint T R) :
    twoSelectedAvoidSetsEvent i j S T R =
      Set.univ.pi (fun l => if l = i then S else if l = j then T else Rᶜ) := by
  ext z
  simp only [twoSelectedAvoidSetsEvent, Set.mem_setOf_eq, Set.mem_pi,
    Set.mem_univ, forall_true_left]
  constructor
  · rintro ⟨hzi, hzj, hav⟩ l
    by_cases hli : l = i
    · simpa [hli] using hzi
    · by_cases hlj : l = j
      · simpa [hli, hlj, hij.symm] using hzj
      · simp [hli, hlj, hav l]
  · intro h
    have hi := h i
    have hj := h j
    simp only [if_pos] at hi
    simp only [hij.symm, if_false, if_pos] at hj
    refine ⟨hi, hj, ?_⟩
    intro l hlR
    have hl := h l
    by_cases hli : l = i
    · subst l
      exact Set.disjoint_left.1 hSR hi hlR
    · by_cases hlj : l = j
      · subst l
        exact Set.disjoint_left.1 hTR hj hlR
      · simpa [hli, hlj, hlR] using hl

private lemma measurableSet_oneSelectedAvoidSetEvent {m : Nat} (i : Fin m)
    {S R : Set Omega} (hS : MeasurableSet S) (hR : MeasurableSet R) :
    MeasurableSet (oneSelectedAvoidSetEvent i S R) := by
  rw [show oneSelectedAvoidSetEvent i S R =
      {z | z i ∈ S} ∩ ⋂ j, {z | z j ∈ Rᶜ} by
    ext z
    simp [oneSelectedAvoidSetEvent]]
  exact (hS.preimage (measurable_pi_apply i)).inter
    (MeasurableSet.iInter fun j => hR.compl.preimage (measurable_pi_apply j))

private lemma measurableSet_twoSelectedAvoidSetsEvent {m : Nat} (i j : Fin m)
    {S T R : Set Omega} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hR : MeasurableSet R) :
    MeasurableSet (twoSelectedAvoidSetsEvent i j S T R) := by
  rw [show twoSelectedAvoidSetsEvent i j S T R =
      {z | z i ∈ S} ∩ {z | z j ∈ T} ∩ ⋂ l, {z | z l ∈ Rᶜ} by
    ext z
    simp [twoSelectedAvoidSetsEvent, and_assoc]]
  exact ((hS.preimage (measurable_pi_apply i)).inter
    (hT.preimage (measurable_pi_apply j))).inter
      (MeasurableSet.iInter fun l => hR.compl.preimage (measurable_pi_apply l))

private lemma measure_oneSelectedAvoidSetEvent {m : Nat}
    (mu : Measure Omega) [IsProbabilityMeasure mu] (i : Fin m)
    (S R : Set Omega) (hSR : Disjoint S R) :
    (Measure.pi (fun _ : Fin m => mu)) (oneSelectedAvoidSetEvent i S R) =
      mu S * mu (Rᶜ) ^ (m - 1) := by
  rw [oneSelectedAvoidSetEvent_eq_pi i S R hSR, Measure.pi_pi]
  have hfun : (fun l : Fin m => mu (if l = i then S else Rᶜ)) =
      fun l => if l = i then mu S else mu (Rᶜ) := by
    funext l
    by_cases hli : l = i <;> simp [hli]
  rw [hfun]
  simpa using prod_one_distinguished i (mu S) (mu (Rᶜ))

private lemma measure_twoSelectedAvoidSetsEvent {m : Nat}
    (mu : Measure Omega) [IsProbabilityMeasure mu] (i j : Fin m)
    (S T R : Set Omega) (hij : i ≠ j) (hSR : Disjoint S R)
    (hTR : Disjoint T R) :
    (Measure.pi (fun _ : Fin m => mu))
        (twoSelectedAvoidSetsEvent i j S T R) =
      mu S * mu T * mu (Rᶜ) ^ (m - 2) := by
  rw [twoSelectedAvoidSetsEvent_eq_pi i j S T R hij hSR hTR, Measure.pi_pi]
  have hfun : (fun l : Fin m =>
      mu (if l = i then S else if l = j then T else Rᶜ)) =
      fun l => if l = i then mu S else if l = j then mu T else mu (Rᶜ) := by
    funext l
    by_cases hli : l = i
    · simp [hli]
    · by_cases hlj : l = j
      · simp [hli, hlj, hij.symm]
      · simp [hli, hlj]
  rw [hfun]
  simpa using prod_two_distinguished i j (mu S) (mu T) (mu (Rᶜ)) hij

private lemma armCategoryEvent_subset_categoryEvent
    (group : Omega → kappa) (arm : Omega → Bool) (a : Bool) (k : kappa) :
    armCategoryEvent group arm a k ⊆ categoryEvent group k := by
  intro omega h
  exact h.1

private lemma categoryEvent_disjoint_of_ne (group : Omega → kappa)
    {k l : kappa} (hkl : k ≠ l) :
    Disjoint (categoryEvent group k) (categoryEvent group l) := by
  rw [Set.disjoint_left]
  intro omega hk hl
  exact hkl (hk.symm.trans hl)

private lemma missingArmCount_eq_sum_indicator {m : Nat}
    (group : Omega → kappa) (arm : Omega → Bool) (z : Fin m → Omega)
    (a : Bool) (k : kappa) :
    (missingArmCount group arm z a k : ℝ) =
      ∑ i : Fin m,
        (oneSelectedAvoidSetEvent i
          (categoryEvent group k \ armCategoryEvent group arm a k)
          (armCategoryEvent group arm a k)).indicator (fun _ => (1 : ℝ)) z := by
  classical
  by_cases hzero : categoryArmCount group arm z a k = 0
  · have hav : ∀ i, z i ∉ armCategoryEvent group arm a k := by
      intro i hi
      have himem : i ∈ Finset.univ.filter
          (fun j => group (z j) = k ∧ arm (z j) = a) := by
        simpa [armCategoryEvent, Causalean.Stat.armGroupEvent] using hi
      have hne : categoryArmCount group arm z a k ≠ 0 := by
        unfold categoryArmCount Causalean.Stat.groupArmCount
        exact Finset.card_ne_zero.mpr ⟨i, himem⟩
      exact hne hzero
    have hnot : ∀ i, group (z i) = k → arm (z i) ≠ a := by
      intro i hik hia
      exact hav i (by simp [armCategoryEvent, Causalean.Stat.armGroupEvent, hik, hia])
    simp only [missingArmCount, hzero, if_true, oneSelectedAvoidSetEvent,
      Set.indicator, Set.mem_setOf_eq]
    unfold categoryCount Causalean.Stat.groupCount
    unfold Causalean.Stat.groupArmCount
    simp only [Nat.cast_add, Finset.card_filter]
    rw [Nat.cast_sum, Nat.cast_sum, ← Finset.sum_add_distrib]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    cases a <;>
      apply Finset.sum_congr rfl <;>
      intro i hi <;>
      by_cases hik : group (z i) = k <;>
      by_cases hia : arm (z i) = false <;>
      simp_all [categoryEvent, Causalean.Stat.groupEvent,
        armCategoryEvent, Causalean.Stat.armGroupEvent]
  · have hex : ∃ i, z i ∈ armCategoryEvent group arm a k := by
      have hpos : 0 < categoryArmCount group arm z a k := Nat.pos_of_ne_zero hzero
      change 0 < (Finset.univ.filter
        (fun j => group (z j) = k ∧ arm (z j) = a)).card at hpos
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
      exact ⟨i, by simpa [armCategoryEvent, Causalean.Stat.armGroupEvent] using hi⟩
    rcases hex with ⟨i0, hi0⟩
    simp only [missingArmCount, hzero, if_false, Nat.cast_zero]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Set.indicator]
    rw [if_neg]
    intro hevent
    exact hevent.2 i0 hi0

private lemma one_indicator_sq {m : Nat} (z : Fin m → Omega) (i : Fin m)
    (S R : Set Omega) :
    ((oneSelectedAvoidSetEvent i S R).indicator (fun _ => (1 : ℝ)) z) ^ 2 =
      (oneSelectedAvoidSetEvent i S R).indicator (fun _ => (1 : ℝ)) z := by
  by_cases h : z ∈ oneSelectedAvoidSetEvent i S R <;> simp [Set.indicator, h]

private lemma one_indicator_mul {m : Nat} (z : Fin m → Omega) (i j : Fin m)
    (S R : Set Omega) :
    (oneSelectedAvoidSetEvent i S R).indicator (fun _ => (1 : ℝ)) z *
        (oneSelectedAvoidSetEvent j S R).indicator (fun _ => (1 : ℝ)) z =
      (twoSelectedAvoidSetsEvent i j S S R).indicator (fun _ => (1 : ℝ)) z := by
  by_cases hi : z ∈ oneSelectedAvoidSetEvent i S R
  · by_cases hj : z ∈ oneSelectedAvoidSetEvent j S R
    · have ht : z ∈ twoSelectedAvoidSetsEvent i j S S R := ⟨hi.1, hj.1, hi.2⟩
      simp [Set.indicator, hi, hj, ht]
    · have ht : z ∉ twoSelectedAvoidSetsEvent i j S S R :=
        fun h => hj ⟨h.2.1, h.2.2⟩
      simp [Set.indicator, hi, hj, ht]
  · have ht : z ∉ twoSelectedAvoidSetsEvent i j S S R :=
      fun h => hi ⟨h.1, h.2.2⟩
    simp [Set.indicator, hi, ht]

private lemma missingArmCount_sq_eq_sum_indicator {m : Nat}
    (group : Omega → kappa) (arm : Omega → Bool) (z : Fin m → Omega)
    (a : Bool) (k : kappa) :
    (missingArmCount group arm z a k : ℝ) ^ 2 =
      ∑ i : Fin m, (oneSelectedAvoidSetEvent i
          (categoryEvent group k \ armCategoryEvent group arm a k)
          (armCategoryEvent group arm a k)).indicator (fun _ => (1 : ℝ)) z +
        ∑ i : Fin m, ∑ j ∈ (Finset.univ : Finset (Fin m)).erase i,
          (twoSelectedAvoidSetsEvent i j
            (categoryEvent group k \ armCategoryEvent group arm a k)
            (categoryEvent group k \ armCategoryEvent group arm a k)
            (armCategoryEvent group arm a k)).indicator (fun _ => (1 : ℝ)) z := by
  classical
  rw [missingArmCount_eq_sum_indicator group arm z a k, sq, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_comm]
  congr 1
  · simpa [sq] using one_indicator_sq z i
      (categoryEvent group k \ armCategoryEvent group arm a k)
      (armCategoryEvent group arm a k)
  · apply Finset.sum_congr rfl
    intro j hj
    exact one_indicator_mul z i j
      (categoryEvent group k \ armCategoryEvent group arm a k)
      (armCategoryEvent group arm a k)

private lemma one_indicator_mul_cross {m : Nat} (z : Fin m → Omega)
    (i j : Fin m) (S T R Q : Set Omega) :
    (oneSelectedAvoidSetEvent i S R).indicator (fun _ => (1 : ℝ)) z *
        (oneSelectedAvoidSetEvent j T Q).indicator (fun _ => (1 : ℝ)) z =
      (twoSelectedAvoidSetsEvent i j S T (R ∪ Q)).indicator
        (fun _ => (1 : ℝ)) z := by
  by_cases hi : z ∈ oneSelectedAvoidSetEvent i S R
  · by_cases hj : z ∈ oneSelectedAvoidSetEvent j T Q
    · have ht : z ∈ twoSelectedAvoidSetsEvent i j S T (R ∪ Q) := by
        refine ⟨hi.1, hj.1, ?_⟩
        intro l hl
        exact hl.elim (hi.2 l) (hj.2 l)
      simp [Set.indicator, hi, hj, ht]
    · have ht : z ∉ twoSelectedAvoidSetsEvent i j S T (R ∪ Q) :=
        fun h => hj ⟨h.2.1, fun l hl => h.2.2 l (Or.inr hl)⟩
      simp [Set.indicator, hi, hj, ht]
  · have ht : z ∉ twoSelectedAvoidSetsEvent i j S T (R ∪ Q) :=
      fun h => hi ⟨h.1, fun l hl => h.2.2 l (Or.inl hl)⟩
    simp [Set.indicator, hi, ht]

private lemma one_indicator_mul_zero_of_disjoint {m : Nat}
    (z : Fin m → Omega) (i : Fin m) (S T R Q : Set Omega)
    (hST : Disjoint S T) :
    (oneSelectedAvoidSetEvent i S R).indicator (fun _ => (1 : ℝ)) z *
        (oneSelectedAvoidSetEvent i T Q).indicator (fun _ => (1 : ℝ)) z = 0 := by
  by_cases hi : z ∈ oneSelectedAvoidSetEvent i S R
  · have hj : z ∉ oneSelectedAvoidSetEvent i T Q := fun h =>
      Set.disjoint_left.1 hST hi.1 h.1
    simp [Set.indicator, hi, hj]
  · simp [Set.indicator, hi]

private lemma missingArmCount_mul_eq_sum_indicator {m : Nat}
    (group : Omega → kappa) (arm : Omega → Bool) (z : Fin m → Omega)
    (a : Bool) {k l : kappa} (hkl : k ≠ l) :
    (missingArmCount group arm z a k : ℝ) *
        (missingArmCount group arm z a l : ℝ) =
      ∑ i : Fin m, ∑ j ∈ (Finset.univ : Finset (Fin m)).erase i,
        (twoSelectedAvoidSetsEvent i j
          (categoryEvent group k \ armCategoryEvent group arm a k)
          (categoryEvent group l \ armCategoryEvent group arm a l)
          (armCategoryEvent group arm a k ∪ armCategoryEvent group arm a l)).indicator
            (fun _ => (1 : ℝ)) z := by
  classical
  rw [missingArmCount_eq_sum_indicator group arm z a k,
    missingArmCount_eq_sum_indicator group arm z a l, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [one_indicator_mul_zero_of_disjoint z i
    (categoryEvent group k \ armCategoryEvent group arm a k)
    (categoryEvent group l \ armCategoryEvent group arm a l)
    (armCategoryEvent group arm a k) (armCategoryEvent group arm a l)
    ((categoryEvent_disjoint_of_ne group hkl).mono Set.diff_subset Set.diff_subset),
    add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  exact one_indicator_mul_cross z i j
    (categoryEvent group k \ armCategoryEvent group arm a k)
    (categoryEvent group l \ armCategoryEvent group arm a l)
    (armCategoryEvent group arm a k) (armCategoryEvent group arm a l)

/-- [Measurable group and arm labels](hyp:hgroup,harm) imply that [the expected
category occupancy retained only when one arm is absent equals the sample size
times the off-arm category mass times the empty-arm probability for the other
coordinates](goal). -/
theorem integral_missingArmCount_eq {m : Nat} (mu : Measure Omega)
    [IsProbabilityMeasure mu] (group : Omega → kappa) (arm : Omega → Bool)
    (hgroup : Measurable group) (harm : Measurable arm) (a : Bool) (k : kappa) :
    ∫ z : Fin m → Omega, (missingArmCount group arm z a k : Real)
        ∂(Measure.pi (fun _ : Fin m => mu)) =
      (m : Real) *
        (categoryMass mu group k - armCategoryMass mu group arm a k) *
        (1 - armCategoryMass mu group arm a k) ^ (m - 1) := by
  classical
  let C := categoryEvent group k
  let R := armCategoryEvent group arm a k
  let S := C \ R
  have hC : MeasurableSet C :=
    Causalean.Stat.measurableSet_groupEvent group hgroup k
  have hR : MeasurableSet R :=
    Causalean.Stat.measurableSet_armGroupEvent group arm hgroup harm a k
  have hRC : R ⊆ C := armCategoryEvent_subset_categoryEvent group arm a k
  have hSR : Disjoint S R := Set.disjoint_sdiff_left
  rw [show (fun z : Fin m → Omega => (missingArmCount group arm z a k : ℝ)) =
      fun z => ∑ i : Fin m,
        (oneSelectedAvoidSetEvent i S R).indicator (fun _ => (1 : ℝ)) z by
    funext z
    exact missingArmCount_eq_sum_indicator group arm z a k]
  have hintg (i : Fin m) : Integrable
      ((oneSelectedAvoidSetEvent i S R).indicator (fun _ => (1 : ℝ)))
      (Measure.pi (fun _ : Fin m => mu)) :=
    (integrable_const (1 : ℝ)).indicator
      (measurableSet_oneSelectedAvoidSetEvent i (hC.diff hR) hR)
  rw [integral_finset_sum Finset.univ (fun i _ => hintg i)]
  have hint (i : Fin m) :
      ∫ z : Fin m → Omega,
          (oneSelectedAvoidSetEvent i S R).indicator (fun _ => (1 : ℝ)) z
          ∂(Measure.pi (fun _ : Fin m => mu)) =
        (Measure.pi (fun _ : Fin m => mu)).real
          (oneSelectedAvoidSetEvent i S R) :=
    integral_indicator_one
      (measurableSet_oneSelectedAvoidSetEvent i (hC.diff hR) hR)
  simp_rw [hint, measureReal_def,
    measure_oneSelectedAvoidSetEvent mu _ S R hSR]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  have hSreal : (mu S).toReal =
      categoryMass mu group k - armCategoryMass mu group arm a k := by
    change mu.real S = mu.real C - mu.real R
    exact measureReal_sdiff hRC hR
  have hRcompl : (mu Rᶜ).toReal =
      1 - armCategoryMass mu group arm a k := by
    rw [← measureReal_def, measureReal_compl hR, probReal_univ]
    rfl
  rw [hSreal, hRcompl]
  simp only [Fintype.card_fin]
  ring

/-- [Measurable group and arm labels](hyp:hgroup,harm) imply that [the exact
second moment of one missing-arm category count is the sum of its one-coordinate
diagonal and ordered two-coordinate contributions](goal). -/
theorem integral_missingArmCount_sq_eq {m : Nat} (mu : Measure Omega)
    [IsProbabilityMeasure mu] (group : Omega → kappa) (arm : Omega → Bool)
    (hgroup : Measurable group) (harm : Measurable arm) (a : Bool) (k : kappa) :
    ∫ z : Fin m → Omega, (missingArmCount group arm z a k : Real) ^ 2
        ∂(Measure.pi (fun _ : Fin m => mu)) =
      (m : Real) *
          (categoryMass mu group k - armCategoryMass mu group arm a k) *
          (1 - armCategoryMass mu group arm a k) ^ (m - 1) +
        (m.descFactorial 2 : Real) *
          (categoryMass mu group k - armCategoryMass mu group arm a k) ^ 2 *
          (1 - armCategoryMass mu group arm a k) ^ (m - 2) := by
  classical
  let C := categoryEvent group k
  let R := armCategoryEvent group arm a k
  let S := C \ R
  have hC : MeasurableSet C :=
    Causalean.Stat.measurableSet_groupEvent group hgroup k
  have hR : MeasurableSet R :=
    Causalean.Stat.measurableSet_armGroupEvent group arm hgroup harm a k
  have hRC : R ⊆ C := armCategoryEvent_subset_categoryEvent group arm a k
  have hSR : Disjoint S R := Set.disjoint_sdiff_left
  rw [show (fun z : Fin m → Omega =>
      (missingArmCount group arm z a k : ℝ) ^ 2) = fun z =>
        ∑ i : Fin m, (oneSelectedAvoidSetEvent i S R).indicator
            (fun _ => (1 : ℝ)) z +
          ∑ i : Fin m, ∑ j ∈ (Finset.univ : Finset (Fin m)).erase i,
            (twoSelectedAvoidSetsEvent i j S S R).indicator
              (fun _ => (1 : ℝ)) z by
    funext z
    exact missingArmCount_sq_eq_sum_indicator group arm z a k]
  have hintg1 (i : Fin m) : Integrable
      ((oneSelectedAvoidSetEvent i S R).indicator (fun _ => (1 : ℝ)))
      (Measure.pi (fun _ : Fin m => mu)) :=
    (integrable_const (1 : ℝ)).indicator
      (measurableSet_oneSelectedAvoidSetEvent i (hC.diff hR) hR)
  have hintg2 (i j : Fin m) : Integrable
      ((twoSelectedAvoidSetsEvent i j S S R).indicator (fun _ => (1 : ℝ)))
      (Measure.pi (fun _ : Fin m => mu)) :=
    (integrable_const (1 : ℝ)).indicator
      (measurableSet_twoSelectedAvoidSetsEvent i j (hC.diff hR) (hC.diff hR) hR)
  rw [integral_add
    (integrable_finset_sum Finset.univ (fun i _ => hintg1 i))
    (integrable_finset_sum Finset.univ (fun i _ =>
      integrable_finset_sum ((Finset.univ : Finset (Fin m)).erase i)
        (fun j _ => hintg2 i j)))]
  rw [integral_finset_sum Finset.univ (fun i _ => hintg1 i)]
  rw [integral_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum ((Finset.univ : Finset (Fin m)).erase i)
      (fun j _ => hintg2 i j))]
  simp_rw [integral_finset_sum ((Finset.univ : Finset (Fin m)).erase _)
    (fun j _ => hintg2 _ j)]
  have hint1 (i : Fin m) :
      ∫ z : Fin m → Omega,
          (oneSelectedAvoidSetEvent i S R).indicator (fun _ => (1 : ℝ)) z
          ∂(Measure.pi (fun _ : Fin m => mu)) =
        (Measure.pi (fun _ : Fin m => mu)).real
          (oneSelectedAvoidSetEvent i S R) :=
    integral_indicator_one
      (measurableSet_oneSelectedAvoidSetEvent i (hC.diff hR) hR)
  have hint2 (i j : Fin m) :
      ∫ z : Fin m → Omega,
          (twoSelectedAvoidSetsEvent i j S S R).indicator (fun _ => (1 : ℝ)) z
          ∂(Measure.pi (fun _ : Fin m => mu)) =
        (Measure.pi (fun _ : Fin m => mu)).real
          (twoSelectedAvoidSetsEvent i j S S R) :=
    integral_indicator_one
      (measurableSet_twoSelectedAvoidSetsEvent i j (hC.diff hR) (hC.diff hR) hR)
  simp_rw [hint1, hint2, measureReal_def]
  simp_rw [measure_oneSelectedAvoidSetEvent mu _ S R hSR]
  have hmeasure2 (i j : Fin m)
      (hj : j ∈ (Finset.univ : Finset (Fin m)).erase i) :
      (Measure.pi (fun _ : Fin m => mu)) (twoSelectedAvoidSetsEvent i j S S R) =
        mu S * mu S * mu (Rᶜ) ^ (m - 2) :=
    measure_twoSelectedAvoidSetsEvent mu i j S S R
      (Finset.ne_of_mem_erase hj).symm hSR hSR
  have hcross :
      (∑ i : Fin m, ∑ j ∈ (Finset.univ : Finset (Fin m)).erase i,
        ((Measure.pi (fun _ : Fin m => mu))
          (twoSelectedAvoidSetsEvent i j S S R)).toReal) =
      ∑ i : Fin m, ∑ _j ∈ (Finset.univ : Finset (Fin m)).erase i,
        (mu S * mu S * mu (Rᶜ) ^ (m - 2)).toReal := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hmeasure2 i j hj]
  rw [hcross]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow]
  rw [Finset.sum_const, Finset.card_univ]
  simp only [Finset.sum_const, Finset.card_erase_of_mem, Finset.mem_univ,
    nsmul_eq_mul, Finset.card_univ]
  have hdesc : m.descFactorial 2 = m * (m - 1) := by
    cases m <;> simp [Nat.descFactorial, Nat.mul_comm]
  have hSreal : (mu S).toReal =
      categoryMass mu group k - armCategoryMass mu group arm a k := by
    change mu.real S = mu.real C - mu.real R
    exact measureReal_sdiff hRC hR
  have hRcompl : (mu Rᶜ).toReal =
      1 - armCategoryMass mu group arm a k := by
    rw [← measureReal_def, measureReal_compl hR, probReal_univ]
    rfl
  rw [hSreal, hRcompl, hdesc, Nat.cast_mul]
  simp only [Fintype.card_fin]
  ring

/-- [Measurable group and arm labels](hyp:hgroup,harm) and [distinct
categories](hyp:hkl) imply that [their missing-arm counts have the exact
ordered-pair cross moment obtained by excluding the union of the two
arm/category cells](goal). -/
theorem integral_missingArmCount_mul_eq {m : Nat} (mu : Measure Omega)
    [IsProbabilityMeasure mu] (group : Omega → kappa) (arm : Omega → Bool)
    (hgroup : Measurable group) (harm : Measurable arm) (a : Bool) {k l : kappa}
    (hkl : k ≠ l) :
    ∫ z : Fin m → Omega,
        (missingArmCount group arm z a k : Real) *
          (missingArmCount group arm z a l : Real)
        ∂(Measure.pi (fun _ : Fin m => mu)) =
      (m.descFactorial 2 : Real) *
        (categoryMass mu group k - armCategoryMass mu group arm a k) *
        (categoryMass mu group l - armCategoryMass mu group arm a l) *
        (1 - armCategoryMass mu group arm a k -
          armCategoryMass mu group arm a l) ^ (m - 2) := by
  classical
  let C := categoryEvent group k
  let D := categoryEvent group l
  let R := armCategoryEvent group arm a k
  let Q := armCategoryEvent group arm a l
  let S := C \ R
  let T := D \ Q
  let U := R ∪ Q
  have hC : MeasurableSet C :=
    Causalean.Stat.measurableSet_groupEvent group hgroup k
  have hD : MeasurableSet D :=
    Causalean.Stat.measurableSet_groupEvent group hgroup l
  have hR : MeasurableSet R :=
    Causalean.Stat.measurableSet_armGroupEvent group arm hgroup harm a k
  have hQ : MeasurableSet Q :=
    Causalean.Stat.measurableSet_armGroupEvent group arm hgroup harm a l
  have hRC : R ⊆ C := armCategoryEvent_subset_categoryEvent group arm a k
  have hQD : Q ⊆ D := armCategoryEvent_subset_categoryEvent group arm a l
  have hCD : Disjoint C D := categoryEvent_disjoint_of_ne group hkl
  have hRQ : Disjoint R Q := hCD.mono hRC hQD
  have hSU : Disjoint S U := by
    rw [Set.disjoint_left]
    intro omega hS hU
    rcases hU with hR' | hQ'
    · exact hS.2 hR'
    · exact Set.disjoint_left.1 hCD hS.1 (hQD hQ')
  have hTU : Disjoint T U := by
    rw [Set.disjoint_left]
    intro omega hT hU
    rcases hU with hR' | hQ'
    · exact Set.disjoint_left.1 hCD (hRC hR') hT.1
    · exact hT.2 hQ'
  rw [show (fun z : Fin m → Omega =>
      (missingArmCount group arm z a k : ℝ) *
        (missingArmCount group arm z a l : ℝ)) = fun z =>
      ∑ i : Fin m, ∑ j ∈ (Finset.univ : Finset (Fin m)).erase i,
        (twoSelectedAvoidSetsEvent i j S T U).indicator
          (fun _ => (1 : ℝ)) z by
    funext z
    exact missingArmCount_mul_eq_sum_indicator group arm z a hkl]
  have hintg (i j : Fin m) : Integrable
      ((twoSelectedAvoidSetsEvent i j S T U).indicator (fun _ => (1 : ℝ)))
      (Measure.pi (fun _ : Fin m => mu)) :=
    (integrable_const (1 : ℝ)).indicator
      (measurableSet_twoSelectedAvoidSetsEvent i j (hC.diff hR) (hD.diff hQ)
        (hR.union hQ))
  rw [integral_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum ((Finset.univ : Finset (Fin m)).erase i)
      (fun j _ => hintg i j))]
  simp_rw [integral_finset_sum ((Finset.univ : Finset (Fin m)).erase _)
    (fun j _ => hintg _ j)]
  have hint (i j : Fin m) :
      ∫ z : Fin m → Omega,
          (twoSelectedAvoidSetsEvent i j S T U).indicator (fun _ => (1 : ℝ)) z
          ∂(Measure.pi (fun _ : Fin m => mu)) =
        (Measure.pi (fun _ : Fin m => mu)).real
          (twoSelectedAvoidSetsEvent i j S T U) :=
    integral_indicator_one
      (measurableSet_twoSelectedAvoidSetsEvent i j (hC.diff hR) (hD.diff hQ)
        (hR.union hQ))
  simp_rw [hint, measureReal_def]
  have hmeasure (i j : Fin m)
      (hj : j ∈ (Finset.univ : Finset (Fin m)).erase i) :
      (Measure.pi (fun _ : Fin m => mu)) (twoSelectedAvoidSetsEvent i j S T U) =
        mu S * mu T * mu (Uᶜ) ^ (m - 2) :=
    measure_twoSelectedAvoidSetsEvent mu i j S T U
      (Finset.ne_of_mem_erase hj).symm hSU hTU
  have hcross :
      (∑ i : Fin m, ∑ j ∈ (Finset.univ : Finset (Fin m)).erase i,
        ((Measure.pi (fun _ : Fin m => mu))
          (twoSelectedAvoidSetsEvent i j S T U)).toReal) =
      ∑ i : Fin m, ∑ _j ∈ (Finset.univ : Finset (Fin m)).erase i,
        (mu S * mu T * mu (Uᶜ) ^ (m - 2)).toReal := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hmeasure i j hj]
  rw [hcross]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, Finset.sum_const,
    Finset.card_erase_of_mem, Finset.mem_univ, nsmul_eq_mul, Finset.card_univ]
  have hdesc : m.descFactorial 2 = m * (m - 1) := by
    cases m <;> simp [Nat.descFactorial, Nat.mul_comm]
  have hSreal : (mu S).toReal =
      categoryMass mu group k - armCategoryMass mu group arm a k := by
    change mu.real S = mu.real C - mu.real R
    exact measureReal_sdiff hRC hR
  have hTreal : (mu T).toReal =
      categoryMass mu group l - armCategoryMass mu group arm a l := by
    change mu.real T = mu.real D - mu.real Q
    exact measureReal_sdiff hQD hQ
  have hUcompl : (mu Uᶜ).toReal =
      1 - armCategoryMass mu group arm a k -
        armCategoryMass mu group arm a l := by
    rw [← measureReal_def, measureReal_compl (hR.union hQ), probReal_univ,
      measureReal_union hRQ hQ]
    change 1 - (armCategoryMass mu group arm a k +
      armCategoryMass mu group arm a l) = _
    ring
  rw [hSreal, hTreal, hUcompl, hdesc, Nat.cast_mul]
  simp only [Fintype.card_fin]
  ring

/-- The aggregate exponentially damped missing-arm envelope sums each
category mass times the overlap-driven empty-arm decay. -/
noncomputable def missingArmExponentialEnvelope (mu : Measure Omega)
    (group : Omega → kappa) (m : Nat) (epsilon : Real) (H : Finset kappa) : Real :=
  ∑ k ∈ H, categoryMass mu group k *
    Real.exp (-(((m - 2 : Nat) : Real) / 2 * epsilon * categoryMass mu group k))

/-- The lower-mass envelope uses inverse-polynomial decay when its denominator
is positive and otherwise falls back to total selected mass, so it remains
defined for small samples, zero overlap, and a zero mass lower bound. -/
noncomputable def lowerMassMissingEnvelope (mu : Measure Omega)
    (group : Omega → kappa) (m : Nat) (epsilon B : Real) (H : Finset kappa) : Real :=
  let D := ((((m - 2 : Nat) : Real) / 2 * epsilon) ^ 2) * B
  if 0 < D then (H.card : Real) / D else ∑ k ∈ H, categoryMass mu group k

private lemma exp_neg_le_inv_sq (t : ℝ) (ht : 0 < t) :
    Real.exp (-t) ≤ (t ^ 2)⁻¹ := by
  have hlin : t ≤ Real.exp (t / 2) := by
    convert Real.two_mul_le_exp (x := t / 2) using 1 <;> ring
  have hsq : t ^ 2 ≤ Real.exp t := by
    calc
      t ^ 2 ≤ (Real.exp (t / 2)) ^ 2 := pow_le_pow_left₀ ht.le hlin 2
      _ = Real.exp t := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  rw [Real.exp_neg]
  exact inv_anti₀ (sq_pos_of_pos ht) hsq

/-- [A measurable group label](hyp:hgroup), [a positive overlap
margin](hyp:hepsilon), and [a deterministic lower bound on every selected
category mass](hyp:hp) ensure that [the exponential missing-arm envelope is at
most the boundary-safe lower-mass envelope](goal). -/
theorem missingArmExponentialEnvelope_le_lowerMass
    (mu : Measure Omega) [IsProbabilityMeasure mu] (group : Omega → kappa)
    (hgroup : Measurable group) (m : Nat) (epsilon B : Real) (H : Finset kappa)
    (hepsilon : 0 < epsilon) (hp : ∀ k ∈ H, B ≤ categoryMass mu group k) :
    missingArmExponentialEnvelope mu group m epsilon H ≤
      lowerMassMissingEnvelope mu group m epsilon B H := by
  classical
  let u : ℝ := ((m - 2 : Nat) : ℝ) / 2 * epsilon
  let D : ℝ := u ^ 2 * B
  have hu0 : 0 ≤ u := by
    dsimp [u]
    positivity
  have hp0 (k : kappa) : 0 ≤ categoryMass mu group k :=
    ENNReal.toReal_nonneg
  unfold missingArmExponentialEnvelope lowerMassMissingEnvelope
  change (∑ k ∈ H, categoryMass mu group k *
      Real.exp (-(u * categoryMass mu group k))) ≤
    if 0 < D then (H.card : ℝ) / D
    else ∑ k ∈ H, categoryMass mu group k
  by_cases hD : 0 < D
  · rw [if_pos hD]
    have hBpos : 0 < B := by
      by_contra hn
      have hBle : B ≤ 0 := le_of_not_gt hn
      have hDle : D ≤ 0 := by
        dsimp [D]
        exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg u) hBle
      exact (not_lt_of_ge hDle) hD
    have hu_ne : u ≠ 0 := by
      intro huz
      simp [D, huz] at hD
    have hu : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu_ne)
    calc
      (∑ k ∈ H, categoryMass mu group k *
          Real.exp (-(u * categoryMass mu group k))) ≤
          ∑ _k ∈ H, 1 / D := by
        apply Finset.sum_le_sum
        intro k hk
        have hpk : 0 < categoryMass mu group k := hBpos.trans_le (hp k hk)
        have hut : 0 < u * categoryMass mu group k := mul_pos hu hpk
        calc
          categoryMass mu group k *
              Real.exp (-(u * categoryMass mu group k)) ≤
            categoryMass mu group k *
              ((u * categoryMass mu group k) ^ 2)⁻¹ := by
            gcongr
            exact exp_neg_le_inv_sq (u * categoryMass mu group k) hut
          _ = 1 / (u ^ 2 * categoryMass mu group k) := by
            field_simp [hu.ne', hpk.ne']
          _ ≤ 1 / (u ^ 2 * B) := by
            apply one_div_le_one_div_of_le
            · positivity
            · gcongr
              exact hp k hk
          _ = 1 / D := by rfl
      _ = (H.card : ℝ) / D := by simp [div_eq_mul_inv]
  · rw [if_neg hD]
    apply Finset.sum_le_sum
    intro k hk
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hu0 (hp0 k))))
      (hp0 k)

/-- [A sample size of at least three](hyp:hm), [a positive overlap
margin](hyp:hepsilon), and [a positive category-mass lower bound](hyp:hB) make
[the boundary-safe lower-mass envelope equal its inverse-polynomial
expression](goal). -/
theorem lowerMassMissingEnvelope_eq_of_pos
    (mu : Measure Omega) (group : Omega → kappa) {m : Nat} {epsilon B : Real}
    (H : Finset kappa) (hm : 3 ≤ m) (hepsilon : 0 < epsilon) (hB : 0 < B) :
    lowerMassMissingEnvelope mu group m epsilon B H =
      (H.card : Real) /
        (((((m - 2 : Nat) : Real) / 2 * epsilon) ^ 2) * B) := by
  unfold lowerMassMissingEnvelope
  dsimp only
  rw [if_pos]
  have hm2 : 0 < m - 2 := by omega
  positivity

end Causalean.Stat.FiniteStratumMarkedRatioMse
