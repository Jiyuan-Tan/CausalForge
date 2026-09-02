/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Sample.FiniteStratumMarkedRatioMse.MissingMoments

/-!
# Second-moment bound for the missing-arm remainder

This module bounds the aggregate missing-arm count by separating its
one-coordinate diagonal contribution from its ordered two-coordinate
contribution and applying overlap-driven exponential decay.
-/

namespace Causalean.Stat.FiniteStratumMarkedRatioMse

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Omega kappa : Type*} [MeasurableSpace Omega]
  [Fintype kappa] [DecidableEq kappa]
  [MeasurableSpace kappa] [MeasurableSingletonClass kappa]

private lemma categoryMass_nonneg (mu : Measure Omega) (group : Omega → kappa)
    (k : kappa) : 0 ≤ categoryMass mu group k :=
  ENNReal.toReal_nonneg

private lemma armCategoryMass_nonneg (mu : Measure Omega)
    (group : Omega → kappa) (arm : Omega → Bool) (a : Bool) (k : kappa) :
    0 ≤ armCategoryMass mu group arm a k :=
  ENNReal.toReal_nonneg

private lemma armCategoryMass_le_categoryMass (mu : Measure Omega)
    [IsProbabilityMeasure mu] (group : Omega → kappa) (arm : Omega → Bool)
    (a : Bool) (k : kappa) :
    armCategoryMass mu group arm a k ≤ categoryMass mu group k := by
  exact measureReal_mono
    (by intro omega h; exact h.1)

private lemma sum_categoryMass_le_one (mu : Measure Omega)
    [IsProbabilityMeasure mu] (group : Omega → kappa) (hgroup : Measurable group)
    (H : Finset kappa) : ∑ k ∈ H, categoryMass mu group k ≤ 1 := by
  have h := sum_measureReal_le_measureReal_univ (μ := mu) (s := H)
    (t := fun k ↦ categoryEvent group k)
    (fun k _ ↦ Causalean.Stat.measurableSet_groupEvent group hgroup k)
    (by
      intro k _ l _ hkl
      change Disjoint (categoryEvent group k) (categoryEvent group l)
      rw [Set.disjoint_left]
      intro omega hk hl
      exact hkl (hk.symm.trans hl))
  change (∑ k ∈ H, mu.real (categoryEvent group k)) ≤ 1
  simpa [probReal_univ] using h

private lemma missingArmCount_le_sampleSize {m : Nat}
    (group : Omega → kappa) (arm : Omega → Bool) (z : Fin m → Omega)
    (a : Bool) (k : kappa) : missingArmCount group arm z a k ≤ m := by
  unfold missingArmCount categoryCount Causalean.Stat.groupCount
    Causalean.Stat.groupArmCount
  split_ifs
  · let s := (Finset.univ.filter fun i : Fin m =>
        group (z i) = k ∧ arm (z i) = false)
    let t := (Finset.univ.filter fun i : Fin m =>
        group (z i) = k ∧ arm (z i) = true)
    have hdis : Disjoint s t := by
      rw [Finset.disjoint_left]
      intro i his hit
      simp only [s, t, Finset.mem_filter] at his hit
      simp_all
    have hsub : s ∪ t ⊆ (Finset.univ : Finset (Fin m)) := by simp
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis] at hc
    simpa [s, t] using hc
  · omega

/-- When the stratum label and the arm assignment are measurable, the product of the counts of
missing arm/category cells for two categories is integrable over the product sample, because
the two counts are bounded by the sample size. -/
@[fun_prop]
lemma integrable_missingArmCount_mul {m : Nat}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (group : Omega → kappa) (arm : Omega → Bool)
    (hgroup : Measurable group) (harm : Measurable arm) (a : Bool)
    (k l : kappa) :
    Integrable (fun z : Fin m → Omega ↦
      (missingArmCount group arm z a k : Real) *
        (missingArmCount group arm z a l : Real))
      (Measure.pi (fun _ : Fin m ↦ mu)) := by
  apply Integrable.of_bound
    (((Measurable.of_discrete : Measurable fun n : Nat => (n : Real)).comp
        (measurable_missingArmCount (m := m) group arm hgroup harm a k)).mul
      ((Measurable.of_discrete : Measurable fun n : Nat => (n : Real)).comp
        (measurable_missingArmCount (m := m) group arm hgroup harm a l))).aestronglyMeasurable
    ((m : Real) ^ 2)
  filter_upwards [] with z
  change ‖(missingArmCount group arm z a k : Real) *
    (missingArmCount group arm z a l : Real)‖ ≤ (m : Real) ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  have hk : (missingArmCount group arm z a k : Real) ≤ (m : Real) := by
    exact_mod_cast missingArmCount_le_sampleSize group arm z a k
  have hl : (missingArmCount group arm z a l : Real) ≤ (m : Real) := by
    exact_mod_cast missingArmCount_le_sampleSize group arm z a l
  nlinarith [(Nat.cast_nonneg (missingArmCount group arm z a k) :
      (0 : Real) ≤ (missingArmCount group arm z a k : Real)),
    (Nat.cast_nonneg (missingArmCount group arm z a l) :
      (0 : Real) ≤ (missingArmCount group arm z a l : Real)),
    (Nat.cast_nonneg m : (0 : Real) ≤ (m : Real))]

private lemma one_sub_pow_le_exp {n : Nat} {x : Real}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 - x) ^ n ≤ Real.exp (-(n : Real) * x) := by
  calc
    (1 - x) ^ n ≤ (Real.exp (-x)) ^ n :=
      pow_le_pow_left₀ (sub_nonneg.mpr hx1) (Real.one_sub_le_exp_neg x) n
    _ = Real.exp (-(n : Real) * x) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

private lemma overlap_all (mu : Measure Omega) [IsProbabilityMeasure mu]
    (group : Omega → kappa)
    (arm : Omega → Bool) (a : Bool) (epsilon : Real)
    (hoverlap : ∀ k, 0 < categoryMass mu group k →
      epsilon * categoryMass mu group k ≤ armCategoryMass mu group arm a k)
    (k : kappa) :
    epsilon * categoryMass mu group k ≤ armCategoryMass mu group arm a k := by
  by_cases hp : 0 < categoryMass mu group k
  · exact hoverlap k hp
  · have hp0 : categoryMass mu group k = 0 :=
      le_antisymm (le_of_not_gt hp) (categoryMass_nonneg mu group k)
    have hq0 : armCategoryMass mu group arm a k = 0 :=
      le_antisymm (hp0 ▸ armCategoryMass_le_categoryMass mu group arm a k)
        (armCategoryMass_nonneg mu group arm a k)
    simp [hp0, hq0]

private lemma diagonal_decay_bound {m : Nat} (mu : Measure Omega)
    [IsProbabilityMeasure mu] (group : Omega → kappa) (arm : Omega → Bool) (a : Bool)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hoverlap : ∀ k, 0 < categoryMass mu group k →
      epsilon * categoryMass mu group k ≤ armCategoryMass mu group arm a k)
    (k : kappa) :
    (categoryMass mu group k - armCategoryMass mu group arm a k) ^ 2 *
        (1 - armCategoryMass mu group arm a k) ^ (m - 2) ≤
      (categoryMass mu group k *
        Real.exp (-(((m - 2 : Nat) : Real) / 2 * epsilon *
          categoryMass mu group k))) ^ 2 := by
  let p := categoryMass mu group k
  let q := armCategoryMass mu group arm a k
  have hp : 0 ≤ p := categoryMass_nonneg mu group k
  have hq : 0 ≤ q := armCategoryMass_nonneg mu group arm a k
  have hqp : q ≤ p := armCategoryMass_le_categoryMass mu group arm a k
  have hp1 : p ≤ 1 := by
    calc p ≤ mu.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := probReal_univ
  have hq1 : q ≤ 1 := hqp.trans hp1
  have hov : epsilon * p ≤ q := overlap_all mu group arm a epsilon hoverlap k
  have hpow := one_sub_pow_le_exp (n := m - 2) hq hq1
  have hexp : Real.exp (-((m - 2 : Nat) : Real) * q) ≤
      Real.exp (-((m - 2 : Nat) : Real) * (epsilon * p)) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hov
      (Nat.cast_nonneg (m - 2) : (0 : Real) ≤ ((m - 2 : Nat) : Real))
    linarith
  calc
    (p - q) ^ 2 * (1 - q) ^ (m - 2) ≤
        p ^ 2 * Real.exp (-((m - 2 : Nat) : Real) * q) := by
      have hr : (p - q) ^ 2 ≤ p ^ 2 := by nlinarith
      exact mul_le_mul hr hpow (pow_nonneg (sub_nonneg.mpr hq1) _)
        (sq_nonneg p)
    _ ≤ p ^ 2 * Real.exp (-((m - 2 : Nat) : Real) * (epsilon * p)) := by
      gcongr
    _ = (p * Real.exp (-(((m - 2 : Nat) : Real) / 2 * epsilon * p))) ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 1
      norm_num
      ring

private lemma cross_decay_bound {m : Nat} (mu : Measure Omega)
    [IsProbabilityMeasure mu] (group : Omega → kappa) (arm : Omega → Bool) (a : Bool)
    (epsilon : Real) (hgroup : Measurable group) (hepsilon : 0 < epsilon)
    (hoverlap : ∀ k, 0 < categoryMass mu group k →
      epsilon * categoryMass mu group k ≤ armCategoryMass mu group arm a k)
    {k l : kappa} (hkl : k ≠ l) :
    (categoryMass mu group k - armCategoryMass mu group arm a k) *
        (categoryMass mu group l - armCategoryMass mu group arm a l) *
        (1 - armCategoryMass mu group arm a k -
          armCategoryMass mu group arm a l) ^ (m - 2) ≤
      (categoryMass mu group k *
          Real.exp (-(((m - 2 : Nat) : Real) / 2 * epsilon *
            categoryMass mu group k))) *
        (categoryMass mu group l *
          Real.exp (-(((m - 2 : Nat) : Real) / 2 * epsilon *
            categoryMass mu group l))) := by
  let pk := categoryMass mu group k
  let pl := categoryMass mu group l
  let qk := armCategoryMass mu group arm a k
  let ql := armCategoryMass mu group arm a l
  have hpk : 0 ≤ pk := categoryMass_nonneg mu group k
  have hpl : 0 ≤ pl := categoryMass_nonneg mu group l
  have hqk : 0 ≤ qk := armCategoryMass_nonneg mu group arm a k
  have hql : 0 ≤ ql := armCategoryMass_nonneg mu group arm a l
  have hqkpk : qk ≤ pk := armCategoryMass_le_categoryMass mu group arm a k
  have hqlpl : ql ≤ pl := armCategoryMass_le_categoryMass mu group arm a l
  have hsum1 : qk + ql ≤ 1 := by
    have hpairs := sum_categoryMass_le_one mu group hgroup ({k, l} : Finset kappa)
    have hpairs' : pk + pl ≤ 1 := by
      simpa [hkl] using hpairs
    linarith
  have hovk : epsilon * pk ≤ qk := overlap_all mu group arm a epsilon hoverlap k
  have hovl : epsilon * pl ≤ ql := overlap_all mu group arm a epsilon hoverlap l
  have hpow := one_sub_pow_le_exp (n := m - 2) (add_nonneg hqk hql) hsum1
  have hepk : 0 ≤ epsilon * pk := mul_nonneg hepsilon.le hpk
  have hepl : 0 ≤ epsilon * pl := mul_nonneg hepsilon.le hpl
  have hovsum : epsilon * pk + epsilon * pl ≤ qk + ql := add_le_add hovk hovl
  have hn : 0 ≤ ((m - 2 : Nat) : Real) := Nat.cast_nonneg _
  have hhalf : ((m - 2 : Nat) : Real) / 2 *
        (epsilon * pk + epsilon * pl) ≤
      ((m - 2 : Nat) : Real) * (qk + ql) := by
    calc
      ((m - 2 : Nat) : Real) / 2 * (epsilon * pk + epsilon * pl) ≤
          ((m - 2 : Nat) : Real) * (epsilon * pk + epsilon * pl) := by
        nlinarith
      _ ≤ ((m - 2 : Nat) : Real) * (qk + ql) := by gcongr
  have hexp : Real.exp (-((m - 2 : Nat) : Real) * (qk + ql)) ≤
      Real.exp (-(((m - 2 : Nat) : Real) / 2 *
        (epsilon * pk + epsilon * pl))) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc
    (pk - qk) * (pl - ql) * (1 - qk - ql) ^ (m - 2) ≤
        (pk * pl) * Real.exp (-((m - 2 : Nat) : Real) * (qk + ql)) := by
      have hrk : 0 ≤ pk - qk := sub_nonneg.mpr hqkpk
      have hrl : 0 ≤ pl - ql := sub_nonneg.mpr hqlpl
      have hr : (pk - qk) * (pl - ql) ≤ pk * pl := by nlinarith
      rw [show 1 - qk - ql = 1 - (qk + ql) by ring]
      exact mul_le_mul hr hpow (pow_nonneg (sub_nonneg.mpr hsum1) _)
        (mul_nonneg hpk hpl)
    _ ≤ (pk * pl) *
        Real.exp (-(((m - 2 : Nat) : Real) / 2 *
          (epsilon * pk + epsilon * pl))) := by gcongr
    _ = (pk * Real.exp (-(((m - 2 : Nat) : Real) / 2 * epsilon * pk))) *
        (pl * Real.exp (-(((m - 2 : Nat) : Real) / 2 * epsilon * pl))) := by
      calc
        pk * pl * Real.exp (-(((m - 2 : Nat) : Real) / 2 *
            (epsilon * pk + epsilon * pl))) =
            pk * pl * Real.exp
              (-((m - 2 : Nat) : Real) / 2 * epsilon * pk +
               -((m - 2 : Nat) : Real) / 2 * epsilon * pl) := by
                congr 2
                ring
        _ = _ := by rw [Real.exp_add]; ring_nf

private lemma integral_sum_missingArmCount_sq_le {m : Nat}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (group : Omega → kappa) (arm : Omega → Bool) (H : Finset kappa)
    (a : Bool) (epsilon : Real) (hgroup : Measurable group)
    (harm : Measurable arm) (hepsilon : 0 < epsilon)
    (hoverlap : ∀ k, 0 < categoryMass mu group k →
      epsilon * categoryMass mu group k ≤ armCategoryMass mu group arm a k) :
    ∫ z : Fin m → Omega,
        (∑ k ∈ H, (missingArmCount group arm z a k : Real)) ^ 2
        ∂(Measure.pi (fun _ : Fin m ↦ mu)) ≤
      (m : Real) * (∑ k ∈ H, categoryMass mu group k) +
        (m.descFactorial 2 : Real) *
          (missingArmExponentialEnvelope mu group m epsilon H) ^ 2 := by
  classical
  let X : kappa → (Fin m → Omega) → Real := fun k z ↦
    (missingArmCount group arm z a k : Real)
  let w : kappa → Real := fun k ↦ categoryMass mu group k *
    Real.exp (-(((m - 2 : Nat) : Real) / 2 * epsilon *
      categoryMass mu group k))
  have hprodInt (k l : kappa) : Integrable (fun z : Fin m → Omega ↦
      X k z * X l z) (Measure.pi (fun _ : Fin m ↦ mu)) := by
    exact integrable_missingArmCount_mul mu group arm hgroup harm a k l
  have hexpand :
      (∫ z : Fin m → Omega, (∑ k ∈ H, X k z) ^ 2
          ∂(Measure.pi (fun _ : Fin m ↦ mu))) =
        ∑ k ∈ H, ∑ l ∈ H,
          ∫ z : Fin m → Omega, X k z * X l z
            ∂(Measure.pi (fun _ : Fin m ↦ mu)) := by
    rw [show (fun z : Fin m → Omega ↦ (∑ k ∈ H, X k z) ^ 2) =
        fun z ↦ ∑ k ∈ H, ∑ l ∈ H, X k z * X l z by
      funext z
      rw [sq, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]]
    rw [integral_finset_sum H]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [integral_finset_sum H]
      exact fun l hl ↦ hprodInt k l
    · intro k hk
      exact integrable_finsetSum H fun l _ ↦ hprodInt k l
  have hw0 (k : kappa) : 0 ≤ w k := by
    dsimp [w]
    exact mul_nonneg (categoryMass_nonneg mu group k) (Real.exp_nonneg _)
  have hdiag (k : kappa) :
      (∫ z : Fin m → Omega, X k z * X k z
          ∂(Measure.pi (fun _ : Fin m ↦ mu))) ≤
        (m : Real) * categoryMass mu group k +
          (m.descFactorial 2 : Real) * (w k) ^ 2 := by
    let p := categoryMass mu group k
    let q := armCategoryMass mu group arm a k
    have hp : 0 ≤ p := categoryMass_nonneg mu group k
    have hq : 0 ≤ q := armCategoryMass_nonneg mu group arm a k
    have hqp : q ≤ p := armCategoryMass_le_categoryMass mu group arm a k
    have hp1 : p ≤ 1 := by
      calc p ≤ mu.real Set.univ := measureReal_mono (Set.subset_univ _)
        _ = 1 := probReal_univ
    have hq1 : q ≤ 1 := hqp.trans hp1
    have hpow1 : (1 - q) ^ (m - 1) ≤ 1 := by
      simpa using pow_le_one₀ (sub_nonneg.mpr hq1) (by linarith : 1 - q ≤ 1)
    have hfirst : (m : Real) * (p - q) * (1 - q) ^ (m - 1) ≤
        (m : Real) * p := by
      have hr : 0 ≤ p - q := sub_nonneg.mpr hqp
      have hrp : p - q ≤ p := by linarith
      calc
        (m : Real) * (p - q) * (1 - q) ^ (m - 1) ≤
            (m : Real) * (p - q) * 1 :=
          mul_le_mul_of_nonneg_left hpow1
            (mul_nonneg (Nat.cast_nonneg _) hr)
        _ ≤ (m : Real) * p := by
          simpa using mul_le_mul_of_nonneg_left hrp
            (Nat.cast_nonneg m : (0 : Real) ≤ (m : Real))
    have hsecond := diagonal_decay_bound (m := m) mu group arm a epsilon
      hepsilon hoverlap k
    rw [show (fun z : Fin m → Omega ↦ X k z * X k z) =
        fun z ↦ (missingArmCount group arm z a k : Real) ^ 2 by
      funext z; simp [X, sq]]
    rw [integral_missingArmCount_sq_eq mu group arm hgroup harm a k]
    dsimp [p, q] at hfirst hsecond ⊢
    dsimp [w]
    have hd0 : 0 ≤ (m.descFactorial 2 : Real) := Nat.cast_nonneg _
    have hs := mul_le_mul_of_nonneg_left hsecond hd0
    nlinarith
  have hcross (k l : kappa) (hkl : k ≠ l) :
      (∫ z : Fin m → Omega, X k z * X l z
          ∂(Measure.pi (fun _ : Fin m ↦ mu))) ≤
        (m.descFactorial 2 : Real) * w k * w l := by
    rw [show (fun z : Fin m → Omega ↦ X k z * X l z) =
        fun z ↦ (missingArmCount group arm z a k : Real) *
          (missingArmCount group arm z a l : Real) by rfl]
    rw [integral_missingArmCount_mul_eq mu group arm hgroup harm a hkl]
    have hd := cross_decay_bound (m := m) mu group arm a epsilon hgroup
      hepsilon hoverlap hkl
    dsimp [w]
    have hd0 : 0 ≤ (m.descFactorial 2 : Real) := Nat.cast_nonneg _
    have hs := mul_le_mul_of_nonneg_left hd hd0
    nlinarith
  rw [hexpand]
  calc
    (∑ k ∈ H, ∑ l ∈ H,
        ∫ z : Fin m → Omega, X k z * X l z
          ∂(Measure.pi (fun _ : Fin m ↦ mu))) =
        ∑ k ∈ H, ((∫ z : Fin m → Omega, X k z * X k z
            ∂(Measure.pi (fun _ : Fin m ↦ mu))) +
          ∑ l ∈ H.erase k, ∫ z : Fin m → Omega, X k z * X l z
            ∂(Measure.pi (fun _ : Fin m ↦ mu))) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_erase_add _ _ hk, add_comm]
    _ ≤ ∑ k ∈ H, ((m : Real) * categoryMass mu group k +
        (m.descFactorial 2 : Real) * w k ^ 2 +
        ∑ l ∈ H.erase k, (m.descFactorial 2 : Real) * w k * w l) := by
      apply Finset.sum_le_sum
      intro k hk
      exact add_le_add (hdiag k) (Finset.sum_le_sum fun l hl ↦
        hcross k l (Finset.ne_of_mem_erase hl).symm)
    _ = (m : Real) * (∑ k ∈ H, categoryMass mu group k) +
        (m.descFactorial 2 : Real) * (∑ k ∈ H, w k) ^ 2 := by
      rw [Finset.mul_sum]
      rw [sq, Finset.sum_mul]
      simp_rw [add_assoc]
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_erase_add _ _ hk, ← Finset.mul_sum]
      ring
    _ = (m : Real) * (∑ k ∈ H, categoryMass mu group k) +
        (m.descFactorial 2 : Real) *
          (missingArmExponentialEnvelope mu group m epsilon H) ^ 2 := by
      rfl

/-- [Measurable group and arm labels](hyp:hgroup,harm), [cell centers bounded in
absolute value by the envelope](hyp:hcenterBound), [a positive overlap
margin](hyp:hepsilon), and [arm mass at least that margin times category
mass](hyp:hoverlap) imply that [the missing-arm remainder has a boundary-safe
diagonal-plus-exponential second-moment bound](goal). -/
theorem integral_fixedStratumArmMissingRemainder_sq_le_aux {m : Nat}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (group : Omega → kappa) (arm : Omega → Bool)
    (center : Bool → kappa → Real) (H : Finset kappa) (a : Bool)
    (M epsilon : Real) (hgroup : Measurable group) (harm : Measurable arm)
    (hcenterBound : ∀ k, |center a k| ≤ M) (hepsilon : 0 < epsilon)
    (hoverlap : ∀ k, 0 < categoryMass mu group k →
      epsilon * categoryMass mu group k ≤ armCategoryMass mu group arm a k) :
    ∫ z : Fin m → Omega,
        (fixedStratumArmMissingRemainder group arm center H a z) ^ 2
        ∂(Measure.pi (fun _ : Fin m => mu)) ≤
      M ^ 2 * (1 / safeSampleSize m +
        (missingArmExponentialEnvelope mu group m epsilon H) ^ 2) := by
  classical
  by_cases hm : m = 0
  · subst m
    simp [fixedStratumArmMissingRemainder, safeSampleSize]
    exact mul_nonneg (sq_nonneg M)
      (add_nonneg (by norm_num) (sq_nonneg _))
  by_cases hH : H.Nonempty
  · obtain ⟨k0, hk0⟩ := hH
    have hM : 0 ≤ M := (abs_nonneg (center a k0)).trans (hcenterBound k0)
    let X : kappa → (Fin m → Omega) → Real := fun k z ↦
      (missingArmCount group arm z a k : Real)
    let S : (Fin m → Omega) → Real := fun z ↦ ∑ k ∈ H, X k z
    let T : (Fin m → Omega) → Real := fun z ↦
      ∑ k ∈ H, center a k * X k z
    have hprodInt (k l : kappa) : Integrable (fun z : Fin m → Omega ↦
        X k z * X l z) (Measure.pi (fun _ : Fin m ↦ mu)) := by
      exact integrable_missingArmCount_mul mu group arm hgroup harm a k l
    have hSsqInt : Integrable (fun z : Fin m → Omega ↦ (S z) ^ 2)
        (Measure.pi (fun _ : Fin m ↦ mu)) := by
      apply (integrable_finsetSum H (fun k _ ↦
        integrable_finsetSum H (fun l _ ↦ hprodInt k l))).congr
      filter_upwards [] with z
      dsimp [S]
      rw [sq, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
    have hTsqInt : Integrable (fun z : Fin m → Omega ↦ (T z) ^ 2)
        (Measure.pi (fun _ : Fin m ↦ mu)) := by
      have hterm (k l : kappa) : Integrable (fun z : Fin m → Omega ↦
          (center a k * center a l) * (X k z * X l z))
          (Measure.pi (fun _ : Fin m ↦ mu)) :=
        (hprodInt k l).const_mul _
      apply (integrable_finsetSum H (fun k _ ↦
        integrable_finsetSum H (fun l _ ↦ hterm k l))).congr
      filter_upwards [] with z
      dsimp [T]
      rw [sq, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    have hS0 (z : Fin m → Omega) : 0 ≤ S z := by
      dsimp [S, X]
      positivity
    have hTbound (z : Fin m → Omega) : |T z| ≤ M * S z := by
      calc
        |T z| ≤ ∑ k ∈ H, |center a k * X k z| := by
          dsimp [T]
          exact Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k ∈ H, |center a k| * X k z := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [abs_mul, abs_of_nonneg (show 0 ≤ X k z by
            exact Nat.cast_nonneg _)]
        _ ≤ ∑ k ∈ H, M * X k z := by
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_right (hcenterBound k) (Nat.cast_nonneg _)
        _ = M * S z := by simp [S, Finset.mul_sum]
    have hrem (z : Fin m → Omega) :
        fixedStratumArmMissingRemainder group arm center H a z =
          T z / (m : Real) := by
      unfold fixedStratumArmMissingRemainder
      dsimp [T, X]
      rw [Finset.sum_div]
    have hpoint (z : Fin m → Omega) :
        (fixedStratumArmMissingRemainder group arm center H a z) ^ 2 ≤
          (M ^ 2 / (m : Real) ^ 2) * (S z) ^ 2 := by
      have hmR : (m : Real) ≠ 0 := by exact_mod_cast hm
      rw [hrem z]
      have hsquare : (T z) ^ 2 ≤ (M * S z) ^ 2 := by
        rw [← sq_abs (T z)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hTbound z) 2
      calc
        (T z / (m : Real)) ^ 2 = (T z) ^ 2 / (m : Real) ^ 2 := by ring
        _ ≤ (M * S z) ^ 2 / (m : Real) ^ 2 := by gcongr
        _ = (M ^ 2 / (m : Real) ^ 2) * (S z) ^ 2 := by ring
    have hint :
        (∫ z : Fin m → Omega,
            (fixedStratumArmMissingRemainder group arm center H a z) ^ 2
            ∂(Measure.pi (fun _ : Fin m ↦ mu))) ≤
          (M ^ 2 / (m : Real) ^ 2) *
            ∫ z : Fin m → Omega, (S z) ^ 2
              ∂(Measure.pi (fun _ : Fin m ↦ mu)) := by
      have hremSqInt : Integrable (fun z : Fin m → Omega ↦
          (fixedStratumArmMissingRemainder group arm center H a z) ^ 2)
          (Measure.pi (fun _ : Fin m ↦ mu)) := by
        apply (hTsqInt.div_const ((m : Real) ^ 2)).congr
        filter_upwards [] with z
        rw [hrem z]
        ring
      rw [← integral_const_mul]
      apply integral_mono hremSqInt
        (hSsqInt.const_mul (M ^ 2 / (m : Real) ^ 2))
      intro z
      exact hpoint z
    have hagg := integral_sum_missingArmCount_sq_le (m := m) mu group arm H a epsilon
      hgroup harm hepsilon hoverlap
    have hmass := sum_categoryMass_le_one mu group hgroup H
    have hd : (m.descFactorial 2 : Real) ≤ (m : Real) ^ 2 := by
      exact_mod_cast Nat.descFactorial_le_pow m 2
    have henv0 : 0 ≤ (missingArmExponentialEnvelope mu group m epsilon H) ^ 2 :=
      sq_nonneg _
    have hagg' :
        (∫ z : Fin m → Omega, (S z) ^ 2
          ∂(Measure.pi (fun _ : Fin m ↦ mu))) ≤
        (m : Real) + (m : Real) ^ 2 *
          (missingArmExponentialEnvelope mu group m epsilon H) ^ 2 := by
      dsimp [S, X]
      calc
        (∫ z : Fin m → Omega,
            (∑ k ∈ H, (missingArmCount group arm z a k : Real)) ^ 2
            ∂(Measure.pi (fun _ : Fin m ↦ mu))) ≤
            (m : Real) * (∑ k ∈ H, categoryMass mu group k) +
              (m.descFactorial 2 : Real) *
                (missingArmExponentialEnvelope mu group m epsilon H) ^ 2 := hagg
        _ ≤ (m : Real) + (m : Real) ^ 2 *
              (missingArmExponentialEnvelope mu group m epsilon H) ^ 2 := by
          have hm0 : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
          exact add_le_add
            (by simpa using mul_le_mul_of_nonneg_left hmass hm0)
            (mul_le_mul_of_nonneg_right hd henv0)
    have hmpos : 0 < (m : Real) := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hcoef : 0 ≤ M ^ 2 / (m : Real) ^ 2 := by positivity
    calc
      (∫ z : Fin m → Omega,
          (fixedStratumArmMissingRemainder group arm center H a z) ^ 2
          ∂(Measure.pi (fun _ : Fin m ↦ mu))) ≤
          (M ^ 2 / (m : Real) ^ 2) *
            ∫ z : Fin m → Omega, (S z) ^ 2
              ∂(Measure.pi (fun _ : Fin m ↦ mu)) := hint
      _ ≤ (M ^ 2 / (m : Real) ^ 2) *
          ((m : Real) + (m : Real) ^ 2 *
            (missingArmExponentialEnvelope mu group m epsilon H) ^ 2) := by
        gcongr
      _ = M ^ 2 * (1 / safeSampleSize m +
          (missingArmExponentialEnvelope mu group m epsilon H) ^ 2) := by
        unfold safeSampleSize
        rw [max_eq_right (Nat.one_le_iff_ne_zero.mpr hm)]
        field_simp
  · have hH0 : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
    subst H
    simp [fixedStratumArmMissingRemainder]
    have hs : 0 ≤ (safeSampleSize m)⁻¹ := by
      apply inv_nonneg.mpr
      unfold safeSampleSize
      positivity
    exact mul_nonneg (sq_nonneg M)
      (add_nonneg hs (sq_nonneg _))

end Causalean.Stat.FiniteStratumMarkedRatioMse
