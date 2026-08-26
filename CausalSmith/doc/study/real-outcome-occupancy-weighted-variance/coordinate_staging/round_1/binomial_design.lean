/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.Probability.BernoulliMeasure
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Bernoulli enumeration for occupancy-weighted design factors

This module turns weighted sums over finite Boolean assignments into binomial
sums and controls the inverse-arm contribution of one occupied group. It is
entirely algebraic and does not use conditional probability.
-/

namespace Causalean.Stat

open scoped BigOperators
open Causalean.Mathlib.Probability

private def boolFunEquivFinset (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (ι → Bool) ≃ Finset ι where
  toFun b := Finset.univ.filter fun i => b i = true
  invFun s := fun i => decide (i ∈ s)
  left_inv b := by
    funext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases b i <;> simp
  right_inv s := by
    ext i
    simp

private lemma prod_bernoulli_eq_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Real) (b : ι → Bool) :
    (∏ i, if b i then p else 1 - p) =
      p ^ (Finset.univ.filter fun i => b i = true).card *
        (1 - p) ^ (Fintype.card ι - (Finset.univ.filter fun i => b i = true).card) := by
  classical
  let s := Finset.univ.filter fun i => b i = true
  let t := Finset.univ.filter fun i => ¬ b i = true
  have hcard : t.card = Fintype.card ι - s.card := by
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ι)) (fun i => b i = true)
    simp only [Finset.card_univ] at hsum
    dsimp [s, t]
    omega
  calc
    (∏ i, if b i then p else 1 - p) =
        (∏ i ∈ s, (if b i then p else 1 - p)) *
          ∏ i ∈ t, (if b i then p else 1 - p) := by
      rw [Finset.prod_filter_mul_prod_filter_not]
    _ = p ^ s.card * (1 - p) ^ t.card := by
      congr 1
      · apply Finset.prod_eq_pow_card
        intro i hi
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp [hi]
      · apply Finset.prod_eq_pow_card
        intro i hi
        simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        cases h : b i <;> simp_all
    _ = _ := by rw [hcard]

/-- [A Bernoulli-weighted sum of any function of the success count equals the
corresponding sum against the binomial mass function](goal). -/
lemma sum_bernoulli_eq_binomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Real) (F : Nat → Real) :
    (∑ b : ι → Bool, (∏ i, if b i then p else 1 - p) *
      F (Finset.univ.filter fun i => b i = true).card) =
    ∑ j ∈ Finset.range (Fintype.card ι + 1),
      binomialWeight (Fintype.card ι) p j * F j := by
  classical
  rw [Fintype.sum_equiv (boolFunEquivFinset ι) _
    (fun s : Finset ι => p ^ s.card * (1 - p) ^ (Fintype.card ι - s.card) * F s.card)
    (fun b => by
      rw [prod_bernoulli_eq_card]
      rfl)]
  rw [show (Finset.univ : Finset (Finset ι)) = Finset.univ.powerset by
    ext s
    simp]
  rw [Finset.sum_powerset]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_powersetCard j Finset.univ
    (fun j => p ^ j * (1 - p) ^ (Fintype.card ι - j) * F j)]
  simp only [Finset.card_univ, binomialWeight]
  ring

private lemma sum_binomialWeight (m : Nat) (p : Real) :
    (∑ j ∈ Finset.range (m + 1), binomialWeight m p j) = 1 := by
  calc
    (∑ j ∈ Finset.range (m + 1), binomialWeight m p j) =
        (p + (1 - p)) ^ m := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [binomialWeight]
      ring
    _ = 1 := by ring

private lemma sum_binomialWeight_interior {m : Nat} (hm : 2 ≤ m) (p : Real) :
    (∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
      (if 0 < j ∧ j < m then (1 : Real) else 0)) =
      1 - p ^ m - (1 - p) ^ m := by
  classical
  let interior := (Finset.range m).erase 0
  have hinterior :
      (Finset.range (m + 1)).filter (fun j => 0 < j ∧ j < m) = interior := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase, ne_eq, interior]
    omega
  have hzero : binomialWeight m p 0 = (1 - p) ^ m := by
    simp [binomialWeight]
  have hmterm : binomialWeight m p m = p ^ m := by
    simp [binomialWeight]
  have h0mem : 0 ∈ Finset.range m := by simp [show 0 < m by omega]
  have hsplit0 :
      (∑ j ∈ Finset.range m, binomialWeight m p j) =
        binomialWeight m p 0 + ∑ j ∈ interior, binomialWeight m p j := by
    rw [show Finset.range m = insert 0 interior by
      simp [interior, h0mem]]
    simp [interior]
  have hsplitm :
      (∑ j ∈ Finset.range (m + 1), binomialWeight m p j) =
        (∑ j ∈ Finset.range m, binomialWeight m p j) +
          binomialWeight m p m := by
    rw [Finset.sum_range_succ]
  have hlhs :
      (∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
        (if 0 < j ∧ j < m then (1 : Real) else 0)) =
        ∑ j ∈ interior, binomialWeight m p j := by
    simp_rw [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    rw [hinterior]
  rw [hlhs]
  have hall := sum_binomialWeight m p
  rw [hsplitm, hsplit0, hzero, hmterm] at hall
  linarith

private lemma sum_binomialWeight_interior_lower {m : Nat} (hm : 2 ≤ m)
    (p epsilon : Real) (hepsilon : 0 < epsilon)
    (hlo : epsilon ≤ p) (hhi : p ≤ 1 - epsilon) :
    2 * epsilon * (1 - epsilon) ≤
      ∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
        (if 0 < j ∧ j < m then (1 : Real) else 0) := by
  have hp0 : 0 ≤ p := (hepsilon.trans_le hlo).le
  have hp1 : p ≤ 1 := by linarith
  have hq0 : 0 ≤ 1 - p := by linarith
  have hq1 : 1 - p ≤ 1 := by linarith
  have hpm : p ^ m ≤ p ^ 2 := pow_le_pow_of_le_one hp0 hp1 hm
  have hqm : (1 - p) ^ m ≤ (1 - p) ^ 2 :=
    pow_le_pow_of_le_one hq0 hq1 hm
  have hpq : epsilon * (1 - epsilon) ≤ p * (1 - p) := by
    have : 0 ≤ (p - epsilon) * (1 - epsilon - p) :=
      mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
    nlinarith
  rw [sum_binomialWeight_interior hm p]
  nlinarith

/-- The two-arm inverse-count contribution is the sum of the inverse success
and failure counts when both are positive, and zero at either endpoint. -/
noncomputable def inverseTwoCounts (m j : Nat) : Real :=
  if 0 < j ∧ j < m then
    (j : Real)⁻¹ + ((m - j : Nat) : Real)⁻¹
  else 0

/-- The binomial interior indicator is one when both success and failure counts
are positive, and zero at either endpoint. -/
def interiorIndicator (m j : Nat) : Real :=
  if 0 < j ∧ j < m then 1 else 0

/-- If [the overlap margin is positive](hyp:hepsilon) and [one group's success
probability lies between the margin and one minus the margin](hyp:hlo,hhi),
[that group's expected inverse-arm variance contribution is controlled by its
expected share of reciprocal usable occupancy](goal). -/
lemma sum_bernoulli_local_variance_le_share
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Nat) (p epsilon : Real) (hepsilon : 0 < epsilon)
    (hlo : epsilon ≤ p) (hhi : p ≤ 1 - epsilon) :
    (∑ b : ι → Bool, (∏ i, if b i then p else 1 - p) *
      ((Fintype.card ι : Real) ^ 2 *
        (((r + Fintype.card ι : Nat) : Real)⁻¹ ^ 2) *
        inverseTwoCounts (Fintype.card ι)
          (Finset.univ.filter fun i => b i = true).card)) ≤
      (4 / (epsilon ^ 2 * (1 - epsilon))) *
        ∑ b : ι → Bool, (∏ i, if b i then p else 1 - p) *
          ((Fintype.card ι : Real) *
            (((r + Fintype.card ι : Nat) : Real)⁻¹ ^ 2) *
            interiorIndicator (Fintype.card ι)
              (Finset.univ.filter fun i => b i = true).card) := by
  classical
  let m := Fintype.card ι
  by_cases hm : 2 ≤ m
  · have hnum := binomial_inverse_two_arms_interior_le m p epsilon
      hepsilon hlo hhi
    have hmass := sum_binomialWeight_interior_lower hm p epsilon
      hepsilon hlo hhi
    have heps1 : 0 < 1 - epsilon := by linarith
    have hmpos : (0 : Real) < (m + 1 : Nat) := by positivity
    have hA :
        (m : Real) *
          (∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
            inverseTwoCounts m j) ≤ 4 / epsilon := by
      have hmle : (m : Real) ≤ (m + 1 : Nat) := by norm_num
      have hden : 0 < ((m + 1 : Nat) : Real) * epsilon := by positivity
      unfold inverseTwoCounts at hnum
      calc
        (m : Real) * (∑ j ∈ Finset.range (m + 1),
            binomialWeight m p j * inverseTwoCounts m j) ≤
            (m : Real) * (4 / (((m + 1 : Nat) : Real) * epsilon)) := by
          gcongr
          simpa [inverseTwoCounts] using hnum
        _ ≤ 4 / epsilon := by
          have hratio : (m : Real) / ((m + 1 : Nat) : Real) ≤ 1 :=
            (div_le_one hmpos).2 hmle
          calc
            (m : Real) * (4 / (((m + 1 : Nat) : Real) * epsilon)) =
                (4 / epsilon) * ((m : Real) / ((m + 1 : Nat) : Real)) := by
              field_simp
              <;> ring
            _ ≤ (4 / epsilon) * 1 :=
              mul_le_mul_of_nonneg_left hratio (by positivity)
            _ = 4 / epsilon := by ring
    have hB : 4 / epsilon ≤
        (4 / (epsilon ^ 2 * (1 - epsilon))) *
          (∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
            interiorIndicator m j) := by
      dsimp [interiorIndicator]
      have hconst : 0 < epsilon ^ 2 * (1 - epsilon) := by positivity
      calc
        4 / epsilon ≤ 8 / epsilon := by
          exact div_le_div_of_nonneg_right (by norm_num) hepsilon.le
        _ = (4 / (epsilon ^ 2 * (1 - epsilon))) *
            (2 * epsilon * (1 - epsilon)) := by
          field_simp
          <;> ring
        _ ≤ (4 / (epsilon ^ 2 * (1 - epsilon))) *
            (∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
              (if 0 < j ∧ j < m then (1 : Real) else 0)) := by
          exact mul_le_mul_of_nonneg_left hmass (by positivity)
    rw [sum_bernoulli_eq_binomial p (fun j =>
      (m : Real) ^ 2 * (((r + m : Nat) : Real)⁻¹ ^ 2) * inverseTwoCounts m j)]
    rw [sum_bernoulli_eq_binomial p (fun j =>
      (m : Real) * (((r + m : Nat) : Real)⁻¹ ^ 2) * interiorIndicator m j)]
    simp only [m]
    have hscale : 0 ≤ (m : Real) * (((r + m : Nat) : Real)⁻¹ ^ 2) := by positivity
    calc
      (∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
          ((m : Real) ^ 2 * (((r + m : Nat) : Real)⁻¹ ^ 2) *
            inverseTwoCounts m j)) =
          ((m : Real) * (((r + m : Nat) : Real)⁻¹ ^ 2)) *
            ((m : Real) * ∑ j ∈ Finset.range (m + 1),
              binomialWeight m p j * inverseTwoCounts m j) := by
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring_nf
      _ ≤ ((m : Real) * (((r + m : Nat) : Real)⁻¹ ^ 2)) * (4 / epsilon) := by
        gcongr
      _ ≤ ((m : Real) * (((r + m : Nat) : Real)⁻¹ ^ 2)) *
          ((4 / (epsilon ^ 2 * (1 - epsilon))) *
            ∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
              interiorIndicator m j) := by
        gcongr
      _ = (4 / (epsilon ^ 2 * (1 - epsilon))) *
          ∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
            ((m : Real) * (((r + m : Nat) : Real)⁻¹ ^ 2) *
              interiorIndicator m j) := by
        simp_rw [Finset.mul_sum]
        ring
  · have hmle : m ≤ 1 := by omega
    have hzero (j : Nat) : inverseTwoCounts (Fintype.card ι) j = 0 := by
      simp only [inverseTwoCounts]
      rw [if_neg]
      dsimp [m] at hmle
      omega
    rw [show (∑ b : ι → Bool, (∏ i, if b i then p else 1 - p) *
        ((Fintype.card ι : Real) ^ 2 *
          (((r + Fintype.card ι : Nat) : Real)⁻¹ ^ 2) *
          inverseTwoCounts (Fintype.card ι)
            (Finset.univ.filter fun i => b i = true).card)) = 0 by
      apply Finset.sum_eq_zero
      intro b hb
      rw [hzero]
      ring]
    apply mul_nonneg
    · have heps1 : 0 < 1 - epsilon := by linarith
      positivity
    · apply Finset.sum_nonneg
      intro b hb
      apply mul_nonneg
      · apply Finset.prod_nonneg
        intro i hi
        split
        · exact (hepsilon.trans_le hlo).le
        · linarith
      · dsimp [interiorIndicator]
        split <;> positivity

end Causalean.Stat
