/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Finite randomization design: expectation, variance, covariance

The probability layer for design-based (randomization) causal inference.  In contrast
to the measure-theoretic superpopulation model used elsewhere in Causalean, here the
only source of randomness is the experimenter's assignment mechanism over a *finite*
set of assignments `Ω`, with known design weights `p z`.  Expectation, variance and
covariance are plain finite sums, so every downstream identity (Horvitz–Thompson
unbiasedness and variance, conservative variance estimators) reduces to `Finset`
algebra with no integrability obligations.

This file provides the reusable algebra: linearity of expectation, the
`Var X = E[X²] − (E X)²` and `Cov X Y = E[X·Y] − E X · E Y` identities, bilinearity
of covariance, the variance of a finite linear combination, and the indicator facts
`E[1_A] = Pr A`, `Var[1_A] = π(1−π)`, `Cov[1_A, 1_B] = Pr(A∩B) − Pr A · Pr B`.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! # Finite randomization design

A `FiniteDesign Ω` is a probability mass function on a finite assignment space `Ω`.
All estimators below are real-valued functions of the realized assignment `z : Ω`,
and `E`, `Var`, `Cov` are their finite-sum moments under the design. -/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace DesignBased

/-- A randomization design: a probability mass function `p` on a finite assignment
space `Ω`. `p_sum` records that the design probabilities sum to one. -/
structure FiniteDesign (Ω : Type*) [Fintype Ω] where
  /-- Design probability of assignment `z`. -/
  p : Ω → ℝ
  /-- Design probabilities are nonnegative. -/
  p_nonneg : ∀ z, 0 ≤ p z
  /-- Design probabilities sum to one. -/
  p_sum : ∑ z, p z = 1

namespace FiniteDesign

variable {Ω : Type*} [Fintype Ω] (D : FiniteDesign Ω)

/-- Expectation of a random variable `X : Ω → ℝ` under the design. -/
def E (X : Ω → ℝ) : ℝ := ∑ z, D.p z * X z

/-- Variance of `X` under the design. -/
def Var (X : Ω → ℝ) : ℝ := D.E (fun z => (X z - D.E X) ^ 2)

/-- Covariance of `X` and `Y` under the design. -/
def Cov (X Y : Ω → ℝ) : ℝ := D.E (fun z => (X z - D.E X) * (Y z - D.E Y))

/-- Indicator of an event `A`, as a `{0,1}`-valued random variable. -/
def ind (A : Ω → Prop) [DecidablePred A] : Ω → ℝ := fun z => if A z then 1 else 0

/-- Probability of an event `A` under the design. -/
def Pr (A : Ω → Prop) [DecidablePred A] : ℝ := D.E (ind A)

/-! ### Linearity of expectation -/

/-- The expectation of a constant random variable is that constant. -/
@[simp] lemma E_const (c : ℝ) : D.E (fun _ => c) = c := by
  simp only [E, ← Finset.sum_mul, D.p_sum, one_mul]

/-- The expectation of a sum is the sum of expectations. -/
lemma E_add (X Y : Ω → ℝ) : D.E (fun z => X z + Y z) = D.E X + D.E Y := by
  simp only [E, mul_add, Finset.sum_add_distrib]

/-- The expectation of a difference is the difference of expectations. -/
lemma E_sub (X Y : Ω → ℝ) : D.E (fun z => X z - Y z) = D.E X - D.E Y := by
  simp only [E, mul_sub, Finset.sum_sub_distrib]

/-- Multiplying a random variable by a constant on the left multiplies its expectation by that
constant. -/
lemma E_const_mul (c : ℝ) (X : Ω → ℝ) : D.E (fun z => c * X z) = c * D.E X := by
  simp only [E, Finset.mul_sum]; congr 1; funext z; ring

/-- Multiplying a random variable by a constant on the right multiplies its expectation by that
constant. -/
lemma E_mul_const (X : Ω → ℝ) (c : ℝ) : D.E (fun z => X z * c) = D.E X * c := by
  simp only [E, Finset.sum_mul]; congr 1; funext z; ring

/-- The expectation of a negated random variable is the negated expectation. -/
lemma E_neg (X : Ω → ℝ) : D.E (fun z => -X z) = -D.E X := by
  simp only [E, mul_neg, Finset.sum_neg_distrib]

/-- The expectation of a finite sum of random variables is the corresponding finite sum of
expectations. -/
lemma E_sum {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ) :
    D.E (fun z => ∑ i ∈ s, f i z) = ∑ i ∈ s, D.E (f i) := by
  simp only [E, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Congruence: pointwise-equal random variables have equal expectation. -/
lemma E_congr {X Y : Ω → ℝ} (h : ∀ z, X z = Y z) : D.E X = D.E Y := by
  unfold E; exact Finset.sum_congr rfl (fun z _ => by rw [h z])

/-- Congruence: pointwise-equal random variables have equal variance. -/
lemma Var_congr {X Y : Ω → ℝ} (h : ∀ z, X z = Y z) : D.Var X = D.Var Y := by
  have hE : D.E X = D.E Y := D.E_congr h
  unfold Var; rw [hE]; exact D.E_congr (fun z => by rw [h z])

/-- Congruence: pointwise-equal random variables have equal covariance. -/
lemma Cov_congr {X Y X' Y' : Ω → ℝ} (hX : ∀ z, X z = X' z) (hY : ∀ z, Y z = Y' z) :
    D.Cov X Y = D.Cov X' Y' := by
  have hEX : D.E X = D.E X' := D.E_congr hX
  have hEY : D.E Y = D.E Y' := D.E_congr hY
  unfold Cov; rw [hEX, hEY]; exact D.E_congr (fun z => by rw [hX z, hY z])

/-! ### Variance and covariance identities -/

/-- Variance equals the second moment minus the square of the mean. -/
lemma Var_eq (X : Ω → ℝ) : D.Var X = D.E (fun z => (X z) ^ 2) - (D.E X) ^ 2 := by
  have h : (fun z => (X z - D.E X) ^ 2)
      = (fun z => (X z) ^ 2 + ((-(2 * D.E X)) * X z + (D.E X) ^ 2)) := by
    funext z; ring
  rw [Var, h, E_add, E_add, E_const_mul, E_const]; ring

/-- Covariance equals the mixed second moment minus the product of the two means. -/
lemma Cov_eq (X Y : Ω → ℝ) :
    D.Cov X Y = D.E (fun z => X z * Y z) - D.E X * D.E Y := by
  have h : (fun z => (X z - D.E X) * (Y z - D.E Y))
      = (fun z => X z * Y z + ((-(D.E Y)) * X z + ((-(D.E X)) * Y z + D.E X * D.E Y))) := by
    funext z; ring
  rw [Cov, h, E_add, E_add, E_add, E_const_mul, E_const_mul, E_const]; ring

/-- The covariance of a random variable with itself is its variance. -/
lemma Cov_self (X : Ω → ℝ) : D.Cov X X = D.Var X := by
  unfold Cov Var; exact D.E_congr (fun z => by ring)

/-- Covariance is symmetric in its two arguments. -/
lemma Cov_comm (X Y : Ω → ℝ) : D.Cov X Y = D.Cov Y X := by
  unfold Cov; exact D.E_congr (fun z => by ring)

/-! ### Bilinearity of covariance -/

/-- Multiplying the left random variable by a constant multiplies covariance by that constant. -/
lemma Cov_const_mul_left (c : ℝ) (X Y : Ω → ℝ) :
    D.Cov (fun z => c * X z) Y = c * D.Cov X Y := by
  rw [Cov_eq, Cov_eq, E_const_mul]
  have : D.E (fun z => c * X z * Y z) = c * D.E (fun z => X z * Y z) := by
    rw [← E_const_mul]; exact D.E_congr (fun z => by ring)
  rw [this]; ring

/-- Covariance with a finite sum in the left argument is the finite sum of covariances. -/
lemma Cov_sum_left {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ) (Y : Ω → ℝ) :
    D.Cov (fun z => ∑ i ∈ s, f i z) Y = ∑ i ∈ s, D.Cov (f i) Y := by
  have hEY : D.E (fun z => (∑ i ∈ s, f i z) * Y z)
      = ∑ i ∈ s, D.E (fun z => f i z * Y z) := by
    rw [← E_sum]; exact D.E_congr (fun z => by rw [Finset.sum_mul])
  simp only [Cov_eq]
  rw [hEY, E_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]

/-- Covariance with a finite sum in the right argument is the finite sum of covariances. -/
lemma Cov_sum_right {ι : Type*} (s : Finset ι) (X : Ω → ℝ) (g : ι → Ω → ℝ) :
    D.Cov X (fun z => ∑ i ∈ s, g i z) = ∑ i ∈ s, D.Cov X (g i) := by
  rw [Cov_comm, Cov_sum_left]
  exact Finset.sum_congr rfl (fun i _ => D.Cov_comm _ _)

/-- Multiplying the right random variable by a constant multiplies covariance by that constant. -/
lemma Cov_const_mul_right (c : ℝ) (X Y : Ω → ℝ) :
    D.Cov X (fun z => c * Y z) = c * D.Cov X Y := by
  rw [Cov_comm, Cov_const_mul_left, Cov_comm]

/-- Covariance is linear over differences in its left argument. -/
lemma Cov_sub_left (X Y Z : Ω → ℝ) :
    D.Cov (fun z => X z - Y z) Z = D.Cov X Z - D.Cov Y Z := by
  have h1 : D.E (fun z => (X z - Y z) * Z z)
      = D.E (fun z => X z * Z z) - D.E (fun z => Y z * Z z) := by
    rw [← E_sub]; exact D.E_congr (fun z => by ring)
  rw [Cov_eq, Cov_eq, Cov_eq, E_sub, h1]; ring

/-- Covariance is linear over differences in its right argument. -/
lemma Cov_sub_right (X Y Z : Ω → ℝ) :
    D.Cov X (fun z => Y z - Z z) = D.Cov X Y - D.Cov X Z := by
  rw [Cov_comm, Cov_sub_left, D.Cov_comm Y X, D.Cov_comm Z X]

/-- Variance of a difference: `Var(X−Y) = Var X + Var Y − 2 Cov(X,Y)`. -/
lemma Var_sub (X Y : Ω → ℝ) :
    D.Var (fun z => X z - Y z) = D.Var X + D.Var Y - 2 * D.Cov X Y := by
  rw [← Cov_self, Cov_sub_left, Cov_sub_right, Cov_sub_right, Cov_self, Cov_self, D.Cov_comm Y X]
  ring

/-- Variance scales by the square of a constant: `Var(c·X) = c²·Var X`. -/
lemma Var_const_mul (c : ℝ) (X : Ω → ℝ) :
    D.Var (fun z => c * X z) = c ^ 2 * D.Var X := by
  rw [← Cov_self, Cov_const_mul_left, Cov_const_mul_right, Cov_self]; ring

/-- Covariance of two finite linear combinations as a double sum of covariances. -/
lemma Cov_linear_comb {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (c : ι → ℝ) (e : κ → ℝ) (X : ι → Ω → ℝ) (Y : κ → Ω → ℝ) :
    D.Cov (fun z => ∑ i ∈ s, c i * X i z) (fun z => ∑ j ∈ t, e j * Y j z)
      = ∑ i ∈ s, ∑ j ∈ t, c i * e j * D.Cov (X i) (Y j) := by
  rw [Cov_sum_left]
  apply Finset.sum_congr rfl; intro i _
  rw [Cov_const_mul_left, Cov_sum_right, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  rw [Cov_const_mul_right]; ring

/-- Variance of a finite linear combination `∑ cᵢ Xᵢ` as a double sum of covariances. -/
lemma Var_linear_comb {ι : Type*} (s : Finset ι) (c : ι → ℝ) (X : ι → Ω → ℝ) :
    D.Var (fun z => ∑ i ∈ s, c i * X i z)
      = ∑ i ∈ s, ∑ j ∈ s, c i * c j * D.Cov (X i) (X j) := by
  rw [← Cov_self]; exact D.Cov_linear_comb s s c c X X

/-! ### Indicator facts -/

/-- The expectation of an event indicator is the design probability of that event. -/
@[simp] lemma E_ind (A : Ω → Prop) [DecidablePred A] : D.E (ind A) = D.Pr A := rfl

omit [Fintype Ω] in
/-- `1_A ^ 2 = 1_A`, the idempotence of an indicator. -/
lemma ind_sq (A : Ω → Prop) [DecidablePred A] :
    (fun z => (ind A z) ^ 2) = ind A := by
  funext z; unfold ind; by_cases h : A z <;> simp [h]

/-- The variance of an event indicator is its probability times one minus its probability. -/
lemma Var_ind (A : Ω → Prop) [DecidablePred A] :
    D.Var (ind A) = D.Pr A * (1 - D.Pr A) := by
  rw [Var_eq, ind_sq, E_ind]; ring

/-! ### Elementary bounds -/

/-- Expectation of a nonnegative random variable is nonnegative. -/
lemma E_nonneg {X : Ω → ℝ} (h : ∀ z, 0 ≤ X z) : 0 ≤ D.E X :=
  Finset.sum_nonneg (fun z _ => mul_nonneg (D.p_nonneg z) (h z))

/-- Expectation of a random variable bounded above by one is at most one. -/
lemma E_le_one {X : Ω → ℝ} (h1 : ∀ z, X z ≤ 1) : D.E X ≤ 1 := by
  calc D.E X = ∑ z, D.p z * X z := rfl
    _ ≤ ∑ z, D.p z * 1 :=
        Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (h1 z) (D.p_nonneg z))
    _ = 1 := by simp [D.p_sum]

omit [Fintype Ω] in
/-- An event indicator is always nonnegative. -/
lemma ind_nonneg (A : Ω → Prop) [DecidablePred A] (z : Ω) : 0 ≤ ind A z := by
  unfold ind; by_cases h : A z <;> simp [h]

omit [Fintype Ω] in
/-- An event indicator is always at most one. -/
lemma ind_le_one (A : Ω → Prop) [DecidablePred A] (z : Ω) : ind A z ≤ 1 := by
  unfold ind; by_cases h : A z <;> simp [h]

/-- A probability lies in `[0,1]`: nonnegativity. -/
lemma Pr_nonneg (A : Ω → Prop) [DecidablePred A] : 0 ≤ D.Pr A :=
  D.E_nonneg (fun z => ind_nonneg A z)

/-- A probability lies in `[0,1]`: at most one. -/
lemma Pr_le_one (A : Ω → Prop) [DecidablePred A] : D.Pr A ≤ 1 :=
  D.E_le_one (fun z => ind_le_one A z)

/-- Probability respects pointwise-equivalent events. -/
lemma Pr_congr (A B : Ω → Prop) [DecidablePred A] [DecidablePred B] (h : ∀ z, A z ↔ B z) :
    D.Pr A = D.Pr B := by
  unfold Pr; exact D.E_congr (fun z => by unfold ind; simp only [h z])

/-- Monotonicity of probability: a smaller event has smaller probability. -/
lemma Pr_mono (A B : Ω → Prop) [DecidablePred A] [DecidablePred B] (h : ∀ z, A z → B z) :
    D.Pr A ≤ D.Pr B := by
  unfold Pr E ind
  apply Finset.sum_le_sum
  intro z _
  apply mul_le_mul_of_nonneg_left _ (D.p_nonneg z)
  by_cases hA : A z
  · simp [hA, h z hA]
  · by_cases hB : B z <;> simp [hA, hB]

/-- Finite additivity: splitting an event by a second event. -/
lemma Pr_split (B A : Ω → Prop) [DecidablePred A] [DecidablePred B] :
    D.Pr B = D.Pr (fun z => B z ∧ A z) + D.Pr (fun z => B z ∧ ¬ A z) := by
  unfold Pr E ind
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hB : B z <;> by_cases hA : A z <;> simp [hB, hA]

/-! ### Pushforward along a map -/

/-- The **pushforward** design `f_* D` of `D` along `f : Ω → Ω'`: the law of the transformed
assignment `f z` when `z` is drawn from `D`.  Its weight on `y` is the total design weight of the
fiber `f⁻¹{y}`. -/
noncomputable def map {Ω' : Type*} [Fintype Ω'] [DecidableEq Ω'] (f : Ω → Ω') :
    FiniteDesign Ω' where
  p := fun y => ∑ z, if f z = y then D.p z else 0
  p_nonneg := fun y => Finset.sum_nonneg fun z _ => by
    by_cases h : f z = y <;> simp [h, D.p_nonneg z]
  p_sum := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact D.p_sum

/-- The pushforward weight of `y` is the fiber sum `∑_{z} 1[f z = y] · D.p z`. -/
@[simp] lemma map_p {Ω' : Type*} [Fintype Ω'] [DecidableEq Ω'] (f : Ω → Ω') (y : Ω') :
    (D.map f).p y = ∑ z, if f z = y then D.p z else 0 := rfl

/-- **Transfer of expectation across a pushforward.**  The expectation of `g` under the
pushforward `f_* D` equals the expectation of the composite `g ∘ f` under `D`. -/
lemma E_map {Ω' : Type*} [Fintype Ω'] [DecidableEq Ω'] (f : Ω → Ω') (g : Ω' → ℝ) :
    (D.map f).E g = D.E (fun z => g (f z)) := by
  unfold E map
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hpt : ∀ y, (if f z = y then D.p z else 0) * g y
      = if f z = y then D.p z * g y else 0 := fun y => by
    by_cases h : f z = y <;> simp [h]
  simp only [hpt, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- **Transfer of probability across a pushforward.**  The probability of an event `A` under the
pushforward `f_* D` equals the probability of its preimage under `D`. -/
lemma Pr_map {Ω' : Type*} [Fintype Ω'] [DecidableEq Ω'] (f : Ω → Ω')
    (A : Ω' → Prop) [DecidablePred A] :
    (D.map f).Pr A = D.Pr (fun z => A (f z)) := by
  unfold Pr; rw [E_map]; rfl

end FiniteDesign

end DesignBased
end Experimentation
end Causalean
