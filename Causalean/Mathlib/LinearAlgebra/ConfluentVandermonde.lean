/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Confluent Vandermonde certificates
-/

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Confluent Vandermonde matrices

This file proves nonsingularity of the Hermite evaluation matrix at distinct
complex nodes, together with the pinned variant having one simple node and all
remaining nodes doubled.
-/

namespace Causalean.Mathlib.LinearAlgebra

open scoped BigOperators

noncomputable section

/-- The monomial exponent attached to the two copies of `Fin n`. -/
def doubledExponent {n : ℕ} : Fin n ⊕ Fin n → ℕ
  | Sum.inl i => i.val
  | Sum.inr i => n + i.val

/-- The doubled exponent encoding is injective. -/
lemma doubledExponent_injective {n : ℕ} :
    Function.Injective (doubledExponent : Fin n ⊕ Fin n → ℕ) := by
  intro i j hij
  rcases i with i | i <;> rcases j with j | j
  · simp only [doubledExponent] at hij
    exact congrArg Sum.inl (Fin.ext hij)
  · simp only [doubledExponent] at hij
    exfalso
    have := i.isLt
    omega
  · simp only [doubledExponent] at hij
    exfalso
    have := j.isLt
    omega
  · simp only [doubledExponent] at hij
    exact congrArg Sum.inr (Fin.ext (Nat.add_left_cancel hij))

/-- Every doubled exponent is strictly below `2n`. -/
lemma doubledExponent_lt {n : ℕ} (hn : 1 ≤ n) (i : Fin n ⊕ Fin n) :
    doubledExponent i < 2 * n := by
  rcases i with i | i <;> simp only [doubledExponent]
  · omega
  · have := i.isLt
    omega

/-- Monomial coefficients encoded by the doubled finite index. -/
def doubledCoefficientPolynomial {n : ℕ} (v : Fin n ⊕ Fin n → ℂ) : Polynomial ℂ :=
  ∑ i, Polynomial.monomial (doubledExponent i) (v i)

/-- Reading a doubled coefficient polynomial at an encoded exponent recovers
the corresponding coefficient. -/
lemma coeff_doubledCoefficientPolynomial {n : ℕ}
    (v : Fin n ⊕ Fin n → ℂ) (i : Fin n ⊕ Fin n) :
    (doubledCoefficientPolynomial v).coeff (doubledExponent i) = v i := by
  classical
  change (Polynomial.lcoeff ℂ (doubledExponent i))
      (∑ j, Polynomial.monomial (doubledExponent j) (v j)) = v i
  rw [map_sum]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
    exact if_neg (doubledExponent_injective.ne hji)
  · simp

/-- A doubled coefficient polynomial vanishes exactly when its coefficient
vector vanishes. -/
lemma doubledCoefficientPolynomial_eq_zero_iff {n : ℕ}
    (v : Fin n ⊕ Fin n → ℂ) : doubledCoefficientPolynomial v = 0 ↔ v = 0 := by
  constructor
  · intro hp
    funext i
    have := congrArg (fun p : Polynomial ℂ => p.coeff (doubledExponent i)) hp
    simpa [coeff_doubledCoefficientPolynomial] using this
  · rintro rfl
    simp [doubledCoefficientPolynomial]

/-- A nonzero doubled coefficient polynomial has degree below `2n`. -/
lemma natDegree_doubledCoefficientPolynomial_lt {n : ℕ} (hn : 1 ≤ n)
    {v : Fin n ⊕ Fin n → ℂ} (hv : v ≠ 0) :
    (doubledCoefficientPolynomial v).natDegree < 2 * n := by
  apply lt_of_le_of_lt
    (Polynomial.natDegree_sum_le_of_forall_le (Finset.univ) _
      (fun i _ => (Polynomial.natDegree_monomial_le _).trans
        (Nat.le_pred_of_lt (doubledExponent_lt hn i))))
  have hpos : 0 < 2 * n := by omega
  exact Nat.pred_lt hpos.ne'

/-- The square Hermite-evaluation matrix with value and first-derivative
columns at every node.  Rows are monomials of degrees `0, ..., 2n-1`. -/
def confluentVandermonde (s : Fin n → ℂ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  fun a b => match b with
    | Sum.inl i => s i ^ doubledExponent a
    | Sum.inr i => (doubledExponent a : ℂ) * s i ^ (doubledExponent a - 1)

private lemma eval_doubledCoefficientPolynomial {n : ℕ}
    (v : Fin n ⊕ Fin n → ℂ) (x : ℂ) :
    (doubledCoefficientPolynomial v).eval x =
      ∑ a, x ^ doubledExponent a * v a := by
  simp only [doubledCoefficientPolynomial]
  rw [Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro a _
  ring

private lemma eval_derivative_doubledCoefficientPolynomial {n : ℕ}
    (v : Fin n ⊕ Fin n → ℂ) (x : ℂ) :
    (doubledCoefficientPolynomial v).derivative.eval x =
      ∑ a, ((doubledExponent a : ℂ) * x ^ (doubledExponent a - 1)) * v a := by
  simp only [doubledCoefficientPolynomial, map_sum,
    Polynomial.derivative_monomial]
  rw [Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- A polynomial of degree below `2n` whose value and derivative vanish at
`n` distinct points is zero. -/
lemma doubledCoefficientPolynomial_eq_zero_of_eval_derivative
    {n : ℕ} (hn : 1 ≤ n) (s : Fin n → ℂ) (hs : Function.Injective s)
    (v : Fin n ⊕ Fin n → ℂ)
    (heval : ∀ i, (doubledCoefficientPolynomial v).eval (s i) = 0)
    (hderiv : ∀ i, (doubledCoefficientPolynomial v).derivative.eval (s i) = 0) :
    v = 0 := by
  by_contra hv
  have hp : doubledCoefficientPolynomial v ≠ 0 :=
    (doubledCoefficientPolynomial_eq_zero_iff v).not.mpr hv
  have hfactor (i : Fin n) : (Polynomial.X - Polynomial.C (s i)) ^ 2 ∣
      doubledCoefficientPolynomial v := by
    rw [← Polynomial.le_rootMultiplicity_iff hp]
    apply (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).2
    exact ⟨heval i, hderiv i⟩
  have hcop : Pairwise (Function.onFun IsCoprime
      fun i : Fin n => (Polynomial.X - Polynomial.C (s i)) ^ 2) := by
    intro i j hij
    apply (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (show IsUnit (s i - s j) from (sub_ne_zero.mpr (hs.ne hij)).isUnit)).pow
  have hprod : (∏ i : Fin n, (Polynomial.X - Polynomial.C (s i)) ^ 2) ∣
      doubledCoefficientPolynomial v :=
    Fintype.prod_dvd_of_coprime hcop hfactor
  have hdegree := Polynomial.natDegree_le_of_dvd hprod hp
  have hleft : (∏ i : Fin n,
      (Polynomial.X - Polynomial.C (s i)) ^ 2).natDegree = 2 * n := by
    calc
      _ = ∑ i : Fin n,
          ((Polynomial.X - Polynomial.C (s i)) ^ 2).natDegree := by
        apply Polynomial.natDegree_prod
        intro i _
        exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero (s i))
      _ = 2 * n := by simp [Polynomial.natDegree_pow,
        Polynomial.natDegree_X_sub_C, Nat.mul_comm]
  rw [hleft] at hdegree
  exact (not_lt_of_ge hdegree)
    (natDegree_doubledCoefficientPolynomial_lt hn hv)

/-- The confluent Vandermonde determinant is nonzero at pairwise distinct
nodes. -/
theorem det_confluentVandermonde_ne_zero {n : ℕ} (hn : 1 ≤ n)
    (s : Fin n → ℂ) (hs : Function.Injective s) :
    (confluentVandermonde s).det ≠ 0 := by
  let M := confluentVandermonde s
  have hmul : Function.Injective M.transpose.mulVec := by
    intro u v huv
    apply sub_eq_zero.mp
    let w := u - v
    have hw : M.transpose.mulVec w = 0 := by
      funext b
      simp only [w, Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.zero_apply,
        mul_sub, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (congrFun huv b)
    apply doubledCoefficientPolynomial_eq_zero_of_eval_derivative hn s hs w
    · intro i
      have hi := congrFun hw (Sum.inl i)
      simpa [M, confluentVandermonde, Matrix.mulVec, dotProduct,
        eval_doubledCoefficientPolynomial, mul_comm] using hi
    · intro i
      have hi := congrFun hw (Sum.inr i)
      simpa [M, confluentVandermonde, Matrix.mulVec, dotProduct,
        eval_derivative_doubledCoefficientPolynomial, mul_comm, mul_left_comm,
        mul_assoc] using hi
  have hu : IsUnit M.transpose := Matrix.mulVec_injective_iff_isUnit.mp hmul
  have hdet : IsUnit M.transpose.det :=
    hu.map (Matrix.detMonoidHom (n := Fin n ⊕ Fin n) (R := ℂ))
  simpa [M, Matrix.det_transpose] using hdet.ne_zero

/-! ### A pinned Hermite minor: one simple node and the remaining double nodes -/

/-- Monomial degrees for one simple node and `n - 1` doubled nodes. -/
def pinnedExponent {n : ℕ} : Fin n ⊕ Fin (n - 1) → ℕ
  | Sum.inl i => i.val
  | Sum.inr i => n + i.val

/-- Embed the doubled-node index as a positive node index. -/
def pinnedSucc {n : ℕ} (hn : 1 ≤ n) (i : Fin (n - 1)) : Fin n :=
  ⟨i.val + 1, by have := i.isLt; omega⟩

/-- The positive-node embedding is injective. -/
lemma pinnedSucc_injective {n : ℕ} (hn : 1 ≤ n) :
    Function.Injective (pinnedSucc hn) := by
  intro i j hij
  apply Fin.ext
  have := congrArg Fin.val hij
  simp only [pinnedSucc] at this
  omega

/-- A positive-node index never equals the distinguished zero node. -/
lemma pinnedSucc_ne_zero {n : ℕ} (hn : 1 ≤ n) (i : Fin (n - 1)) :
    pinnedSucc hn i ≠ ⟨0, hn⟩ := by
  intro h
  have := congrArg Fin.val h
  simp [pinnedSucc] at this

/-- The pinned exponent encoding is injective. -/
lemma pinnedExponent_injective {n : ℕ} :
    Function.Injective (pinnedExponent : Fin n ⊕ Fin (n - 1) → ℕ) := by
  intro i j hij
  rcases i with i | i <;> rcases j with j | j
  · exact congrArg Sum.inl (Fin.ext hij)
  · exfalso
    simp only [pinnedExponent] at hij
    have := i.isLt
    omega
  · exfalso
    simp only [pinnedExponent] at hij
    have := j.isLt
    omega
  · simp only [pinnedExponent] at hij
    exact congrArg Sum.inr (Fin.ext (Nat.add_left_cancel hij))

/-- Every pinned exponent is strictly below `2n - 1`. -/
lemma pinnedExponent_lt {n : ℕ} (hn : 1 ≤ n)
    (i : Fin n ⊕ Fin (n - 1)) : pinnedExponent i < 2 * n - 1 := by
  rcases i with i | i <;> simp only [pinnedExponent]
  · have := i.isLt
    omega
  · have := i.isLt
    omega

/-- Encode pinned Hermite coefficients as a polynomial. -/
def pinnedCoefficientPolynomial {n : ℕ}
    (v : Fin n ⊕ Fin (n - 1) → ℂ) : Polynomial ℂ :=
  ∑ i, Polynomial.monomial (pinnedExponent i) (v i)

/-- Reading a pinned coefficient polynomial at an encoded exponent recovers
the corresponding coefficient. -/
lemma coeff_pinnedCoefficientPolynomial {n : ℕ}
    (v : Fin n ⊕ Fin (n - 1) → ℂ) (i : Fin n ⊕ Fin (n - 1)) :
    (pinnedCoefficientPolynomial v).coeff (pinnedExponent i) = v i := by
  classical
  change (Polynomial.lcoeff ℂ (pinnedExponent i))
      (∑ j, Polynomial.monomial (pinnedExponent j) (v j)) = v i
  rw [map_sum, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
    exact if_neg (pinnedExponent_injective.ne hji)
  · simp

/-- A pinned coefficient polynomial vanishes exactly when its coefficient
vector vanishes. -/
lemma pinnedCoefficientPolynomial_eq_zero_iff {n : ℕ}
    (v : Fin n ⊕ Fin (n - 1) → ℂ) :
    pinnedCoefficientPolynomial v = 0 ↔ v = 0 := by
  constructor
  · intro hp
    funext i
    have hi := congrArg
      (fun p : Polynomial ℂ => p.coeff (pinnedExponent i)) hp
    simpa [coeff_pinnedCoefficientPolynomial] using hi
  · rintro rfl
    simp [pinnedCoefficientPolynomial]

/-- A pinned coefficient polynomial has degree below `2n - 1`. -/
lemma natDegree_pinnedCoefficientPolynomial_lt {n : ℕ} (hn : 1 ≤ n)
    {v : Fin n ⊕ Fin (n - 1) → ℂ} :
    (pinnedCoefficientPolynomial v).natDegree < 2 * n - 1 := by
  have hpos : 0 < 2 * n - 1 := by omega
  apply lt_of_le_of_lt
    (Polynomial.natDegree_sum_le_of_forall_le (Finset.univ) _
      (fun i _ => (Polynomial.natDegree_monomial_le _).trans
        (Nat.le_pred_of_lt (pinnedExponent_lt hn i))))
  exact Nat.pred_lt hpos.ne'

/-- The pinned Hermite matrix records values at all nodes and derivatives at
nodes `1, ..., n-1`, with the derivative at node zero deleted. -/
def pinnedConfluentVandermonde (hn : 1 ≤ n) (s : Fin n → ℂ) :
    Matrix (Fin n ⊕ Fin (n - 1)) (Fin n ⊕ Fin (n - 1)) ℂ :=
  fun a b => match b with
    | Sum.inl i => s i ^ pinnedExponent a
    | Sum.inr i => (pinnedExponent a : ℂ) *
        s (pinnedSucc hn i) ^ (pinnedExponent a - 1)

private lemma eval_pinnedCoefficientPolynomial {n : ℕ}
    (v : Fin n ⊕ Fin (n - 1) → ℂ) (x : ℂ) :
    (pinnedCoefficientPolynomial v).eval x =
      ∑ a, x ^ pinnedExponent a * v a := by
  simp only [pinnedCoefficientPolynomial]
  rw [Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro a _
  ring

private lemma eval_derivative_pinnedCoefficientPolynomial {n : ℕ}
    (v : Fin n ⊕ Fin (n - 1) → ℂ) (x : ℂ) :
    (pinnedCoefficientPolynomial v).derivative.eval x =
      ∑ a, ((pinnedExponent a : ℂ) * x ^ (pinnedExponent a - 1)) * v a := by
  simp only [pinnedCoefficientPolynomial, map_sum,
    Polynomial.derivative_monomial]
  rw [Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- A polynomial in the pinned coefficient model is zero when it vanishes at
all nodes and its derivative vanishes at every nondistinguished node. -/
lemma pinnedCoefficientPolynomial_eq_zero_of_eval_derivative
    {n : ℕ} (hn : 1 ≤ n) (s : Fin n → ℂ) (hs : Function.Injective s)
    (v : Fin n ⊕ Fin (n - 1) → ℂ)
    (heval : ∀ i, (pinnedCoefficientPolynomial v).eval (s i) = 0)
    (hderiv : ∀ i : Fin (n - 1),
      (pinnedCoefficientPolynomial v).derivative.eval (s (pinnedSucc hn i)) = 0) :
    v = 0 := by
  by_contra hv
  have hp : pinnedCoefficientPolynomial v ≠ 0 :=
    (pinnedCoefficientPolynomial_eq_zero_iff v).not.mpr hv
  let first := Polynomial.X - Polynomial.C (s ⟨0, hn⟩)
  let rest : Fin (n - 1) → Polynomial ℂ := fun i =>
    (Polynomial.X - Polynomial.C (s (pinnedSucc hn i))) ^ 2
  have hfirst : first ∣ pinnedCoefficientPolynomial v := by
    rw [Polynomial.dvd_iff_isRoot]
    exact heval ⟨0, hn⟩
  have hrest (i : Fin (n - 1)) : rest i ∣ pinnedCoefficientPolynomial v := by
    dsimp [rest]
    rw [← Polynomial.le_rootMultiplicity_iff hp]
    apply (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).2
    exact ⟨heval (pinnedSucc hn i), hderiv i⟩
  have hrestcop : Pairwise (Function.onFun IsCoprime rest) := by
    intro i j hij
    apply (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (show IsUnit (s (pinnedSucc hn i) - s (pinnedSucc hn j)) from
        (sub_ne_zero.mpr (by
          intro h
          apply hij
          apply pinnedSucc_injective hn
          exact hs h)).isUnit)).pow
  have hrestprod : (∏ i, rest i) ∣ pinnedCoefficientPolynomial v :=
    Fintype.prod_dvd_of_coprime hrestcop hrest
  have hfirstrest : IsCoprime first (∏ i, rest i) := by
    apply IsCoprime.prod_right
    intro i _
    dsimp [first, rest]
    exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (show IsUnit (s ⟨0, hn⟩ - s (pinnedSucc hn i)) from
        (sub_ne_zero.mpr (hs.ne (pinnedSucc_ne_zero hn i).symm)).isUnit)).pow_right
  have htotal : first * (∏ i, rest i) ∣ pinnedCoefficientPolynomial v :=
    hfirstrest.mul_dvd hfirst hrestprod
  have hdegree := Polynomial.natDegree_le_of_dvd htotal hp
  have hleft : (first * ∏ i, rest i).natDegree = 2 * n - 1 := by
    rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _
        (Polynomial.X_sub_C_ne_zero _)))]
    have hrestdeg : (∏ i, rest i).natDegree = 2 * (n - 1) := by
      calc
        _ = ∑ i : Fin (n - 1), (rest i).natDegree := by
          apply Polynomial.natDegree_prod
          intro i _
          exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
        _ = 2 * (n - 1) := by simp [rest, Polynomial.natDegree_pow,
          Nat.mul_comm]
    rw [hrestdeg]
    simp [first]
    omega
  rw [hleft] at hdegree
  exact (not_lt_of_ge hdegree)
    (natDegree_pinnedCoefficientPolynomial_lt hn)

/-- The pinned confluent Vandermonde determinant is nonzero at pairwise distinct
nodes: one node contributes only value evaluation and every other node contributes
both value and first-derivative evaluation. -/
theorem det_pinnedConfluentVandermonde_ne_zero {n : ℕ} (hn : 1 ≤ n)
    (s : Fin n → ℂ) (hs : Function.Injective s) :
    (pinnedConfluentVandermonde hn s).det ≠ 0 := by
  let M := pinnedConfluentVandermonde hn s
  have hmul : Function.Injective M.transpose.mulVec := by
    intro u v huv
    apply sub_eq_zero.mp
    let w := u - v
    have hw : M.transpose.mulVec w = 0 := by
      funext b
      simp only [w, Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.zero_apply,
        mul_sub, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (congrFun huv b)
    apply pinnedCoefficientPolynomial_eq_zero_of_eval_derivative hn s hs w
    · intro i
      have hi := congrFun hw (Sum.inl i)
      simpa [M, pinnedConfluentVandermonde, Matrix.mulVec, dotProduct,
        eval_pinnedCoefficientPolynomial, mul_comm] using hi
    · intro i
      have hi := congrFun hw (Sum.inr i)
      simpa [M, pinnedConfluentVandermonde, Matrix.mulVec, dotProduct,
        eval_derivative_pinnedCoefficientPolynomial, mul_comm, mul_left_comm,
        mul_assoc] using hi
  have hu : IsUnit M.transpose := Matrix.mulVec_injective_iff_isUnit.mp hmul
  have hdet : IsUnit M.transpose.det := hu.map
    (Matrix.detMonoidHom (n := Fin n ⊕ Fin (n - 1)) (R := ℂ))
  simpa [M, Matrix.det_transpose] using hdet.ne_zero

end

end Causalean.Mathlib.LinearAlgebra
