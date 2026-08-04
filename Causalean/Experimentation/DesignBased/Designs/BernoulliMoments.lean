/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Higher-order product moments of the Bernoulli design

`Designs/Bernoulli.lean` records the first- and second-order inclusion facts — the expectation of
one treatment indicator, and of a product of two.  This file removes the arity ceiling: under a
Bernoulli randomization the coins are independent, so the expectation of a product of *any* family
of one-coordinate statistics factors into the product of the one-coordinate expectations, over the
whole population or over any `Finset` of units.

On top of that factorization it builds the **centered monomials** `∏_{j ∈ S} (1{z j} − p j)`, the
Walsh/Fourier basis of the biased Boolean cube.  Distinct centered monomials are uncorrelated and
the `S`-monomial has second moment `∏_{j ∈ S} p j (1 − p j)`; this orthogonality is the
computational core of exact design-variance formulas for statistics of a Bernoulli assignment.
The basis is complete, so every statistic has an expansion, its second moment is the Parseval
energy of the coefficients, and a statistic that only looks at a block of units has coefficients
supported on the subsets of that block.
-/

import Causalean.Experimentation.DesignBased.Designs.Bernoulli
import Causalean.Experimentation.DesignBased.ProductBlock

/-! # Product moments and centered monomials of the Bernoulli design

This file provides the arbitrary-arity product-expectation identities for `bernoulliDesign`
(`bernoulliDesign_E_prod` and its `Finset`-restricted form `bernoulliDesign_E_prod_finset`), the
raw-monomial expectation `bernoulliDesign_E_treatInd_prod`, and the centered monomial basis
`centeredMonomial` with its orthogonality theorem
`bernoulliDesign_E_centeredMonomial_mul` and its pairing against a raw monomial
`bernoulliDesign_E_centeredMonomial_mul_treatInd_prod`.

It then develops the centered-monomial (Walsh/Fourier) expansion of an arbitrary statistic:
`exists_centeredMonomial_expansion` (completeness), `bernoulliDesign_E_sq_of_expansion`
(Parseval), and the coefficient-support facts `centeredMonomial_coef_empty_eq_zero` and
`centeredMonomial_coef_eq_zero_of_not_subset` for statistics satisfying `DependsOnBlock`. -/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {U : Type*} [Fintype U] [DecidableEq U]

/-! ### Product expectations -/

/-- Independence across units turns the expectation of a product into a product of expectations:
if every unit contributes a factor that depends only on its own coin, the design expectation of
the whole product is the product over units of `p i · g i (treated) + (1 − p i) · g i (control)`. -/
lemma bernoulliDesign_E_prod (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (g : U → Bool → ℝ) :
    (bernoulliDesign p hp0 hp1).E (fun z => ∏ i, g i (z i)) =
      ∏ i, (p i * g i true + (1 - p i) * g i false) := by
  unfold bernoulliDesign
  rw [FiniteDesign.E_prod_prod]
  exact Finset.prod_congr rfl fun i _ => coinDesign_E (p i) (hp0 i) (hp1 i) (g i)

/-- The same factorization when only the units in a finite set `S` contribute a factor: the units
outside `S` are simply averaged out and leave no trace. -/
lemma bernoulliDesign_E_prod_finset (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (S : Finset U) (g : U → Bool → ℝ) :
    (bernoulliDesign p hp0 hp1).E (fun z => ∏ k ∈ S, g k (z k)) =
      ∏ k ∈ S, (p k * g k true + (1 - p k) * g k false) := by
  rw [show (fun z : U → Bool => ∏ k ∈ S, g k (z k)) =
      (fun z => ∏ k, (fun i b => if i ∈ S then g i b else 1) k (z k)) by
    funext z
    rw [Finset.prod_ite_mem, Finset.univ_inter]]
  rw [bernoulliDesign_E_prod p hp0 hp1 (fun i b => if i ∈ S then g i b else 1)]
  rw [show (fun k => p k * (if k ∈ S then g k true else 1) +
        (1 - p k) * (if k ∈ S then g k false else 1)) =
      (fun k => if k ∈ S then p k * g k true + (1 - p k) * g k false else 1) by
    funext k
    by_cases hk : k ∈ S <;> simp [hk]]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

/-- **Higher-order inclusion probability.** The units in a finite set `S` are all treated together
with probability `∏_{j ∈ S} p j`; equivalently, the expectation of the product of their treatment
indicators is the product of their treatment probabilities. -/
theorem bernoulliDesign_E_treatInd_prod (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (S : Finset U) :
    (bernoulliDesign p hp0 hp1).E (fun z => ∏ j ∈ S, treatInd j z) = ∏ j ∈ S, p j := by
  rw [show (fun z : U → Bool => ∏ j ∈ S, treatInd j z) =
      (fun z => ∏ j ∈ S, (fun _ : U => fun b : Bool => if b then (1 : ℝ) else 0) j (z j)) from rfl]
  rw [bernoulliDesign_E_prod_finset p hp0 hp1 S (fun _ b => if b then (1 : ℝ) else 0)]
  simp

/-- The units in a finite set `S` are all left untreated together with probability
`∏_{j ∈ S} (1 − p j)`: the expectation of the product of their control indicators is the product of
their control probabilities. -/
theorem bernoulliDesign_E_ctrlInd_prod (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (S : Finset U) :
    (bernoulliDesign p hp0 hp1).E (fun z => ∏ j ∈ S, (1 - treatInd j z)) =
      ∏ j ∈ S, (1 - p j) := by
  rw [show (fun z : U → Bool => ∏ j ∈ S, (1 - treatInd j z)) =
      (fun z => ∏ j ∈ S, (fun _ : U => fun b : Bool => 1 - if b then (1 : ℝ) else 0) j (z j))
        from rfl]
  rw [bernoulliDesign_E_prod_finset p hp0 hp1 S (fun _ b => 1 - if b then (1 : ℝ) else 0)]
  exact Finset.prod_congr rfl fun j _ => by simp

omit [Fintype U] in
/-- Treatment indicators take only the values zero and one, so two overlapping products of them
collapse into a single product over the union of the two sets of units. -/
lemma treatInd_prod_mul_prod (S T : Finset U) (z : U → Bool) :
    (∏ j ∈ S, treatInd j z) * (∏ j ∈ T, treatInd j z) = ∏ j ∈ S ∪ T, treatInd j z := by
  by_cases h : ∀ j ∈ S ∪ T, z j = true
  · have hone : ∀ A : Finset U, A ⊆ S ∪ T → ∏ j ∈ A, treatInd j z = 1 := fun A hA =>
      Finset.prod_eq_one fun j hj => by simp [treatInd, h j (hA hj)]
    rw [hone S Finset.subset_union_left, hone T Finset.subset_union_right,
      hone (S ∪ T) Finset.Subset.rfl, one_mul]
  · push_neg at h
    obtain ⟨j, hj, hzj⟩ := h
    have hzero : treatInd j z = 0 := by simp [treatInd, Bool.eq_false_iff.mpr hzj]
    rw [Finset.prod_eq_zero hj hzero]
    rcases Finset.mem_union.mp hj with hjS | hjT
    · rw [Finset.prod_eq_zero hjS hzero, zero_mul]
    · rw [Finset.prod_eq_zero hjT hzero, mul_zero]

omit [Fintype U] in
/-- Control indicators take only the values zero and one, so two overlapping products of them
collapse into a single product over the union of the two sets of units. -/
lemma ctrlInd_prod_mul_prod (S T : Finset U) (z : U → Bool) :
    (∏ j ∈ S, (1 - treatInd j z)) * (∏ j ∈ T, (1 - treatInd j z)) =
      ∏ j ∈ S ∪ T, (1 - treatInd j z) := by
  by_cases h : ∀ j ∈ S ∪ T, z j = false
  · have hone : ∀ A : Finset U, A ⊆ S ∪ T → ∏ j ∈ A, (1 - treatInd j z) = 1 := fun A hA =>
      Finset.prod_eq_one fun j hj => by simp [treatInd, h j (hA hj)]
    rw [hone S Finset.subset_union_left, hone T Finset.subset_union_right,
      hone (S ∪ T) Finset.Subset.rfl, one_mul]
  · push_neg at h
    obtain ⟨j, hj, hzj⟩ := h
    have hzj' : z j = true := by cases hzj' : z j <;> simp_all
    have hzero : 1 - treatInd j z = 0 := by simp [treatInd, hzj']
    rw [Finset.prod_eq_zero hj hzero]
    rcases Finset.mem_union.mp hj with hjS | hjT
    · rw [Finset.prod_eq_zero hjS hzero, zero_mul]
    · rw [Finset.prod_eq_zero hjT hzero, mul_zero]

/-- Two overlapping sets of units are simultaneously treated with probability
`∏_{j ∈ S ∪ T} p j`: the shared units are counted once, not twice. -/
theorem bernoulliDesign_E_treatInd_prod_mul_prod (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (S T : Finset U) :
    (bernoulliDesign p hp0 hp1).E
        (fun z => (∏ j ∈ S, treatInd j z) * ∏ j ∈ T, treatInd j z) = ∏ j ∈ S ∪ T, p j := by
  rw [show (fun z : U → Bool => (∏ j ∈ S, treatInd j z) * ∏ j ∈ T, treatInd j z) =
      (fun z => ∏ j ∈ S ∪ T, treatInd j z) from funext fun z => treatInd_prod_mul_prod S T z]
  exact bernoulliDesign_E_treatInd_prod p hp0 hp1 (S ∪ T)

/-- Two overlapping sets of units are simultaneously left untreated with probability
`∏_{j ∈ S ∪ T} (1 − p j)`: the shared units are counted once, not twice. -/
theorem bernoulliDesign_E_ctrlInd_prod_mul_prod (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (S T : Finset U) :
    (bernoulliDesign p hp0 hp1).E
        (fun z => (∏ j ∈ S, (1 - treatInd j z)) * ∏ j ∈ T, (1 - treatInd j z)) =
      ∏ j ∈ S ∪ T, (1 - p j) := by
  rw [show (fun z : U → Bool => (∏ j ∈ S, (1 - treatInd j z)) * ∏ j ∈ T, (1 - treatInd j z)) =
      (fun z => ∏ j ∈ S ∪ T, (1 - treatInd j z)) from funext fun z => ctrlInd_prod_mul_prod S T z]
  exact bernoulliDesign_E_ctrlInd_prod p hp0 hp1 (S ∪ T)

/-! ### Centered monomials and their orthogonality -/

/-- The **centered monomial** attached to a finite set of units `S`: the product over `j ∈ S` of
unit `j`'s treatment indicator minus its treatment probability.  These are the Walsh/Fourier basis
functions of the biased Boolean cube; the empty set gives the constant `1`. -/
noncomputable def centeredMonomial (p : U → ℝ) (S : Finset U) : (U → Bool) → ℝ :=
  fun z => ∏ j ∈ S, (treatInd j z - p j)

omit [Fintype U] [DecidableEq U] in
/-- The centered monomial of the empty set of units is the constant function `1`. -/
@[simp] lemma centeredMonomial_empty (p : U → ℝ) : centeredMonomial p (∅ : Finset U) = fun _ => 1 :=
  rfl

/-- **Orthogonality of the centered monomials.** Two centered monomials attached to different sets
of units are uncorrelated under a Bernoulli randomization, and the monomial attached to `S` has
second moment `∏_{j ∈ S} p j (1 − p j)` — the product of the per-unit assignment variances.  This
is the design-based analogue of the orthonormality of a Fourier basis. -/
theorem bernoulliDesign_E_centeredMonomial_mul (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (S T : Finset U) :
    (bernoulliDesign p hp0 hp1).E (fun z => centeredMonomial p S z * centeredMonomial p T z) =
      if S = T then ∏ j ∈ S, p j * (1 - p j) else 0 := by
  set x : U → Bool → ℝ := fun j b => (if b then (1 : ℝ) else 0) - p j with hx
  rw [show (fun z : U → Bool => centeredMonomial p S z * centeredMonomial p T z) =
      (fun z => ∏ j, ((if j ∈ S then x j (z j) else 1) * (if j ∈ T then x j (z j) else 1))) by
    funext z
    rw [Finset.prod_mul_distrib]
    simp [centeredMonomial, treatInd, hx]]
  rw [bernoulliDesign_E_prod p hp0 hp1
    (fun j b => (if j ∈ S then x j b else 1) * (if j ∈ T then x j b else 1))]
  by_cases hST : S = T
  · subst hST
    rw [if_pos rfl]
    have hfactor (j : U) :
        p j * ((if j ∈ S then x j true else 1) * (if j ∈ S then x j true else 1)) +
            (1 - p j) * ((if j ∈ S then x j false else 1) * (if j ∈ S then x j false else 1)) =
          if j ∈ S then p j * (1 - p j) else 1 := by
      by_cases hj : j ∈ S <;> simp [hj, hx]
      ring
    simp_rw [hfactor]
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  · rw [if_neg hST]
    have hdiff : ∃ j, (j ∈ S ∧ j ∉ T) ∨ (j ∈ T ∧ j ∉ S) := by
      by_contra h
      exact hST (Finset.ext fun j => ⟨fun hjS => by
        by_contra hjT; exact h ⟨j, Or.inl ⟨hjS, hjT⟩⟩, fun hjT => by
        by_contra hjS; exact h ⟨j, Or.inr ⟨hjT, hjS⟩⟩⟩)
    obtain ⟨j, hj⟩ := hdiff
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    rcases hj with hj | hj
    · simp [hj.1, hj.2, hx]; ring
    · simp [hj.1, hj.2, hx]; ring

/-- A centered monomial has mean zero unless it is the constant one: the design expectation of the
`S`-centered monomial is `1` when `S` is empty and `0` otherwise. -/
theorem bernoulliDesign_E_centeredMonomial (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (S : Finset U) :
    (bernoulliDesign p hp0 hp1).E (centeredMonomial p S) = if S = ∅ then 1 else 0 := by
  rcases eq_or_ne S ∅ with hS | hS
  · subst hS
    simp
  · have h := bernoulliDesign_E_centeredMonomial_mul p hp0 hp1 S ∅
    rw [if_neg hS] at h
    simpa [centeredMonomial, hS] using h

/-- **Pairing a centered monomial with a raw monomial.** The expectation of the `S`-centered
monomial times the product of the treatment indicators of a set `T` vanishes unless every unit of
`S` also lies in `T`; when it does, it equals the product of the assignment variances
`p j (1 − p j)` over `S` times the treatment probabilities of the units of `T` outside `S`. -/
theorem bernoulliDesign_E_centeredMonomial_mul_treatInd_prod (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (S T : Finset U) :
    (bernoulliDesign p hp0 hp1).E
        (fun z => centeredMonomial p S z * ∏ j ∈ T, treatInd j z) =
      if S ⊆ T then (∏ j ∈ S, p j * (1 - p j)) * ∏ j ∈ T \ S, p j else 0 := by
  set x : U → Bool → ℝ := fun j b => (if b then (1 : ℝ) else 0) - p j with hx
  set y : Bool → ℝ := fun b => if b then (1 : ℝ) else 0 with hy
  rw [show (fun z : U → Bool => centeredMonomial p S z * ∏ j ∈ T, treatInd j z) =
      (fun z => ∏ j, ((if j ∈ S then x j (z j) else 1) * (if j ∈ T then y (z j) else 1))) by
    funext z
    rw [Finset.prod_mul_distrib]
    simp [centeredMonomial, treatInd, hx, hy]]
  rw [bernoulliDesign_E_prod p hp0 hp1
    (fun j b => (if j ∈ S then x j b else 1) * (if j ∈ T then y b else 1))]
  have hfactor (j : U) :
      p j * ((if j ∈ S then x j true else 1) * (if j ∈ T then y true else 1)) +
          (1 - p j) * ((if j ∈ S then x j false else 1) * (if j ∈ T then y false else 1)) =
        if j ∈ S then (if j ∈ T then p j * (1 - p j) else 0) else if j ∈ T then p j else 1 := by
    by_cases hjS : j ∈ S <;> by_cases hjT : j ∈ T <;> simp [hjS, hjT, hx, hy]
    ring
  simp_rw [hfactor]
  by_cases hsub : S ⊆ T
  · rw [if_pos hsub]
    have hsplit (j : U) :
        (if j ∈ S then (if j ∈ T then p j * (1 - p j) else 0) else if j ∈ T then p j else 1) =
          (if j ∈ S then p j * (1 - p j) else 1) * (if j ∈ T \ S then p j else 1) := by
      by_cases hjS : j ∈ S
      · simp [hjS, hsub hjS]
      · by_cases hjT : j ∈ T <;> simp [hjS, hjT]
    simp_rw [hsplit]
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter,
      Finset.prod_ite_mem, Finset.univ_inter]
  · rw [if_neg hsub]
    obtain ⟨j, hjS, hjT⟩ : ∃ j, j ∈ S ∧ j ∉ T := by
      simpa only [Finset.not_subset] using hsub
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hjS, hjT])

/-! ### The centered-monomial expansion -/

omit [DecidableEq U] in
/-- **Completeness of the centered-monomial basis.** Every real-valued statistic of a Bernoulli
assignment can be written as a linear combination of the centered monomials indexed by the subsets
of the population — the design-based Fourier (Walsh) expansion of the statistic. -/
lemma exists_centeredMonomial_expansion (p : U → ℝ) (F : (U → Bool) → ℝ) :
    ∃ a : Finset U → ℝ, ∀ z,
      F z = ∑ S ∈ (Finset.univ : Finset U).powerset, a S * centeredMonomial p S z := by
  classical
  set sgn : Bool → ℝ := fun b => if b then 1 else -1 with hsgn
  set base : U → Bool → ℝ := fun j b => if b then p j else 1 - p j with hbase
  refine ⟨fun S => ∑ w : U → Bool, F w * (∏ j ∈ S, sgn (w j)) *
      ∏ j ∈ (Finset.univ : Finset U) \ S, base j (w j), fun z => ?_⟩
  have hdelta (w : U → Bool) :
      (if z = w then (1 : ℝ) else 0) =
        ∑ S ∈ (Finset.univ : Finset U).powerset,
          ((∏ j ∈ S, sgn (w j)) * ∏ j ∈ (Finset.univ : Finset U) \ S, base j (w j)) *
            centeredMonomial p S z := by
    rw [show (if z = w then (1 : ℝ) else 0) = ∏ j : U, if z j = w j then (1 : ℝ) else 0 by
      by_cases hzw : z = w
      · subst hzw; simp
      · rw [if_neg hzw]
        obtain ⟨j, hj⟩ : ∃ j, z j ≠ w j := by simpa [funext_iff] using hzw
        exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])).symm]
    rw [show (∏ j : U, if z j = w j then (1 : ℝ) else 0) =
        ∏ j : U, (sgn (w j) * (treatInd j z - p j) + base j (w j)) by
      refine Finset.prod_congr rfl fun j _ => ?_
      cases hz : z j <;> cases hw : w j <;> simp [hz, hsgn, hbase, treatInd]]
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [show (∏ i ∈ S, sgn (w i) * (treatInd i z - p i)) =
        (∏ i ∈ S, sgn (w i)) * centeredMonomial p S z by
      rw [Finset.prod_mul_distrib]; rfl]
    ring
  calc
    F z = ∑ w : U → Bool, F w * (if z = w then (1 : ℝ) else 0) := by
      rw [Finset.sum_eq_single z]
      · simp
      · intro w _ hwz; simp [Ne.symm hwz]
      · simp
    _ = ∑ w : U → Bool, F w * ∑ S ∈ (Finset.univ : Finset U).powerset,
        ((∏ j ∈ S, sgn (w j)) * ∏ j ∈ (Finset.univ : Finset U) \ S, base j (w j)) *
          centeredMonomial p S z :=
      Finset.sum_congr rfl fun w _ => by rw [hdelta w]
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun w _ => by ring

/-- **Parseval's identity for the Bernoulli design.** Once a statistic is written in the
centered-monomial basis, its second moment is the sum over subsets of the squared coefficient times
the product of the per-unit assignment variances on that subset — the basis is orthogonal, so no
cross terms survive. -/
theorem bernoulliDesign_E_sq_of_expansion (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (F : (U → Bool) → ℝ) (a : Finset U → ℝ)
    (ha : ∀ z, F z = ∑ S ∈ (Finset.univ : Finset U).powerset, a S * centeredMonomial p S z) :
    (bernoulliDesign p hp0 hp1).E (fun z => F z ^ 2) =
      ∑ S ∈ (Finset.univ : Finset U).powerset, a S ^ 2 * ∏ j ∈ S, p j * (1 - p j) := by
  rw [show (fun z => F z ^ 2) =
      (fun z => (∑ S ∈ (Finset.univ : Finset U).powerset, a S * centeredMonomial p S z) *
        ∑ T ∈ (Finset.univ : Finset U).powerset, a T * centeredMonomial p T z) by
    funext z; rw [ha z]; ring]
  simp only [Finset.sum_mul, Finset.mul_sum, FiniteDesign.E_sum]
  have hterm (S T : Finset U) :
      (bernoulliDesign p hp0 hp1).E
          (fun z => (a S * centeredMonomial p S z) * (a T * centeredMonomial p T z)) =
        a S * a T * (if S = T then ∏ j ∈ S, p j * (1 - p j) else 0) := by
    rw [show (fun z => (a S * centeredMonomial p S z) * (a T * centeredMonomial p T z)) =
        (fun z => (a S * a T) * (centeredMonomial p S z * centeredMonomial p T z)) by
      funext z; ring]
    rw [FiniteDesign.E_const_mul, bernoulliDesign_E_centeredMonomial_mul p hp0 hp1 S T]
  simp_rw [hterm]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.sum_eq_single S]
  · rw [if_pos rfl]; ring
  · intro T _ hTS; rw [if_neg hTS]; ring
  · exact fun hS' => (hS' hS).elim

/-- A statistic with design mean zero has no constant term: the coefficient of the empty subset in
any centered-monomial expansion of it vanishes. -/
theorem centeredMonomial_coef_empty_eq_zero (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (F : (U → Bool) → ℝ) (a : Finset U → ℝ)
    (ha : ∀ z, F z = ∑ S ∈ (Finset.univ : Finset U).powerset, a S * centeredMonomial p S z)
    (hmean : (bernoulliDesign p hp0 hp1).E F = 0) :
    a ∅ = 0 := by
  rw [show F = fun z => ∑ S ∈ (Finset.univ : Finset U).powerset, a S * centeredMonomial p S z from
      funext ha, FiniteDesign.E_sum] at hmean
  have hterm (S : Finset U) :
      (bernoulliDesign p hp0 hp1).E (fun z => a S * centeredMonomial p S z) =
        if S = ∅ then a S else 0 := by
    rw [FiniteDesign.E_const_mul, bernoulliDesign_E_centeredMonomial p hp0 hp1 S]
    by_cases hS : S = ∅ <;> simp [hS]
  simp_rw [hterm] at hmean
  simpa using hmean

/-- A statistic **depends only on the coordinate block `N`** if changing the assignment of any unit
outside `N` leaves its value unchanged. -/
def DependsOnBlock (N : Finset U) (F : (U → Bool) → ℝ) : Prop :=
  ∀ z z', (∀ j ∈ N, z j = z' j) → F z = F z'

omit [DecidableEq U] in
/-- **Locality of the Fourier support.** If a statistic depends only on the units of a block `N`,
every centered-monomial coefficient attached to a subset that is not contained in `N` is zero, so
its expansion is supported on the subsets of `N`.  (Only treatment probabilities on `S` must be
strictly between zero and one, so those selected coordinates are nondegenerate.) -/
theorem centeredMonomial_coef_eq_zero_of_not_subset (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (N : Finset U) (F : (U → Bool) → ℝ) (hF : DependsOnBlock N F)
    (a : Finset U → ℝ)
    (ha : ∀ z, F z = ∑ S ∈ (Finset.univ : Finset U).powerset, a S * centeredMonomial p S z)
    (S : Finset U) (hSN : ¬ S ⊆ N) (hp0S : ∀ i ∈ S, 0 < p i)
    (hp1S : ∀ i ∈ S, p i < 1) :
    a S = 0 := by
  classical
  have hS : S ∈ (Finset.univ : Finset U).powerset :=
    Finset.mem_powerset.mpr (Finset.subset_univ S)
  obtain ⟨j, hjS, hjN⟩ : ∃ j, j ∈ S ∧ j ∉ N := by simpa only [Finset.not_subset] using hSN
  have hp0' : ∀ i, 0 ≤ p i := hp0
  have hp1' : ∀ i, p i ≤ 1 := hp1
  set Dcoin : U → FiniteDesign Bool := fun i => coinDesign (p i) (hp0' i) (hp1' i) with hDcoin
  set R : (U → Bool) → ℝ := fun z => F z * centeredMonomial p (S.erase j) z with hR
  have hzero : (bernoulliDesign p hp0' hp1').E (fun z => F z * centeredMonomial p S z) = 0 := by
    unfold bernoulliDesign
    rw [show (fun z => F z * centeredMonomial p S z) =
        (fun z => (treatInd j z - p j) * R z) by
      funext z
      rw [hR]
      simp only [centeredMonomial]
      rw [← Finset.mul_prod_erase S (fun k => treatInd k z - p k) hjS]
      ring]
    rw [FiniteDesign.E_prod_block_mul Dcoin {j} (fun z => treatInd j z - p j) R]
    · have hx : (prodDesign Dcoin).E (fun z => treatInd j z - p j) = 0 := by
        have hE := bernoulliDesign_E_centeredMonomial p hp0' hp1' ({j} : Finset U)
        rw [if_neg (Finset.singleton_ne_empty j),
          show centeredMonomial p ({j} : Finset U) = fun z => treatInd j z - p j from
            funext fun z => by simp [centeredMonomial]] at hE
        simpa [bernoulliDesign, hDcoin] using hE
      rw [hx, zero_mul]
    · intro z z' hzz
      simp only [treatInd, hzz j (Finset.mem_singleton_self j)]
    · intro z z' hzz
      rw [hR]
      refine congrArg₂ (· * ·) (hF z z' fun k hkN => hzz k ?_) ?_
      · exact fun hkj => hjN (by rw [Finset.mem_singleton.mp hkj] at hkN; exact hkN)
      · simp only [centeredMonomial]
        refine Finset.prod_congr rfl fun k hk => ?_
        simp only [treatInd, hzz k (by simpa using Finset.ne_of_mem_erase hk)]
  have hcoef : (bernoulliDesign p hp0' hp1').E (fun z => F z * centeredMonomial p S z) =
      a S * ∏ i ∈ S, p i * (1 - p i) := by
    rw [show (fun z => F z * centeredMonomial p S z) =
        (fun z => ∑ T ∈ (Finset.univ : Finset U).powerset,
          a T * (centeredMonomial p T z * centeredMonomial p S z)) by
      funext z
      rw [ha z, Finset.sum_mul]
      exact Finset.sum_congr rfl fun T _ => by ring]
    rw [FiniteDesign.E_sum]
    simp_rw [FiniteDesign.E_const_mul, bernoulliDesign_E_centeredMonomial_mul p hp0' hp1']
    rw [Finset.sum_eq_single S]
    · simp
    · intro T _ hTS; simp [hTS]
    · exact fun h => (h hS).elim
  rw [hzero] at hcoef
  have hv : (∏ i ∈ S, p i * (1 - p i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi =>
      (mul_pos (hp0S i hi) (sub_pos.mpr (hp1S i hi))).ne'
  exact (mul_eq_zero.mp hcoef.symm).resolve_right hv

end DesignBased
end Experimentation
end Causalean
