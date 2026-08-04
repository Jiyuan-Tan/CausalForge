/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Cross-coordinate independence of the product design

Functions of distinct coordinates of a product design are uncorrelated, so the variance
of a linear combination of single-coordinate functions is the sum of the coordinate
variances.  This is the within-group variance term for a between-group / within-group
variance decomposition (Hudgens–Halloran-style partial interference): assembling the
coordinate randomizations into a `prodDesign` makes cross-coordinate independence a
structural fact.

The payload is `Var_prod_linear_comb`:

    (prodDesign D).Var (fun w => ∑ i, c i * g i (w i)) = ∑ i, (c i)^2 * (D i).Var (g i).

It rests on the two-coordinate factorization `E_prod_apply₂`, the single-coordinate
variance `Var_prod_apply`, and the cross-coordinate covariance vanishing
`Cov_prod_apply_of_ne`.
-/

import Causalean.Experimentation.DesignBased.ProductBlock

/-! # Product-design variance identities

Distinct coordinates of a finite product design are uncorrelated.

`FiniteDesign.E_prod_apply₂` factors expectations of products of statistics on two distinct
coordinates, yielding `FiniteDesign.Var_prod_apply` for one-coordinate variances and
`FiniteDesign.Cov_prod_apply_of_ne` for zero cross-coordinate covariance.  The payload
`FiniteDesign.Var_prod_linear_comb` states that the variance of a linear combination of
single-coordinate statistics is the sum of squared coefficients times the marginal variances.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : ι → Type*} [∀ i, Fintype (α i)]

namespace FiniteDesign

/-- Two-coordinate factorization: under the product design, the expectation of a product
of a function of one coordinate and a function of a distinct coordinate factors into the
product of the two marginal expectations. -/
lemma E_prod_apply₂ (D : ∀ i, FiniteDesign (α i)) {i j : ι} (h : i ≠ j)
    (g : α i → ℝ) (hfun : α j → ℝ) :
    (prodDesign D).E (fun w => g (w i) * hfun (w j))
      = (D i).E g * (D j).E hfun := by
  rw [E_prod_block_mul D {i} (fun w => g (w i)) (fun w => hfun (w j))]
  · rw [E_prod_apply D i g, E_prod_apply D j hfun]
  · intro w w' hw
    exact congrArg g (hw i (by simp))
  · intro w w' hw
    exact congrArg hfun (hw j (by simpa using h.symm))

/-- Single-coordinate variance: under the product design, the variance of a function of one
coordinate equals the variance of that function under the coordinate's own design. -/
lemma Var_prod_apply (D : ∀ i, FiniteDesign (α i)) (j : ι) (g : α j → ℝ) :
    (prodDesign D).Var (fun w => g (w j)) = (D j).Var g := by
  rw [Var_eq, Var_eq]
  congr 1
  · -- E[(g (w j))^2] = (D j).E (fun a => g a ^ 2)
    have : (fun w : ∀ i, α i => g (w j) ^ 2) = (fun w => (fun a => g a ^ 2) (w j)) := rfl
    rw [this, E_prod_apply D j (fun a => g a ^ 2)]
  · -- (prodDesign D).E (fun w => g (w j)) = (D j).E g
    rw [E_prod_apply D j g]

/-- Cross-coordinate independence: under the product design, functions of two distinct
coordinates have zero covariance. -/
lemma Cov_prod_apply_of_ne (D : ∀ i, FiniteDesign (α i)) {i j : ι} (h : i ≠ j)
    (g : α i → ℝ) (hfun : α j → ℝ) :
    (prodDesign D).Cov (fun w => g (w i)) (fun w => hfun (w j)) = 0 := by
  rw [Cov_eq]
  rw [show (fun w : ∀ i, α i => g (w i) * hfun (w j))
        = (fun w => g (w i) * hfun (w j)) from rfl,
      E_prod_apply₂ D h g hfun, E_prod_apply D i g, E_prod_apply D j hfun]
  ring

/-- **The payload.** Under the product design, the variance of a linear combination of
single-coordinate functions is the sum of the squared coefficients times the coordinate
variances — cross-coordinate covariances vanish. -/
lemma Var_prod_linear_comb (D : ∀ i, FiniteDesign (α i)) (c : ι → ℝ) (g : ∀ i, α i → ℝ) :
    (prodDesign D).Var (fun w => ∑ i, c i * g i (w i))
      = ∑ i, (c i) ^ 2 * (D i).Var (g i) := by
  rw [(prodDesign D).Var_linear_comb univ c (fun i w => g i (w i))]
  apply Finset.sum_congr rfl
  intro i _
  -- The inner sum over `j` collapses to the diagonal `j = i`.
  rw [Finset.sum_eq_single i]
  · -- diagonal term
    rw [Cov_self, Var_prod_apply]
    ring
  · -- off-diagonal terms vanish
    intro j _ hji
    rw [Cov_prod_apply_of_ne D (Ne.symm hji) (g i) (g j)]
    ring
  · intro hi; exact absurd (Finset.mem_univ i) hi

end FiniteDesign

end DesignBased
end Experimentation
end Causalean
