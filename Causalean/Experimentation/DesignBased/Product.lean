/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Product of finite randomization designs

Given a finite family of independent designs `D i : FiniteDesign (α i)` — one per index
`i` (here: one per group in a partial-interference experiment) — their **product design**
`prodDesign D` randomizes every coordinate independently:

    (prodDesign D).p w = ∏ i, (D i).p (w i).

This is the substrate form of **partial interference**: assembling the within-group
randomizations into a product makes cross-group independence a structural fact, not an
assumption.  The key consequences are `E_prod_prod` (the expectation of a product of
single-coordinate functions factors into the product of coordinate expectations) and
`E_prod_apply` (a function of one coordinate has the marginal expectation of that
coordinate's design).
-/

import Causalean.Experimentation.DesignBased.DesignCore
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Product finite randomization designs

This file constructs `prodDesign`, the finite product of a family of independent randomization
designs.  Its probability mass function is the product of the coordinate probabilities, recorded by
`prodDesign_p`.

The main expectation identities are `FiniteDesign.E_prod_prod`, which factors expectations of
products of coordinate functions, and `FiniteDesign.E_prod_apply`, which says a statistic depending
on one coordinate has the expectation induced by that coordinate's marginal design. -/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : ι → Type*} [∀ i, Fintype (α i)]

/-- The **product design** of a finite family `D i : FiniteDesign (α i)`: each coordinate is
randomized independently, with joint pmf `w ↦ ∏ i, (D i).p (w i)`. -/
def prodDesign (D : ∀ i, FiniteDesign (α i)) : FiniteDesign (∀ i, α i) where
  p w := ∏ i, (D i).p (w i)
  p_nonneg w := Finset.prod_nonneg (fun i _ => (D i).p_nonneg (w i))
  p_sum := by
    rw [show (∑ w : ∀ i, α i, ∏ i, (D i).p (w i)) = ∏ i, ∑ a : α i, (D i).p a from by
          rw [Finset.prod_univ_sum]; rw [Fintype.piFinset_univ]]
    simp only [FiniteDesign.p_sum, Finset.prod_const_one]

/-- The assignment probability in a product design is the product of the coordinate
probabilities. -/
@[simp] lemma prodDesign_p (D : ∀ i, FiniteDesign (α i)) (w : ∀ i, α i) :
    (prodDesign D).p w = ∏ i, (D i).p (w i) := rfl

namespace FiniteDesign

/-- The expectation under the product design of a product of single-coordinate functions
factors into the product of the coordinate expectations. -/
lemma E_prod_prod (D : ∀ i, FiniteDesign (α i)) (g : ∀ i, α i → ℝ) :
    (prodDesign D).E (fun w => ∏ i, g i (w i)) = ∏ i, (D i).E (g i) := by
  simp only [FiniteDesign.E, prodDesign_p]
  rw [show (∑ w : ∀ i, α i, (∏ i, (D i).p (w i)) * ∏ i, g i (w i))
        = ∑ w : ∀ i, α i, ∏ i, ((D i).p (w i) * g i (w i)) from
        Finset.sum_congr rfl (fun w _ => by rw [Finset.prod_mul_distrib])]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- A function of a single coordinate has the marginal expectation of that coordinate's
design under the product design. -/
lemma E_prod_apply (D : ∀ i, FiniteDesign (α i)) (j : ι) (g : α j → ℝ) :
    (prodDesign D).E (fun w => g (w j)) = (D j).E g := by
  have hg : (fun w : ∀ i, α i => g (w j))
      = (fun w => ∏ i, (fun (i : ι) (a : α i) => if h : i = j then g (h ▸ a) else 1) i (w i)) := by
    funext w
    simp only
    rw [Finset.prod_dite_eq' univ j (fun i h => g (h ▸ w i))]
    simp
  rw [hg, E_prod_prod D (fun (i : ι) (a : α i) => if h : i = j then g (h ▸ a) else 1)]
  rw [Finset.prod_eq_single j]
  · congr 1
    funext a
    simp
  · intro i _ hij
    have hF : (fun a : α i => (if h : i = j then g (h ▸ a) else (1 : ℝ))) = (fun _ => 1) := by
      funext a; rw [dif_neg hij]
    simp only at hF ⊢
    rw [hF, (D i).E_const]
  · intro h; exact absurd (Finset.mem_univ j) h

end FiniteDesign

end DesignBased
end Experimentation
end Causalean
