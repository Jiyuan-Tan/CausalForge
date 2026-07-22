/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Compound (two-stage) randomization designs

A **compound design** models a two-stage randomization: a stage-1 design `D₁` on `Ω₁`
(e.g. which groups receive which allocation strategy), and then, conditionally on the
stage-1 outcome `s`, an independent within-coordinate design `D₂ s i` for each index `i`
(e.g. the within-group treatment randomization, whose distribution may depend on the strategy
group `i` was assigned).  The joint pmf is

    (compound D₁ D₂).p (s, w) = D₁.p s · ∏ i, (D₂ s i).p (w i).

The workhorse is `E_compound_factor`: the expectation of `h(s)·g(wⱼ)` — a stage-1 quantity
times a function of a single group's within-assignment — collapses the inner (stage-2)
randomization to the marginal expectation of group `j`'s conditional design,
`E[h(s)·g(wⱼ)] = E_{s}[h(s)·E_{D₂ s j}[g]]`.  This is the substrate engine behind the
Hudgens–Halloran unbiasedness theorems.
-/

import Causalean.Experimentation.DesignBased.Product

/-! # Two-stage compound randomization designs

Compound designs combine a stage-one design with conditionally independent stage-two designs.

The definition `compound` builds the joint finite design on `(stage_one, stage_two_assignments)`
from a first-stage design and conditionally independent coordinate designs.  Lemma
`FiniteDesign.E_compound` expands expectations as an iterated finite sum, and
`FiniteDesign.E_compound_factor` collapses the stage-two expectation of a statistic that depends on
one coordinate to that coordinate's conditional marginal expectation.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {Ω₁ : Type*} [Fintype Ω₁]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : ι → Type*} [∀ i, Fintype (α i)]

/-- The **compound (two-stage) design**: stage-1 design `D₁` on `Ω₁`, then, conditionally on
the stage-1 outcome `s`, the independent within-coordinate designs `D₂ s i`. -/
def compound (D₁ : FiniteDesign Ω₁) (D₂ : Ω₁ → ∀ i, FiniteDesign (α i)) :
    FiniteDesign (Ω₁ × ∀ i, α i) where
  p sw := D₁.p sw.1 * ∏ i, (D₂ sw.1 i).p (sw.2 i)
  p_nonneg sw :=
    mul_nonneg (D₁.p_nonneg sw.1)
      (Finset.prod_nonneg fun i _ => (D₂ sw.1 i).p_nonneg (sw.2 i))
  p_sum := by
    rw [Fintype.sum_prod_type]
    have hs : ∀ s, (∑ w : ∀ i, α i, D₁.p s * ∏ i, (D₂ s i).p (w i)) = D₁.p s := by
      intro s
      rw [← Finset.mul_sum,
        show (∑ w : ∀ i, α i, ∏ i, (D₂ s i).p (w i)) = 1 from (prodDesign (D₂ s)).p_sum, mul_one]
    rw [Finset.sum_congr rfl (fun s _ => hs s), D₁.p_sum]

namespace FiniteDesign

/-- Expand the compound expectation as the iterated stage-1/stage-2 sum. -/
lemma E_compound (D₁ : FiniteDesign Ω₁) (D₂ : Ω₁ → ∀ i, FiniteDesign (α i))
    (X : (Ω₁ × ∀ i, α i) → ℝ) :
    (compound D₁ D₂).E X
      = ∑ s, ∑ w : ∀ i, α i, D₁.p s * (∏ i, (D₂ s i).p (w i)) * X (s, w) := by
  simp only [FiniteDesign.E, compound]
  rw [Fintype.sum_prod_type]

/-- **Stage-2 collapse.** The expectation of a stage-1 quantity `h(s)` times a function `g`
of a single group's within-assignment `wⱼ` factors through the marginal expectation of group
`j`'s conditional design: `E[h(s)·g(wⱼ)] = E_s[h(s)·E_{D₂ s j}[g]]`. -/
lemma E_compound_factor (D₁ : FiniteDesign Ω₁) (D₂ : Ω₁ → ∀ i, FiniteDesign (α i))
    (h : Ω₁ → ℝ) (j : ι) (g : α j → ℝ) :
    (compound D₁ D₂).E (fun sw => h sw.1 * g (sw.2 j))
      = D₁.E (fun s => h s * (D₂ s j).E g) := by
  rw [E_compound]
  conv_rhs => rw [FiniteDesign.E]
  apply Finset.sum_congr rfl
  intro s _
  rw [show (∑ w : ∀ i, α i, D₁.p s * (∏ i, (D₂ s i).p (w i)) * (h s * g (w j)))
        = D₁.p s * h s * ((prodDesign (D₂ s)).E (fun w => g (w j))) from by
        rw [FiniteDesign.E, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        simp only [prodDesign_p]
        ring]
  rw [FiniteDesign.E_prod_apply]
  ring

end FiniteDesign

end DesignBased
end Experimentation
end Causalean
