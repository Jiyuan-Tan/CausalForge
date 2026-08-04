/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# A scale-free local-dependence variance bound

A design-based interference argument routinely has to bound the variance of a sum `∑ᵢ Fᵢ` of
unit-level terms that are *not* independent, because each term reads the treatments of a small
neighbourhood of units and neighbourhoods overlap.  This file records the sharpest elementary bound
of that kind on a Bernoulli assignment: if every term has mean zero and depends only on its own
block of units, and no single unit belongs to more than `d` blocks, then

    E[(∑ᵢ Fᵢ)²] ≤ d · ∑ᵢ E[Fᵢ²].

The proof goes through the centered-monomial (Walsh/Fourier) expansion of
`Designs/BernoulliMoments.lean`: locality confines each term's coefficients to the subsets of its
own block, so at most `d` terms can contribute to any one basis direction, and Cauchy–Schwarz on
each direction plus Parseval gives the bound.

The interest of the statement is what it does *not* assume: no uniform bound on the terms, no
explicit decorrelation hypothesis (locality supplies it), and no dependence on the population size.
Contrast `Experimentation/DesignBased/EdgeVarianceBound.lean`'s `var_edge_sum_le`, which is indexed
by the edges of a dependency graph, needs a uniform pointwise bound on the summands, takes
decorrelation as a hypothesis, and pays a population-size factor.
-/

import Causalean.Experimentation.DesignBased.Designs.BernoulliMoments
import Mathlib.Algebra.Order.Chebyshev

/-! # Local-dependence variance bound on a Bernoulli design

This file provides `BlockDegreeLE`, the condition that no unit lies in more than `d` of the
dependence blocks, and `bernoulliDesign_E_sum_sq_le_blockDegree_mul_sum_sq`, the resulting bound
`E[(∑ᵢ Fᵢ)²] ≤ d · ∑ᵢ E[Fᵢ²]` for mean-zero, block-dependent summands. -/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- A family of dependence blocks has **degree at most `d`** if no single unit's treatment is read
by more than `d` of the blocks.  When the blocks are the in-neighbourhoods of a dependency graph
this is the bound on out-degree. -/
def BlockDegreeLE (N : U → Finset U) (d : ℕ) : Prop :=
  ∀ j : U, (Finset.univ.filter fun i => j ∈ N i).card ≤ d

/-- **Local-dependence variance bound.** Suppose each unit contributes a term that has mean zero
under the Bernoulli design and depends only on the treatments of its own block of units, and
suppose no unit's treatment is read by more than `d` blocks.  Then the second moment of the total
is at most `d` times the total of the individual second moments.  The bound is scale free: it needs
no uniform bound on the terms, no explicit decorrelation assumption, and no dependence on the
population size. -/
theorem bernoulliDesign_E_sum_sq_le_blockDegree_mul_sum_sq (p : U → ℝ) (hp0 : ∀ i, 0 < p i)
    (hp1 : ∀ i, p i < 1) (N : U → Finset U) (d : ℕ) (hdeg : BlockDegreeLE N d)
    (F : U → (U → Bool) → ℝ)
    (hmean : ∀ i, (bernoulliDesign p (fun k => (hp0 k).le) (fun k => (hp1 k).le)).E (F i) = 0)
    (hdep : ∀ i, DependsOnBlock (N i) (F i)) :
    (bernoulliDesign p (fun k => (hp0 k).le) (fun k => (hp1 k).le)).E
        (fun z => (∑ i, F i z) ^ 2) ≤
      (d : ℝ) * ∑ i, (bernoulliDesign p (fun k => (hp0 k).le) (fun k => (hp1 k).le)).E
        (fun z => F i z ^ 2) := by
  classical
  have hp0' : ∀ i, 0 ≤ p i := fun i => (hp0 i).le
  have hp1' : ∀ i, p i ≤ 1 := fun i => (hp1 i).le
  set v : Finset U → ℝ := fun S => ∏ j ∈ S, p j * (1 - p j) with hv
  have hv0 (S : Finset U) : 0 ≤ v S :=
    Finset.prod_nonneg fun j _ => mul_nonneg (hp0 j).le (sub_pos.mpr (hp1 j)).le
  choose a ha using fun i => exists_centeredMonomial_expansion (U := U) p (F i)
  have ha0 (i : U) : a i ∅ = 0 :=
    centeredMonomial_coef_empty_eq_zero p hp0' hp1' (F i) (a i) (ha i) (hmean i)
  -- The units whose block can carry the basis direction `S`.
  set I : Finset U → Finset U := fun S => Finset.univ.filter fun i => S ⊆ N i with hI
  have hcardI (S : Finset U) (hSne : S.Nonempty) : (I S).card ≤ d := by
    obtain ⟨j, hjS⟩ := hSne
    refine (Finset.card_le_card ?_).trans (hdeg j)
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2 hjS⟩
  have hsumI (S : Finset U) (hS : S ∈ (Finset.univ : Finset U).powerset) :
      (∑ i, a i S) = ∑ i ∈ I S, a i S := by
    symm
    refine Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _) (fun i hi => ?_) (fun _ _ => rfl)
    exact centeredMonomial_coef_eq_zero_of_not_subset p hp0' hp1' (N i) (F i) (hdep i) (a i)
      (ha i) S (by simpa [hI] using (Finset.mem_sdiff.mp hi).2)
      (fun j _ => hp0 j) (fun j _ => hp1 j)
  set A : Finset U → ℝ := fun S => ∑ i, a i S with hA
  have hsumExpansion (z : U → Bool) :
      (∑ i, F i z) =
        ∑ S ∈ (Finset.univ : Finset U).powerset, A S * centeredMonomial p S z := by
    simp_rw [ha]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun S _ => by rw [hA, Finset.sum_mul]
  rw [bernoulliDesign_E_sq_of_expansion p hp0' hp1' (fun z => ∑ i, F i z) A hsumExpansion]
  calc
    (∑ S ∈ (Finset.univ : Finset U).powerset, A S ^ 2 * v S) ≤
        ∑ S ∈ (Finset.univ : Finset U).powerset, (d : ℝ) * (∑ i, a i S ^ 2) * v S := by
      refine Finset.sum_le_sum fun S hS => ?_
      by_cases hSne : S.Nonempty
      · have hcardR : ((I S).card : ℝ) ≤ d := by exact_mod_cast hcardI S hSne
        have hsquares : (0 : ℝ) ≤ ∑ i ∈ I S, a i S ^ 2 := by positivity
        have hCS' : A S ^ 2 ≤ (d : ℝ) * ∑ i, a i S ^ 2 := by
          rw [show A S = ∑ i ∈ I S, a i S from hsumI S hS]
          calc
            (∑ i ∈ I S, a i S) ^ 2 ≤ ((I S).card : ℝ) * ∑ i ∈ I S, a i S ^ 2 :=
              sq_sum_le_card_mul_sum_sq
            _ ≤ (d : ℝ) * ∑ i ∈ I S, a i S ^ 2 := mul_le_mul_of_nonneg_right hcardR hsquares
            _ ≤ (d : ℝ) * ∑ i, a i S ^ 2 := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                fun _ _ _ => sq_nonneg _
        exact mul_le_mul_of_nonneg_right hCS' (hv0 S)
      · have hSe : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
        subst hSe
        simp [hA, ha0]
    _ = (d : ℝ) * ∑ i, ∑ S ∈ (Finset.univ : Finset U).powerset, a i S ^ 2 * v S := by
      rw [show (∑ S ∈ (Finset.univ : Finset U).powerset, (d : ℝ) * (∑ i, a i S ^ 2) * v S) =
          ∑ S ∈ (Finset.univ : Finset U).powerset, ∑ i, (d : ℝ) * a i S ^ 2 * v S from
        Finset.sum_congr rfl fun S _ => by rw [Finset.mul_sum, Finset.sum_mul]]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun S _ => by ring
    _ = _ := by
      refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
      exact (bernoulliDesign_E_sq_of_expansion p hp0' hp1' (F i) (a i) (ha i)).symm

end DesignBased
end Experimentation
end Causalean
