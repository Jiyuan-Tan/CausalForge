/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Relabeling a product design by a coordinate permutation

This file records a single, reusable algebraic fact about the product of a finite family of
identical-coordinate-type randomization designs: permuting the coordinate index by a bijection
`σ : ι ≃ ι` relabels the product design.  Concretely, the probability that a permuted predicate
holds under the original product design equals the probability that the predicate holds under the
permuted product design.

The statement is purely a finite-sum reindexing — no measure theory — and is the clean kernel used
by the Liu–Hudgens identical-groups derivation to show that the conditional studentized CDF depends
on a stage-1 selection only through the number of selected groups.
-/

import Causalean.Experimentation.DesignBased.Product

/-! # Reindexing product designs

Permuting coordinate labels only relabels probabilities under a product design.

The theorem `FiniteDesign.prodDesign_Pr_reindex` is a finite-sum reindexing identity: for a
coordinate permutation `sigma`, the probability of a permuted predicate under `prodDesign D`
equals the probability of the original predicate under the correspondingly permuted product
design.  It is used to express selection symmetry in identical-group two-stage arguments without
invoking measure theory.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace DesignBased
namespace FiniteDesign

/-- **Relabeling a product design by a coordinate permutation.** For a family of designs `D` over a
common coordinate space `W`, indexed by `ι`, and a permutation `σ : ι ≃ ι`, the probability under
`prodDesign D` of the predicate `w ↦ P (w ∘ σ)` equals the probability under the permuted product
`prodDesign (D ∘ σ)` of `P`.  Pure finite-sum reindexing: precomposition by `σ` is a bijection of
the assignment space `ι → W`, and the product pmf reindexes term-by-term. -/
theorem prodDesign_Pr_reindex {ι : Type*} [Fintype ι] [DecidableEq ι] {W : Type*} [Fintype W]
    (σ : ι ≃ ι) (D : ι → FiniteDesign W) (P : (ι → W) → Prop) [DecidablePred P] :
    (prodDesign D).Pr (fun w => P (fun i => w (σ i)))
      = (prodDesign (fun i => D (σ i))).Pr P := by
  classical
  -- Precomposition by `σ.symm` is a bijection on the assignment space `ι → W`; it carries the
  -- permuted predicate back to the plain predicate.
  let e : (ι → W) ≃ (ι → W) := Equiv.arrowCongr σ (Equiv.refl W)
  have he : ∀ (w : ι → W) (i : ι), e w i = w (σ.symm i) := by
    intro w i; simp [e, Equiv.arrowCongr]
  -- Unfold `Pr`/`E`/`ind` to a finite sum over the assignment space and reindex by `e`.
  simp only [Pr, E, ind, prodDesign_p]
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  -- The predicate argument `fun i => (e w) (σ i)` equals `w`, and the probability product
  -- reindexes coordinate-by-coordinate.
  have hpred : (fun i => e w (σ i)) = w := by
    funext i; rw [he w (σ i), σ.symm_apply_apply]
  have hprob : (∏ i, (D i).p (e w i)) = ∏ i, (D (σ i)).p (w i) := by
    rw [← Equiv.prod_comp σ (fun i => (D i).p (e w i))]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [he w (σ i), σ.symm_apply_apply]
  rw [hprob]
  simp only [hpred]

end FiniteDesign
end DesignBased
end Experimentation
end Causalean
