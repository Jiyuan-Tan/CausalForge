/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Disjoint-block independence of the product design

Functions of **disjoint coordinate blocks** of a product design are uncorrelated.  This
generalizes the single-coordinate facts `E_prod_apply₂` / `Cov_prod_apply_of_ne` in
`ProductVariance.lean` from singleton coordinates to arbitrary disjoint index sets, and is the
substrate behind both Horvitz–Thompson unbiasedness (`Z_i` vs. a function of the other
coordinates — block `{i}` vs. its complement) and the Sävje–Aronow–Hudgens variance bound
(two HT summands with disjoint interferer supports).

The payload is `E_prod_block_mul`: if `f` depends only on the coordinates in `A` and `g` only on
the coordinates outside `A`, then `E[f·g] = E[f]·E[g]` under the product design.  Two corollaries
package this as a vanishing covariance: `Cov_prod_block_zero` (complement split) and
`Cov_prod_disjoint_zero` (arbitrary disjoint blocks).
-/

import Causalean.Experimentation.DesignBased.Product
import Causalean.Experimentation.DesignBased.ProductMeasure
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Probability.Independence.Integration

/-! # Disjoint-block independence for product designs

Functions of disjoint coordinate blocks factor under a finite product design.

The theorem `FiniteDesign.E_prod_block_mul` factors the expectation of `f * g` when `f` depends
only on coordinates in a block `A` and `g` depends only on the complement.  The covariance
corollaries `FiniteDesign.Cov_prod_block_zero` and `FiniteDesign.Cov_prod_disjoint_zero` package
that independence for complement blocks and for arbitrary disjoint blocks.
-/

open scoped BigOperators
open Finset
open MeasureTheory ProbabilityTheory

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : ι → Type*} [∀ i, Fintype (α i)]

namespace FiniteDesign

/-- **Disjoint-block factorization of expectation.** If `f` depends only on the coordinates in the
block `A` (it is invariant under changes to coordinates outside `A`) and `g` depends only on the
coordinates outside `A`, then under the product design their product's expectation factors:
`E[f·g] = E[f]·E[g]`.  The general (block-level) form of `E_prod_apply₂`. -/
theorem E_prod_block_mul (D : ∀ i, FiniteDesign (α i)) (A : Finset ι)
    (f g : (∀ i, α i) → ℝ)
    (hf : ∀ w w' : ∀ i, α i, (∀ i ∈ A, w i = w' i) → f w = f w')
    (hg : ∀ w w' : ∀ i, α i, (∀ i ∉ A, w i = w' i) → g w = g w') :
    (prodDesign D).E (fun w => f w * g w)
      = (prodDesign D).E f * (prodDesign D).E g := by
  classical
  letI : (i : ι) → MeasurableSpace (α i) := fun _ => ⊤
  haveI : (i : ι) → MeasurableSingletonClass (α i) := fun _ => inferInstance
  -- Each coordinate type is nonempty: its design probabilities sum to `1 ≠ 0`.
  have hne : ∀ i, Nonempty (α i) := by
    intro i
    by_contra h
    rw [not_nonempty_iff] at h
    have := (D i).p_sum
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    exact one_ne_zero this.symm
  -- A global reference point used to fill in the coordinates we drop.
  let x₀ : ∀ i, α i := fun i => (hne i).some
  -- Factor `f` through the `A`-block restriction and `g` through the `Aᶜ`-block restriction.
  let F : (∀ k : (A : Finset ι), α k) → ℝ :=
    fun a => f (fun i => if h : i ∈ A then a ⟨i, h⟩ else x₀ i)
  let G : (∀ k : ((Aᶜ : Finset ι) : Finset ι), α k) → ℝ :=
    fun b => g (fun i => if h : i ∈ (Aᶜ : Finset ι) then b ⟨i, h⟩ else x₀ i)
  have hfF : ∀ w, f w = F (fun k : (A : Finset ι) => w k) := by
    intro w
    refine hf _ _ (fun i hi => ?_)
    simp [hi]
  have hgG : ∀ w, g w = G (fun k : ((Aᶜ : Finset ι) : Finset ι) => w k) := by
    intro w
    refine hg _ _ (fun i hi => ?_)
    have hi' : i ∈ (Aᶜ : Finset ι) := by simpa using hi
    simp [hi']
  -- Independence of the two disjoint coordinate blocks `A` and `Aᶜ`.
  have hindep :
      IndepFun (fun w : ∀ k, α k => f w) (fun w => g w) (prodDesign D).toMeasure := by
    have hdisj : Disjoint A (Aᶜ : Finset ι) := disjoint_compl_right
    have hblk := (indepFun_prodDesign_blocks D hdisj).comp
      (φ := F) (ψ := G) (measurable_of_finite F) (measurable_of_finite G)
    refine hblk.congr ?_ ?_
    · filter_upwards with w using (hfF w).symm
    · filter_upwards with w using (hgG w).symm
  -- Convert the design expectations to integrals and apply independence.
  rw [← integral_toMeasure, ← integral_toMeasure, ← integral_toMeasure]
  exact ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral hindep
    (measurable_of_finite f).aestronglyMeasurable
    (measurable_of_finite g).aestronglyMeasurable

/-- **Disjoint-block covariance vanishing (complement form).** If `f` depends only on the
coordinates in `A` and `g` only on the coordinates outside `A`, their covariance under the product
design is zero. -/
theorem Cov_prod_block_zero (D : ∀ i, FiniteDesign (α i)) (A : Finset ι)
    (f g : (∀ i, α i) → ℝ)
    (hf : ∀ w w' : ∀ i, α i, (∀ i ∈ A, w i = w' i) → f w = f w')
    (hg : ∀ w w' : ∀ i, α i, (∀ i ∉ A, w i = w' i) → g w = g w') :
    (prodDesign D).Cov f g = 0 := by
  rw [Cov_eq, E_prod_block_mul D A f g hf hg, sub_self]

/-- **Disjoint-block covariance vanishing (two-block form).** If `f` depends only on the
coordinates in `S` and `g` only on the coordinates in `T`, and `S` and `T` are disjoint, then their
covariance under the product design is zero. -/
theorem Cov_prod_disjoint_zero (D : ∀ i, FiniteDesign (α i)) (S T : Finset ι)
    (hST : Disjoint S T) (f g : (∀ i, α i) → ℝ)
    (hf : ∀ w w' : ∀ i, α i, (∀ i ∈ S, w i = w' i) → f w = f w')
    (hg : ∀ w w' : ∀ i, α i, (∀ i ∈ T, w i = w' i) → g w = g w') :
    (prodDesign D).Cov f g = 0 := by
  -- `g` depends only on `T ⊆ Sᶜ`, hence only on the coordinates outside `S`.
  refine Cov_prod_block_zero D S f g hf (fun w w' h => hg w w' (fun i hiT => ?_))
  exact h i (fun hiS => (Finset.disjoint_left.mp hST hiS) hiT)

end FiniteDesign

end DesignBased
end Experimentation
end Causalean
