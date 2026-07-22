/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bridge: a product design's measure IS Mathlib's product measure

The measure induced by a product design is the product of the coordinate measures, so functions
of disjoint coordinates are probabilistically independent — the bridge that lets the
dependency-graph CLT see cross-group independence as genuine measure-theoretic independence.

Concretely, for a finite family of independent designs `D i : FiniteDesign (α i)`, the measure
`(prodDesign D).toMeasure` of the assembled product design coincides with Mathlib's product
measure `Measure.pi (fun i => (D i).toMeasure)` (`prodDesign_toMeasure_eq_pi`).  Pushing this
through Mathlib's independence-of-coordinates-under-a-product-measure machinery
(`iIndepFun_pi`, `iIndepFun.indepFun`, `iIndepFun.indepFun_finset`) yields the two facts a
diagonal dependency graph consumes: distinct coordinate evaluations are `IndepFun`
(`indepFun_prodDesign_eval`), and tuples of functions of two disjoint coordinate blocks are
`IndepFun` (`indepFun_prodDesign_blocks`, `indepFun_prodDesign_apply_blocks`).
-/

import Causalean.Experimentation.DesignBased.Product
import Causalean.Experimentation.DesignBased.FiniteDesignMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic

/-! # Product-design measures

The measure induced by a finite product design is Mathlib's product measure.

`prodDesign_toMeasure_eq_pi` identifies `(prodDesign D).toMeasure` with
`Measure.pi (fun i => (D i).toMeasure)`, using `FiniteDesign.toMeasure_singleton` to compare
singleton masses.  The independence results `iIndepFun_prodDesign_eval`,
`indepFun_prodDesign_eval`, `indepFun_prodDesign_blocks`, and
`indepFun_prodDesign_apply_blocks` then expose Mathlib's product-measure independence for
coordinate projections and disjoint coordinate blocks.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : ι → Type*} [∀ i, Fintype (α i)]
variable [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]

namespace FiniteDesign

/-- The design measure of a singleton equals that singleton's design probability:
`(D i).toMeasure {a} = (D i).p a`.  (The dirac sum collapses to the single term `z = a`.) -/
lemma toMeasure_singleton {β : Type*} [Fintype β] [MeasurableSpace β]
    [MeasurableSingletonClass β] (D : FiniteDesign β) (a : β) :
    D.toMeasure {a} = ENNReal.ofReal (D.p a) := by
  rw [toMeasure, Measure.finset_sum_apply]
  rw [Finset.sum_eq_single a]
  · rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' a (measurableSet_singleton a)]
    simp
  · intro z _ hz
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' z (measurableSet_singleton a),
      Set.indicator_of_notMem (by simpa using hz)]
    simp
  · intro h; exact absurd (Finset.mem_univ a) h

end FiniteDesign

/-- **The product design IS Mathlib's product measure.**  The measure induced by the product
design `prodDesign D` coincides with the Mathlib product measure of the coordinate design
measures: `(prodDesign D).toMeasure = Measure.pi (fun i => (D i).toMeasure)`.  Both are finite
measures on the Fintype `∀ i, α i`, so they agree iff they agree on every singleton `{w}`; on a
singleton both sides evaluate to `∏ i, (D i).p (w i)`. -/
theorem prodDesign_toMeasure_eq_pi (D : ∀ i, FiniteDesign (α i)) :
    (prodDesign D).toMeasure = Measure.pi (fun i => (D i).toMeasure) := by
  refine Measure.ext_of_singleton (fun w => ?_)
  -- LHS: the product-design measure of `{w}` is `∏ i, (D i).p (w i)`.
  rw [FiniteDesign.toMeasure_singleton (prodDesign D) w, prodDesign_p,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => (D i).p_nonneg (w i))]
  -- RHS: `{w} = Set.univ.pi (fun i => {w i})`, so `Measure.pi … {w} = ∏ i, (D i).toMeasure {w i}`.
  have hsingleton : ({w} : Set (∀ i, α i)) = Set.univ.pi (fun i => {w i}) := by
    ext x; simp [funext_iff]
  rw [hsingleton, Measure.pi_pi]
  exact Finset.prod_congr rfl (fun i _ => (FiniteDesign.toMeasure_singleton (D i) (w i)).symm)

/-- Coordinate evaluations are mutually independent under the product-design measure: viewing
`fun (i) (w) => w i` as the family of coordinate projections, this family is `iIndepFun` under
`(prodDesign D).toMeasure`.  (The push-forward of `iIndepFun_pi` along
`prodDesign_toMeasure_eq_pi`.) -/
lemma iIndepFun_prodDesign_eval (D : ∀ i, FiniteDesign (α i)) :
    iIndepFun (fun (i : ι) (w : ∀ j, α j) => w i) (prodDesign D).toMeasure := by
  rw [prodDesign_toMeasure_eq_pi]
  exact iIndepFun_pi (X := fun _ => id) (fun i => aemeasurable_id)

/-- For `i ≠ j`, the two coordinate evaluations `w ↦ w i` and `w ↦ w j` are independent under the
product-design measure. -/
theorem indepFun_prodDesign_eval (D : ∀ i, FiniteDesign (α i)) {i j : ι} (hij : i ≠ j) :
    IndepFun (fun w : ∀ k, α k => w i) (fun w => w j) (prodDesign D).toMeasure :=
  (iIndepFun_prodDesign_eval D).indepFun hij

/-- **Disjoint-block independence.**  For disjoint finite index sets `A B : Finset ι`, the tuple of
coordinates indexed by `A` is independent of the tuple indexed by `B`, under the product-design
measure.  This is the form a diagonal dependency graph `G a b := a = b` consumes. -/
theorem indepFun_prodDesign_blocks (D : ∀ i, FiniteDesign (α i)) {A B : Finset ι}
    (hAB : Disjoint A B) :
    IndepFun (fun (w : ∀ k, α k) (k : A) => w k) (fun w (k : B) => w k)
      (prodDesign D).toMeasure :=
  (iIndepFun_prodDesign_eval D).indepFun_finset A B hAB
    (fun i => measurable_pi_apply i)

/-- **Functions of disjoint coordinate blocks are independent.**  Composing
`indepFun_prodDesign_blocks` with a measurable family `g i : α i → ℝ`: the tuple
`(g k (w k))_{k ∈ A}` is independent of `(g k (w k))_{k ∈ B}` whenever `A` and `B` are disjoint,
under the product-design measure. -/
theorem indepFun_prodDesign_apply_blocks (D : ∀ i, FiniteDesign (α i))
    {g : ∀ i, α i → ℝ} (hg : ∀ i, Measurable (g i)) {A B : Finset ι} (hAB : Disjoint A B) :
    IndepFun (fun (w : ∀ k, α k) (k : A) => g k (w k))
      (fun w (k : B) => g k (w k)) (prodDesign D).toMeasure :=
  (indepFun_prodDesign_blocks D hAB).comp
    (φ := fun (v : ∀ k : A, α k) (k : A) => g k (v k))
    (ψ := fun (v : ∀ k : B, α k) (k : B) => g k (v k))
    (by fun_prop) (by fun_prop)

/-- **General functions of disjoint coordinate blocks are independent.**  The strict generalization
of `indepFun_prodDesign_apply_blocks` from coordinatewise-separable maps `(g k (w k))_k` to
*arbitrary* measurable functions that each depend only on a block: if `F` is unchanged by any
assignment that agrees on `S`, and `G` is unchanged by any assignment that agrees on the disjoint
set `T`, then `F` and `G` are independent under the product-design measure.  This is the hypothesis
a dependency-graph construction actually consumes, where each summand depends jointly (not
coordinatewise) on a neighbourhood block. -/
theorem indepFun_prodDesign_of_depends_on_disjoint_blocks
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (D : ∀ i, FiniteDesign (α i)) {S T : Finset ι} (hST : Disjoint S T)
    (F : (∀ i, α i) → β) (G : (∀ i, α i) → γ)
    (hF : ∀ w w' : ∀ i, α i, (∀ i ∈ S, w i = w' i) → F w = F w')
    (hG : ∀ w w' : ∀ i, α i, (∀ i ∈ T, w i = w' i) → G w = G w') :
    IndepFun F G (prodDesign D).toMeasure := by
  classical
  have hne : ∀ i, Nonempty (α i) := by
    intro i
    by_contra h
    rw [not_nonempty_iff] at h
    have := (D i).p_sum
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    exact one_ne_zero this.symm
  let x₀ : ∀ i, α i := fun i => (hne i).some
  let F₀ : (∀ k : (S : Finset ι), α k) → β :=
    fun a => F (fun i => if h : i ∈ S then a ⟨i, h⟩ else x₀ i)
  let G₀ : (∀ k : (T : Finset ι), α k) → γ :=
    fun b => G (fun i => if h : i ∈ T then b ⟨i, h⟩ else x₀ i)
  have hF₀ : ∀ w, F w = F₀ (fun k : (S : Finset ι) => w k) := by
    intro w
    refine hF _ _ (fun i hi => ?_)
    simp [hi]
  have hG₀ : ∀ w, G w = G₀ (fun k : (T : Finset ι) => w k) := by
    intro w
    refine hG _ _ (fun i hi => ?_)
    simp [hi]
  have hblk := (indepFun_prodDesign_blocks D hST).comp
    (φ := F₀) (ψ := G₀) (measurable_of_finite F₀) (measurable_of_finite G₀)
  exact hblk.congr
    (Filter.Eventually.of_forall fun w => (hF₀ w).symm)
    (Filter.Eventually.of_forall fun w => (hG₀ w).symm)

end DesignBased
end Experimentation
end Causalean
