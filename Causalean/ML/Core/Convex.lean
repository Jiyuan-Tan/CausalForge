/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Core.ERM
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact

/-! # Convex-analysis substrate for ERM

Reusable convexity, existence, first-order-optimality and subgradient facts that
the convex methods (logistic regression, lasso, generic convex ERM) instantiate.
This file is method-agnostic: it speaks only about an abstract objective on a
real vector / inner-product / normed space.
-/

namespace Causalean.ML

open MeasureTheory Filter

section Convexity
variable {ι Θ X Y : Type*} [Fintype ι] [Nonempty ι] [AddCommGroup Θ] [Module ℝ Θ]

/-- If every per-sample parameter loss is convex on `Θset`, so is the empirical
risk of the predictor. -/
theorem empiricalRiskP_convexOn_of_loss_convex
    (M : Predictor Θ X Y) (loss : Loss Y) (S : ι → X × Y) (Θset : Set Θ)
    (hconv : Convex ℝ Θset)
    (hloss : ∀ i, ConvexOn ℝ Θset (fun θ => loss (M.predict θ (S i).1) (S i).2)) :
    ConvexOn ℝ Θset (empiricalRiskP M loss S) := by
  unfold empiricalRiskP empiricalRisk
  have hsum : ConvexOn ℝ Θset (fun θ => ∑ i, loss (M.predict θ (S i).1) (S i).2) := by
    classical
    have hfin : ∀ t : Finset ι,
        ConvexOn ℝ Θset
          (fun θ => t.sum (fun i => loss (M.predict θ (S i).1) (S i).2)) := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
          simpa using
            (convexOn_const (𝕜 := ℝ) (E := Θ) (β := ℝ) (s := Θset) (0 : ℝ) hconv)
      | insert i t hi ht =>
          simpa [Finset.sum_insert hi, Pi.add_apply] using (hloss i).add ht
    simpa using hfin Finset.univ
  simpa [smul_eq_mul] using
    hsum.smul (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card ι)))

end Convexity

section CompLinear
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A convex scalar function precomposed with the linear score `θ ↦ ⟪θ, x⟫` is
convex.  This is the workhorse turning convexity of a margin loss into convexity
of the parameter objective. -/
theorem convexOn_comp_inner
    {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) (x : E) :
    ConvexOn ℝ Set.univ (fun θ : E => φ (inner ℝ θ x)) := by
  simpa [Function.comp_def, innerSL_apply_apply, real_inner_comm] using
    hφ.comp_linearMap ((innerSL ℝ x).toLinearMap)

end CompLinear

section Existence
variable {Θ : Type*} [TopologicalSpace Θ]

/-- Existence of a minimizer on a nonempty compact set (Weierstrass). -/
theorem exists_isMinOn_of_isCompact
    {objective : Θ → ℝ} {Θset : Set Θ}
    (hne : Θset.Nonempty) (hcompact : IsCompact Θset)
    (hcont : ContinuousOn objective Θset) :
    ∃ θhat ∈ Θset, IsMinOn objective Θset θhat := by
  exact hcompact.exists_isMinOn hne hcont

end Existence

section CoerciveExistence
variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/-- Existence of a global minimizer of a continuous coercive objective: if
`objective → ∞` along the cocompact filter, a global minimizer exists. -/
theorem exists_isMinOn_univ_of_coercive
    {objective : E → ℝ} (hcont : Continuous objective)
    (hcoer : Tendsto objective (cocompact E) atTop) :
    ∃ a, IsMinOn objective Set.univ a := by
  have _ : ProperSpace E := inferInstance
  obtain ⟨a, ha⟩ := hcont.exists_forall_le hcoer
  exact ⟨a, isMinOn_univ_iff.2 ha⟩

end CoerciveExistence

section FirstOrder
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- First-order optimality on the whole space: at an unconstrained minimizer the
Fréchet derivative vanishes. -/
theorem fderiv_eq_zero_of_isMinOn_univ
    {f : E → ℝ} {f' : E →L[ℝ] ℝ} {a : E}
    (hmin : IsMinOn f Set.univ a) (hderiv : HasFDerivAt f f' a) : f' = 0 := by
  exact (hmin.isLocalMin univ_mem).hasFDerivAt_eq_zero hderiv

end FirstOrder

section Subgradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `g` is a subgradient of `f` at `x` relative to `s`: the affine support
inequality `f x + ⟪g, y − x⟫ ≤ f y` holds for all `y ∈ s` (and `x ∈ s`). -/
def SubgradientAt (f : E → ℝ) (s : Set E) (g x : E) : Prop :=
  x ∈ s ∧ ∀ y ∈ s, f x + inner ℝ g (y - x) ≤ f y

/-- Fermat's rule, subgradient form: `0` is a subgradient at `x` over `s` iff `x`
minimizes `f` over `s`. -/
theorem subgradientAt_zero_iff_isMinOn
    {f : E → ℝ} {s : Set E} {x : E} (hx : x ∈ s) :
    SubgradientAt f s 0 x ↔ IsMinOn f s x := by
  constructor
  · intro h
    exact isMinOn_iff.2 fun y hy => by
      have := h.2 y hy
      simpa [SubgradientAt, inner_zero_left] using this
  · intro hmin
    refine ⟨hx, ?_⟩
    intro y hy
    simpa [SubgradientAt, inner_zero_left] using (isMinOn_iff.1 hmin y hy)

end Subgradient

end Causalean.ML
