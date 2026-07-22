/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.Do.SemiGraphoid

/-! # Full Conditional Independence

This file defines conditional independence on the full random state of a structural
causal model, including both observed variables and latent variables. It also
develops the semi-graphoid rules needed before projecting full-distribution Markov
statements down to observational distributions.
-/

namespace Causalean

open scoped MeasureTheory ProbabilityTheory

namespace SCM

universe uN uΩ

variable {N : Type uN} [DecidableEq N] [Fintype N]
variable {Ω : N → Type uΩ} [∀ n, MeasurableSpace (Ω n)]

-- ============================================================
-- § 1. Definition
-- ============================================================

/-- **Full conditional independence** on `RandomValues M` (= `V ∪ L`).

    Analogous to `ObsCondIndep` but operates on the full joint distribution
    `jointKernel M s` rather than the observational distribution `obsKernel M s`.
    The full distribution includes latent nodes, so we can condition on ALL
    parents (including latent ones).

    Used in the full local Markov property, which is the base for the
    observational global Markov via projection. -/
def FullCondIndep (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    (X Y Z : Finset (SWIGNode N))
    (hX : X ⊆ M.randomVars) (hY : Y ⊆ M.randomVars)
    (hZ : Z ⊆ M.randomVars)
    (μ : MeasureTheory.Measure M.RandomValues)
    [MeasureTheory.IsFiniteMeasure μ] : Prop :=
  ProbabilityTheory.CondIndepFun
    (MeasurableSpace.comap (valuesProjection hZ) inferInstance)
    (comap_valuesProjection_le hZ)
    (valuesProjection hX)
    (valuesProjection hY)
    μ

-- ============================================================
-- § 2. Semi-graphoid axioms for FullCondIndep
-- ============================================================

/-- Symmetry for FullCondIndep. -/
theorem fullCondIndep_symm (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    {X Y Z : Finset (SWIGNode N)}
    (hX : X ⊆ M.randomVars) (hY : Y ⊆ M.randomVars) (hZ : Z ⊆ M.randomVars)
    {μ : MeasureTheory.Measure M.RandomValues} [MeasureTheory.IsFiniteMeasure μ]
    (h : FullCondIndep M X Y Z hX hY hZ μ) :
    FullCondIndep M Y X Z hY hX hZ μ := by
  unfold FullCondIndep at h ⊢
  exact condIndep_valuesProjection_symm hX hY hZ h

/-- Subset right for FullCondIndep. -/
theorem fullCondIndep_subset_right (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    {X Y Y' Z : Finset (SWIGNode N)}
    (hX : X ⊆ M.randomVars) (hY : Y ⊆ M.randomVars) (hY' : Y' ⊆ M.randomVars)
    (hZ : Z ⊆ M.randomVars)
    (hY'Y : Y' ⊆ Y)
    {μ : MeasureTheory.Measure M.RandomValues} [MeasureTheory.IsFiniteMeasure μ]
    (h : FullCondIndep M X Y Z hX hY hZ μ) :
    FullCondIndep M X Y' Z hX hY' hZ μ := by
  unfold FullCondIndep at h ⊢
  exact condIndep_valuesProjection_subset_right hX hY hY' hZ hY'Y h

/-- Decomposition for FullCondIndep. -/
theorem fullCondIndep_decomposition (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    {X Y W Z : Finset (SWIGNode N)}
    (hX : X ⊆ M.randomVars) (hYW : (Y ∪ W) ⊆ M.randomVars)
    (hY : Y ⊆ M.randomVars) (hZ : Z ⊆ M.randomVars)
    {μ : MeasureTheory.Measure M.RandomValues} [MeasureTheory.IsFiniteMeasure μ]
    (h : FullCondIndep M X (Y ∪ W) Z hX hYW hZ μ) :
    FullCondIndep M X Y Z hX hY hZ μ := by
  unfold FullCondIndep at h ⊢
  exact condIndep_valuesProjection_decomposition hX hYW hY hZ h

/-- Weak union for FullCondIndep. -/
theorem fullCondIndep_weak_union (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    {X Y W Z : Finset (SWIGNode N)}
    (hX : X ⊆ M.randomVars) (hYW : (Y ∪ W) ⊆ M.randomVars)
    (hY : Y ⊆ M.randomVars) (hZ : Z ⊆ M.randomVars)
    (hZW : (Z ∪ W) ⊆ M.randomVars)
    {μ : MeasureTheory.Measure M.RandomValues} [MeasureTheory.IsFiniteMeasure μ]
    (h : FullCondIndep M X (Y ∪ W) Z hX hYW hZ μ) :
    FullCondIndep M X Y (Z ∪ W) hX hY hZW μ := by
  unfold FullCondIndep at h ⊢
  exact condIndep_valuesProjection_weak_union_axiom hX hYW hY hZ hZW h

/-- Contraction for FullCondIndep. -/
theorem fullCondIndep_contraction (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    {X Y W Z : Finset (SWIGNode N)}
    (hX : X ⊆ M.randomVars) (hY : Y ⊆ M.randomVars)
    (hW : W ⊆ M.randomVars) (hZ : Z ⊆ M.randomVars)
    (hYW : (Y ∪ W) ⊆ M.randomVars) (hZW : (Z ∪ W) ⊆ M.randomVars)
    {μ : MeasureTheory.Measure M.RandomValues} [MeasureTheory.IsFiniteMeasure μ]
    (h1 : FullCondIndep M X Y (Z ∪ W) hX hY hZW μ)
    (h2 : FullCondIndep M X W Z hX hW hZ μ) :
    FullCondIndep M X (Y ∪ W) Z hX hYW hZ μ := by
  unfold FullCondIndep at h1 h2 ⊢
  exact condIndep_valuesProjection_contraction_axiom hX hY hW hZ hYW hZW h1 h2

-- ============================================================
-- § 3. Congruence helper
-- ============================================================

/-- Transport `FullCondIndep` along a Finset equality in the first argument.
    Used in the Verma–Pearl induction to convert `{a} ∪ A'` to `insert a A'`. -/
theorem fullCondIndep_congr_left (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    {X X' Y Z : Finset (SWIGNode N)} (heq : X = X')
    {hX : X ⊆ M.randomVars} {hX' : X' ⊆ M.randomVars}
    {hY : Y ⊆ M.randomVars} {hZ : Z ⊆ M.randomVars}
    {μ : MeasureTheory.Measure M.RandomValues} [MeasureTheory.IsFiniteMeasure μ]
    (h : FullCondIndep M X Y Z hX hY hZ μ) :
    FullCondIndep M X' Y Z hX' hY hZ μ := by
  subst heq; exact h

/-- Transport `FullCondIndep` along a Finset equality in the conditioning set.
    Used to align an empty conditioning set with `parents v ∩ randomVars` when
    `v` is a latent root. -/
theorem fullCondIndep_congr_right (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    {X Y Z Z' : Finset (SWIGNode N)} (heq : Z = Z')
    {hX : X ⊆ M.randomVars} {hY : Y ⊆ M.randomVars}
    {hZ : Z ⊆ M.randomVars} {hZ' : Z' ⊆ M.randomVars}
    {μ : MeasureTheory.Measure M.RandomValues} [MeasureTheory.IsFiniteMeasure μ]
    (h : FullCondIndep M X Y Z hX hY hZ μ) :
    FullCondIndep M X Y Z' hX hY hZ' μ := by
  subst heq; exact h

/-- The empty source set is conditionally independent of anything: with `X = ∅`,
    the projection `valuesProjection ∅` is constant, so `FullCondIndep` holds
    trivially. Interprets the `nil` constructor of `OrderedLocalSG`. -/
theorem fullCondIndep_const_left (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    {Y Z : Finset (SWIGNode N)} (hY : Y ⊆ M.randomVars) (hZ : Z ⊆ M.randomVars)
    {μ : MeasureTheory.Measure M.RandomValues} [MeasureTheory.IsFiniteMeasure μ] :
    FullCondIndep M ∅ Y Z (Finset.empty_subset _) hY hZ μ := by
  unfold FullCondIndep
  let c : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω) :=
    fun w => absurd w.property (Finset.notMem_empty _)
  have hconst : valuesProjection (Ω := swigΩ Ω) (Finset.empty_subset M.randomVars)
      = fun _ => c := by
    funext ξ w; exact absurd w.property (Finset.notMem_empty _)
  rw [hconst]
  exact ProbabilityTheory.condIndepFun_const_left c (valuesProjection hY)

end SCM

end Causalean
