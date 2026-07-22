/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Law of total variance for the two-stage compound design

The total variance of a random variable under the two-stage `compound` design equals the
expected within-stage (stage-2 conditional) variance plus the variance of the stage-2
conditional mean across the stage-1 randomization:

    Var X = E_{stage 1}[ Var_{stage 2}(X | s) ] + Var_{stage 1}( E_{stage 2}(X | s) ).

This is the design-based form of the law of total variance.  It underlies the
between-group / within-group variance decompositions of design-based inference under
partial interference (e.g. the Hudgens–Halloran between-group variance theorems), where
stage 1 randomizes the group-level allocation strategies and stage 2 randomizes the
within-group assignments.  The enabling step is the tower property of expectation
(`E_compound_tower`): the compound expectation iterates as a stage-1 expectation of the
stage-2 (product-design) conditional expectation.
-/

import Causalean.Experimentation.DesignBased.TwoStage

/-!
# Compound-design variance decomposition

This file proves the expectation tower property `FiniteDesign.E_compound_tower` for the two-stage
`compound` design and the corresponding law of total variance
`FiniteDesign.Var_compound_eq_tower`. The decomposition writes total variance as expected
within-stage variance plus the stage-1 variance of the stage-2 conditional mean, the algebraic form
used by partial-interference between-group and within-group variance decompositions.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {Ω₁ : Type*} [Fintype Ω₁]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : ι → Type*} [∀ i, Fintype (α i)]

namespace FiniteDesign

/-- **Tower property of expectation** for the compound design. The compound expectation iterates as
the stage-1 expectation of the stage-2 product-design conditional expectation,
`E[F] = E_s[E_{D₂ s}[F(s, ·)]]`. -/
lemma E_compound_tower (D₁ : FiniteDesign Ω₁) (D₂ : Ω₁ → ∀ i, FiniteDesign (α i))
    (F : (Ω₁ × ∀ i, α i) → ℝ) :
    (compound D₁ D₂).E F
      = D₁.E (fun s => (prodDesign (D₂ s)).E (fun w => F (s, w))) := by
  rw [E_compound]
  simp only [FiniteDesign.E, prodDesign_p]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  ring

/-- **Law of total variance** for the two-stage compound design. The total variance decomposes as
expected stage-2 conditional variance plus the stage-1 variance of the stage-2 conditional mean:

    Var X = E_{s}[ Var_{D₂ s}(X(s, ·)) ] + Var_{s}( E_{D₂ s}(X(s, ·)) ). -/
lemma Var_compound_eq_tower (D₁ : FiniteDesign Ω₁) (D₂ : Ω₁ → ∀ i, FiniteDesign (α i))
    (X : (Ω₁ × ∀ i, α i) → ℝ) :
    (compound D₁ D₂).Var X
      = D₁.E (fun s => (prodDesign (D₂ s)).Var (fun w => X (s, w)))
        + D₁.Var (fun s => (prodDesign (D₂ s)).E (fun w => X (s, w))) := by
  -- stage-2 conditional mean and variance
  set m : Ω₁ → ℝ := fun s => (prodDesign (D₂ s)).E (fun w => X (s, w)) with hm
  set v : Ω₁ → ℝ := fun s => (prodDesign (D₂ s)).Var (fun w => X (s, w)) with hv
  -- Var X = E[X²] − (E X)²
  rw [Var_eq]
  -- E[X²] = E_s[ E_{D₂ s}[ X(s,·)² ] ] = E_s[ v s + (m s)² ]  (inner Var_eq)
  have hEsq : (compound D₁ D₂).E (fun sw => X sw ^ 2)
      = D₁.E (fun s => v s + (m s) ^ 2) := by
    rw [E_compound_tower]
    apply D₁.E_congr
    intro s
    have hinner : (prodDesign (D₂ s)).E (fun w => X (s, w) ^ 2)
        = v s + (m s) ^ 2 := by
      rw [hv, hm]
      simp only
      rw [Var_eq]
      ring
    -- the goal's inner expectation is over `fun w => (fun sw => X sw ^ 2) (s, w)`
    simpa using hinner
  -- E X = E_s[ m s ]
  have hEX : (compound D₁ D₂).E X = D₁.E m := by
    rw [E_compound_tower]
  rw [hEsq, hEX, E_add]
  -- now: D₁.E v + D₁.E (fun s => (m s)²) − (D₁.E m)² = D₁.E v + D₁.Var m
  rw [Var_eq]
  ring

end FiniteDesign

end DesignBased
end Experimentation
end Causalean
