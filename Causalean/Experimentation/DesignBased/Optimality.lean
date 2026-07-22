/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Design families, domination, and optimal designs

This file promotes the randomization design from a fixed object to a *parameter* that the
experimenter chooses.  A **design family** is a set of candidate designs on a common
assignment space; a **risk** `R` assigns each design a real number (its mean squared error
for a chosen estimator and target — see `mseRisk` — or any other criterion).  One design
**dominates** another when it carries no larger risk, and a design is **optimal** in a
family when it dominates every member.  The main result is that over a nonempty *finite*
family an optimal design exists.  Keeping the optimality layer generic in `R` isolates the
order-theoretic content from the particular estimation problem being optimized.
-/

import Causalean.Experimentation.DesignBased.Risk

/-!
# Design-family optimality criteria

This file treats a randomization design as the object being chosen from a finite family under a
real-valued risk criterion.

The declarations `DesignFamily`, `Dominates`, and `IsOptimalOn` formalize candidate sets,
weak domination, and least-risk designs. The theorem `exists_isOptimalOn` shows that every
nonempty finite design family has an optimal member. The risk functional `mseRisk` packages the
mean squared error of a design-indexed estimator, with `mseRisk_nonneg` and
`mseRisk_eq_var_of_unbiased` connecting it to nonnegativity and variance for unbiased estimators.
-/

open scoped BigOperators

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {Ω : Type*} [Fintype Ω]

/-- A **design family**: a set of candidate randomization designs on a common assignment
space `Ω`, among which the experimenter chooses. -/
abbrev DesignFamily (Ω : Type*) [Fintype Ω] : Type _ := Set (FiniteDesign Ω)

/-- `D₁` weakly **dominates** `D₂` under the risk criterion `R` when it carries no larger
risk: `R D₁ ≤ R D₂`. -/
def Dominates (R : FiniteDesign Ω → ℝ) (D₁ D₂ : FiniteDesign Ω) : Prop := R D₁ ≤ R D₂

/-- Domination is reflexive: every design dominates itself. -/
lemma Dominates.refl (R : FiniteDesign Ω → ℝ) (D : FiniteDesign Ω) : Dominates R D D :=
  le_refl _

/-- Domination is transitive. -/
lemma Dominates.trans {R : FiniteDesign Ω → ℝ} {D₁ D₂ D₃ : FiniteDesign Ω}
    (h₁ : Dominates R D₁ D₂) (h₂ : Dominates R D₂ D₃) : Dominates R D₁ D₃ :=
  le_trans h₁ h₂

/-- A design `D₀` is **optimal** in the family `𝒟` under risk `R` when it belongs to `𝒟`
and carries the least risk among all members. -/
def IsOptimalOn (𝒟 : DesignFamily Ω) (R : FiniteDesign Ω → ℝ) (D₀ : FiniteDesign Ω) : Prop :=
  D₀ ∈ 𝒟 ∧ ∀ D ∈ 𝒟, R D₀ ≤ R D

/-- An optimal design dominates every member of its family. -/
lemma IsOptimalOn.dominates {𝒟 : DesignFamily Ω} {R : FiniteDesign Ω → ℝ} {D₀ : FiniteDesign Ω}
    (h : IsOptimalOn 𝒟 R D₀) {D : FiniteDesign Ω} (hD : D ∈ 𝒟) : Dominates R D₀ D :=
  h.2 D hD

/-- **Existence of an optimal design.** Over a nonempty finite design family, some design
minimizes the risk. -/
theorem exists_isOptimalOn (𝒟 : DesignFamily Ω) (R : FiniteDesign Ω → ℝ)
    (hfin : 𝒟.Finite) (hne : 𝒟.Nonempty) : ∃ D₀, IsOptimalOn 𝒟 R D₀ := by
  let s := hfin.toFinset
  have hs : s.Nonempty := by
    simpa [s] using hfin.toFinset_nonempty.mpr hne
  rcases Finset.exists_min_image s R hs with ⟨D₀, hD₀, hmin⟩
  refine ⟨D₀, hfin.mem_toFinset.mp hD₀, ?_⟩
  intro D hD
  exact hmin D (hfin.mem_toFinset.mpr hD)

/-! ### Mean-squared-error risk of a design-indexed estimator

The canonical risk: fix an estimator that may use each design's known probabilities
(`est D : Ω → ℝ`, e.g. Horvitz–Thompson) and a design-independent target `μ`; the risk of a
design is the estimator's mean squared error under it. -/

/-- The **mean-squared-error risk** of a design-indexed estimator `est` for target `μ`:
the risk assigned to a design `D` is `est D`'s mean squared error under `D`. -/
def mseRisk (est : FiniteDesign Ω → Ω → ℝ) (μ : ℝ) : FiniteDesign Ω → ℝ :=
  fun D => D.mse (est D) μ

/-- Mean-squared-error risk is nonnegative. -/
lemma mseRisk_nonneg (est : FiniteDesign Ω → Ω → ℝ) (μ : ℝ) (D : FiniteDesign Ω) :
    0 ≤ mseRisk est μ D :=
  D.mse_nonneg _ _

/-- For an estimator that is unbiased under every design in the family, the
mean-squared-error risk coincides with the variance there. -/
lemma mseRisk_eq_var_of_unbiased {est : FiniteDesign Ω → Ω → ℝ} {μ : ℝ} {D : FiniteDesign Ω}
    (h : D.Unbiased (est D) μ) : mseRisk est μ D = D.Var (est D) :=
  D.mse_eq_var_of_unbiased h

end DesignBased
end Experimentation
end Causalean
