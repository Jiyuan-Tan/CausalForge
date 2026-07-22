/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Data.Real.Basic

/-! # Criterion Sets

This file defines the basic objects in the Chernozhukov-Hong-Tamer
criterion-function approach to partial identification. The identified set is
the zero set of a population criterion, and a sample level-set estimator is the
set of parameters whose sample criterion value is below a cutoff.

The file contains only definitions and elementary set lemmas; Hausdorff
consistency of the level-set estimator is developed separately. -/

namespace Causalean.PartialID.CriterionSet

variable {Θ : Type*}

/-- A criterion function's identified set is the set of parameters where the population
criterion reaches zero.

This is the zero set `{θ | Q θ = 0}`; for a nonnegative criterion normalized to
have infimum zero, it is the argmin set. -/
def identifiedSet (Q : Θ → ℝ) : Set Θ := {θ | Q θ = 0}

/-- The level-set estimator keeps the parameters whose sample criterion is no larger
than the cutoff.

It is the set `{θ | Qn θ ≤ c}`, the sample analogue of the identified set relaxed
by a cutoff `c ≥ 0`. -/
def levelSet (Qn : Θ → ℝ) (c : ℝ) : Set Θ := {θ | Qn θ ≤ c}

/-- Membership in the identified set is the same as having zero criterion value. -/
@[simp] theorem mem_identifiedSet {Q : Θ → ℝ} {θ : Θ} :
    θ ∈ identifiedSet Q ↔ Q θ = 0 := Iff.rfl

/-- Membership in a level set is the same as having criterion value below the cutoff. -/
@[simp] theorem mem_levelSet {Qn : Θ → ℝ} {c : ℝ} {θ : Θ} :
    θ ∈ levelSet Qn c ↔ Qn θ ≤ c := Iff.rfl

/-- The level set is monotone in the cutoff `c`. -/
theorem levelSet_mono {Qn : Θ → ℝ} {c₁ c₂ : ℝ} (h : c₁ ≤ c₂) :
    levelSet Qn c₁ ⊆ levelSet Qn c₂ := fun _ hθ => le_trans hθ h

/-- For a nonnegative criterion, the identified set is the level-`0` set of the same
criterion (since `Q θ = 0 ↔ Q θ ≤ 0` under nonnegativity). -/
theorem identifiedSet_eq_levelSet_zero_of_nonneg {Q : Θ → ℝ} (hQ : ∀ θ, 0 ≤ Q θ) :
    identifiedSet Q = levelSet Q 0 := by
  ext θ
  simp only [mem_identifiedSet, mem_levelSet]
  exact ⟨fun h => h.le, fun h => le_antisymm h (hQ θ)⟩

/-- The identified set sits inside any nonnegative-cutoff level set of the same criterion. -/
theorem identifiedSet_subset_levelSet_self {Q : Θ → ℝ} {c : ℝ} (hc : 0 ≤ c) :
    identifiedSet Q ⊆ levelSet Q c := fun _ hθ => by
  rw [mem_levelSet, mem_identifiedSet.mp hθ]; exact hc

end Causalean.PartialID.CriterionSet
