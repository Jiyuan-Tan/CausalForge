/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality.NonemptyDuality

/-!
# Strong duality from distinct interpolation nodes

This file specializes the feasibility-based finite-dimensional ℓ¹/ℓ∞ duality
API to distinct nodes with degree bound `β ≤ k`. Vandermonde feasibility is
provided by `momentSol_nonempty`, while the Hahn–Banach certificate is supplied
by `exists_moment_le_dual_of_momentSol_nonempty`.
-/

namespace Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality

variable {k β : ℕ} {p : Fin (k + 1) → ℝ}

/-- **Strong duality (existence of an optimal weight).**  For distinct nodes and
`β ≤ k` there is an admissible weight `w ∈ MomentSol p β` whose ℓ¹ norm does not
exceed the dual value `sSup (dualValSet p β)`. -/
theorem exists_moment_le_dual (hp : Function.Injective p) (hβ : β ≤ k) :
    ∃ w ∈ MomentSol p β, ∑ j, |w j| ≤ sSup (dualValSet p β) :=
  exists_moment_le_dual_of_momentSol_nonempty (momentSol_nonempty hp hβ)

/-- **Strong duality (inequality form).**  `sInf (primalNormSet p β) ≤ sSup (dualValSet p β)`.
Immediate from `exists_moment_le_dual`: the witness `w` gives a primal value
`∑ j, |w j| ∈ primalNormSet p β` that is `≤` the dual value, and the infimum is a
lower bound. -/
theorem sInf_primal_le_sSup_dual (hp : Function.Injective p) (hβ : β ≤ k) :
    sInf (primalNormSet p β) ≤ sSup (dualValSet p β) := by
  obtain ⟨w, hw, hw_norm⟩ := exists_moment_le_dual hp hβ
  exact le_trans (csInf_le primalNormSet_bddBelow ⟨w, hw, rfl⟩) hw_norm

end Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality
