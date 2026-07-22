/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Basic
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.SimplexTruncationDefs

/-! # Bridge between reduced triangle coordinates and weighted-simplex coordinates -/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators

-- @node: reducedTriangle_to_simplex
/-- The change of variables `t = (q x, y, z)` sends the reduced triangle to `Δ_{2m}`. -/
lemma reducedTriangle_to_simplex (m : ℕ) (x y z : ℝ)
    (hq0 : 0 ≤ qParam m) (hT : InReducedTriangle m x y z) :
    InSimplex (2 * (m : ℝ)) ![qParam m * x, y, z] := by
  rcases hT with ⟨hx, hy, hz, hsum⟩
  constructor
  · intro i
    fin_cases i
    · simp [mul_nonneg hq0 hx]
    · simpa using hy
    · simpa using hz
  · simpa [Fin.sum_univ_three] using hsum

-- @node: simplex_to_reducedTriangle
/-- The inverse change of variables `x = t_x/q`, `y = t_y`, `z = t_z`. -/
lemma simplex_to_reducedTriangle (m : ℕ) (t : Fin 3 → ℝ)
    (hq : 0 < qParam m) (hS : InSimplex (2 * (m : ℝ)) t) :
    InReducedTriangle m (t 0 / qParam m) (t 1) (t 2) := by
  rcases hS with ⟨hnonneg, hsum⟩
  constructor
  · exact div_nonneg (hnonneg 0) (le_of_lt hq)
  constructor
  · exact hnonneg 1
  constructor
  · exact hnonneg 2
  · rw [Fin.sum_univ_three] at hsum
    field_simp [ne_of_gt hq]
    exact hsum

-- @node: reducedObjective_eq_wsObj
/-- Under `t = (q x, y, z)`, the reduced objective is the weighted-simplex objective
with `α = (c_x/q, c_y, c_z)` and `β = (1/q, 1, 1)`. -/
lemma reducedObjective_eq_wsObj (q cx cy cz kappa x y z : ℝ) (hq : q ≠ 0) :
    reducedObjective q cx cy cz kappa x y z =
      wsObj ![cx / q, cy, cz] ![1 / q, 1, 1] kappa ![q * x, y, z] := by
  unfold reducedObjective wsObj
  simp [Fin.sum_univ_three]
  field_simp [hq]

-- @node: wsObj_eq_reducedObjective
/-- The inverse form of `reducedObjective_eq_wsObj`, for a simplex point `t`. -/
lemma wsObj_eq_reducedObjective (q cx cy cz kappa : ℝ) (t : Fin 3 → ℝ) (hq : q ≠ 0) :
    wsObj ![cx / q, cy, cz] ![1 / q, 1, 1] kappa t =
      reducedObjective q cx cy cz kappa (t 0 / q) (t 1) (t 2) := by
  unfold reducedObjective wsObj
  simp [Fin.sum_univ_three]
  field_simp [hq]

end CausalSmith.Experimentation.DesignPm1
