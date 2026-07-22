/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Local information program: Rayleigh complexity assembly

Stage-2 scaffold.  This file proves the Rayleigh quotient formula for the local
complexity and the feasible-direction positivity lemma, importing the score-cost
definitions and arm-wise score-program solution from `ScoreProgramDefs`.
-/

import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.ScoreProgramDefs

namespace CausalSmith.Stat.NeymanRegretMinimax

open MeasureTheory
open scoped BigOperators Topology

-- @node: lem:local-complexity-rayleigh
/-- Rayleigh-quotient closed form for the local complexity.  The note states BOTH
the diagonal positive-definite form of the local information
`J_nu(u) = p u₁²/r₁ + (1−p) u₀²/r₀` (with `p = π_nu*`) AND the resulting complexity
`κ_nu = {r₀ m₁²/m₀³ + r₁ m₀²/m₁³} / (4 (m₀+m₁))`; both are recorded here (the
`J_nu` form is added per the redirect, not just the κ closed form). -/
lemma local_complexity_rayleigh (nu : Measure (ℝ × ℝ)) (hnu : MTan nu) :
    (∀ u : ℝ × ℝ, localInformation nu u
        = oracleAllocation nu * u.2 ^ 2 / armTangentStrength nu 1
          + (1 - oracleAllocation nu) * u.1 ^ 2 / armTangentStrength nu 0)
      ∧ localComplexity nu =
        (armTangentStrength nu 0 * rootSecondMoment nu 1 ^ 2 / rootSecondMoment nu 0 ^ 3
          + armTangentStrength nu 1 * rootSecondMoment nu 0 ^ 2 / rootSecondMoment nu 1 ^ 3)
          / (4 * (rootSecondMoment nu 0 + rootSecondMoment nu 1)) := by
  let m0 : ℝ := rootSecondMoment nu 0
  let m1 : ℝ := rootSecondMoment nu 1
  let r0 : ℝ := armTangentStrength nu 0
  let r1 : ℝ := armTangentStrength nu 1
  let S : ℝ := m0 + m1
  have hm0 : 0 < m0 := hnu.interiorMoments 0
  have hm1 : 0 < m1 := hnu.interiorMoments 1
  have hr0 : 0 < r0 := hnu.tangent 0
  have hr1 : 0 < r1 := hnu.tangent 1
  have hS_pos : 0 < S := add_pos hm0 hm1
  have hm0_ne : m0 ≠ 0 := ne_of_gt hm0
  have hm1_ne : m1 ≠ 0 := ne_of_gt hm1
  have hr0_ne : r0 ≠ 0 := ne_of_gt hr0
  have hr1_ne : r1 ≠ 0 := ne_of_gt hr1
  have hS_ne : S ≠ 0 := ne_of_gt hS_pos
  have halloc : oracleAllocation nu = m1 / S := by
    dsimp [m0, m1, S]
    rw [oracleAllocation, Causalean.Experimentation.DesignBased.neymanFraction]
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
    rw [abs_of_pos (hnu.interiorMoments 1), abs_of_pos (hnu.interiorMoments 0)]
    ring
  have hone_alloc : 1 - oracleAllocation nu = m0 / S := by
    rw [halloc]
    dsimp [S]
    field_simp [hS_ne]
    ring
  rcases arm_score_program_solution nu hnu 0 with
    ⟨_e0, _he00, _he01, _he02, _he03, _hr0pos, _hb0, hcost0⟩
  rcases arm_score_program_solution nu hnu 1 with
    ⟨_e1, _he10, _he11, _he12, _he13, _hr1pos, _hb1, hcost1⟩
  have hJ : ∀ u : ℝ × ℝ, localInformation nu u
      = oracleAllocation nu * u.2 ^ 2 / armTangentStrength nu 1
        + (1 - oracleAllocation nu) * u.1 ^ 2 / armTangentStrength nu 0 := by
    intro u
    rw [localInformation, (hcost1 u.2).1, (hcost0 u.1).1]
    ring
  let a : ℝ := (m1 / S) / r1
  let b : ℝ := (m0 / S) / r0
  let α : ℝ := m0 / m1
  let β : ℝ := -(m1 / m0)
  let c : ℝ := 1 / (4 * S ^ 2)
  have ha : 0 < a := div_pos (div_pos hm1 hS_pos) hr1
  have hb : 0 < b := div_pos (div_pos hm0 hS_pos) hr0
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hα_ne : α ≠ 0 := by
    dsimp [α]
    exact div_ne_zero hm0_ne hm1_ne
  have hJdiag : ∀ u : ℝ × ℝ, localInformation nu u = a * u.2 ^ 2 + b * u.1 ^ 2 := by
    intro u
    rw [hJ u, halloc]
    dsimp [a, b, r0, r1, S]
    field_simp [hS_ne]
    ring
  have hsens : ∀ u : ℝ × ℝ,
      oracleSensitivity nu u = (α * u.2 + β * u.1) / (2 * S ^ 2) := by
    intro u
    dsimp [oracleSensitivity, α, β, S, m0, m1]
    ring
  constructor
  · exact hJ
  · have hset :
        {v | ∃ u ∈ feasibleDirectionSet nu,
          v = (rootSecondMoment nu 0 + rootSecondMoment nu 1) ^ 2
            * oracleSensitivity nu u ^ 2 / localInformation nu u}
          =
        {v | ∃ x y : ℝ,
          0 < a * y ^ 2 + b * x ^ 2
            ∧ α * y + β * x ≠ 0
            ∧ v = c * ((α * y + β * x) ^ 2 / (a * y ^ 2 + b * x ^ 2))} := by
      ext v
      constructor
      · rintro ⟨u, hu, rfl⟩
        have hqpos : 0 < a * u.2 ^ 2 + b * u.1 ^ 2 := by
          simpa [hJdiag u] using hu.1
        have hq_ne : a * u.2 ^ 2 + b * u.1 ^ 2 ≠ 0 := ne_of_gt hqpos
        have hlin_ne : α * u.2 + β * u.1 ≠ 0 := by
          intro hzero
          apply hu.2
          rw [hsens u, hzero]
          simp
        refine ⟨u.1, u.2, hqpos, hlin_ne, ?_⟩
        rw [hJdiag u, hsens u]
        dsimp [c, S, m0, m1]
        field_simp [hS_ne, hq_ne]
        ring
      · rintro ⟨x, y, hqpos, hlin_ne, rfl⟩
        have hq_ne : a * y ^ 2 + b * x ^ 2 ≠ 0 := ne_of_gt hqpos
        refine ⟨(x, y), ?_, ?_⟩
        · constructor
          · simpa [hJdiag (x, y)] using hqpos
          · intro hsens_zero
            apply hlin_ne
            have hs := hsens (x, y)
            rw [hs] at hsens_zero
            have hden_ne : 2 * S ^ 2 ≠ 0 := by positivity
            rcases (div_eq_zero_iff).mp hsens_zero with hnum | hden
            · exact hnum
            · exact (hden_ne hden).elim
        · rw [hJdiag (x, y), hsens (x, y)]
          dsimp [c, S, m0, m1]
          field_simp [hS_ne, hq_ne]
          ring
    rw [localComplexity, hset]
    rw [diagonal_rayleigh_sSup c a b α β hc ha hb (Or.inl hα_ne)]
    dsimp [c, a, b, α, β, S, m0, m1, r0, r1]
    field_simp [hm0_ne, hm1_ne, hr0_ne, hr1_ne, hS_ne]
    ring

-- @node: lem:feasible-directions
/-- The feasible-direction set is nonempty and the local complexity is finite and
positive (`0 < κ_nu < ∞`). -/
lemma feasible_directions_nonempty (nu : Measure (ℝ × ℝ)) (h : MTan nu) :
    (feasibleDirectionSet nu).Nonempty ∧ 0 < localComplexity nu := by
  have hm0 : 0 < rootSecondMoment nu 0 := h.interiorMoments 0
  have hm1 : 0 < rootSecondMoment nu 1 := h.interiorMoments 1
  have hr0 : 0 < armTangentStrength nu 0 := h.tangent 0
  have hr1 : 0 < armTangentStrength nu 1 := h.tangent 1
  have hπ : 0 < oracleAllocation nu ∧ oracleAllocation nu < 1 := by
    rw [oracleAllocation]
    exact Causalean.Experimentation.DesignBased.neymanFraction_mem_Ioo
      (by positivity) (by positivity)
  have hπ0 : 0 < oracleAllocation nu := hπ.1
  have hsens : oracleSensitivity nu (0, 1) ≠ 0 := by
    have hsum : 0 < rootSecondMoment nu 0 + rootSecondMoment nu 1 :=
      add_pos hm0 hm1
    have hnum : 0 < rootSecondMoment nu 0 / rootSecondMoment nu 1 :=
      div_pos hm0 hm1
    have hden :
        0 < 2 * (rootSecondMoment nu 0 + rootSecondMoment nu 1) ^ 2 := by
      positivity
    have hsens_pos : 0 < oracleSensitivity nu (0, 1) := by
      rw [oracleSensitivity]
      norm_num
      exact div_pos hnum hden
    exact ne_of_gt hsens_pos
  have hray := local_complexity_rayleigh nu h
  constructor
  · refine ⟨(0, 1), ?_⟩
    constructor
    · rw [hray.1]
      norm_num
      exact div_pos hπ0 hr1
    · exact hsens
  · rw [hray.2]
    have hterm0 :
        0 < armTangentStrength nu 0 * rootSecondMoment nu 1 ^ 2
            / rootSecondMoment nu 0 ^ 3 := by
      positivity
    have hterm1 :
        0 < armTangentStrength nu 1 * rootSecondMoment nu 0 ^ 2
            / rootSecondMoment nu 1 ^ 3 := by
      positivity
    have hnum :
        0 < armTangentStrength nu 0 * rootSecondMoment nu 1 ^ 2
              / rootSecondMoment nu 0 ^ 3
            + armTangentStrength nu 1 * rootSecondMoment nu 0 ^ 2
              / rootSecondMoment nu 1 ^ 3 :=
      add_pos hterm0 hterm1
    have hden : 0 < 4 * (rootSecondMoment nu 0 + rootSecondMoment nu 1) := by
      positivity
    exact div_pos hnum hden

end CausalSmith.Stat.NeymanRegretMinimax
