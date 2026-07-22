/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# No-extrapolation boundary
-/

import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.ScheduleGrid

open scoped BigOperators

namespace CausalSmith.Experimentation.RolloutChebyshev

-- @node: prop:no-extrapolation-boundary
/-- No-extrapolation boundary at the full-budget point `q = 1`: the endpoint rule
`w₀ = -1, w_β = 1, wⱼ = 0` for `1 ≤ j ≤ β-1` lies in `W_β(p^eq(β,1))`, hence `A_β(p^eq(β,1)) ≤ 4`.
Marks the limit where node optimization becomes trivial (a β-uniform lower bound cannot extend to
`q = 1`). -/
lemma no_extrapolation_boundary (beta : ℕ) (hbeta : 1 ≤ beta) :
    UnbiasedWeights beta beta (equalSchedule beta 1)
        (fun j => if j = (0 : Fin (beta + 1)) then -1
          else if j = Fin.last beta then 1 else 0) ∧
      amplification beta beta (equalSchedule beta 1) ≤ 4 := by
  let w : Fin (beta + 1) → ℝ := fun j => if j = (0 : Fin (beta + 1)) then -1
    else if j = Fin.last beta then 1 else 0
  have hne : (Fin.last beta) ≠ (0 : Fin (beta + 1)) := by
    intro h
    have hv : (Fin.last beta).val = (0 : Fin (beta + 1)).val := congrArg Fin.val h
    simp at hv
    omega
  have hbeta_ne : beta ≠ 0 := by omega
  have hw : UnbiasedWeights beta beta (equalSchedule beta 1) w := by
    constructor
    · have hsum_split : (∑ j, w j) =
          (∑ j, if j = (0 : Fin (beta + 1)) then (-1 : ℝ) else 0) +
            (∑ j, if j = Fin.last beta then (1 : ℝ) else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases h0 : j = (0 : Fin (beta + 1))
        · simp [w, h0, hne.symm]
        · by_cases hl : j = Fin.last beta
          · simp [w, hl, hbeta_ne]
          · simp [w, h0, hl]
      norm_num [hsum_split, Finset.sum_ite_eq']
    · intro ell hell hle
      have hsum_split : (∑ j, w j * (equalSchedule beta 1 j) ^ ell) =
          (∑ j, if j = (0 : Fin (beta + 1)) then -((equalSchedule beta 1 j) ^ ell)
              else 0) +
            (∑ j, if j = Fin.last beta then (equalSchedule beta 1 j) ^ ell else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases h0 : j = (0 : Fin (beta + 1))
        · simp [w, h0, hne.symm]
        · by_cases hl : j = Fin.last beta
          · simp [w, hl, hbeta_ne]
          · simp [w, h0, hl]
      rw [hsum_split]
      simp [Finset.sum_ite_eq', equalSchedule, hbeta_ne, zero_pow (ne_of_gt hell)]
  constructor
  · exact hw
  · unfold amplification
    apply csInf_le
    · use 0
      intro x hx
      rcases hx with ⟨w', hw', rfl⟩
      positivity
    · refine ⟨w, hw, ?_⟩
      have hsum_abs : (∑ j, |w j|) = 2 := by
        have hsum_split : (∑ j, |w j|) =
            (∑ j, if j = (0 : Fin (beta + 1)) then (1 : ℝ) else 0) +
              (∑ j, if j = Fin.last beta then (1 : ℝ) else 0) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j hj
          by_cases h0 : j = (0 : Fin (beta + 1))
          · simp [w, h0, hne.symm]
          · by_cases hl : j = Fin.last beta
            · simp [w, hl, hbeta_ne]
            · simp [w, h0, hl]
        norm_num [hsum_split, Finset.sum_ite_eq']
      norm_num [hsum_abs]

end CausalSmith.Experimentation.RolloutChebyshev
