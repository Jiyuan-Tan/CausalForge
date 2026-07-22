/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Chebyshev schedule admissibility
-/

import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.ScheduleGrid
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open scoped BigOperators

namespace CausalSmith.Experimentation.RolloutChebyshev

-- @node: lem:chebyshev-schedule-admissible
/-- For every integer `k ≥ 1` and `q ∈ (0,1]`, the shifted Chebyshev-Lobatto schedule
`p^Ch(k,q)` belongs to `S_{k,q}`: endpoints `0` and `q`, with strict monotonicity from the
strict decrease of cosine on `[0,π]`. This lemma is the load-bearing member that pins the
Chebyshev schedule's core space `p^Ch(k,q) ∈ [0,1]^(k+1)`: its conclusion `BudgetedSchedule`
has as first conjunct `∀ j, p^Ch(k,q) j ∈ Set.Icc 0 1`, i.e. the `[0,1]^(k+1)` range, holding
exactly under the admissibility hypotheses `k ≥ 1` and `q ∈ (0,1]`. The range predicate
`hq : 0 < q ∧ q ≤ 1` realizes the core space `q ∈ (0,1]`.
@realizes p^Ch(k,q)(range [0,1]^(k+1): BudgetedSchedule Icc conjunct; k≥1, q∈(0,1])
@realizes q(carrier ℝ; range 0 < q ≤ 1 via hq — the `p^Ch` admissibility range) -/
lemma chebyshev_schedule_admissible (k : ℕ) (q : ℝ) (hk : 1 ≤ k)
    (hq : 0 < q ∧ q ≤ 1) :  -- @realizes q(0 < q ∧ q ≤ 1)
    BudgetedSchedule k q (chebyshevSchedule k q) := by
    -- @realizes p^Ch(k,q)(∈ [0,1]^(k+1) via BudgetedSchedule.1)
  have hkpos_nat : 0 < k := by omega
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos_nat
  refine ⟨?range, ?zero, ?mono, ?last⟩
  · intro j
    unfold chebyshevSchedule
    have hcos_le : Real.cos (Real.pi * (j : ℝ) / (k : ℝ)) ≤ 1 := Real.cos_le_one _
    have hcos_ge : -1 ≤ Real.cos (Real.pi * (j : ℝ) / (k : ℝ)) := Real.neg_one_le_cos _
    constructor
    · have hnonneg : 0 ≤ 1 - Real.cos (Real.pi * (j : ℝ) / (k : ℝ)) := by linarith
      nlinarith [hq.1]
    · have hle2 : 1 - Real.cos (Real.pi * (j : ℝ) / (k : ℝ)) ≤ 2 := by linarith
      have hmul : q * (1 - Real.cos (Real.pi * (j : ℝ) / (k : ℝ))) ≤ q * 2 :=
        mul_le_mul_of_nonneg_left hle2 (le_of_lt hq.1)
      nlinarith [hq.2]
  · simp [chebyshevSchedule]
  · intro a b hab
    have hb_le_nat : (b : ℕ) ≤ k := Nat.le_of_lt_succ b.isLt
    have hb_le : (b : ℝ) ≤ (k : ℝ) := by exact_mod_cast hb_le_nat
    have hθa_nonneg : 0 ≤ Real.pi * (a : ℝ) / (k : ℝ) := by positivity
    have hratio_le : (b : ℝ) / (k : ℝ) ≤ 1 := (div_le_one hkpos).2 hb_le
    have hθb_le_pi : Real.pi * (b : ℝ) / (k : ℝ) ≤ Real.pi := by
      calc
        Real.pi * (b : ℝ) / (k : ℝ) = Real.pi * ((b : ℝ) / (k : ℝ)) := by ring
        _ ≤ Real.pi * 1 := mul_le_mul_of_nonneg_left hratio_le (le_of_lt Real.pi_pos)
        _ = Real.pi := by ring
    have hab_nat : (a : ℕ) < (b : ℕ) := by exact_mod_cast hab
    have hab_real : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab_nat
    have hmul_arg : Real.pi * (a : ℝ) < Real.pi * (b : ℝ) :=
      mul_lt_mul_of_pos_left hab_real Real.pi_pos
    have hθlt : Real.pi * (a : ℝ) / (k : ℝ) < Real.pi * (b : ℝ) / (k : ℝ) :=
      (div_lt_div_iff_of_pos_right hkpos).2 hmul_arg
    have hcos : Real.cos (Real.pi * (b : ℝ) / (k : ℝ)) <
        Real.cos (Real.pi * (a : ℝ) / (k : ℝ)) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi hθa_nonneg hθb_le_pi hθlt
    unfold chebyshevSchedule
    have hdiff : 1 - Real.cos (Real.pi * (a : ℝ) / (k : ℝ)) <
        1 - Real.cos (Real.pi * (b : ℝ) / (k : ℝ)) := by linarith
    have hmul : q * (1 - Real.cos (Real.pi * (a : ℝ) / (k : ℝ))) <
        q * (1 - Real.cos (Real.pi * (b : ℝ) / (k : ℝ))) :=
      mul_lt_mul_of_pos_left hdiff hq.1
    nlinarith
  · unfold chebyshevSchedule
    have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
    simp [hk_ne, Real.cos_pi]
    ring

end CausalSmith.Experimentation.RolloutChebyshev
