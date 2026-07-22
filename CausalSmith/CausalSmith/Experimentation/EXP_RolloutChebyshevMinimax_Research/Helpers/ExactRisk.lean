/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Exact nested-rollout risk: the open exact-optimality question and rate feasibility

`oeq:exact-nested-minimax` (STATED as a Prop, an acknowledged open problem — not a proof
obligation, excluded from the theorem manifest) and `lem:exact-chebyshev-rate-feasible`.
-/

import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Basic
import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.Variance
import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.Schedule
import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.T_chebyshev_minimax
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Causalean.Experimentation.DesignBased
open scoped BigOperators

namespace CausalSmith.Experimentation.RolloutChebyshev

-- @node: oeq:exact-nested-minimax
/-- **OPEN QUESTION (D0 residual `oeq:exact-nested-minimax`, status to-prove).** Stated as a
named `Prop`, NOT a theorem and NOT a proof obligation: it asks whether, in the low-budget
regime with `k = ⌈c·β⌉`, the shifted Chebyshev-Lobatto schedule `p^Ch(k,q)` also *solves* the
exact finite-population nested-rollout minimax problem `R_exact(β,k,q)` for the true
monotone-Bernoulli covariance `Γ_P(p)` — i.e. its fixed-schedule exact risk attains
`exactNestedRisk`, the infimum over `S_{k,q}`. Rate-feasibility (the provable half) is
`exact_chebyshev_rate_feasible`; exact optimality is left open (no theorem depends on this).

The oversampling ratio is admissible (`1 < c`, the note's `c ∈ (1,∞)`); together with `1 ≤ β`
this forces `k = ⌈c·β⌉₊ ≥ 2 ≥ 1` and, with `q ∈ (0,1]`, makes `p^Ch(k,q)` a genuine member of
`S_{k,q}` (`chebyshev_schedule_admissible`) so the question ranges over the admissible schedule
the note states, not over a possibly-inadmissible grid. The antecedents `1 < c` and
`0 < q → LowBudgetCap q qmax` realize the core spaces `c ∈ (1,∞)` and `q ∈ (0, q_max] ⊆ (0,1]`.
@realizes c(carrier ℝ; range 1 < c via the `1 < c →` antecedent)
@realizes q(carrier ℝ; range 0 < q ≤ q_max < 1 via `0 < q → LowBudgetCap q qmax`) -/
def exactNestedMinimaxQuestion (c : ℝ) (n beta k : ℕ) {Ω : Type*} [Fintype Ω]
    (D : FiniteDesign Ω) (q qmax sigma0sq : ℝ) : Prop :=
  1 < c → 0 < q → LowBudgetCap q qmax → 1 ≤ beta → k = ⌈c * (beta : ℝ)⌉₊ →
    sInf { rw : ℝ | ∃ w : Fin (k + 1) → ℝ, UnbiasedWeights beta k (chebyshevSchedule k q) w ∧
        rw = sSup { rP : ℝ | ∃ (Y : Fin n → (Fin n → Bool) → ℝ)
            (Z : Fin (k + 1) → Ω → (Fin n → Bool)) (barY : Fin (k + 1) → Ω → ℝ)
            (m : ℝ → ℝ) (a : ℕ → ℝ),
          RolloutLawClass n k beta D Y Z barY m a sigma0sq (chebyshevSchedule k q) ∧
            rP = D.Var (fun z => ∑ j, w j * barY j z) } }
      = exactNestedRisk n k beta D q sigma0sq

-- @node: lem:exact-chebyshev-rate-feasible
/-- Rate-feasibility of the Chebyshev-Lobatto schedule for the exact risk: for `c > 1`,
`β ≥ 1`, `k = ⌈c·β⌉`, and `q ∈ (0, q_max]`, the fixed-Chebyshev exact risk obeys
`inf_{w∈W_β(p^Ch)} sup_{P∈P_β} w'Γ_P(p^Ch)w ≤ (σ₀²/n) C₊(c,q_max) (ρ(q)/q)^{2β}`, hence
`R_exact(β,k,q) ≤ (σ₀²/n) C₊(c,q_max) (ρ(q)/q)^{2β}`. Pure composition of
`exact_risk_envelope_upper` (applied to the admissible `p^Ch` via `chebyshev_schedule_admissible`)
with the Chebyshev upper half of `chebyshev_minimax`. The range predicate `hc : 1 < c` realizes
the core space `c ∈ (1,∞)`; `hq : 0 < q` with `hcap : LowBudgetCap q qmax` realizes `q ∈ (0,1]`.
@realizes c(carrier ℝ; range 1 < c via hc)
@realizes q(carrier ℝ; range 0 < q ≤ q_max < 1 via hq + hcap) -/
lemma exact_chebyshev_rate_feasible (c qmax : ℝ) (hc : 1 < c) (hqmax : 0 < qmax ∧ qmax < 1)
    : ∃ Cplus : ℝ, 0 < Cplus ∧
      ∀ (n beta k : ℕ) {Ω : Type*} [Fintype Ω] (D : FiniteDesign Ω) (q sigma0sq : ℝ),
        1 ≤ beta → 0 < q → LowBudgetCap q qmax → 0 ≤ sigma0sq →
        k = ⌈c * (beta : ℝ)⌉₊ →
          sInf { rw : ℝ | ∃ w : Fin (k + 1) → ℝ, UnbiasedWeights beta k (chebyshevSchedule k q) w ∧
              rw = sSup { rP : ℝ | ∃ (Y : Fin n → (Fin n → Bool) → ℝ)
                  (Z : Fin (k + 1) → Ω → (Fin n → Bool)) (barY : Fin (k + 1) → Ω → ℝ)
                (m : ℝ → ℝ) (a : ℕ → ℝ),
                RolloutLawClass n k beta D Y Z barY m a sigma0sq (chebyshevSchedule k q) ∧
                  rP = D.Var (fun z => ∑ j, w j * barY j z) } }
            ≤ sigma0sq / (n : ℝ) * Cplus * ((1 + Real.sqrt (1 - q)) ^ 2 / q) ^ (2 * beta) := by
  rcases chebyshev_minimax qmax hqmax with ⟨_, _, hcheb⟩
  rcases hcheb c hc with ⟨Cplus, hCplus, hbounds⟩
  refine ⟨Cplus, hCplus, ?_⟩
  intro n beta k Ω _ D q sigma0sq hbeta hq hcap hsig hk
  have hk_real : c * (beta : ℝ) ≤ (k : ℝ) := by
    simpa [hk] using Nat.le_ceil (c * (beta : ℝ))
  have hbeta_pos_real : 0 < (beta : ℝ) := by exact_mod_cast hbeta
  have hbeta_le_cbeta : (beta : ℝ) ≤ c * (beta : ℝ) := by nlinarith
  have hk_beta : beta ≤ k := by
    exact_mod_cast (le_trans hbeta_le_cbeta hk_real)
  have hq_le_one : q ≤ 1 := by
    linarith [hcap.2.1, hcap.2.2]
  have hq01 : 0 < q ∧ q ≤ 1 := ⟨hq, hq_le_one⟩
  have hk_one : 1 ≤ k := le_trans hbeta hk_beta
  have hpCh : BudgetedSchedule k q (chebyshevSchedule k q) :=
    chebyshev_schedule_admissible k q hk_one hq01
  have hrisk := (exact_risk_envelope_upper n k beta D q sigma0sq hbeta hk_beta hq01 hsig
    (chebyshevSchedule k q) hpCh).1
  have hupper :=
    (hbounds beta k q hbeta hk_real hcap hq).2.1
  have hscale_nonneg : 0 ≤ sigma0sq / (n : ℝ) :=
    div_nonneg hsig (Nat.cast_nonneg n)
  calc
    sInf { rw : ℝ | ∃ w : Fin (k + 1) → ℝ,
        UnbiasedWeights beta k (chebyshevSchedule k q) w ∧
          rw = sSup { rP : ℝ | ∃ (Y : Fin n → (Fin n → Bool) → ℝ)
              (Z : Fin (k + 1) → Ω → (Fin n → Bool)) (barY : Fin (k + 1) → Ω → ℝ)
              (m : ℝ → ℝ) (a : ℕ → ℝ),
            RolloutLawClass n k beta D Y Z barY m a sigma0sq (chebyshevSchedule k q) ∧
              rP = D.Var (fun z => ∑ j, w j * barY j z) } }
        ≤ sigma0sq / (n : ℝ) * amplification beta k (chebyshevSchedule k q) := hrisk
    _ ≤ sigma0sq / (n : ℝ) *
        (Cplus * ((1 + Real.sqrt (1 - q)) ^ 2 / q) ^ (2 * beta)) :=
      mul_le_mul_of_nonneg_left hupper hscale_nonneg
    _ = sigma0sq / (n : ℝ) * Cplus *
        ((1 + Real.sqrt (1 - q)) ^ 2 / q) ^ (2 * beta) := by ring

end CausalSmith.Experimentation.RolloutChebyshev
