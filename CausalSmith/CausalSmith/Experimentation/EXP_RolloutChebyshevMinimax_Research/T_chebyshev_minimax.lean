/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Headline theorem: matched Chebyshev-Lobatto minimax over budgeted rollout schedules

`thm:chebyshev-minimax`.
-/

import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Basic
import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.Amplification
import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.ChebyshevEndpoint
import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.ChebyshevExtremal
import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.EhlichZeller
import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.MinimaxUpper
import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.Schedule
import Mathlib.Analysis.SpecialFunctions.Sqrt

open scoped BigOperators

namespace CausalSmith.Experimentation.RolloutChebyshev

-- @node: thm:chebyshev-minimax
/-- **Headline theorem (Chebyshev-Lobatto matched minimax).** Fix `q_max ∈ (0,1)` and let
`ρ(q) = (1 + √(1-q))²`. There is a positive constant `C₋(q_max)` — chosen UNIFORMLY IN `c`,
depending only on `q_max` — and, for every oversampling ratio `c > 1`, a positive constant
`C₊(c,q_max)`, such that (both uniform in `β, k, q`) for every `β ≥ 1`, every integer `k ≥ c·β`,
and every `q ∈ (0, q_max]`:

* every budgeted schedule `p ∈ S_{k,q}` satisfies `A_β(p) ≥ C₋(q_max) (ρ(q)/q)^{2β}` (lower
  bound, via `amplification_dual_norm` and the `T_β` exterior growth in
  `continuous_chebyshev_endpoint_bound`);
* the shifted Chebyshev-Lobatto schedule satisfies
  `A_β(p^Ch(k,q)) ≤ C₊(c,q_max) (ρ(q)/q)^{2β}` (upper bound, via
  `oversampled_chebyshev_lobatto_norming` and `continuous_chebyshev_endpoint_bound`).

Hence the **minimax value `M_{β,k,q}` is itself trapped two-sided** between positive constant
multiples of `(ρ(q)/q)^{2β}` — the achievability (the admissible Chebyshev schedule attains the
upper base) and the converse (no budgeted schedule beats the lower base) — so `M_{β,k,q}` has
pointwise low-budget exponential base `ρ(q)/q` (→ `4/q` as `q ↓ 0`), the intrinsic exponent is
`2β`, and the equal-spacing `β/q` factor is not minimax once the rollout uses more than `β+1`
nodes. The gate `EhlichZellerMesh` enters only through `oversampled_chebyshev_lobatto_norming`,
so it is threaded there, not on this signature.

Symbol spaces realized here: the oversampling ratio `c ∈ (1,∞)` is pinned by the inner
`1 < c` hypothesis (carrier `c : ℝ` + range predicate `1 < c`, bound AFTER the uniform
`C₋`); the treated fraction `q ∈ (0,1]` (here further
restricted to `(0, q_max] ⊆ (0,1)` by the low-budget cap) is pinned by the range predicates
`LowBudgetCap q qmax` (giving `q ≤ q_max < 1`) together with `0 < q`. The named minimax base
`ρ_Ch(c,q_max) ∈ [1,∞)` (carrier `rhoCh` in `Basic.lean`) has its `[1,∞)` range discharged by
the dedicated range lemma `one_le_rhoCh` (`1 ≤ rhoCh c qmax`); this theorem SUPPLIES the
nonempty witness that lemma consumes — trapping `A_β(p^Ch(k,q))` two-sided between constant
multiples of `(ρ(q)/q)^{2β}` with `ρ(q)/q ≥ 1` for `q ∈ (0,1]` exhibits a finite base `≥ 1` in
the defining set, so `rhoCh`'s infimum is `≥ 1` rather than the empty-set junk value `0`.
@realizes c(carrier ℝ; range 1 < c via the inner 1 < c hypothesis)
@realizes q(carrier ℝ; range 0 < q ≤ q_max < 1 via LowBudgetCap + 0<q)
@realizes rho_Ch(c,q_max)(supplies nonempty witness A_β(p^Ch) ≍ (ρ(q)/q)^{2β} for one_le_rhoCh) -/
theorem chebyshev_minimax (qmax : ℝ) (hqmax : 0 < qmax ∧ qmax < 1) :
    ∃ Cminus : ℝ, 0 < Cminus ∧
      ∀ (c : ℝ), 1 < c → ∃ Cplus : ℝ, 0 < Cplus ∧
        ∀ (beta k : ℕ) (q : ℝ), 1 ≤ beta → (k : ℝ) ≥ c * beta → LowBudgetCap q qmax → 0 < q →
          (∀ p : Fin (k + 1) → ℝ, BudgetedSchedule k q p →
              amplification beta k p
                ≥ Cminus * ((1 + Real.sqrt (1 - q)) ^ 2 / q) ^ (2 * beta)) ∧
            amplification beta k (chebyshevSchedule k q)
              ≤ Cplus * ((1 + Real.sqrt (1 - q)) ^ 2 / q) ^ (2 * beta) ∧
            minimaxAmplification beta k q
                ≥ Cminus * ((1 + Real.sqrt (1 - q)) ^ 2 / q) ^ (2 * beta) ∧
              minimaxAmplification beta k q
                ≤ Cplus * ((1 + Real.sqrt (1 - q)) ^ 2 / q) ^ (2 * beta) := by
  rcases continuous_chebyshev_endpoint_bound qmax hqmax with
    ⟨Cupper, clower, hCupper_pos, hclower_pos, hendpoint⟩
  refine ⟨clower ^ 2, by positivity, ?_⟩
  intro c hc
  rcases oversampled_chebyshev_lobatto_norming ehlichZellerMesh c hc with
    ⟨K, hKpos, hnorming⟩
  refine ⟨(K * Cupper) ^ 2, by positivity, ?_⟩
  intro beta k q hbeta hk hcap hq
  have hqle : q ≤ qmax := hcap.2.1
  have hqmax_lt : qmax < 1 := hqmax.2
  have hq_le_one : q ≤ 1 := le_trans hqle (le_of_lt hqmax_lt)
  have hbeta_pos_nat : 0 < beta := by omega
  have hbeta_pos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbeta_pos_nat
  have hkβ : beta ≤ k := by
    have hkβ_real : (beta : ℝ) ≤ (k : ℝ) := by nlinarith [hk, hc, hbeta_pos]
    exact_mod_cast hkβ_real
  have hk_one : 1 ≤ k := hbeta.trans hkβ
  have hpCh : BudgetedSchedule k q (chebyshevSchedule k q) :=
    chebyshev_schedule_admissible k q hk_one ⟨hq, hq_le_one⟩
  let Bminus : ℝ := clower ^ 2 * ((1 + Real.sqrt (1 - q)) ^ 2 / q) ^ (2 * beta)
  let Bplus : ℝ := (K * Cupper) ^ 2 * ((1 + Real.sqrt (1 - q)) ^ 2 / q) ^ (2 * beta)
  have hlower : ∀ p : Fin (k + 1) → ℝ, BudgetedSchedule k q p →
      Bminus ≤ amplification beta k p := by
    intro p hp
    dsimp [Bminus]
    exact chebyshev_amplification_lower qmax clower hclower_pos
      (fun beta q hbeta hq hqle => (hendpoint beta q hbeta hq hqle).2)
      hbeta hkβ hq hqle hqmax_lt p hp
  have hupper : amplification beta k (chebyshevSchedule k q) ≤ Bplus := by
    dsimp [Bplus]
    exact chebyshev_amplification_upper c qmax Cupper K hCupper_pos hKpos
      (fun beta q hbeta hq hqle R hdeg hbound =>
        (hendpoint beta q hbeta hq hqle).1 R hdeg hbound)
      hnorming hbeta hkβ hk hq hqle hqmax_lt
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    exact hlower p hp
  · exact hupper
  · exact minimaxAmplification_lower_of_forall beta k q Bminus
      ⟨chebyshevSchedule k q, hpCh⟩ hlower
  · exact (minimaxAmplification_le_of_budgeted beta k q (chebyshevSchedule k q) hpCh).trans hupper

-- @node: one_le_rhoCh
/-- Range realization for `ρ_Ch(c,q_max) ∈ [1,∞)`: the minimal-base infimum is `≥ 1`, pinning
the symbol's declared space `[1,∞)` VALUE-wise (not merely element-wise). The defining set
`{ρ | 1 ≤ ρ ∧ ∃ M, …}` has `1` as a lower bound (every member satisfies the `1 ≤ ρ` conjunct)
and is nonempty: the Chebyshev upper half gives
`A_β(p^Ch) ≤ C₊·(((1+√(1-q))²)/q)^{2β}`, so after multiplying by `q^β` the base is bounded by
`4^β`. Thus `ρ = 4` is a finite witness, and `le_csInf` gives `1 ≤ sInf`.
@realizes rho_Ch(c,q_max)(range [1,∞): 1 ≤ rhoCh established value-wise via nonempty witness) -/
lemma one_le_rhoCh (c qmax : ℝ) (hc : 1 < c) (hqmax : 0 < qmax ∧ qmax < 1) :
    1 ≤ rhoCh c qmax := by
  rcases chebyshev_minimax qmax hqmax with ⟨_Cminus, _hCminus_pos, hbounds⟩
  rcases hbounds c hc with ⟨Cplus, hCplus_pos, hcheb⟩
  let S : Set ℝ := { rho : ℝ | 1 ≤ rho ∧
    ∃ M : ℝ, ∀ beta : ℕ, 1 ≤ beta → ∀ q : ℝ, 0 < q → q ≤ qmax →
      q ^ beta * Real.sqrt (amplification beta ⌈c * (beta : ℝ)⌉₊
          (chebyshevSchedule ⌈c * (beta : ℝ)⌉₊ q)) ≤ M * rho ^ beta }
  have hS_nonempty : S.Nonempty := by
    refine ⟨4, ?_⟩
    constructor
    · norm_num
    · refine ⟨Real.sqrt Cplus, ?_⟩
      intro beta hbeta q hq hqle
      let k : ℕ := ⌈c * (beta : ℝ)⌉₊
      let base : ℝ := (1 + Real.sqrt (1 - q)) ^ 2 / q
      have hk : (k : ℝ) ≥ c * beta := by
        dsimp [k]
        simpa using Nat.le_ceil (c * (beta : ℝ))
      have hcap : LowBudgetCap q qmax := ⟨hqmax.1, hqle, hqmax.2⟩
      have hupper :
          amplification beta k (chebyshevSchedule k q) ≤ Cplus * base ^ (2 * beta) := by
        simpa [k, base] using (hcheb beta k q hbeta hk hcap hq).2.1
      have hbase_nonneg : 0 ≤ base := by
        exact div_nonneg (sq_nonneg _) (le_of_lt hq)
      have hsqrt_upper :
          Real.sqrt (amplification beta k (chebyshevSchedule k q)) ≤
            Real.sqrt Cplus * base ^ beta := by
        calc
          Real.sqrt (amplification beta k (chebyshevSchedule k q))
              ≤ Real.sqrt (Cplus * base ^ (2 * beta)) := Real.sqrt_le_sqrt hupper
          _ = Real.sqrt Cplus * Real.sqrt (base ^ (2 * beta)) := by
              rw [Real.sqrt_mul (le_of_lt hCplus_pos)]
          _ = Real.sqrt Cplus * base ^ beta := by
              have hpow : base ^ (2 * beta) = (base ^ beta) ^ 2 := by
                rw [Nat.mul_comm 2 beta, pow_mul]
              rw [hpow, Real.sqrt_sq_eq_abs, abs_of_nonneg (pow_nonneg hbase_nonneg beta)]
      have hbase_cancel :
          q ^ beta * (Real.sqrt Cplus * base ^ beta) =
            Real.sqrt Cplus * ((1 + Real.sqrt (1 - q)) ^ 2) ^ beta := by
        have hq_ne : q ≠ 0 := ne_of_gt hq
        calc
          q ^ beta * (Real.sqrt Cplus * base ^ beta)
              = Real.sqrt Cplus * (q ^ beta * base ^ beta) := by ring
          _ = Real.sqrt Cplus * (q * base) ^ beta := by rw [mul_pow]
          _ = Real.sqrt Cplus * ((1 + Real.sqrt (1 - q)) ^ 2) ^ beta := by
              congr 1
              congr 1
              dsimp [base]
              field_simp [hq_ne]
      have hsqrt_le_one : Real.sqrt (1 - q) ≤ 1 := by
        simpa using Real.sqrt_le_sqrt (by linarith : 1 - q ≤ 1)
      have hrad_nonneg : 0 ≤ Real.sqrt (1 - q) := Real.sqrt_nonneg _
      have hbase4 : (1 + Real.sqrt (1 - q)) ^ 2 ≤ (4 : ℝ) := by
        nlinarith
      have hpow4 :
          ((1 + Real.sqrt (1 - q)) ^ 2) ^ beta ≤ (4 : ℝ) ^ beta := by
        exact pow_le_pow_left₀ (sq_nonneg _) hbase4 beta
      calc
        q ^ beta * Real.sqrt (amplification beta ⌈c * (beta : ℝ)⌉₊
            (chebyshevSchedule ⌈c * (beta : ℝ)⌉₊ q))
            = q ^ beta * Real.sqrt (amplification beta k (chebyshevSchedule k q)) := by
              simp [k]
        _ ≤ q ^ beta * (Real.sqrt Cplus * base ^ beta) :=
              mul_le_mul_of_nonneg_left hsqrt_upper (pow_nonneg (le_of_lt hq) beta)
        _ = Real.sqrt Cplus * ((1 + Real.sqrt (1 - q)) ^ 2) ^ beta := hbase_cancel
        _ ≤ Real.sqrt Cplus * (4 : ℝ) ^ beta :=
              mul_le_mul_of_nonneg_left hpow4 (Real.sqrt_nonneg Cplus)
  unfold rhoCh
  change 1 ≤ sInf S
  exact le_csInf hS_nonempty (by
    intro rho hrho
    exact hrho.1)

end CausalSmith.Experimentation.RolloutChebyshev
