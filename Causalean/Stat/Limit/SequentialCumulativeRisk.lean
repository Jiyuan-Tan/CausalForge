/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Sequential-experiment cumulative-risk engine

This file isolates the purely real-analytic core of the `Ω(log T)` minimax lower
bound for cumulative Neyman regret of an adaptive two-arm Horvitz–Thompson
estimator.  In words: suppose a nonnegative "per-round mean-squared-error"
sequence `b₁, b₂, …` (with running totals `Bₙ = b₁ + ⋯ + bₙ`) obeys the
predictable van Trees / Bayes–Cramér–Rao recursion

    `bₜ ≥ (d²/4) / (Iq + (5J/4)·t + L·√(t·B_{t-1}))`

for every round `t ≥ 1`, where `J > 0` is the per-round Fisher information scale,
`d ≠ 0` the oracle-sensitivity, `L ≥ 0` a fixed feedback constant, and `Iq ≥ 0`
the prior information.  Then the cumulative total is forced to grow at least
logarithmically: there is a threshold `T₀` beyond which `B_T ≥ (d²/(32 J))·log T`.
This is the "self-bounding + harmonic-sum" argument that converts a per-round
information bound into a cumulative one — the crux of the lower bound — with the
measure-theoretic van Trees inequality and the Neyman-gap quadratic conversion
taken as clean hypotheses so the engine is self-contained and reusable.

The main engine is `cumulative_risk_engine`.  It is assembled into the regret
form `sequential_cumulative_risk_regret`, the radius-monotone lemma
`lem:local-neighborhood-cumulative-risk` of the Neyman-regret writeup, by
combining it with the two assumed inputs: the Neyman-gap quadratic conversion
`R^B_T ≥ 2 S² B_T` and `sup regret ≥ R^B_T`.  A standalone harmonic-tail bound
`harmonic_sum_ge_log_sub_log` is proved on the way and is independently reusable.
-/

namespace Causalean.Stat

open scoped BigOperators
open Finset
open Filter

/-- Elementary per-term bound `log(x+1) - log x ≤ 1/x` for `x > 0`, i.e.
`log(1 + 1/x) ≤ 1/x`.  This is the pointwise ingredient of the harmonic-tail
lower bound. -/
lemma log_add_one_sub_log_le_inv {x : ℝ} (hx : 0 < x) :
    Real.log (x + 1) - Real.log x ≤ 1 / x := by
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have hx1_pos : 0 < x + 1 := by linarith
  calc
    Real.log (x + 1) - Real.log x = Real.log ((x + 1) / x) := by
      rw [Real.log_div hx1_pos.ne' hx_ne]
    _ ≤ (x + 1) / x - 1 := Real.log_le_sub_one_of_pos (div_pos hx1_pos hx)
    _ = 1 / x := by
      field_simp [hx_ne]
      ring

/-- Harmonic-tail lower bound: for natural numbers with `1 ≤ m`,
`∑_{t=m}^{n} 1/t ≥ log(n+1) - log m`.  Proof by telescoping the pointwise bound
`1/t ≥ log(t+1) - log t`. -/
lemma harmonic_sum_ge_log_sub_log (m n : ℕ) (hm : 1 ≤ m) :
    Real.log ((n : ℝ) + 1) - Real.log (m : ℝ)
      ≤ ∑ t ∈ Finset.Icc m n, (1 : ℝ) / (t : ℝ) := by
  by_cases hmn : m ≤ n
  · induction n with
    | zero =>
        have : m = 0 := Nat.eq_zero_of_le_zero hmn
        omega
    | succ n ih =>
        by_cases hmn' : m ≤ n
        · have hstep :
            Real.log (((n : ℝ) + 1) + 1) - Real.log ((n : ℝ) + 1)
              ≤ (1 : ℝ) / ((n : ℝ) + 1) := by
            exact log_add_one_sub_log_le_inv (by positivity)
          have htel :
              Real.log (((n + 1 : ℕ) : ℝ) + 1) - Real.log (m : ℝ)
                =
              (Real.log ((n : ℝ) + 1) - Real.log (m : ℝ)) +
                (Real.log (((n : ℝ) + 1) + 1) -
                  Real.log ((n : ℝ) + 1)) := by
            norm_num
          rw [Finset.sum_Icc_succ_top hmn]
          rw [htel]
          simpa [Nat.cast_add, Nat.cast_one, add_assoc] using add_le_add (ih hmn') hstep
        · have hm_eq : m = n + 1 := by omega
          subst hm_eq
          simp only [Finset.Icc_self, Finset.sum_singleton]
          exact log_add_one_sub_log_le_inv (by positivity : 0 < ((n + 1 : ℕ) : ℝ))
  · have hlt : n < m := lt_of_not_ge hmn
    have hle : (n : ℝ) + 1 ≤ (m : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hlt
    have hlog : Real.log ((n : ℝ) + 1) ≤ Real.log (m : ℝ) := by
      exact Real.log_le_log (by positivity) hle
    rw [Finset.Icc_eq_empty hmn, Finset.sum_empty]
    linarith

private lemma log_lin_log_le_half_log_of_log_ge {c x : ℝ} (hc : 0 < c)
    (hx : 16 * c + 16 ≤ x) :
    Real.log (c * x + 1) ≤ (1 / 2) * x := by
  have hx0 : 0 ≤ x := by nlinarith
  have hpos : 0 < c * x + 1 := by nlinarith [mul_nonneg hc.le hx0]
  have hquad : c * x + 1 ≤ x ^ 2 / 16 := by
    nlinarith [sq_nonneg (x - (16 * c + 16)), hc]
  have hlin : x / 4 + 1 ≤ Real.exp (x / 4) := Real.add_one_le_exp (x / 4)
  have hlin_nonneg : 0 ≤ x / 4 + 1 := by nlinarith
  have hsq : (x / 4 + 1) ^ 2 ≤ (Real.exp (x / 4)) ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hlin_nonneg, abs_of_nonneg (Real.exp_nonneg _)] using hlin
  have hpoly : x ^ 2 / 16 ≤ (x / 4 + 1) ^ 2 := by nlinarith
  have hexp : x ^ 2 / 16 ≤ Real.exp (x / 2) := by
    calc
      x ^ 2 / 16 ≤ (x / 4 + 1) ^ 2 := hpoly
      _ ≤ (Real.exp (x / 4)) ^ 2 := hsq
      _ = Real.exp (x / 2) := by
        rw [sq]
        rw [← Real.exp_add]
        ring_nf
  calc
    Real.log (c * x + 1) ≤ Real.log (Real.exp (x / 2)) :=
      Real.log_le_log hpos (hquad.trans hexp)
    _ = (1 / 2) * x := by
      rw [Real.log_exp]
      ring_nf

/-- Sub-logarithmic growth of `log (c·log T + 1)`: for any `c > 0` there is a
threshold `N` beyond which `log (c · log T + 1) ≤ (1/2) · log T`.  This is the
`log log T = o(log T)` book-keeping that lets the harmonic tail dominate the
`t_* = Θ(log T)` cutoff.  (Route: `c·log T + 1 ≤ (log T)²/16 ≤ exp((log T)/2)`
for large `T`, then take `log`.) -/
lemma log_lin_log_le_half_log {c : ℝ} (hc : 0 < c) :
    ∃ N : ℕ, ∀ T : ℕ, N ≤ T →
      Real.log (c * Real.log (T : ℝ) + 1) ≤ (1 / 2) * Real.log (T : ℝ) := by
  have htend : Tendsto (fun T : ℕ => Real.log (T : ℝ)) atTop atTop := by
    simpa using Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.mp (htend.eventually_ge_atTop (16 * c + 16))
  exact ⟨N, fun T hT => log_lin_log_le_half_log_of_log_ge hc (hN T hT)⟩

set_option maxHeartbeats 800000 in
-- The engine proof combines several nonlinear real-arithmetic normalizations.

/-- **Sequential-experiment cumulative-risk engine.**

Let `b : ℕ → ℝ` be a per-round sequence with running totals
`B n = ∑_{t=1}^{n} b t`.  Assume the predictable van Trees / Bayes–Cramér–Rao
recursion: for every `t ≥ 1`,

    `b t ≥ (d²/4) / (Iq + (5 J / 4) · t + L · √(t · B (t-1)))`,

with `J > 0`, `d ≠ 0`, `L ≥ 0`, `Iq ≥ 0`.  Then the cumulative total grows at
least logarithmically: there is a threshold `T₀` such that for every `T ≥ T₀`,

    `B T ≥ (d² / (32 J)) · log T`.

The constant `1/32` is universal (independent of `S, J, d, L, Iq`); the threshold
`T₀` depends on all the parameters (through the local path constant `L` and the
prior information `Iq`), matching the `T₀(η)` of the writeup. -/
theorem cumulative_risk_engine
    (J d L Iq : ℝ) (hJ : 0 < J) (hd : d ≠ 0) (hL : 0 ≤ L) (hIq : 0 ≤ Iq)
    (b : ℕ → ℝ)
    (B : ℕ → ℝ) (hB : ∀ n, B n = ∑ t ∈ Finset.Icc 1 n, b t)
    (hrec : ∀ t : ℕ, 1 ≤ t →
      (d ^ 2 / 4) / (Iq + (5 * J / 4) * (t : ℝ) + L * Real.sqrt ((t : ℝ) * B (t - 1)))
        ≤ b t) :
    ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → (d ^ 2 / (32 * J)) * Real.log (T : ℝ) ≤ B T := by
  classical
  have hd2 : 0 < d ^ 2 := sq_pos_of_ne_zero hd
  have hJ_ne : J ≠ 0 := ne_of_gt hJ
  have hden_pos : ∀ t : ℕ, 1 ≤ t →
      0 < Iq + (5 * J / 4) * (t : ℝ) +
        L * Real.sqrt ((t : ℝ) * B (t - 1)) := by
    intro t ht
    have htpos : 0 < (t : ℝ) := by exact_mod_cast ht
    have hmain : 0 < (5 * J / 4) * (t : ℝ) := by positivity
    have hsqrt_nonneg : 0 ≤ L * Real.sqrt ((t : ℝ) * B (t - 1)) := by positivity
    nlinarith
  have hb_nonneg : ∀ t : ℕ, 1 ≤ t → 0 ≤ b t := by
    intro t ht
    have hnum_pos : 0 < d ^ 2 / 4 := by positivity
    have hfrac_pos :
        0 < (d ^ 2 / 4) /
          (Iq + (5 * J / 4) * (t : ℝ) + L * Real.sqrt ((t : ℝ) * B (t - 1))) := by
      positivity
    exact (hfrac_pos.le.trans (hrec t ht))
  have hB_nonneg : ∀ n : ℕ, 0 ≤ B n := by
    intro n
    rw [hB n]
    exact Finset.sum_nonneg fun t ht => hb_nonneg t ((Finset.mem_Icc.mp ht).1)
  have hB_mono : Monotone B := by
    intro n n' hnn'
    rw [hB n, hB n']
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro t ht
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ht).1,
          (Finset.mem_Icc.mp ht).2.trans hnn'⟩)
      (by
        intro t ht' ht
        exact hb_nonneg t ((Finset.mem_Icc.mp ht').1))
  let C₁ : ℝ := L ^ 2 * d ^ 2 / (8 * J ^ 3) + 1
  have hC₁_pos : 0 < C₁ := by
    have hden : 0 < 8 * J ^ 3 := by positivity
    have hfrac_nonneg : 0 ≤ L ^ 2 * d ^ 2 / (8 * J ^ 3) := by positivity
    dsimp [C₁]
    nlinarith
  obtain ⟨Nlog, hNlog⟩ := log_lin_log_le_half_log hC₁_pos
  have htend : Tendsto (fun T : ℕ => Real.log (T : ℝ)) atTop atTop := by
    simpa using Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨NIq, hNIq⟩ :=
    Filter.eventually_atTop.mp (htend.eventually_ge_atTop (4 * Iq / (J * C₁)))
  refine ⟨Nlog ⊔ NIq ⊔ 3, ?_⟩
  intro T hT
  have hTlog : Nlog ≤ T :=
    le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hT
  have hTIq : NIq ≤ T :=
    le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hT
  have hT3 : 3 ≤ T := le_trans (Nat.le_max_right _ _) hT
  let LT : ℝ := Real.log (T : ℝ)
  have hTpos_nat : 0 < T := by omega
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast hTpos_nat
  have hTone : 1 ≤ (T : ℝ) := by exact_mod_cast (by omega : 1 ≤ T)
  have hLT_nonneg : 0 ≤ LT := by simpa [LT] using Real.log_nonneg hTone
  have hLT_pos : 0 < LT := by
    have hTgt1 : (1 : ℝ) < T := by exact_mod_cast (by omega : 1 < T)
    simpa [LT] using Real.log_pos hTgt1
  have hlog_bound : Real.log (C₁ * LT + 1) ≤ (1 / 2) * LT := by
    simpa [LT] using hNlog T hTlog
  have hIq_log : 4 * Iq / (J * C₁) ≤ LT := by
    simpa [LT] using hNIq T hTIq
  by_contra hgoal
  have hBTlt : B T < (d ^ 2 / (32 * J)) * LT := by
    exact not_le.mp hgoal
  let M : ℝ := (d ^ 2 / (32 * J)) * LT
  let tstar : ℕ := Nat.ceil (C₁ * LT)
  have hcut_pos : 0 < C₁ * LT := mul_pos hC₁_pos hLT_pos
  have hcut_nonneg : 0 ≤ C₁ * LT := hcut_pos.le
  have htstar_one : 1 ≤ tstar := by
    simpa [tstar] using (Nat.one_le_ceil_iff.mpr hcut_pos)
  have htstar_lower : C₁ * LT ≤ (tstar : ℝ) := by
    simpa [tstar] using (Nat.le_ceil (C₁ * LT))
  have harg_pos : 0 < C₁ * LT + 1 := by positivity
  have harg_le_T : C₁ * LT + 1 ≤ (T : ℝ) := by
    have harg_le_exp : C₁ * LT + 1 ≤ Real.exp ((1 / 2) * LT) := by
      exact (Real.log_le_iff_le_exp harg_pos).mp hlog_bound
    have hexp_le_T : Real.exp ((1 / 2) * LT) ≤ (T : ℝ) := by
      calc
        Real.exp ((1 / 2) * LT) ≤ Real.exp LT := Real.exp_le_exp.mpr (by nlinarith)
        _ = (T : ℝ) := by simpa [LT] using Real.exp_log hTpos
    exact harg_le_exp.trans hexp_le_T
  have htstar_upper : (tstar : ℝ) ≤ C₁ * LT + 1 := by
    simpa [tstar] using (Nat.ceil_lt_add_one hcut_nonneg).le
  have htstar_le_T : tstar ≤ T := by
    rw [Nat.ceil_le]
    exact (le_add_of_nonneg_right zero_le_one).trans harg_le_T
  have hclaim : ∀ t : ℕ, tstar ≤ t → t ≤ T →
      d ^ 2 / (8 * J) * ((1 : ℝ) / (t : ℝ)) ≤ b t := by
    intro t htt htT
    have ht1 : 1 ≤ t := le_trans htstar_one htt
    have htpos : 0 < (t : ℝ) := by exact_mod_cast ht1
    have ht_nonneg : 0 ≤ (t : ℝ) := htpos.le
    have ht_lower : C₁ * LT ≤ (t : ℝ) := by
      exact htstar_lower.trans (by exact_mod_cast htt)
    have hBt_le : B (t - 1) ≤ B T := hB_mono (by omega)
    have hBt_lt : B (t - 1) < M := by
      exact hBt_le.trans_lt (by simpa [M] using hBTlt)
    have hM_nonneg : 0 ≤ M := by
      dsimp [M]
      positivity
    have hBtM : B (t - 1) ≤ M := hBt_lt.le
    have hfeedback : L * Real.sqrt ((t : ℝ) * B (t - 1)) ≤ (J / 2) * (t : ℝ) := by
      by_cases hL0 : L = 0
      · rw [hL0]
        simp only [zero_mul]
        exact mul_nonneg (div_nonneg hJ.le (by norm_num)) ht_nonneg
      · have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
        have hM_le : M ≤ (J ^ 2 / (4 * L ^ 2)) * (t : ℝ) := by
          have hpart : (L ^ 2 * d ^ 2 / (8 * J ^ 3)) * LT ≤ (t : ℝ) := by
            dsimp [C₁] at ht_lower
            nlinarith [ht_lower, hLT_nonneg]
          calc
            M = (J ^ 2 / (4 * L ^ 2)) *
                ((L ^ 2 * d ^ 2 / (8 * J ^ 3)) * LT) := by
              dsimp [M]
              field_simp [ne_of_gt hJ, ne_of_gt hLpos]
              ring
            _ ≤ (J ^ 2 / (4 * L ^ 2)) * (t : ℝ) :=
              mul_le_mul_of_nonneg_left hpart (by positivity)
        have hprod_le : (t : ℝ) * B (t - 1) ≤ ((J / (2 * L)) * (t : ℝ)) ^ 2 := by
          calc
            (t : ℝ) * B (t - 1) ≤ (t : ℝ) * M :=
              mul_le_mul_of_nonneg_left hBtM ht_nonneg
            _ ≤ (t : ℝ) * ((J ^ 2 / (4 * L ^ 2)) * (t : ℝ)) :=
              mul_le_mul_of_nonneg_left hM_le ht_nonneg
            _ = ((J / (2 * L)) * (t : ℝ)) ^ 2 := by
              field_simp [ne_of_gt hLpos]
              ring
        have hy_nonneg : 0 ≤ (J / (2 * L)) * (t : ℝ) := by positivity
        have hsqrt_le : Real.sqrt ((t : ℝ) * B (t - 1)) ≤ (J / (2 * L)) * (t : ℝ) := by
          exact (Real.sqrt_le_iff).mpr ⟨hy_nonneg, hprod_le⟩
        calc
          L * Real.sqrt ((t : ℝ) * B (t - 1))
              ≤ L * ((J / (2 * L)) * (t : ℝ)) := mul_le_mul_of_nonneg_left hsqrt_le hL
          _ = (J / 2) * (t : ℝ) := by
            field_simp [ne_of_gt hLpos]
    have hIq_le : Iq ≤ (J / 4) * (t : ℝ) := by
      have haux : Iq ≤ J / 4 * (C₁ * LT) := by
        field_simp [ne_of_gt hJ, ne_of_gt hC₁_pos] at hIq_log ⊢
        nlinarith
      have hcoef : 0 ≤ J / 4 := by positivity
      exact haux.trans (mul_le_mul_of_nonneg_left ht_lower hcoef)
    let D : ℝ :=
      Iq + (5 * J / 4) * (t : ℝ) + L * Real.sqrt ((t : ℝ) * B (t - 1))
    have hD_pos : 0 < D := by
      simpa [D] using hden_pos t ht1
    have hD_le : D ≤ 2 * J * (t : ℝ) := by
      dsimp [D]
      nlinarith [hIq_le, hfeedback]
    have hright_pos : 0 < 2 * J * (t : ℝ) := by positivity
    have hnum_nonneg : 0 ≤ d ^ 2 / 4 := by positivity
    have hfrac :
        d ^ 2 / (8 * J) * ((1 : ℝ) / (t : ℝ)) ≤ (d ^ 2 / 4) / D := by
      calc
        d ^ 2 / (8 * J) * ((1 : ℝ) / (t : ℝ)) =
            (d ^ 2 / 4) / (2 * J * (t : ℝ)) := by
          field_simp [hJ_ne, ne_of_gt htpos]
          ring
        _ ≤ (d ^ 2 / 4) / D :=
          div_le_div_of_nonneg_left hnum_nonneg hD_pos hD_le
    exact hfrac.trans (by simpa [D] using hrec t ht1)
  have htail_subset : Finset.Icc tstar T ⊆ Finset.Icc 1 T := by
    intro t ht
    exact Finset.mem_Icc.mpr
      ⟨le_trans htstar_one (Finset.mem_Icc.mp ht).1, (Finset.mem_Icc.mp ht).2⟩
  have htail_le_B :
      ∑ t ∈ Finset.Icc tstar T, b t ≤ B T := by
    rw [hB T]
    exact Finset.sum_le_sum_of_subset_of_nonneg htail_subset
      (by
        intro t htBig htSmall
        exact hb_nonneg t ((Finset.mem_Icc.mp htBig).1))
  have hscaled_tail :
      (d ^ 2 / (8 * J)) * (∑ t ∈ Finset.Icc tstar T, (1 : ℝ) / (t : ℝ))
        ≤ ∑ t ∈ Finset.Icc tstar T, b t := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun t ht =>
      hclaim t (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp ht).2
  have hharm := harmonic_sum_ge_log_sub_log tstar T htstar_one
  have hcoef_nonneg : 0 ≤ d ^ 2 / (8 * J) := by positivity
  have hlog_tail :
      (d ^ 2 / (8 * J)) *
          (Real.log ((T : ℝ) + 1) - Real.log (tstar : ℝ))
        ≤ (d ^ 2 / (8 * J)) *
          (∑ t ∈ Finset.Icc tstar T, (1 : ℝ) / (t : ℝ)) :=
    mul_le_mul_of_nonneg_left hharm hcoef_nonneg
  have hLT_le_log_succ : LT ≤ Real.log ((T : ℝ) + 1) := by
    exact Real.log_le_log hTpos (by nlinarith)
  have htstar_pos_real : 0 < (tstar : ℝ) := by exact_mod_cast htstar_one
  have hlog_tstar_le : Real.log (tstar : ℝ) ≤ Real.log (C₁ * LT + 1) := by
    exact Real.log_le_log htstar_pos_real htstar_upper
  have hlog_tstar_half : Real.log (tstar : ℝ) ≤ (1 / 2) * LT :=
    hlog_tstar_le.trans hlog_bound
  have htail_lower :
      (d ^ 2 / (8 * J)) * ((1 / 2) * LT) ≤ B T := by
    have hdiff : (1 / 2) * LT ≤ Real.log ((T : ℝ) + 1) - Real.log (tstar : ℝ) := by
      nlinarith
    exact (mul_le_mul_of_nonneg_left hdiff hcoef_nonneg).trans
      (hlog_tail.trans (hscaled_tail.trans htail_le_B))
  have hstrong : (d ^ 2 / (16 * J)) * LT ≤ B T := by
    convert htail_lower using 1
    field_simp [hJ_ne]
    ring
  have hcontr : (d ^ 2 / (32 * J)) * LT < (d ^ 2 / (16 * J)) * LT := by
    have hposcoef : 0 < d ^ 2 / (32 * J) := by positivity
    have htwice : d ^ 2 / (16 * J) = 2 * (d ^ 2 / (32 * J)) := by
      field_simp [hJ_ne]
      ring
    calc
      (d ^ 2 / (32 * J)) * LT < 2 * ((d ^ 2 / (32 * J)) * LT) := by
        nlinarith [mul_pos hposcoef hLT_pos]
      _ = (d ^ 2 / (16 * J)) * LT := by
        rw [htwice]
        ring
  exact (lt_irrefl _ (hstrong.trans_lt (hBTlt.trans hcontr))).elim

/-- **Radius-monotone cumulative Neyman-regret lower bound**
(`lem:local-neighborhood-cumulative-risk`).

Assembly of `cumulative_risk_engine` with the two measure-theoretic inputs of the
writeup taken as hypotheses: the Neyman-gap quadratic conversion
`2 S² · B T ≤ R^B_T` (Bayes-average cumulative regret dominates twice the scaled
cumulative Bayes MSE) and `R^B_T ≤ Rsup T` (the worst-case regret over the local
neighborhood dominates the Bayes average).  Under the predictable van Trees
per-round bound driving `b`, the worst-case cumulative regret is `Ω(log T)`:

    `Rsup T ≥ (S² d² / (16 J)) · log T`  for all `T ≥ T₀`,

with universal constant `1/16`.  This is the target radius-monotone lemma; the
van Trees inequality itself (`lem:bayes-cramer-rao-predictable`) and the
Neyman-gap identity (`lem:neyman-gap-identity`) enter only through the assumed
hypotheses `hrec`, `hconv`, `hsup`. -/
theorem sequential_cumulative_risk_regret
    (S J d L Iq : ℝ) (hS : 0 < S) (hJ : 0 < J) (hd : d ≠ 0)
    (hL : 0 ≤ L) (hIq : 0 ≤ Iq)
    (b B RB Rsup : ℕ → ℝ) (hB : ∀ n, B n = ∑ t ∈ Finset.Icc 1 n, b t)
    (hrec : ∀ t : ℕ, 1 ≤ t →
      (d ^ 2 / 4) / (Iq + (5 * J / 4) * (t : ℝ) + L * Real.sqrt ((t : ℝ) * B (t - 1)))
        ≤ b t)
    (hconv : ∀ T : ℕ, 2 * S ^ 2 * B T ≤ RB T)
    (hsup : ∀ T : ℕ, RB T ≤ Rsup T) :
    ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T →
      (S ^ 2 * d ^ 2 / (16 * J)) * Real.log (T : ℝ) ≤ Rsup T := by
  rcases cumulative_risk_engine J d L Iq hJ hd hL hIq b B hB hrec with ⟨T₀, hBT⟩
  refine ⟨T₀, ?_⟩
  intro T hT
  have hbase := hBT T hT
  have hscale_nonneg : 0 ≤ 2 * S ^ 2 := by positivity
  have hscaled :
      2 * S ^ 2 * ((d ^ 2 / (32 * J)) * Real.log (T : ℝ)) ≤
        2 * S ^ 2 * B T :=
    mul_le_mul_of_nonneg_left hbase hscale_nonneg
  have hchain :
      2 * S ^ 2 * ((d ^ 2 / (32 * J)) * Real.log (T : ℝ)) ≤ Rsup T :=
    hscaled.trans ((hconv T).trans (hsup T))
  convert hchain using 1
  field_simp [ne_of_gt hJ]
  ring

end Causalean.Stat
