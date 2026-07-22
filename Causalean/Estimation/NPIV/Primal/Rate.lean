/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# TRAE primal estimator: rate theorem (`thm:est-trae-rate-theorem`)

Defines the headline rate theorem of
`doc/basic_concepts/po/estimation/trae_inverse_problems.tex` (lines
174–384, simplified proof following Theorem 101 of the lecture notes).

The theorem states: with probability ≥ 1−ζ over the nuisance fold `A(n)`,
the strong and weak inverse-problem rates hold simultaneously,

    ‖ĥ_n − h₀‖²_{L²(P_X)}
        = O(δ_n² / λ + ‖w₀‖_{L²(P_X)} λ^{min(β, 1)}),
    ‖T(ĥ_n − h₀)‖²_{L²(P_Z)}
        = O(δ_n² + ‖w₀‖_{L²(P_X)} λ^{min(β+1, 2)}).

## Decomposition (per the simplified proof)

The proof factors as:

* **Population strong convexity** (deterministic) — exposed as a field
  of `TikhonovBiasBound`.  Says
      λ‖ĥ − h*‖² + ‖T(ĥ − h*)‖² ≤ SC_RHS(ĥ, h*, h₀, λ),
  where `SC_RHS` is the right-hand side of the SC inequality
  (note line 299).

* **Empirical-process / centred-regulariser event** (probabilistic) —
  hypothesis field `empirical_process_event` of
  `TRAERatePrimalAbstractHyps`.
  On a high-probability event, bounds `SC_RHS` by a sum involving
  `R_b²`, `δ_n‖TΔ_n‖`, `δ_n²`, `λδ_n‖Δ_n‖`, `λδ_n²`.  This is the
  combined output of:
    - the EP inequality (note line 308) and
    - the centred-regulariser bound (note line 345).

  The localized wrapper `trae_primal_rate` discharges this through
  `empirical_process_event_of_absorption`, using the four critical-radius
  regimes for `star(H·F), star(m∘F), star(F), star(H)`.

* **Combined-metric rate** (deterministic helper
  `combined_metric_rate`) — chains SC + `empirical_process_event` and
  absorbs the cross terms by AM-GM:
      λ‖Δ‖² + ‖TΔ‖² ≤ K · (R_b² + δ_n²).

* **Strong/weak rates** (deterministic helpers
  `strong_rate_from_combined`, `weak_rate_from_combined`) — apply
  triangle inequality and the two `TikhonovBiasBound` bias bounds to
  the combined inequality.

* **Abstract `trae_primal_rate_from_empirical_process`** assembles the
  deterministic steps once the empirical-process event has already been
  discharged.  The paper-facing localized theorem lives in
  `EmpiricalProcessEvent.EventAssembly.lean`.
-/

import Causalean.Estimation.NPIV.SourceCondition
import Causalean.Estimation.NPIV.Primal.Estimator
import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.EventAssembly
import Causalean.Stat.Concentration.UniformDeviation.UniformDeviationLocalized
import Causalean.Stat.Concentration.UniformDeviation.CriticalRadius

/-!
# Primal NPIV Rate Theorems

This file packages the hypotheses and convergence-rate theorems for the
non-iterated TRAE primal estimator.  `TRAERatePrimalHyps` records the
deterministic source, Tikhonov-bias, closedness, continuity, and boundedness
assumptions, while `TRAERatePrimalAbstractHyps` adds an already-discharged
empirical-process event.  The helper theorems `combined_metric_rate`,
`strong_rate_from_combined`, and `weak_rate_from_combined` turn those inputs into
strong and weak inverse-problem rates, `trae_primal_rate_from_empirical_process`
assembles the abstract theorem, and `trae_primal_rate` is the localized-regime
wrapper that builds the empirical-process event before invoking the abstract
rate theorem.
-/

namespace Causalean
namespace Estimation
namespace NPIV
namespace Primal

open MeasureTheory Causalean.Stat Causalean.Stat.Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Hypothesis bundle for `thm:est-trae-rate-theorem` -/

/-- Deterministic, paper-facing hypotheses for `thm:est-trae-rate-theorem`.

This bundle deliberately excludes the empirical-process event.  It is the
shared deterministic input used both by the abstract rate theorem below and by
the localized-discharge wrapper in
`EmpiricalProcessEvent.EventAssembly.lean`.

The confidence level `ζ` is a parameter of the bundle because the empirical-
process event supplied by the localized wrapper is discharged at this fixed
confidence level. -/
structure TRAERatePrimalHyps
    (S : OperatorSystem Ω μ) (TC : TRAEClasses S)
    {P_W : Measure S.𝒲}
    (sample : IIDSample Ω S.𝒲 μ P_W)
    (split : OneShotSplit sample)
    (lambda β ζ : ℝ) (delta : ℕ → ℝ)
    (h_hat : ℕ → Ω → S.𝒳 → ℝ)
    (is_estimator : IsTRAEPrimalEstimator S TC sample split lambda h_hat) where
  /-- (a) β-source condition at `h₀`. -/
  source_condition : SourceCondition S β
  /-- (b) Tikhonov bias certificate at level `λ`.

      This field is not an additional unresolved bias proof.  It packages the
      already-proved Tikhonov approximation bounds together with the population
      strong-convexity inequality at the chosen regularization level.  In
      spectral applications the certificate is supplied by
      `SpectralSourceCondition.tikhonov_bias_from_spectral`; the primal-rate
      theorem keeps it abstract so other source-condition arguments can reuse
      the same deterministic rate algebra. -/
  tikhonov_bias : TikhonovBiasBound S β lambda source_condition
  /-- (c) Realizability: the population Tikhonov solution `h*_λ` lies in
      the statistical class `H`. -/
  realizability : tikhonov_bias.h_lambda_star_fun ∈ TC.H
  /-- (d) **Closedness (Hilbert form)** of the critic class for primal
      residuals: there is a critic `f ∈ F` whose `L²` lift coincides with
      the projected residual `T(h₀ − h)` as elements of `Lp ℝ 2 μ`
      (proof sketch line 217).  This is the standard NPIV closedness
      hypothesis (Dikkala–Lewis–Mackey–Syrgkanis; Chen–Pouzo); a weak
      (test-against-`Qbar` inner-product) form does not suffice unless
      `{q_L2 g | g ∈ Qbar}` is total in `Qbar_L2`, which the
      `OperatorSystem` interface does not currently assert. -/
  closedness :
    ∀ h, ∀ hh : h ∈ TC.H,
      ∃ f, ∃ hf : f ∈ TC.F,
        S.T (S.hL2 S.h₀_mem - S.hL2 (TC.H_subset hh))
          = S.qL2 (TC.F_subset hf)
  /-- (e) Mean-square continuity of `m` on critics:
      `E[m(W; f)²] ≤ C_m · ‖f‖²_{L²(P_Z)}` for every `f ∈ F`. -/
  msc :
    ∃ Cm : ℝ, 0 ≤ Cm ∧
      ∀ f, ∀ hf : f ∈ TC.F,
        ∫ ω, (S.m (S.W ω) f) ^ 2 ∂μ
          ≤ Cm * S.strongNorm (S.qL2 (TC.F_subset hf)) ^ 2
  /-- (f) Almost-sure uniform boundedness of `m(W; f), h(X), f(Z)` over
      `h ∈ H, f ∈ F`. -/
  bounded :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ᵐ ω ∂μ,
        (∀ f ∈ TC.F, |S.m (S.W ω) f| ≤ B) ∧
        (∀ h ∈ TC.H, |h (S.xOf (S.W ω))| ≤ B) ∧
        (∀ f ∈ TC.F, |f (S.zOf (S.W ω))| ≤ B))
/-- `TRAERatePrimalAbstractHyps` packages the deterministic paper hypotheses
together with the already-discharged empirical-process / centred-regulariser
event.

The key probabilistic hypothesis is `empirical_process_event`, which
bounds the right-hand side of the strong-convexity inequality by a
deterministic-looking expression on a high-probability event.  This
abstracts away the localized empirical-process and centred-regulariser
arguments (note lines 306–348); the localized wrapper discharges it from the
class-specific localized deviation events. -/
structure TRAERatePrimalAbstractHyps
    (S : OperatorSystem Ω μ) (TC : TRAEClasses S)
    {P_W : Measure S.𝒲}
    (sample : IIDSample Ω S.𝒲 μ P_W)
    (split : OneShotSplit sample)
    (lambda β ζ : ℝ) (delta : ℕ → ℝ)
    (h_hat : ℕ → Ω → S.𝒳 → ℝ)
    (is_estimator : IsTRAEPrimalEstimator S TC sample split lambda h_hat)
    extends TRAERatePrimalHyps S TC sample split lambda β ζ delta h_hat
      is_estimator where
  /-- (h) **Empirical-process / centred-regulariser event.**

      For the fixed confidence level `ζ ∈ (0, 1)`, there is an event
      `Aζ ⊆ Ω` of mass `≥ 1 − ζ` and a constant `K_ep ≥ 0` such that for
      all `ω ∈ Aζ` and all `n`, the right-hand side of the strong-
      convexity inequality is bounded:

          [‖T(ĥ_n − h₀)‖² − ‖T(h*_λ − h₀)‖²] + λ(‖ĥ_n‖² − ‖h*_λ‖²)
            ≤ K_ep · (‖T(h*_λ − h₀)‖²
                       + δ_n · ‖T(ĥ_n − h*_λ)‖
                       + δ_n²
                       + λ · δ_n · ‖ĥ_n − h*_λ‖
                       + λ · δ_n²).

      This is the post-substitution form of the EP inequality
      (note line 308) combined with the centred-regulariser bound
      (note line 345). The localized theorem discharges it from the
      class-specific localized deviation events. -/
  empirical_process_event :
    0 < ζ → ζ < 1 →
      ∃ Aζ : Set Ω, ∃ K_ep : ℝ,
        MeasurableSet Aζ ∧ μ Aζ ≥ 1 - ENNReal.ofReal ζ ∧ 0 ≤ K_ep ∧
          ∀ ω ∈ Aζ, ∀ n : ℕ,
            (S.weakNorm
                (S.hL2 (TC.H_subset (is_estimator.mem_H n ω))
                  - S.hL2 S.h₀_mem)) ^ 2
              - (S.weakNorm
                  (S.hL2 tikhonov_bias.h_lambda_star_mem
                    - S.hL2 S.h₀_mem)) ^ 2
              + lambda *
                  ((S.strongNorm
                        (S.hL2 (TC.H_subset (is_estimator.mem_H n ω)))) ^ 2
                    - (S.strongNorm (S.hL2 tikhonov_bias.h_lambda_star_mem)) ^ 2)
              ≤ K_ep *
                  ((S.weakNorm
                      (S.hL2 tikhonov_bias.h_lambda_star_mem
                        - S.hL2 S.h₀_mem)) ^ 2
                    + delta n *
                        S.weakNorm
                          (S.hL2 (TC.H_subset (is_estimator.mem_H n ω))
                            - S.hL2 tikhonov_bias.h_lambda_star_mem)
                    + (delta n) ^ 2
                    + lambda * delta n *
                        S.strongNorm
                          (S.hL2 (TC.H_subset (is_estimator.mem_H n ω))
                            - S.hL2 tikhonov_bias.h_lambda_star_mem)
                    + lambda * (delta n) ^ 2)

/-! ## Deterministic helper lemmas

The proof of `trae_primal_rate_from_empirical_process` factors through three
deterministic lemmas, each consuming one or more fields of
`TRAERatePrimalAbstractHyps`. -/

private lemma combined_metric_algebra
    (K_ep lambda x y r d : ℝ)
    (hKep_nonneg : 0 ≤ K_ep) (lambda_pos : 0 < lambda) (lambda_lt : lambda < 2)
    (hx_nonneg : 0 ≤ x) (hy_nonneg : 0 ≤ y) (_hr_nonneg : 0 ≤ r)
    (h_chain :
      lambda * x ^ 2 + y ^ 2
        ≤ K_ep * (r ^ 2 + d * y + d ^ 2 + lambda * d * x + lambda * d ^ 2)) :
    lambda * x ^ 2 + y ^ 2
      ≤ (4 * (K_ep ^ 2 + K_ep + 1)) * (r ^ 2 + d ^ 2) := by
  have hd_abs_nonneg : 0 ≤ |d| := abs_nonneg d
  have hdy0 : K_ep * d * y ≤ K_ep * |d| * y := by
    have : d ≤ |d| := le_abs_self d
    nlinarith [mul_nonneg hKep_nonneg hy_nonneg]
  have hdy1 : K_ep * |d| * y ≤ K_ep ^ 2 * d ^ 2 + y ^ 2 / 4 := by
    have hsq : 0 ≤ (K_ep * |d| - y / 2) ^ 2 :=
      sq_nonneg (K_ep * |d| - y / 2)
    nlinarith [abs_mul_abs_self d]
  have hdx0 : K_ep * lambda * d * x ≤ K_ep * lambda * |d| * x := by
    have : d ≤ |d| := le_abs_self d
    nlinarith [mul_nonneg (mul_nonneg hKep_nonneg (le_of_lt lambda_pos)) hx_nonneg]
  have hdx1 :
      K_ep * lambda * |d| * x
        ≤ K_ep ^ 2 * lambda * d ^ 2 + lambda * x ^ 2 / 4 := by
    have hsq : 0 ≤ (K_ep * |d| - x / 2) ^ 2 :=
      sq_nonneg (K_ep * |d| - x / 2)
    have h_lam_nonneg : 0 ≤ lambda := le_of_lt lambda_pos
    have hbase :
        K_ep * |d| * x ≤ K_ep ^ 2 * d ^ 2 + x ^ 2 / 4 := by
      nlinarith [hsq, abs_mul_abs_self d]
    nlinarith [mul_le_mul_of_nonneg_left hbase h_lam_nonneg]
  have hlamd : K_ep * lambda * d ^ 2 ≤ 2 * K_ep * d ^ 2 := by
    have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
    nlinarith [mul_nonneg hKep_nonneg hd2]
  have hmain :
      lambda * x ^ 2 + y ^ 2
        ≤ K_ep * r ^ 2 + K_ep * d ^ 2 + 2 * K_ep * d ^ 2
            + K_ep ^ 2 * d ^ 2 + K_ep ^ 2 * lambda * d ^ 2
            + (lambda * x ^ 2 + y ^ 2) / 4 := by
    nlinarith [h_chain, hdy0, hdy1, hdx0, hdx1, hlamd]
  have hkd_lam : K_ep ^ 2 * lambda * d ^ 2 ≤ 2 * K_ep ^ 2 * d ^ 2 := by
    have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
    have hk2 : 0 ≤ K_ep ^ 2 := sq_nonneg K_ep
    nlinarith [mul_nonneg hk2 hd2]
  have hthree :
      (3 / 4 : ℝ) * (lambda * x ^ 2 + y ^ 2)
        ≤ K_ep * r ^ 2 + (3 * K_ep + 3 * K_ep ^ 2) * d ^ 2 := by
    nlinarith [hmain, hkd_lam]
  have hbound :
      K_ep * r ^ 2 + (3 * K_ep + 3 * K_ep ^ 2) * d ^ 2
        ≤ (3 * (K_ep ^ 2 + K_ep + 1)) * (r ^ 2 + d ^ 2) := by
    have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
    have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
    nlinarith [mul_nonneg hKep_nonneg hr2,
      mul_nonneg (by nlinarith [sq_nonneg K_ep]) hd2]
  nlinarith [hthree, hbound]

/-- **Combined-metric rate** (helper, deterministic).

Combines population strong convexity (`tikhonov_bias.strong_convexity`)
with the empirical-process event to produce a clean combined-metric
inequality, on the same high-probability event.  After AM-GM
absorption (note lines 349–360):

    λ‖ĥ_n − h*_λ‖² + ‖T(ĥ_n − h*_λ)‖² ≤ K · (‖T(h*_λ − h₀)‖² + δ_n²).

Holds for all `ω ∈ Aζ` and all `n`. -/
theorem combined_metric_rate
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    {split : OneShotSplit sample}
    {lambda β ζ : ℝ} {delta : ℕ → ℝ}
    {h_hat : ℕ → Ω → S.𝒳 → ℝ}
    {is_estimator : IsTRAEPrimalEstimator S TC sample split lambda h_hat}
    (hyps : TRAERatePrimalAbstractHyps S TC sample split lambda β ζ delta h_hat is_estimator)
    (lambda_pos : 0 < lambda) (lambda_lt : lambda < 2)
    (hζ_pos : 0 < ζ) (hζ_lt : ζ < 1) :
    ∃ Aζ : Set Ω, ∃ K : ℝ,
      MeasurableSet Aζ ∧ μ Aζ ≥ 1 - ENNReal.ofReal ζ ∧ 0 ≤ K ∧
        ∀ ω ∈ Aζ, ∀ n : ℕ,
          lambda *
              (S.strongNorm
                (S.hL2 (TC.H_subset (is_estimator.mem_H n ω))
                  - S.hL2 hyps.tikhonov_bias.h_lambda_star_mem)) ^ 2
            + (S.weakNorm
                (S.hL2 (TC.H_subset (is_estimator.mem_H n ω))
                  - S.hL2 hyps.tikhonov_bias.h_lambda_star_mem)) ^ 2
            ≤ K *
                ((S.weakNorm
                    (S.hL2 hyps.tikhonov_bias.h_lambda_star_mem
                      - S.hL2 S.h₀_mem)) ^ 2
                  + (delta n) ^ 2) := by
  rcases hyps.empirical_process_event hζ_pos hζ_lt with
    ⟨Aζ, K_ep, hAζ_meas, hAζ_prob, hKep_nonneg, h_ep⟩
  refine ⟨Aζ, 4 * (K_ep ^ 2 + K_ep + 1), hAζ_meas, hAζ_prob, ?_, ?_⟩
  · nlinarith [sq_nonneg K_ep]
  · intro ω hω n
    let h_mem : h_hat n ω ∈ S.Hbar := TC.H_subset (is_estimator.mem_H n ω)
    let x : ℝ :=
      S.strongNorm
        (S.hL2 h_mem - S.hL2 hyps.tikhonov_bias.h_lambda_star_mem)
    let y : ℝ :=
      S.weakNorm
        (S.hL2 h_mem - S.hL2 hyps.tikhonov_bias.h_lambda_star_mem)
    let r : ℝ :=
      S.weakNorm
        (S.hL2 hyps.tikhonov_bias.h_lambda_star_mem - S.hL2 S.h₀_mem)
    let d : ℝ := delta n
    have hx_nonneg : 0 ≤ x := by
      simp [x, OperatorSystem.strongNorm]
    have hy_nonneg : 0 ≤ y := by
      simp [y, OperatorSystem.weakNorm]
    have hr_nonneg : 0 ≤ r := by
      simp [r, OperatorSystem.weakNorm]
    have h_sc :
        lambda * x ^ 2 + y ^ 2
          ≤ (S.weakNorm (S.hL2 h_mem - S.hL2 S.h₀_mem)) ^ 2
              - r ^ 2
              + lambda *
                  ((S.strongNorm (S.hL2 h_mem)) ^ 2
                    - (S.strongNorm
                        (S.hL2 hyps.tikhonov_bias.h_lambda_star_mem)) ^ 2) := by
      simpa [h_mem, x, y, r] using
        hyps.tikhonov_bias.strong_convexity (h_hat n ω) h_mem
    have h_emp :
        (S.weakNorm (S.hL2 h_mem - S.hL2 S.h₀_mem)) ^ 2
              - r ^ 2
              + lambda *
                  ((S.strongNorm (S.hL2 h_mem)) ^ 2
                    - (S.strongNorm
                        (S.hL2 hyps.tikhonov_bias.h_lambda_star_mem)) ^ 2)
          ≤ K_ep * (r ^ 2 + d * y + d ^ 2 + lambda * d * x + lambda * d ^ 2) := by
      simpa [h_mem, x, y, r, d] using h_ep ω hω n
    have h_chain :
        lambda * x ^ 2 + y ^ 2
          ≤ K_ep * (r ^ 2 + d * y + d ^ 2 + lambda * d * x + lambda * d ^ 2) := by
      linarith
    have h_alg :
        lambda * x ^ 2 + y ^ 2
          ≤ (4 * (K_ep ^ 2 + K_ep + 1)) * (r ^ 2 + d ^ 2) := by
      exact combined_metric_algebra K_ep lambda x y r d hKep_nonneg lambda_pos lambda_lt
        hx_nonneg hy_nonneg hr_nonneg h_chain
    simpa [h_mem, x, y, r, d] using h_alg

/-- **Strong rate** (helper, deterministic).

From the combined-metric inequality and `tikhonov_bias.strong_bias`,
plus the triangle inequality, derive the strong-metric rate

    ‖ĥ_n − h₀‖² ≤ C_strong · (δ_n²/λ + ‖w₀‖ · λ^{min(β,1)}).

(Note lines 361–382.) -/
theorem strong_rate_from_combined
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    {split : OneShotSplit sample}
    {lambda β ζ : ℝ} {delta : ℕ → ℝ}
    {h_hat : ℕ → Ω → S.𝒳 → ℝ}
    {is_estimator : IsTRAEPrimalEstimator S TC sample split lambda h_hat}
    (hyps : TRAERatePrimalAbstractHyps S TC sample split lambda β ζ delta h_hat is_estimator)
    (lambda_pos : 0 < lambda) (lambda_lt : lambda < 2)
    {Aζ : Set Ω} {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (h_combined :
      ∀ ω ∈ Aζ, ∀ n : ℕ,
        lambda *
            (S.strongNorm
              (S.hL2 (TC.H_subset (is_estimator.mem_H n ω))
                - S.hL2 hyps.tikhonov_bias.h_lambda_star_mem)) ^ 2
          + (S.weakNorm
              (S.hL2 (TC.H_subset (is_estimator.mem_H n ω))
                - S.hL2 hyps.tikhonov_bias.h_lambda_star_mem)) ^ 2
          ≤ K *
              ((S.weakNorm
                  (S.hL2 hyps.tikhonov_bias.h_lambda_star_mem
                    - S.hL2 S.h₀_mem)) ^ 2
                + (delta n) ^ 2)) :
    ∃ C_strong : ℝ, 0 ≤ C_strong ∧
      ∀ ω ∈ Aζ, ∀ n : ℕ,
        (S.strongNorm
            (S.hL2 (TC.H_subset (is_estimator.mem_H n ω)) - S.hL2 S.h₀_mem)) ^ 2
          ≤ C_strong *
              ((delta n) ^ 2 / lambda
                + S.strongNorm (S.hL2 hyps.source_condition.w₀_mem) *
                    lambda ^ (min β 1)) := by
  let Cb : ℝ := hyps.tikhonov_bias.C
  refine ⟨2 * K + 2 * K * Cb + 4 * Cb, ?_, ?_⟩
  · have hCb_nonneg : 0 ≤ Cb := hyps.tikhonov_bias.C_nonneg
    nlinarith [hK_nonneg, hCb_nonneg]
  · intro ω hω n
    set hhatL2 : Lp ℝ 2 μ :=
      S.hL2 (TC.H_subset (is_estimator.mem_H n ω)) with hhhatL2
    set hstarL2 : Lp ℝ 2 μ :=
      S.hL2 hyps.tikhonov_bias.h_lambda_star_mem with hhstarL2
    set h0L2 : Lp ℝ 2 μ := S.hL2 S.h₀_mem with hh0L2
    set Δ_strong : ℝ := S.strongNorm (hhatL2 - hstarL2) with hΔ_strong
    set B_strong : ℝ := S.strongNorm (hstarL2 - h0L2) with hB_strong
    set R_b : ℝ := S.weakNorm (hstarL2 - h0L2) with hR_b
    set W₀ : ℝ := S.strongNorm (S.hL2 hyps.source_condition.w₀_mem) with hW₀
    set U : ℝ := S.strongNorm (hhatL2 - h0L2) with hU
    set X : ℝ := (delta n) ^ 2 / lambda with hX
    set Y : ℝ := W₀ * lambda ^ (min β 1) with hY
    have h_lambda_nonneg : 0 ≤ lambda := le_of_lt lambda_pos
    have hΔ_nonneg : 0 ≤ Δ_strong := by
      simp [hΔ_strong, OperatorSystem.strongNorm]
    have hB_nonneg : 0 ≤ B_strong := by
      simp [hB_strong, OperatorSystem.strongNorm]
    have hU_nonneg : 0 ≤ U := by
      simp [hU, OperatorSystem.strongNorm]
    have hRb_sq_nonneg : 0 ≤ R_b ^ 2 := sq_nonneg R_b
    have hδ_sq_nonneg : 0 ≤ (delta n) ^ 2 := sq_nonneg (delta n)
    have hW₀_nonneg : 0 ≤ W₀ := by
      simp [hW₀, OperatorSystem.strongNorm]
    have hY_nonneg : 0 ≤ Y := by
      have hp : 0 ≤ lambda ^ (min β 1) := Real.rpow_nonneg h_lambda_nonneg _
      exact mul_nonneg hW₀_nonneg hp
    have hX_nonneg : 0 ≤ X := by
      rw [hX]
      exact div_nonneg hδ_sq_nonneg h_lambda_nonneg
    have h_exp_weak : min (β + 1) 2 - 1 = min β 1 := by
      by_cases hβ : β ≤ 1
      · have hβ1 : β + 1 ≤ 2 := by linarith
        have hmin1 : min (β + 1) 2 = β + 1 := min_eq_left hβ1
        have hmin2 : min β 1 = β := min_eq_left hβ
        linarith
      · have hβge : 1 ≤ β := le_of_not_ge hβ
        have hβ1 : 2 ≤ β + 1 := by linarith
        have hmin1 : min (β + 1) 2 = 2 := min_eq_right hβ1
        have hmin2 : min β 1 = 1 := min_eq_right hβge
        linarith
    have h_weak_pow_div :
        lambda ^ (min (β + 1) 2) / lambda = lambda ^ (min β 1) := by
      rw [← Real.rpow_sub_one lambda_pos.ne']
      rw [h_exp_weak]
    have h_strong_pow :
        lambda ^ (min β 2) ≤ 2 * lambda ^ (min β 1) := by
      by_cases hβ : β ≤ 1
      · have hβ2 : β ≤ 2 := le_trans hβ (by norm_num)
        rw [min_eq_left hβ2, min_eq_left hβ]
        have hpow_nonneg : 0 ≤ lambda ^ β := Real.rpow_nonneg h_lambda_nonneg _
        exact le_mul_of_one_le_left hpow_nonneg (by norm_num : (1 : ℝ) ≤ 2)
      · have hβge1 : 1 ≤ β := le_of_not_ge hβ
        have hmin1 : min β 1 = 1 := min_eq_right hβge1
        rw [hmin1]
        by_cases hle : lambda ≤ 1
        · have h_exp : (1 : ℝ) ≤ min β 2 := le_min hβge1 (by norm_num)
          have hp : lambda ^ (min β 2) ≤ lambda ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge lambda_pos hle h_exp
          have hp2 : lambda ^ (1 : ℝ) ≤ 2 * lambda ^ (1 : ℝ) := by
            have hpow_nonneg : 0 ≤ lambda ^ (1 : ℝ) := Real.rpow_nonneg h_lambda_nonneg _
            exact le_mul_of_one_le_left hpow_nonneg (by norm_num : (1 : ℝ) ≤ 2)
          simpa [Real.rpow_one] using hp.trans hp2
        · have hge1 : 1 ≤ lambda := le_of_not_ge hle
          have h_exp2 : min β 2 ≤ 2 := min_le_right β 2
          have hp : lambda ^ (min β 2) ≤ lambda ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hge1 h_exp2
          have hp2 : lambda ^ (2 : ℝ) ≤ 2 * lambda := by
            rw [Real.rpow_two]
            nlinarith
          simpa [Real.rpow_one] using hp.trans hp2
    have htri : U ≤ Δ_strong + B_strong := by
      have hdecomp : hhatL2 - h0L2 = (hhatL2 - hstarL2) + (hstarL2 - h0L2) := by
        abel
      rw [hU, hΔ_strong, hB_strong, OperatorSystem.strongNorm]
      calc
        ‖hhatL2 - h0L2‖ = ‖(hhatL2 - hstarL2) + (hstarL2 - h0L2)‖ := by
          rw [hdecomp]
        _ ≤ ‖hhatL2 - hstarL2‖ + ‖hstarL2 - h0L2‖ := norm_add_le _ _
    have hU_sq : U ^ 2 ≤ 2 * (Δ_strong ^ 2 + B_strong ^ 2) := by
      have hsq_le : U ^ 2 ≤ (Δ_strong + B_strong) ^ 2 := by
        nlinarith [htri, hU_nonneg, hΔ_nonneg, hB_nonneg,
          sq_nonneg (Δ_strong + B_strong - U)]
      exact hsq_le.trans (add_sq_le : (Δ_strong + B_strong) ^ 2
        ≤ 2 * (Δ_strong ^ 2 + B_strong ^ 2))
    have hcombined' :
        lambda * Δ_strong ^ 2
          + (S.weakNorm (hhatL2 - hstarL2)) ^ 2
          ≤ K * (R_b ^ 2 + (delta n) ^ 2) := by
      simpa [hhhatL2, hhstarL2, hh0L2, hΔ_strong, hR_b]
        using h_combined ω hω n
    have hdrop : lambda * Δ_strong ^ 2 ≤ K * (R_b ^ 2 + (delta n) ^ 2) := by
      have hweak_nonneg : 0 ≤ (S.weakNorm (hhatL2 - hstarL2)) ^ 2 := sq_nonneg _
      nlinarith
    have hΔ_sq :
        Δ_strong ^ 2 ≤ K * (R_b ^ 2 / lambda + (delta n) ^ 2 / lambda) := by
      have hdiv := div_le_div_of_nonneg_right hdrop h_lambda_nonneg
      calc
        Δ_strong ^ 2 = lambda * Δ_strong ^ 2 / lambda := by
          field_simp [lambda_pos.ne']
        _ ≤ K * (R_b ^ 2 + (delta n) ^ 2) / lambda := hdiv
        _ = K * (R_b ^ 2 / lambda + (delta n) ^ 2 / lambda) := by
          field_simp [lambda_pos.ne']
    have hRb_div : R_b ^ 2 / lambda ≤ Cb * Y := by
      have hbias := hyps.tikhonov_bias.weak_bias
      have hbias' : R_b ^ 2 ≤ Cb * W₀ * lambda ^ (min (β + 1) 2) := by
        simpa [Cb, hR_b, hW₀, hhstarL2, hh0L2] using hbias
      have hdiv :=
        div_le_div_of_nonneg_right hbias' h_lambda_nonneg
      calc
        R_b ^ 2 / lambda ≤ (Cb * W₀ * lambda ^ (min (β + 1) 2)) / lambda := hdiv
        _ = Cb * Y := by
          rw [hY]
          rw [mul_div_assoc, h_weak_pow_div]
          ring
    have hΔ_sq_bound : Δ_strong ^ 2 ≤ K * X + K * Cb * Y := by
      calc
        Δ_strong ^ 2
            ≤ K * (R_b ^ 2 / lambda + (delta n) ^ 2 / lambda) := hΔ_sq
        _ ≤ K * (Cb * Y + X) := by
          gcongr
        _ = K * X + K * Cb * Y := by ring
    have hB_sq_bound : B_strong ^ 2 ≤ 2 * Cb * Y := by
      have hbias := hyps.tikhonov_bias.strong_bias
      have hbias' : B_strong ^ 2 ≤ Cb * W₀ * lambda ^ (min β 2) := by
        simpa [Cb, hB_strong, hW₀, hhstarL2, hh0L2] using hbias
      have hCbW_nonneg : 0 ≤ Cb * W₀ := by
        exact mul_nonneg hyps.tikhonov_bias.C_nonneg hW₀_nonneg
      calc
        B_strong ^ 2 ≤ Cb * W₀ * lambda ^ (min β 2) := hbias'
        _ ≤ Cb * W₀ * (2 * lambda ^ (min β 1)) := by
          gcongr
        _ = 2 * Cb * Y := by
          rw [hY]
          ring
    calc
      (S.strongNorm
          (S.hL2 (TC.H_subset (is_estimator.mem_H n ω)) - S.hL2 S.h₀_mem)) ^ 2
          = U ^ 2 := by simp [hU, hhhatL2, hh0L2]
      _ ≤ 2 * (Δ_strong ^ 2 + B_strong ^ 2) := hU_sq
      _ ≤ 2 * K * X + (2 * K * Cb + 4 * Cb) * Y := by
        have hsum :
            Δ_strong ^ 2 + B_strong ^ 2
              ≤ (K * X + K * Cb * Y) + 2 * Cb * Y :=
          add_le_add hΔ_sq_bound hB_sq_bound
        calc
          2 * (Δ_strong ^ 2 + B_strong ^ 2)
              ≤ 2 * ((K * X + K * Cb * Y) + 2 * Cb * Y) := by
            exact mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2)
          _ = 2 * K * X + (2 * K * Cb + 4 * Cb) * Y := by ring
      _ ≤ (2 * K + 2 * K * Cb + 4 * Cb) * (X + Y) := by
        have hCb_nonneg : 0 ≤ Cb := hyps.tikhonov_bias.C_nonneg
        have hA_nonneg : 0 ≤ 2 * K :=
          mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hK_nonneg
        have hBcoeff_nonneg : 0 ≤ 2 * K * Cb + 4 * Cb := by
          exact add_nonneg
            (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hK_nonneg) hCb_nonneg)
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hCb_nonneg)
        have hX_le_sum : X ≤ X + Y := le_add_of_nonneg_right hY_nonneg
        have hY_le_sum : Y ≤ X + Y := le_add_of_nonneg_left hX_nonneg
        have hAX : (2 * K) * X ≤ (2 * K) * (X + Y) :=
          mul_le_mul_of_nonneg_left hX_le_sum hA_nonneg
        have hBY :
            (2 * K * Cb + 4 * Cb) * Y
              ≤ (2 * K * Cb + 4 * Cb) * (X + Y) :=
          mul_le_mul_of_nonneg_left hY_le_sum hBcoeff_nonneg
        calc
          2 * K * X + (2 * K * Cb + 4 * Cb) * Y
              = (2 * K) * X + (2 * K * Cb + 4 * Cb) * Y := by ring
          _ ≤ (2 * K) * (X + Y) + (2 * K * Cb + 4 * Cb) * (X + Y) :=
            add_le_add hAX hBY
          _ = (2 * K + 2 * K * Cb + 4 * Cb) * (X + Y) := by ring
      _ = (2 * K + 2 * K * Cb + 4 * Cb) *
            ((delta n) ^ 2 / lambda
              + S.strongNorm (S.hL2 hyps.source_condition.w₀_mem) *
                  lambda ^ (min β 1)) := by
        rw [hX, hY, hW₀]

/-- **Weak rate** (helper, deterministic).

From the combined-metric inequality and `tikhonov_bias.weak_bias`,
plus the triangle inequality, derive the weak-metric rate

    ‖T(ĥ_n − h₀)‖² ≤ C_weak · (δ_n² + ‖w₀‖ · λ^{min(β+1,2)}).

(Note line 383.) -/
theorem weak_rate_from_combined
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    {split : OneShotSplit sample}
    {lambda β ζ : ℝ} {delta : ℕ → ℝ}
    {h_hat : ℕ → Ω → S.𝒳 → ℝ}
    {is_estimator : IsTRAEPrimalEstimator S TC sample split lambda h_hat}
    (hyps : TRAERatePrimalAbstractHyps S TC sample split lambda β ζ delta h_hat is_estimator)
    (lambda_pos : 0 < lambda)
    {Aζ : Set Ω} {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (h_combined :
      ∀ ω ∈ Aζ, ∀ n : ℕ,
        lambda *
            (S.strongNorm
              (S.hL2 (TC.H_subset (is_estimator.mem_H n ω))
                - S.hL2 hyps.tikhonov_bias.h_lambda_star_mem)) ^ 2
          + (S.weakNorm
              (S.hL2 (TC.H_subset (is_estimator.mem_H n ω))
                - S.hL2 hyps.tikhonov_bias.h_lambda_star_mem)) ^ 2
          ≤ K *
              ((S.weakNorm
                  (S.hL2 hyps.tikhonov_bias.h_lambda_star_mem
                    - S.hL2 S.h₀_mem)) ^ 2
                + (delta n) ^ 2)) :
    ∃ C_weak : ℝ, 0 ≤ C_weak ∧
      ∀ ω ∈ Aζ, ∀ n : ℕ,
        (S.weakNorm
            (S.hL2 (TC.H_subset (is_estimator.mem_H n ω)) - S.hL2 S.h₀_mem)) ^ 2
          ≤ C_weak *
              ((delta n) ^ 2
                + S.strongNorm (S.hL2 hyps.source_condition.w₀_mem) *
                    lambda ^ (min (β + 1) 2)) := by
  let Cb : ℝ := hyps.tikhonov_bias.C
  refine ⟨2 * K + (2 * K + 2) * Cb, ?_, ?_⟩
  · have hCb_nonneg : 0 ≤ Cb := hyps.tikhonov_bias.C_nonneg
    nlinarith [hK_nonneg, hCb_nonneg]
  · intro ω hω n
    set hhatL2 : Lp ℝ 2 μ :=
      S.hL2 (TC.H_subset (is_estimator.mem_H n ω)) with hhhatL2
    set hstarL2 : Lp ℝ 2 μ :=
      S.hL2 hyps.tikhonov_bias.h_lambda_star_mem with hhstarL2
    set h0L2 : Lp ℝ 2 μ := S.hL2 S.h₀_mem with hh0L2
    set Δ_weak : ℝ := S.weakNorm (hhatL2 - hstarL2) with hΔ_weak
    set R_b : ℝ := S.weakNorm (hstarL2 - h0L2) with hR_b
    set W₀ : ℝ := S.strongNorm (S.hL2 hyps.source_condition.w₀_mem) with hW₀
    set V : ℝ := S.weakNorm (hhatL2 - h0L2) with hV
    set Y : ℝ := W₀ * lambda ^ (min (β + 1) 2) with hY
    have h_lambda_nonneg : 0 ≤ lambda := le_of_lt lambda_pos
    have hΔ_nonneg : 0 ≤ Δ_weak := by
      simp [hΔ_weak, OperatorSystem.weakNorm]
    have hRb_nonneg : 0 ≤ R_b := by
      simp [hR_b, OperatorSystem.weakNorm]
    have hV_nonneg : 0 ≤ V := by
      simp [hV, OperatorSystem.weakNorm]
    have hδ_sq_nonneg : 0 ≤ (delta n) ^ 2 := sq_nonneg (delta n)
    have hW₀_nonneg : 0 ≤ W₀ := by
      simp [hW₀, OperatorSystem.strongNorm]
    have hY_nonneg : 0 ≤ Y := by
      have hp : 0 ≤ lambda ^ (min (β + 1) 2) := Real.rpow_nonneg h_lambda_nonneg _
      exact mul_nonneg hW₀_nonneg hp
    have htri : V ≤ Δ_weak + R_b := by
      have hdecomp : hhatL2 - h0L2 = (hhatL2 - hstarL2) + (hstarL2 - h0L2) := by
        abel
      rw [hV, hΔ_weak, hR_b, OperatorSystem.weakNorm]
      calc
        ‖S.T (hhatL2 - h0L2)‖
            = ‖S.T ((hhatL2 - hstarL2) + (hstarL2 - h0L2))‖ := by
          rw [hdecomp]
        _ = ‖S.T (hhatL2 - hstarL2) + S.T (hstarL2 - h0L2)‖ := by
          rw [S.T_add]
        _ ≤ ‖S.T (hhatL2 - hstarL2)‖ + ‖S.T (hstarL2 - h0L2)‖ :=
          norm_add_le _ _
    have hV_sq : V ^ 2 ≤ 2 * (Δ_weak ^ 2 + R_b ^ 2) := by
      have hsq_le : V ^ 2 ≤ (Δ_weak + R_b) ^ 2 := by
        nlinarith [htri, hV_nonneg, hΔ_nonneg, hRb_nonneg,
          sq_nonneg (Δ_weak + R_b - V)]
      exact hsq_le.trans (add_sq_le : (Δ_weak + R_b) ^ 2
        ≤ 2 * (Δ_weak ^ 2 + R_b ^ 2))
    have hcombined' :
        lambda *
            (S.strongNorm (hhatL2 - hstarL2)) ^ 2
          + Δ_weak ^ 2
          ≤ K * (R_b ^ 2 + (delta n) ^ 2) := by
      simpa [hhhatL2, hhstarL2, hh0L2, hΔ_weak, hR_b]
        using h_combined ω hω n
    have hdrop : Δ_weak ^ 2 ≤ K * (R_b ^ 2 + (delta n) ^ 2) := by
      have hstrong_nonneg :
          0 ≤ lambda * (S.strongNorm (hhatL2 - hstarL2)) ^ 2 := by
        exact mul_nonneg h_lambda_nonneg (sq_nonneg _)
      nlinarith
    have hRb_sq_bound : R_b ^ 2 ≤ Cb * Y := by
      have hbias := hyps.tikhonov_bias.weak_bias
      have hbias' : R_b ^ 2 ≤ Cb * W₀ * lambda ^ (min (β + 1) 2) := by
        simpa [Cb, hR_b, hW₀, hhstarL2, hh0L2] using hbias
      calc
        R_b ^ 2 ≤ Cb * W₀ * lambda ^ (min (β + 1) 2) := hbias'
        _ = Cb * Y := by
          rw [hY]
          ring
    have hΔ_sq_bound : Δ_weak ^ 2 ≤ K * ((delta n) ^ 2 + Cb * Y) := by
      calc
        Δ_weak ^ 2 ≤ K * (R_b ^ 2 + (delta n) ^ 2) := hdrop
        _ ≤ K * (Cb * Y + (delta n) ^ 2) := by
          gcongr
        _ = K * ((delta n) ^ 2 + Cb * Y) := by ring
    calc
      (S.weakNorm
          (S.hL2 (TC.H_subset (is_estimator.mem_H n ω)) - S.hL2 S.h₀_mem)) ^ 2
          = V ^ 2 := by simp [hV, hhhatL2, hh0L2]
      _ ≤ 2 * (Δ_weak ^ 2 + R_b ^ 2) := hV_sq
      _ ≤ 2 * K * (delta n) ^ 2 + (2 * K * Cb + 2 * Cb) * Y := by
        have hsum :
            Δ_weak ^ 2 + R_b ^ 2
              ≤ K * ((delta n) ^ 2 + Cb * Y) + Cb * Y :=
          add_le_add hΔ_sq_bound hRb_sq_bound
        calc
          2 * (Δ_weak ^ 2 + R_b ^ 2)
              ≤ 2 * (K * ((delta n) ^ 2 + Cb * Y) + Cb * Y) := by
            exact mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2)
          _ = 2 * K * (delta n) ^ 2 + (2 * K * Cb + 2 * Cb) * Y := by ring
      _ ≤ (2 * K + (2 * K + 2) * Cb) * ((delta n) ^ 2 + Y) := by
        have hCb_nonneg : 0 ≤ Cb := hyps.tikhonov_bias.C_nonneg
        have hA_nonneg : 0 ≤ 2 * K :=
          mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hK_nonneg
        have hBcoeff_nonneg : 0 ≤ 2 * K * Cb + 2 * Cb := by
          exact add_nonneg
            (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hK_nonneg) hCb_nonneg)
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hCb_nonneg)
        have hd_le_sum : (delta n) ^ 2 ≤ (delta n) ^ 2 + Y :=
          le_add_of_nonneg_right hY_nonneg
        have hY_le_sum : Y ≤ (delta n) ^ 2 + Y :=
          le_add_of_nonneg_left hδ_sq_nonneg
        have hAd :
            (2 * K) * (delta n) ^ 2
              ≤ (2 * K) * ((delta n) ^ 2 + Y) :=
          mul_le_mul_of_nonneg_left hd_le_sum hA_nonneg
        have hBY :
            (2 * K * Cb + 2 * Cb) * Y
              ≤ (2 * K * Cb + 2 * Cb) * ((delta n) ^ 2 + Y) :=
          mul_le_mul_of_nonneg_left hY_le_sum hBcoeff_nonneg
        calc
          2 * K * (delta n) ^ 2 + (2 * K * Cb + 2 * Cb) * Y
              = (2 * K) * (delta n) ^ 2 + (2 * K * Cb + 2 * Cb) * Y := by ring
          _ ≤ (2 * K) * ((delta n) ^ 2 + Y)
                + (2 * K * Cb + 2 * Cb) * ((delta n) ^ 2 + Y) :=
            add_le_add hAd hBY
          _ = (2 * K + (2 * K + 2) * Cb) * ((delta n) ^ 2 + Y) := by ring
      _ = (2 * K + (2 * K + 2) * Cb) *
            ((delta n) ^ 2
              + S.strongNorm (S.hL2 hyps.source_condition.w₀_mem) *
                  lambda ^ (min (β + 1) 2)) := by
        rw [hY, hW₀]

/-! ## The headline rate theorem -/

/-- **Non-iterated TRAE primal rate theorem** (`thm:est-trae-rate-theorem`,
lines 174–248 of `trae_inverse_problems.tex`).

For any `λ < 2`, with probability at least `1 − ζ` over the nuisance fold
`A(n)`, the strong and weak inverse-problem rates hold simultaneously:

    ‖ĥ_n − h₀‖²_{L²(P_X)}
        ≤ C_strong · (δ_n² / λ + ‖w₀‖_{L²(P_X)} · λ^{min(β, 1)}),
    ‖T(ĥ_n − h₀)‖²_{L²(P_Z)}
        ≤ C_weak · (δ_n² + ‖w₀‖_{L²(P_X)} · λ^{min(β+1, 2)}).

Both rates hold on a single high-probability event `A(ζ)` of mass at
least `1 − ζ` (note line 228 — "with probability at least 1 − ζ"). -/
theorem trae_primal_rate_from_empirical_process
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    {split : OneShotSplit sample}
    {lambda β ζ : ℝ} {delta : ℕ → ℝ}
    {h_hat : ℕ → Ω → S.𝒳 → ℝ}
    {is_estimator : IsTRAEPrimalEstimator S TC sample split lambda h_hat}
    (hyps : TRAERatePrimalAbstractHyps S TC sample split lambda β ζ delta h_hat is_estimator)
    (lambda_pos : 0 < lambda) (lambda_lt : lambda < 2)
    (hζ_pos : 0 < ζ) (hζ_lt : ζ < 1) :
    ∃ (C_strong C_weak : ℝ) (Aζ : Set Ω),
      MeasurableSet Aζ ∧ μ Aζ ≥ 1 - ENNReal.ofReal ζ ∧
      0 ≤ C_strong ∧ 0 ≤ C_weak ∧
      ∀ ω ∈ Aζ, ∀ n : ℕ,
        (S.strongNorm
            (S.hL2 (TC.H_subset (is_estimator.mem_H n ω)) - S.hL2 S.h₀_mem)) ^ 2
          ≤ C_strong *
              ((delta n) ^ 2 / lambda
                + S.strongNorm (S.hL2 hyps.source_condition.w₀_mem) *
                    lambda ^ (min β 1))
        ∧
        (S.weakNorm
            (S.hL2 (TC.H_subset (is_estimator.mem_H n ω)) - S.hL2 S.h₀_mem)) ^ 2
          ≤ C_weak *
              ((delta n) ^ 2
                + S.strongNorm (S.hL2 hyps.source_condition.w₀_mem) *
                    lambda ^ (min (β + 1) 2)) := by
  rcases combined_metric_rate hyps lambda_pos lambda_lt hζ_pos hζ_lt with
    ⟨Aζ, K, hAζ_meas, hAζ_prob, hK_nonneg, h_combined⟩
  rcases strong_rate_from_combined hyps lambda_pos lambda_lt hK_nonneg h_combined with
    ⟨C_strong, hC_strong_nonneg, h_strong⟩
  rcases weak_rate_from_combined hyps lambda_pos hK_nonneg h_combined with
    ⟨C_weak, hC_weak_nonneg, h_weak⟩
  refine ⟨C_strong, C_weak, Aζ, hAζ_meas, hAζ_prob,
    hC_strong_nonneg, hC_weak_nonneg, ?_⟩
  intro ω hω n
  exact ⟨h_strong ω hω n, h_weak ω hω n⟩

/-- **TRAE primal rate from localized regimes.**

This is the paper-facing rate statement: callers provide the deterministic rate
hypotheses, the four localized regimes, and the explicit absorption/small-sample
obligations for the localized discharge.  The theorem builds the abstract
`empirical_process_event` internally via `empirical_process_event_of_absorption` and
then invokes the deterministic abstract theorem. -/
theorem trae_primal_rate
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    {split : OneShotSplit sample}
    {lambda β ζ : ℝ} {delta : ℕ → ℝ}
    {h_hat : ℕ → Ω → S.𝒳 → ℝ}
    {is_estimator : IsTRAEPrimalEstimator S TC sample split lambda h_hat}
    (base :
      TRAERatePrimalHyps S TC sample split lambda β ζ delta h_hat
        is_estimator)
    [IsProbabilityMeasure μ]
    (regimes :
      ∀ n, LocalizedRegimes S TC sample base.source_condition
        base.tikhonov_bias (split.n₁ n) (delta n))
    (lambda_pos : 0 < lambda) (lambda_lt : lambda < 2)
    (hζ_pos : 0 < ζ) (hζ_lt : ζ < 1)
    (absorption :
      ∀ ζ' : ℝ, 0 < ζ' → ζ' < 1 →
        ∃ K_ep : ℝ, 0 ≤ K_ep ∧
          ∀ ω : Ω, ∀ n : ℕ, 1 ≤ split.n₁ n →
            explicitRate regimes is_estimator ω n ζ'
              ≤ K_ep * populationShape (lambda := lambda) (delta := delta)
                          (tb := base.tikhonov_bias) is_estimator ω n)
    (small_n_slack :
      ∀ ζ' : ℝ, 0 < ζ' → ζ' < 1 → ∀ Aζ : Set Ω, ∀ K_ep : ℝ, 0 ≤ K_ep →
        ∀ ω ∈ Aζ, ∀ n : ℕ, ¬ 1 ≤ split.n₁ n →
          (S.weakNorm
              (S.hL2 (TC.H_subset (is_estimator.mem_H n ω))
                - S.hL2 S.h₀_mem)) ^ 2
            - (S.weakNorm
                (S.hL2 base.tikhonov_bias.h_lambda_star_mem
                  - S.hL2 S.h₀_mem)) ^ 2
            + lambda *
                ((S.strongNorm
                      (S.hL2 (TC.H_subset (is_estimator.mem_H n ω)))) ^ 2
                  - (S.strongNorm
                      (S.hL2 base.tikhonov_bias.h_lambda_star_mem)) ^ 2)
            ≤ K_ep *
                populationShape (lambda := lambda) (delta := delta)
                  (tb := base.tikhonov_bias) is_estimator ω n) :
    ∃ (C_strong C_weak : ℝ) (Aζ : Set Ω),
      MeasurableSet Aζ ∧ μ Aζ ≥ 1 - ENNReal.ofReal ζ ∧
      0 ≤ C_strong ∧ 0 ≤ C_weak ∧
      ∀ ω ∈ Aζ, ∀ n : ℕ,
        (S.strongNorm
            (S.hL2 (TC.H_subset (is_estimator.mem_H n ω)) - S.hL2 S.h₀_mem)) ^ 2
          ≤ C_strong *
              ((delta n) ^ 2 / lambda
                + S.strongNorm (S.hL2 base.source_condition.w₀_mem) *
                    lambda ^ (min β 1))
        ∧
        (S.weakNorm
            (S.hL2 (TC.H_subset (is_estimator.mem_H n ω)) - S.hL2 S.h₀_mem)) ^ 2
          ≤ C_weak *
              ((delta n) ^ 2
                + S.strongNorm (S.hL2 base.source_condition.w₀_mem) *
                    lambda ^ (min (β + 1) 2)) := by
  let hyps :
      TRAERatePrimalAbstractHyps S TC sample split lambda β ζ delta h_hat
        is_estimator :=
    { toTRAERatePrimalHyps := base
      empirical_process_event :=
        (empirical_process_event_of_absorption
          (is_estimator := is_estimator) base.source_condition
          base.tikhonov_bias regimes lambda_pos.le absorption small_n_slack)
          ζ }
  exact trae_primal_rate_from_empirical_process hyps lambda_pos lambda_lt hζ_pos hζ_lt

end Primal
end NPIV
end Estimation
end Causalean
