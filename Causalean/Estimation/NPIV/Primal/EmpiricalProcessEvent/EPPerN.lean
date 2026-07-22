/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.EPMasterEvent

/-! # Per-Sample Empirical-Process Bound

This file states the per-sample-size empirical-process control used by the
primal NPIV rate theorem. It packages the master localized event into the
form consumed by the estimator analysis at a fixed sample size. -/

namespace Causalean
namespace Estimation
namespace NPIV
namespace Primal

open MeasureTheory Causalean.Stat Causalean.Stat.Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **EP closedness-witness population identity (Helper B1).**

Pure operator-side algebraic identity, **no sample / probability**.
Given:
- `h ∈ TC.H` with `TC.H_subset hh : h ∈ S.Hbar`,
- `f ∈ TC.F` with `TC.F_subset hf : f ∈ S.Qbar`,
- a **closedness witness** identity
    `S.T (S.hL2 S.h₀_mem - S.hL2 (TC.H_subset hh))
       = S.qL2 (TC.F_subset hf)`,

the **f-dependent part** of the population inner-objective at `(h, f)`
equals the squared weak norm of `h - h₀`:

    `2·E[m(W;f)] − 2·E[h(X)·f(Z)] − E[f(Z)²]
       = (weakNorm (hL2 hh − hL2 h₀))²`.

This is the population analog of "the closedness assumption implies the
adversarial sup is achieved at `T(h - h₀)` with value `‖T(h - h₀)‖²`",
proof-sketch lines ~270–285 of
`doc/basic_concepts/po/estimation/trae_inverse_problems.tex`.

The proof uses `OperatorSystem.T_inner_eq_integral` (line ~270 of
`Operator.lean`) to convert the integral identity into an L²
inner-product form, then `InverseProblemSystem.primal_moment` (line
~121 of `Setup.lean`) to substitute `E[m(W;f)] = E[h₀(X)·f(Z)]`, then
algebraic manipulation `2·⟨a, a⟩ − ‖a‖² = ‖a‖²` for `a := T(...)`. -/
lemma ep_pop_inner_at_closedness_witness
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    [IsProbabilityMeasure μ]
    {h : S.𝒳 → ℝ} (hh : h ∈ TC.H)
    {f : S.𝒵 → ℝ} (hf : f ∈ TC.F)
    (hcl :
      S.T (S.hL2 S.h₀_mem - S.hL2 (TC.H_subset hh))
        = S.qL2 (TC.F_subset hf)) :
    2 * (∫ ω, S.m (S.W ω) f ∂μ)
        - 2 * (∫ ω, h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ)
        - ∫ ω, (f (S.zOf (S.W ω))) ^ 2 ∂μ
      = (S.weakNorm
          (S.hL2 (TC.H_subset hh) - S.hL2 S.h₀_mem)) ^ 2 := by
  haveI := S.isFiniteMeasure
  haveI := S.Qbar_L2_hasProj
  -- Step 1: ⟨T(hL2 h₀ - hL2 hh), qL2 hf⟩ = ∫ (h₀ - h)·f via T_inner_eq_integral.
  have h_inner_int :
      inner ℝ (S.T (S.hL2 S.h₀_mem - S.hL2 (TC.H_subset hh)))
              (S.qL2 (TC.F_subset hf))
        = ∫ ω, (S.h₀ (S.xOf (S.W ω)) - h (S.xOf (S.W ω))) *
                f (S.zOf (S.W ω)) ∂μ :=
    S.T_inner_eq_integral S.h₀_mem (TC.H_subset hh) (TC.F_subset hf)
  -- Step 2: primal_moment: ∫ m(W;f) = ∫ h₀(X)·f(Z).
  have h_moment :
      ∫ ω, S.m (S.W ω) f ∂μ
        = ∫ ω, S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ :=
    S.primal_moment f (TC.F_subset hf)
  -- Step 3: ∫ (h₀ - h)·f = ∫ h₀·f - ∫ h·f via integral_sub.
  have hh₀f_int : Integrable
      (fun ω => S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω))) μ := by
    have := S.integrable_qh S.h₀ S.h₀_mem f (TC.F_subset hf)
    simpa [mul_comm] using this
  have hhf_int : Integrable
      (fun ω => h (S.xOf (S.W ω)) * f (S.zOf (S.W ω))) μ := by
    have := S.integrable_qh h (TC.H_subset hh) f (TC.F_subset hf)
    simpa [mul_comm] using this
  have h_int_diff :
      ∫ ω, (S.h₀ (S.xOf (S.W ω)) - h (S.xOf (S.W ω))) *
              f (S.zOf (S.W ω)) ∂μ
        = (∫ ω, S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ)
            - ∫ ω, h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ := by
    have : (fun ω => (S.h₀ (S.xOf (S.W ω)) - h (S.xOf (S.W ω))) *
                      f (S.zOf (S.W ω)))
              = fun ω => S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω))
                          - h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) := by
      funext ω; ring
    rw [this]
    exact integral_sub hh₀f_int hhf_int
  -- Combine 1+2+3:
  have h_diff_eq_inner :
      (∫ ω, S.m (S.W ω) f ∂μ)
          - ∫ ω, h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ
        = inner ℝ (S.T (S.hL2 S.h₀_mem - S.hL2 (TC.H_subset hh)))
                  (S.qL2 (TC.F_subset hf)) := by
    rw [h_moment, h_inner_int, h_int_diff]
  -- Step 4: ⟨qL2 hf, qL2 hf⟩ = ∫ f².
  have h_qL2_self :
      inner ℝ (S.qL2 (TC.F_subset hf)) (S.qL2 (TC.F_subset hf))
        = ∫ ω, (f (S.zOf (S.W ω))) ^ 2 ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(S.toQbarL2 f (TC.F_subset hf)).coeFn_toLp]
      with ω hω
    simp [OperatorSystem.qL2, hω, pow_two]
  -- Step 5: substitute hcl in the inner-product side, then close with norm.
  have h_diff_eq_int_fsq :
      (∫ ω, S.m (S.W ω) f ∂μ)
          - ∫ ω, h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ
        = ∫ ω, (f (S.zOf (S.W ω))) ^ 2 ∂μ := by
    rw [h_diff_eq_inner, hcl, h_qL2_self]
  -- Step 6: weakNorm of the negated argument.
  have h_T_neg :
      S.T (S.hL2 (TC.H_subset hh) - S.hL2 S.h₀_mem)
        = - S.qL2 (TC.F_subset hf) := by
    rw [S.T_sub]
    have hcl' :
        S.T (S.hL2 S.h₀_mem) - S.T (S.hL2 (TC.H_subset hh))
          = S.qL2 (TC.F_subset hf) := by
      rw [← S.T_sub]; exact hcl
    rw [← hcl']
    abel
  have h_weak_eq_intf :
      (S.weakNorm (S.hL2 (TC.H_subset hh) - S.hL2 S.h₀_mem)) ^ 2
        = ∫ ω, (f (S.zOf (S.W ω))) ^ 2 ∂μ := by
    rw [OperatorSystem.weakNorm, h_T_neg, norm_neg]
    have : ‖S.qL2 (TC.F_subset hf)‖ ^ 2
            = inner ℝ (S.qL2 (TC.F_subset hf))
                      (S.qL2 (TC.F_subset hf)) := by
      rw [real_inner_self_eq_norm_sq]
    rw [this, h_qL2_self]
  -- Final algebraic close:
  -- 2·∫m - 2·∫h·f - ∫f² = 2·(∫m - ∫h·f) - ∫f²
  --                    = 2·∫f² - ∫f² = ∫f² = (weakNorm)².
  rw [h_weak_eq_intf]
  linarith [h_diff_eq_int_fsq]

/-- **EP per-`n` inequality from an objective-level localized modulus
(Helper B).**

Pure analytic per-`n` step, **no probability**.  Given:
- a sample size `n` with `1 ≤ split.n₁ n`,
- a sample point `ω : Ω`,
- the localized objective modulus

    population_excess(ĥ_n, h*_λ) ≤
      empirical_sup_excess(ĥ_n, h*_λ) + localized_envelope,

derive the per-`n` EP inequality.  This statement is intentionally not
vacuous: the hypothesis still contains the empirical sup-objective
excess, and the proof uses `is_estimator.opt n ω` against
`tb.h_lambda_star_fun` to remove it. -/
lemma ep_per_n_inequality_from_deviations
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    {split : OneShotSplit sample}
    {lambda β : ℝ} {delta : ℕ → ℝ}
    {h_hat : ℕ → Ω → S.𝒳 → ℝ}
    (is_estimator : IsTRAEPrimalEstimator S TC sample split lambda h_hat)
    (sc : SourceCondition S β)
    (tb : TikhonovBiasBound S β lambda sc)
    [IsProbabilityMeasure μ]
    (regimes : ∀ n, LocalizedRegimes S TC sample sc tb (split.n₁ n) (delta n))
    {ζ : ℝ} (_hζ_pos : 0 < ζ) (_hζ_lt : ζ < 1)
    (n : ℕ) (_hn : 1 ≤ split.n₁ n) (ω : Ω)
    (objective_gap :
      ((S.weakNorm
          (S.hL2 (TC.H_subset (is_estimator.mem_H n ω))
            - S.hL2 S.h₀_mem)) ^ 2
        + lambda *
            (((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
              (h_hat n ω (S.xOf (sample.Z (k : ℕ) ω))) ^ 2))
        - ((S.weakNorm
            (S.hL2 tb.h_lambda_star_mem
              - S.hL2 S.h₀_mem)) ^ 2
          + lambda *
              (((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
                (tb.h_lambda_star_fun (S.xOf (sample.Z (k : ℕ) ω))) ^ 2))
      ≤ supObjective S TC sample split lambda (h_hat n ω) n ω
          - supObjective S TC sample split lambda tb.h_lambda_star_fun n ω
        + (16 * delta n *
                criticalRadius ((regimes n).bundle_HF.regime.ψ (split.n₁ n))
              + 16 * delta n *
                criticalRadius ((regimes n).bundle_mF.regime.ψ (split.n₁ n))
              + 8 * delta n *
                criticalRadius ((regimes n).bundle_F.regime.ψ (split.n₁ n))
              + (4 * (regimes n).bundle_HF.regime.b
                  + 4 * (regimes n).bundle_mF.regime.b
                  + 2 * (regimes n).bundle_F.regime.b) *
                  Real.sqrt
                    (2 * Real.log (4 * (2 : ℝ) ^ (n + 1) / ζ)
                      / (split.n₁ n)))) :
    (S.weakNorm
        (S.hL2 (TC.H_subset (is_estimator.mem_H n ω))
          - S.hL2 S.h₀_mem)) ^ 2
      - (S.weakNorm
          (S.hL2 tb.h_lambda_star_mem
            - S.hL2 S.h₀_mem)) ^ 2
      ≤ lambda *
          (((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
              (tb.h_lambda_star_fun (S.xOf (sample.Z (k : ℕ) ω))) ^ 2
            - ((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
                (h_hat n ω (S.xOf (sample.Z (k : ℕ) ω))) ^ 2)
        + (16 * delta n *
                criticalRadius ((regimes n).bundle_HF.regime.ψ (split.n₁ n))
              + 16 * delta n *
                criticalRadius ((regimes n).bundle_mF.regime.ψ (split.n₁ n))
              + 8 * delta n *
                criticalRadius ((regimes n).bundle_F.regime.ψ (split.n₁ n))
              + (4 * (regimes n).bundle_HF.regime.b
                  + 4 * (regimes n).bundle_mF.regime.b
                  + 2 * (regimes n).bundle_F.regime.b) *
                  Real.sqrt
                    (2 * Real.log (4 * (2 : ℝ) ^ (n + 1) / ζ)
                      / (split.n₁ n))) := by
  have hopt :
      supObjective S TC sample split lambda (h_hat n ω) n ω
        ≤ supObjective S TC sample split lambda tb.h_lambda_star_fun n ω :=
    is_estimator.opt n ω tb.h_lambda_star_fun (regimes n).realizability
  linarith [objective_gap, hopt]

/-- **Localized empirical-process inequality for the primal NPIV estimator.**

For every confidence level `ζ ∈ (0,1)` there is an Ω-event of mass
`≥ 1 − ζ` such that for all `ω` in the event and all `n` with
`1 ≤ split.n₁ n`,

    ‖T(ĥ_n − h_0)‖² − ‖T(h*_λ − h_0)‖²
      ≤ λ · (‖h*‖²_{A(n)} − ‖ĥ‖²_{A(n)})
        + K_ep_aux · (‖T(h*_λ − h_0)‖²
            + δ_n · ‖T(ĥ_n − h*_λ)‖ + δ_n²),

where `‖h‖²_{A(n)} := (split.n₁ n)⁻¹ ∑_{k < split.n₁ n} h(X_k)²`. This is the
per-sample-size inequality that converts the localized concentration event into
the weak-norm estimation bound for the chosen estimator `ĥ_n`. -/
theorem ep_inequality_from_localized
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    {split : OneShotSplit sample}
    {lambda β : ℝ} {delta : ℕ → ℝ}
    {h_hat : ℕ → Ω → S.𝒳 → ℝ}
    {is_estimator : IsTRAEPrimalEstimator S TC sample split lambda h_hat}
    (sc : SourceCondition S β)
    (tb : TikhonovBiasBound S β lambda sc)
    [IsProbabilityMeasure μ]
    (regimes : ∀ n, LocalizedRegimes S TC sample sc tb (split.n₁ n) (delta n))
    {ζ : ℝ} (hζ_pos : 0 < ζ) (hζ_lt : ζ < 1) :
    ∃ Aζ_ep : Set Ω,
      MeasurableSet Aζ_ep ∧ μ Aζ_ep ≥ 1 - ENNReal.ofReal ζ ∧
      ∀ ω ∈ Aζ_ep, ∀ n : ℕ, 1 ≤ split.n₁ n →
        (S.weakNorm
            (S.hL2 (TC.H_subset (is_estimator.mem_H n ω))
              - S.hL2 S.h₀_mem)) ^ 2
          - (S.weakNorm
              (S.hL2 tb.h_lambda_star_mem
                - S.hL2 S.h₀_mem)) ^ 2
          ≤ lambda *
              (((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
                  (tb.h_lambda_star_fun (S.xOf (sample.Z (k : ℕ) ω))) ^ 2
                - ((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
                    (h_hat n ω (S.xOf (sample.Z (k : ℕ) ω))) ^ 2)
            + (16 * delta n *
                  criticalRadius ((regimes n).bundle_HF.regime.ψ (split.n₁ n))
                + 16 * delta n *
                  criticalRadius ((regimes n).bundle_mF.regime.ψ (split.n₁ n))
                + 8 * delta n *
                  criticalRadius ((regimes n).bundle_F.regime.ψ (split.n₁ n))
                + (4 * (regimes n).bundle_HF.regime.b
                    + 4 * (regimes n).bundle_mF.regime.b
                    + 2 * (regimes n).bundle_F.regime.b) *
                    Real.sqrt
                      (2 * Real.log (4 * (2 : ℝ) ^ (n + 1) / ζ)
                        / (split.n₁ n))) := by
  -- The master event provides the objective-level explicit modulus; the
  -- per-`n` lemma removes the remaining empirical sup-objective excess
  -- using `is_estimator.opt`.
  obtain ⟨Aζ_master, hAζ_meas, hAζ_mass, hAζ_payload⟩ :=
    ep_master_event_from_localized (h_hat := h_hat) is_estimator sc tb regimes
      hζ_pos hζ_lt
  refine ⟨Aζ_master, hAζ_meas, hAζ_mass, ?_⟩
  intro ω hω n hn
  exact ep_per_n_inequality_from_deviations is_estimator sc tb regimes
    hζ_pos hζ_lt n hn ω (hAζ_payload ω hω n hn)



end Primal
end NPIV
end Estimation
end Causalean
