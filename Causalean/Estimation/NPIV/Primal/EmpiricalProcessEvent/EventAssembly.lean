/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.EPInequality
import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.Regulariser

/-!
Assembles the localized empirical-process and centered-regularizer events into
the final NPIV primal-rate event. The module exposes the event-level implication
used by the headline primal estimator theorem.
-/

namespace Causalean
namespace Estimation
namespace NPIV
namespace Primal

open MeasureTheory Causalean.Stat Causalean.Stat.Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Empirical-process event assembly

This file combines the localized empirical-process inequality and the centred
regulariser bound, then exposes the final empirical-process event in the shape
used by the primal NPIV rate theorem. The declarations below are the concrete
event-assembly lemmas discharging the abstract `empirical_process_event` field
of `TRAERatePrimalAbstractHyps`.

Two forms are exposed:

* `empirical_process_event_from_localized` — the **explicit-rate**
  combination of the EP inequality and centred-regulariser bound.  RHS
  carries per-`n` `criticalRadius` and `√(log/n_A)` factors as they come
  out of `localized_uniform_deviation`; this is the most informative
  intermediate form.

* `empirical_process_event_of_absorption` — produces the exact shape of
  `TRAERatePrimalAbstractHyps.empirical_process_event` (`Rate.lean`, line 152),
  consuming an absorption hypothesis that bounds the explicit per-`n`
  rate by a constant multiple of the population shape
  `(R² + δ_n y + δ_n² + λ δ_n x + λ δ_n²)`.

  **Note.** This older explicit all-`n` absorption theorem uses a
  polynomial/geometric union-bound schedule, `ζ_n ∝ ζ/(n+1)²`, and is
  therefore satisfiable under the stronger floor
  `δ_n ≥ c · √((log(n+1) + log(1/ζ))/n)`.  Then
  `√(2 log((n+1)²/ζ)/(split.n₁ n)) ≍ √((log(n+1) + log(1/ζ))/n)`
  is bounded by a constant multiple of `δ_n`, and the explicit per-`n`
  rate fits into `K_ep · populationShape` after standard AM-GM.  The
  headline `Rate.lean` δ-floor records the paper's `log log n` scale; this
  theorem displays the stronger all-`n` schedule as a separate
  `absorption` hypothesis. -/

/-- The intersection of two high-probability events has probability at least one minus the
sum of their two failure probabilities. -/
lemma measure_inter_ge_one_sub_add_of_ge
    [IsProbabilityMeasure μ]
    {A B : Set Ω} {a b : ENNReal}
    (hA_meas : MeasurableSet A) (hB_meas : MeasurableSet B)
    (hA : μ A ≥ 1 - a) (hB : μ B ≥ 1 - b) :
    μ (A ∩ B) ≥ 1 - (a + b) := by
  have hA_compl : μ Aᶜ ≤ a := by
    have hone_le : (1 : ENNReal) ≤ a + μ A := tsub_le_iff_left.mp hA
    rw [measure_compl hA_meas (measure_ne_top _ _), measure_univ]
    exact tsub_le_iff_right.mpr (by simpa [add_comm] using hone_le)
  have hB_compl : μ Bᶜ ≤ b := by
    have hone_le : (1 : ENNReal) ≤ b + μ B := tsub_le_iff_left.mp hB
    rw [measure_compl hB_meas (measure_ne_top _ _), measure_univ]
    exact tsub_le_iff_right.mpr (by simpa [add_comm] using hone_le)
  have hbad_le : μ (A ∩ B)ᶜ ≤ a + b := by
    rw [Set.compl_inter]
    exact (measure_union_le Aᶜ Bᶜ).trans (add_le_add hA_compl hB_compl)
  have hAB_meas : MeasurableSet (A ∩ B) := hA_meas.inter hB_meas
  rw [measure_compl hAB_meas (measure_ne_top _ _), measure_univ] at hbad_le
  have hone_le : (1 : ENNReal) ≤ (a + b) + μ (A ∩ B) :=
    tsub_le_iff_right.mp hbad_le
  exact tsub_le_iff_left.mpr hone_le

/-- **Discharge of `empirical_process_event` from
`localized_uniform_deviation` — explicit-rate form.**

Combines the EP inequality and the centred-regulariser bound on a
common high-probability event.  The RHS is the explicit per-`n` sum of
critical-radius and `√(log/n_A)` terms; see
`empirical_process_event_of_absorption` for the form matching
`Rate.lean`'s `empirical_process_event` field. -/
theorem empirical_process_event_from_localized
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
    (lambda_nonneg : 0 ≤ lambda) :
    ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
      ∃ Aζ : Set Ω,
        MeasurableSet Aζ ∧ μ Aζ ≥ 1 - ENNReal.ofReal ζ ∧
        ∀ ω ∈ Aζ, ∀ n : ℕ, 1 ≤ split.n₁ n →
          (S.weakNorm
              (S.hL2 (TC.H_subset (is_estimator.mem_H n ω))
                - S.hL2 S.h₀_mem)) ^ 2
            - (S.weakNorm
                (S.hL2 tb.h_lambda_star_mem
                  - S.hL2 S.h₀_mem)) ^ 2
            + lambda *
                ((S.strongNorm
                      (S.hL2 (TC.H_subset (is_estimator.mem_H n ω)))) ^ 2
                  - (S.strongNorm
                      (S.hL2 tb.h_lambda_star_mem)) ^ 2)
            ≤
              -- D-side raw explicit rate (EP step, before absorption).
              (16 * delta n *
                    criticalRadius ((regimes n).bundle_HF.regime.ψ (split.n₁ n))
                  + 16 * delta n *
                    criticalRadius ((regimes n).bundle_mF.regime.ψ (split.n₁ n))
                  + 8 * delta n *
                    criticalRadius ((regimes n).bundle_F.regime.ψ (split.n₁ n))
                  + (4 * (regimes n).bundle_HF.regime.b
                      + 4 * (regimes n).bundle_mF.regime.b
                      + 2 * (regimes n).bundle_F.regime.b) *
                      Real.sqrt
                        (2 * Real.log (8 * (2 : ℝ) ^ (n + 1) / ζ)
                          / (split.n₁ n)))
            -- C-side rate (centred regulariser).
            + lambda *
                (4 * ((regimes n).H_diameter + delta n) *
                    criticalRadius ((regimes n).bundle_H.regime.ψ (split.n₁ n))
                  + (regimes n).bundle_H.regime.b *
                      Real.sqrt
                        (2 * Real.log ((2 : ℝ) ^ (n + 2) / ζ)
                          / (split.n₁ n))) := by
  -- Proof: combine `ep_inequality_from_localized` (D) and
  -- `centred_regulariser_bound_from_localized` (C) at confidence `ζ/2`
  -- each.  Splitting `ζ → ζ/2` per side doubles the inner argument of
  -- the log: D-side `log(4·2^(n+1)/(ζ/2)) = log(8·2^(n+1)/ζ)`, C-side
  -- `log(2^(n+1)/(ζ/2)) = log(2^(n+2)/ζ)`.  Intersection of the two
  -- events has mass `≥ 1 - ζ/2 - ζ/2 = 1 - ζ`.
  intro ζ hζ_pos hζ_lt
  have hζ_half_pos : 0 < ζ / 2 := by linarith
  have hζ_half_lt : ζ / 2 < 1 := by linarith
  obtain ⟨Aζ_ep, hAζ_ep_meas, hAζ_ep_mass, hAζ_ep_bound⟩ :=
    ep_inequality_from_localized (h_hat := h_hat) (is_estimator := is_estimator)
      sc tb regimes hζ_half_pos hζ_half_lt
  obtain ⟨Aζ_reg, hAζ_reg_meas, hAζ_reg_mass, hAζ_reg_bound⟩ :=
    centred_regulariser_bound_from_localized (h_hat := h_hat)
      (is_estimator := is_estimator) sc tb regimes lambda_nonneg hζ_half_pos
      hζ_half_lt
  refine ⟨Aζ_ep ∩ Aζ_reg, hAζ_ep_meas.inter hAζ_reg_meas, ?_, ?_⟩
  · have hhalf_nonneg : 0 ≤ ζ / 2 := by linarith
    have hmass :=
      measure_inter_ge_one_sub_add_of_ge hAζ_ep_meas hAζ_reg_meas
        hAζ_ep_mass hAζ_reg_mass
    simpa [← ENNReal.ofReal_add hhalf_nonneg hhalf_nonneg, add_halves] using hmass
  · intro ω hω n hn
    rcases hω with ⟨hω_ep, hω_reg⟩
    have hlog_ep : 4 * (2 : ℝ) ^ (n + 1) / (ζ / 2) =
        8 * (2 : ℝ) ^ (n + 1) / ζ := by
      field_simp [ne_of_gt hζ_pos]
      ring
    have hlog_reg : (2 : ℝ) ^ (n + 1) / (ζ / 2) =
        (2 : ℝ) ^ (n + 2) / ζ := by
      field_simp [ne_of_gt hζ_pos]
      rw [pow_succ]
      ring
    have hD := hAζ_ep_bound ω hω_ep n hn
    rw [hlog_ep] at hD
    have hC_abs := hAζ_reg_bound ω hω_reg n hn
    rw [hlog_reg] at hC_abs
    have hC_upper := (le_abs_self _).trans hC_abs
    nlinarith [hD, hC_upper]

/-- **Per-`n` explicit rate** appearing on the RHS of
`empirical_process_event_from_localized`, packaged as a function of
`(ω, n, ζ)` for use as the LHS of the absorption hypothesis below. -/
noncomputable def explicitRate
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    {split : OneShotSplit sample}
    {lambda β : ℝ} {delta : ℕ → ℝ}
    {h_hat : ℕ → Ω → S.𝒳 → ℝ}
    {sc : SourceCondition S β}
    {tb : TikhonovBiasBound S β lambda sc}
    (regimes : ∀ n, LocalizedRegimes S TC sample sc tb (split.n₁ n) (delta n))
    (_is_estimator : IsTRAEPrimalEstimator S TC sample split lambda h_hat)
    (_ω : Ω) (n : ℕ) (ζ : ℝ) : ℝ :=
  (16 * delta n *
        criticalRadius ((regimes n).bundle_HF.regime.ψ (split.n₁ n))
      + 16 * delta n *
        criticalRadius ((regimes n).bundle_mF.regime.ψ (split.n₁ n))
      + 8 * delta n *
        criticalRadius ((regimes n).bundle_F.regime.ψ (split.n₁ n))
      + (4 * (regimes n).bundle_HF.regime.b
          + 4 * (regimes n).bundle_mF.regime.b
          + 2 * (regimes n).bundle_F.regime.b) *
          Real.sqrt
            (2 * Real.log (8 * (2 : ℝ) ^ (n + 1) / ζ) / (split.n₁ n)))
  + lambda *
      (4 * ((regimes n).H_diameter + delta n) *
          criticalRadius ((regimes n).bundle_H.regime.ψ (split.n₁ n))
        + (regimes n).bundle_H.regime.b *
            Real.sqrt
              (2 * Real.log ((2 : ℝ) ^ (n + 2) / ζ)
                / (split.n₁ n)))

/-- **Population shape** appearing on the RHS of
`TRAERatePrimalAbstractHyps.empirical_process_event` (`Rate.lean`, line 167):

    R² + δ_n · y + δ_n² + λ · δ_n · x + λ · δ_n²

with `R = ‖T(h*_λ − h₀)‖`, `y = ‖T(ĥ_n − h*_λ)‖`,
`x = ‖ĥ_n − h*_λ‖_{strong}`. -/
noncomputable def populationShape
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    {split : OneShotSplit sample}
    {lambda β : ℝ} {delta : ℕ → ℝ}
    {h_hat : ℕ → Ω → S.𝒳 → ℝ}
    {sc : SourceCondition S β}
    {tb : TikhonovBiasBound S β lambda sc}
    (is_estimator : IsTRAEPrimalEstimator S TC sample split lambda h_hat)
    (ω : Ω) (n : ℕ) : ℝ :=
  (S.weakNorm
      (S.hL2 tb.h_lambda_star_mem - S.hL2 S.h₀_mem)) ^ 2
    + delta n *
        S.weakNorm
          (S.hL2 (TC.H_subset (is_estimator.mem_H n ω))
            - S.hL2 tb.h_lambda_star_mem)
    + (delta n) ^ 2
    + lambda * delta n *
        S.strongNorm
          (S.hL2 (TC.H_subset (is_estimator.mem_H n ω))
            - S.hL2 tb.h_lambda_star_mem)
    + lambda * (delta n) ^ 2

/-- **Empirical-process event in the `Rate.lean` shape, conditional on absorption.**

This is *not* an unconditional discharge: given an *absorption* hypothesis
bounding the explicit per-`n` rate by a constant multiple `K_ep` of the
population shape, this theorem produces the exact form of
`TRAERatePrimalAbstractHyps.empirical_process_event`.

The absorption hypothesis is the substantive missing piece: it asserts
that the union-bound log factor `√(log(c · 2^{n+1}/ζ) / split.n₁ n)`
and the per-`n` critical radii are dominated by `K_ep` times the
`δ_n`-rates appearing in the population shape.  Realising this particular
all-`n` absorption typically requires choosing `δ_n` large enough to absorb
a `√(log n / n)` term; the paper-scale loglog path goes through the sharp
localized wrapper and a non-geometric EP discharge. -/
theorem empirical_process_event_of_absorption
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
    (lambda_nonneg : 0 ≤ lambda)
    /- **Absorption hypothesis.** A uniform-in-`n` constant `K_ep ≥ 0`
       (depending on `ζ`) such that the explicit per-`n` rate is bounded
       by `K_ep` times the population shape, on every `(ω, n)` with
       `1 ≤ split.n₁ n`. -/
    (absorption :
      ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
        ∃ K_ep : ℝ, 0 ≤ K_ep ∧
          ∀ ω : Ω, ∀ n : ℕ, 1 ≤ split.n₁ n →
            explicitRate regimes is_estimator ω n ζ
              ≤ K_ep * populationShape (lambda := lambda) (delta := delta)
                          (tb := tb) is_estimator ω n)
    /- **Small-`n` slack.** The `Rate.lean` field quantifies over all
       `n : ℕ` (including `n` for which `split.n₁ n = 0`).  We absorb
       the small-`n` cases into the same `K_ep` via this hypothesis,
       which the caller typically discharges using `split.grow` and a
       finite-set bound. -/
    (small_n_slack :
      ∀ ζ : ℝ, 0 < ζ → ζ < 1 → ∀ Aζ : Set Ω, ∀ K_ep : ℝ, 0 ≤ K_ep →
        ∀ ω ∈ Aζ, ∀ n : ℕ, ¬ 1 ≤ split.n₁ n →
          (S.weakNorm
              (S.hL2 (TC.H_subset (is_estimator.mem_H n ω))
                - S.hL2 S.h₀_mem)) ^ 2
            - (S.weakNorm
                (S.hL2 tb.h_lambda_star_mem
                  - S.hL2 S.h₀_mem)) ^ 2
            + lambda *
                ((S.strongNorm
                      (S.hL2 (TC.H_subset (is_estimator.mem_H n ω)))) ^ 2
                  - (S.strongNorm
                      (S.hL2 tb.h_lambda_star_mem)) ^ 2)
            ≤ K_ep *
                populationShape (lambda := lambda) (delta := delta)
                  (tb := tb) is_estimator ω n) :
    ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
      ∃ Aζ : Set Ω, ∃ K_ep : ℝ,
        MeasurableSet Aζ ∧ μ Aζ ≥ 1 - ENNReal.ofReal ζ ∧ 0 ≤ K_ep ∧
          ∀ ω ∈ Aζ, ∀ n : ℕ,
            (S.weakNorm
                (S.hL2 (TC.H_subset (is_estimator.mem_H n ω))
                  - S.hL2 S.h₀_mem)) ^ 2
              - (S.weakNorm
                  (S.hL2 tb.h_lambda_star_mem
                    - S.hL2 S.h₀_mem)) ^ 2
              + lambda *
                  ((S.strongNorm
                        (S.hL2 (TC.H_subset (is_estimator.mem_H n ω)))) ^ 2
                    - (S.strongNorm
                        (S.hL2 tb.h_lambda_star_mem)) ^ 2)
              ≤ K_ep *
                  populationShape (lambda := lambda) (delta := delta)
                    (tb := tb) is_estimator ω n := by
  -- Proof: combine `empirical_process_event_from_localized` with the
  -- `absorption` and `small_n_slack` hypotheses.  The Aζ event and
  -- K_ep are taken from those hypotheses; the per-`ω, n` inequality
  -- splits on `1 ≤ split.n₁ n`.
  intro ζ hζ_pos hζ_lt
  obtain ⟨Aζ, hAζ_meas, hAζ_mass, hAζ_bound⟩ :=
    empirical_process_event_from_localized
      (is_estimator := is_estimator) sc tb regimes lambda_nonneg ζ hζ_pos hζ_lt
  obtain ⟨K_ep, hK_nonneg, hK_bound⟩ := absorption ζ hζ_pos hζ_lt
  refine ⟨Aζ, K_ep, hAζ_meas, hAζ_mass, hK_nonneg, ?_⟩
  intro ω hω n
  rcases em (1 ≤ split.n₁ n) with hn | hn
  · have hlocalized := hAζ_bound ω hω n hn
    have habsorbed :
        explicitRate regimes is_estimator ω n ζ
          ≤ K_ep *
              populationShape (lambda := lambda) (delta := delta)
                (tb := tb) is_estimator ω n :=
      hK_bound ω n hn
    exact hlocalized.trans (by simpa [explicitRate] using habsorbed)
  · exact small_n_slack ζ hζ_pos hζ_lt Aζ K_ep hK_nonneg ω hω n hn

end Primal
end NPIV
end Estimation
end Causalean
