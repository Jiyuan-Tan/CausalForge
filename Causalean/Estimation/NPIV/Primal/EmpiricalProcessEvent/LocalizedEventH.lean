/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.LocalizedEventsBase

/-! # Localized Deviation for the Primal Class `H`

This file constructs high-probability events controlling empirical fluctuations
over pairs of candidate primal functions in the NPIV primal rate argument. Here
`H` is the primal hypothesis class `TC.H`.  The event is one component of the
localized empirical-process control needed for the Tikhonov-regularized
adversarial estimator. -/

namespace Causalean
namespace Estimation
namespace NPIV
namespace Primal

open MeasureTheory Causalean.Stat Causalean.Stat.Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Ω-side fixed-diameter localized deviation event for the candidate
class `star(H)` — produces a *single* μ-event simultaneously valid for
**every pair** `(h₁, h₂) ∈ TC.H × TC.H`.

The radius is fixed at `H_diameter + δ_n`, using
`regime.H_diameter_bound` and `interp_H_norm`.  This avoids the dyadic
peeling infrastructure needed for a pair-gap rate, at the cost of a
diameter-rate leading term.

For every confidence level `δ ∈ (0,1]` there is a μ-event of mass
`≥ 1 − δ` such that for all `ω` in the event and all
`h₁, h₂ ∈ TC.H`,

    |((1/n) Σ_k h₁(X_k)² − (1/n) Σ_k h₂(X_k)²)
       − (E[h₁(X)²] − E[h₂(X)²])|
      ≤ 4 · (H_diameter + δ_n) · critRad
-/
lemma localized_omega_event_for_H
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    [IsProbabilityMeasure μ]
    {β lambda : ℝ}
    {sc : SourceCondition S β}
    {tb : TikhonovBiasBound S β lambda sc}
    {n : ℕ} {δ_n : ℝ}
    (regime : LocalizedRegimes S TC sample sc tb n δ_n)
    (hn : 0 < n)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1) :
    ∃ E : Set Ω,
      MeasurableSet E ∧ μ E ≥ 1 - ENNReal.ofReal δ ∧
      ∀ ω ∈ E, ∀ h₁, ∀ _hh₁ : h₁ ∈ TC.H, ∀ h₂, ∀ _hh₂ : h₂ ∈ TC.H,
        |((n : ℝ)⁻¹ * ∑ k : Fin n, (h₁ (S.xOf (sample.Z k ω))) ^ 2
            - (n : ℝ)⁻¹ * ∑ k : Fin n, (h₂ (S.xOf (sample.Z k ω))) ^ 2)
          - (∫ ω', (h₁ (S.xOf (S.W ω'))) ^ 2 ∂μ
              - ∫ ω', (h₂ (S.xOf (S.W ω'))) ^ 2 ∂μ)|
          ≤ 4 * (regime.H_diameter + δ_n) *
                criticalRadius (regime.bundle_H.regime.ψ n)
            + regime.bundle_H.regime.b *
                Real.sqrt (2 * Real.log (1 / δ) / n) := by
  classical
  let B := regime.bundle_H
  let r : ℝ := regime.H_diameter + δ_n
  haveI : IsProbabilityMeasure P_W := by
    rw [← regime.law_W]
    exact Measure.isProbabilityMeasure_map S.meas_W.aemeasurable
  have hδn_pos : 0 < δ_n := lt_of_lt_of_le B.crit_pos B.crit_le
  have hδn_nonneg : 0 ≤ δ_n := le_of_lt hδn_pos
  have hdiam_nonneg : 0 ≤ regime.H_diameter :=
    hδn_nonneg.trans regime.H_diameter_lb
  have hr_lb : criticalRadius (B.regime.ψ n) ≤ r := by
    dsimp [r]
    linarith [B.crit_le, hdiam_nonneg]
  have hr_delta : δ_n ≤ r := by
    dsimp [r]
    linarith [hdiam_nonneg]
  obtain ⟨E₀, hE₀_meas, hE₀_prob, hE₀_bound⟩ :=
    localized_uniform_deviation B.F B.norm P_W B.X B.X_meas B.F_meas B.regime
      hδ_pos hδ_le n hn hr_lb B.crit_pos B.crit_fp
      (B.rad_bdd r hr_delta) (B.rad_int r hr_delta)
  let Ψ : Ω → (Fin n → S.𝒲) := fun ω k => sample.Z k ω
  let E : Set Ω := Ψ ⁻¹' E₀
  have hpull :=
    Causalean.Stat.event_pullback_along_iidSample sample n hE₀_meas hE₀_prob
  refine ⟨E, ?_, ?_, ?_⟩
  · simpa [E, Ψ] using hpull.1
  · simpa [E, Ψ] using hpull.2
  · intro ω hω h₁ hh₁ h₂ hh₂
    let i : B.ι := regime.interp_H_idx h₁ h₂ hh₁ hh₂
    have hω₀ : Ψ ω ∈ E₀ := by
      simpa [E, Ψ] using hω
    have hgap_le :
        S.strongNorm (S.hL2 (TC.H_subset hh₁) - S.hL2 (TC.H_subset hh₂))
          ≤ regime.H_diameter :=
      regime.H_diameter_bound h₁ h₂ hh₁ hh₂
    have hi_norm : B.norm (B.F i) ≤ r := by
      have hi_gap := regime.interp_H_norm h₁ h₂ hh₁ hh₂
      dsimp [r]
      linarith
    have hdev := hE₀_bound (Ψ ω) hω₀ i hi_norm
    have hpop :
        ∫ w, B.F i (B.X w) ∂P_W =
          ∫ ω', B.F i (B.X (S.W ω')) ∂μ := by
      exact integral_comp_law_W regime.law_W ((B.F_meas i).comp B.X_meas)
    have heval_sample :
        (Finset.univ.sum fun k : Fin n => B.F i (B.X (sample.Z k ω))) =
          ∑ k : Fin n,
            ((h₁ (S.xOf (sample.Z k ω))) ^ 2
              - (h₂ (S.xOf (sample.Z k ω))) ^ 2) := by
      apply Finset.sum_congr rfl
      intro k _
      simpa [B, i] using regime.interp_H_eval h₁ h₂ hh₁ hh₂ (sample.Z k ω)
    have heval_pop :
        (fun ω' => B.F i (B.X (S.W ω'))) =
          fun ω' =>
            (h₁ (S.xOf (S.W ω'))) ^ 2 - (h₂ (S.xOf (S.W ω'))) ^ 2 := by
      funext ω'
      simpa [B, i] using regime.interp_H_eval h₁ h₂ hh₁ hh₂ (S.W ω')
    have hsample_split :
        (n : ℝ)⁻¹ *
            (∑ k : Fin n,
              ((h₁ (S.xOf (sample.Z k ω))) ^ 2
                - (h₂ (S.xOf (sample.Z k ω))) ^ 2))
          =
        (n : ℝ)⁻¹ * ∑ k : Fin n, (h₁ (S.xOf (sample.Z k ω))) ^ 2
          - (n : ℝ)⁻¹ * ∑ k : Fin n, (h₂ (S.xOf (sample.Z k ω))) ^ 2 := by
      rw [Finset.sum_sub_distrib, mul_sub]
    have hsample_split' :
        (n : ℝ)⁻¹ *
            ((∑ k : Fin n, (h₁ (S.xOf (sample.Z k ω))) ^ 2)
              - ∑ k : Fin n, (h₂ (S.xOf (sample.Z k ω))) ^ 2)
          =
        (n : ℝ)⁻¹ * ∑ k : Fin n, (h₁ (S.xOf (sample.Z k ω))) ^ 2
          - (n : ℝ)⁻¹ * ∑ k : Fin n, (h₂ (S.xOf (sample.Z k ω))) ^ 2 := by
      ring
    have hsq₁_int :
        Integrable (fun ω' => (h₁ (S.xOf (S.W ω'))) ^ 2) μ := by
      exact (S.toHbarL2 h₁ (TC.H_subset hh₁)).integrable_sq
    have hsq₂_int :
        Integrable (fun ω' => (h₂ (S.xOf (S.W ω'))) ^ 2) μ := by
      exact (S.toHbarL2 h₂ (TC.H_subset hh₂)).integrable_sq
    have hpop_split :
        (∫ ω',
            (h₁ (S.xOf (S.W ω'))) ^ 2 - (h₂ (S.xOf (S.W ω'))) ^ 2 ∂μ)
          =
        (∫ ω', (h₁ (S.xOf (S.W ω'))) ^ 2 ∂μ)
          - ∫ ω', (h₂ (S.xOf (S.W ω'))) ^ 2 ∂μ := by
      exact integral_sub hsq₁_int hsq₂_int
    simpa [Ψ, r, hpop, heval_sample, heval_pop, hsample_split,
      hsample_split', hpop_split]
      using hdev

end Primal
end NPIV
end Estimation
end Causalean
