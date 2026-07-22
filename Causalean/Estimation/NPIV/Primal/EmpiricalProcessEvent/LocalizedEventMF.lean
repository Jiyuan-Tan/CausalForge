/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.LocalizedEventsBase

/-! # Localized Deviation for Moment-Critic Products `mF`

This file constructs the high-probability event controlling empirical
fluctuations of the moment map multiplied by critic functions in the primal
NPIV analysis.  Here `mF` denotes the class `W ↦ m(W; f)` indexed by
`f ∈ TC.F`; it supplies the moment-class component of the localized
empirical-process event used downstream. -/

namespace Causalean
namespace Estimation
namespace NPIV
namespace Primal

open MeasureTheory Causalean.Stat Causalean.Stat.Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Ω-side localized deviation event for the moment class
`star(m ∘ F)` — controls `|(1/n) Σ m(W_i; f) − E[m(W; f)]|` uniformly
over `f ∈ TC.F`. -/
lemma localized_omega_event_for_mF
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
      ∀ ω ∈ E, ∀ f ∈ TC.F,
        |(n : ℝ)⁻¹ * ∑ k : Fin n, S.m (sample.Z k ω) f
          - ∫ ω', S.m (S.W ω') f ∂μ|
          ≤ 4 * δ_n * criticalRadius (regime.bundle_mF.regime.ψ n)
            + regime.bundle_mF.regime.b *
                Real.sqrt (2 * Real.log (1 / δ) / n) := by
  classical
  let B := regime.bundle_mF
  haveI : IsProbabilityMeasure P_W := by
    rw [← regime.law_W]
    exact Measure.isProbabilityMeasure_map S.meas_W.aemeasurable
  obtain ⟨E₀, hE₀_meas, hE₀_prob, hE₀_bound⟩ :=
    localized_uniform_deviation B.F B.norm P_W B.X B.X_meas B.F_meas B.regime
      hδ_pos hδ_le n hn B.crit_le B.crit_pos B.crit_fp
      (B.rad_bdd δ_n le_rfl) (B.rad_int δ_n le_rfl)
  let Ψ : Ω → (Fin n → S.𝒲) := fun ω k => sample.Z k ω
  let E : Set Ω := Ψ ⁻¹' E₀
  have hpull :=
    Causalean.Stat.event_pullback_along_iidSample sample n hE₀_meas hE₀_prob
  refine ⟨E, ?_, ?_, ?_⟩
  · simpa [E, Ψ] using hpull.1
  · simpa [E, Ψ] using hpull.2
  · intro ω hω f hf
    let i : B.ι := regime.interp_mF_idx f hf
    have hω₀ : Ψ ω ∈ E₀ := by
      simpa [E, Ψ] using hω
    have hi_norm : B.norm (B.F i) ≤ δ_n := by
      simpa [B, i] using regime.interp_mF_norm f hf
    have hdev := hE₀_bound (Ψ ω) hω₀ i hi_norm
    have hpop :
        ∫ w, B.F i (B.X w) ∂P_W =
          ∫ ω', B.F i (B.X (S.W ω')) ∂μ := by
      exact integral_comp_law_W regime.law_W ((B.F_meas i).comp B.X_meas)
    have heval_sample :
        (Finset.univ.sum fun k : Fin n => B.F i (B.X (sample.Z k ω))) =
          ∑ k : Fin n, S.m (sample.Z k ω) f := by
      apply Finset.sum_congr rfl
      intro k _
      simpa [B, i] using regime.interp_mF_eval f hf (sample.Z k ω)
    have heval_pop :
        (fun ω' => B.F i (B.X (S.W ω'))) =
          fun ω' => S.m (S.W ω') f := by
      funext ω'
      simpa [B, i] using regime.interp_mF_eval f hf (S.W ω')
    simpa [Ψ, hpop, heval_sample, heval_pop] using hdev

/-- Ω-side fixed-diameter pair-form localized deviation event for the
moment class `star(m ∘ F)`.  This is the non-peeled building block for
the Foster pair-gap bridge; the peeled variant can reuse the same
interpretation at dyadic radii below `mF_L2_const * F_diameter`. -/
lemma localized_omega_event_for_mF_pair
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
      ∀ ω ∈ E, ∀ f₁, ∀ _hf₁ : f₁ ∈ TC.F, ∀ f₂, ∀ _hf₂ : f₂ ∈ TC.F,
        |(n : ℝ)⁻¹ * ∑ k : Fin n,
              (S.m (sample.Z k ω) f₁ - S.m (sample.Z k ω) f₂)
          - ∫ ω', (S.m (S.W ω') f₁ - S.m (S.W ω') f₂) ∂μ|
          ≤ 4 * (regime.mF_L2_const * regime.F_diameter) *
                criticalRadius (regime.bundle_mF.regime.ψ n)
            + regime.bundle_mF.regime.b *
                Real.sqrt (2 * Real.log (1 / δ) / n) := by
  classical
  let B := regime.bundle_mF
  let r : ℝ := regime.mF_L2_const * regime.F_diameter
  haveI : IsProbabilityMeasure P_W := by
    rw [← regime.law_W]
    exact Measure.isProbabilityMeasure_map S.meas_W.aemeasurable
  have hδn_pos : 0 < δ_n := lt_of_lt_of_le B.crit_pos B.crit_le
  have hr_delta : δ_n ≤ r := by
    simpa [r] using regime.mF_pair_radius_lb
  have hr_lb : criticalRadius (B.regime.ψ n) ≤ r := by
    exact B.crit_le.trans hr_delta
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
  · intro ω hω f₁ hf₁ f₂ hf₂
    let i : B.ι := regime.interp_mF_idx_pair f₁ f₂ hf₁ hf₂
    have hω₀ : Ψ ω ∈ E₀ := by
      simpa [E, Ψ] using hω
    have hpair :
        S.strongNorm (S.qL2 (TC.F_subset hf₁) - S.qL2 (TC.F_subset hf₂))
          ≤ regime.F_diameter :=
      regime.F_diameter_bound f₁ f₂ hf₁ hf₂
    have hi_norm : B.norm (B.F i) ≤ r := by
      exact (regime.interp_mF_norm_pair f₁ f₂ hf₁ hf₂).trans
        (mul_le_mul_of_nonneg_left hpair regime.mF_L2_const_nonneg)
    have hdev := hE₀_bound (Ψ ω) hω₀ i hi_norm
    have hpop :
        ∫ w, B.F i (B.X w) ∂P_W =
          ∫ ω', B.F i (B.X (S.W ω')) ∂μ := by
      exact integral_comp_law_W regime.law_W ((B.F_meas i).comp B.X_meas)
    have heval_sample :
        (Finset.univ.sum fun k : Fin n => B.F i (B.X (sample.Z k ω))) =
          ∑ k : Fin n, (S.m (sample.Z k ω) f₁ - S.m (sample.Z k ω) f₂) := by
      apply Finset.sum_congr rfl
      intro k _
      simpa [B, i] using regime.interp_mF_eval_pair f₁ f₂ hf₁ hf₂ (sample.Z k ω)
    have heval_pop :
        (fun ω' => B.F i (B.X (S.W ω'))) =
          fun ω' => S.m (S.W ω') f₁ - S.m (S.W ω') f₂ := by
      funext ω'
      simpa [B, i] using regime.interp_mF_eval_pair f₁ f₂ hf₁ hf₂ (S.W ω')
    simpa [Ψ, r, hpop, heval_sample, heval_pop] using hdev

/-- Ω-side peeled pair-form localized deviation event for the moment class
`star(m ∘ F)`.  The dyadic peeling is over the bundle radius of the pair
index for `m(W; f₁) - m(W; f₂)`, producing a Foster-style bound depending
on the critic L² gap rather than the worst-case diameter. -/
lemma localized_omega_event_for_mF_pair_peeled
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
      ∀ ω ∈ E, ∀ f₁, ∀ _hf₁ : f₁ ∈ TC.F, ∀ f₂, ∀ _hf₂ : f₂ ∈ TC.F,
        |(n : ℝ)⁻¹ * ∑ k : Fin n,
              (S.m (sample.Z k ω) f₁ - S.m (sample.Z k ω) f₂)
          - ∫ ω', (S.m (S.W ω') f₁ - S.m (S.W ω') f₂) ∂μ|
          ≤ 8 * regime.mF_L2_const * δ_n *
                S.strongNorm (S.qL2 (TC.F_subset _hf₁) - S.qL2 (TC.F_subset _hf₂))
            + 5 * δ_n ^ 2 := by
  classical
  let B := regime.bundle_mF
  let Rmax : ℝ := max δ_n (regime.mF_L2_const * regime.F_diameter)
  have hδn_pos : 0 < δ_n := lt_of_lt_of_le B.crit_pos B.crit_le
  have hδn_nonneg : 0 ≤ δ_n := le_of_lt hδn_pos
  have hRmax_lb : δ_n ≤ Rmax := by
    exact le_max_left _ _
  have hslack : ∀ K : ℕ,
      Rmax ≤ δ_n * (2 : ℝ) ^ K →
      B.regime.b * Real.sqrt
          (2 * Real.log (2 * ((K : ℝ) + 1) / δ) / n)
        ≤ δ_n ^ 2 := by
    intro K hK
    have htop : regime.mF_L2_const * regime.F_diameter
        ≤ δ_n * (2 : ℝ) ^ K := by
      exact (le_max_right _ _).trans hK
    simpa [B] using regime.peeling_slack_mF K δ hδ_pos hδ_le hn htop
  obtain ⟨E, hE_meas, hE_prob, hE_bound⟩ :=
    localized_omega_event_sharp_for_bundle
      (S := S) (P_W := P_W) (sample := sample) (B := B)
      regime.law_W hn hδ_pos hδ_le hδn_pos hRmax_lb hslack
  refine ⟨E, hE_meas, hE_prob, ?_⟩
  intro ω hω f₁ hf₁ f₂ hf₂
  let i : B.ι := regime.interp_mF_idx_pair f₁ f₂ hf₁ hf₂
  let gap : ℝ :=
    S.strongNorm (S.qL2 (TC.F_subset hf₁) - S.qL2 (TC.F_subset hf₂))
  have hgap_top : gap ≤ regime.F_diameter := by
    simpa [gap] using regime.F_diameter_bound f₁ f₂ hf₁ hf₂
  have hi_gap : B.norm (B.F i) ≤ regime.mF_L2_const * gap := by
    simpa [B, i, gap] using regime.interp_mF_norm_pair f₁ f₂ hf₁ hf₂
  have hi_diam : B.norm (B.F i) ≤ Rmax := by
    have htop : regime.mF_L2_const * gap
        ≤ regime.mF_L2_const * regime.F_diameter :=
      mul_le_mul_of_nonneg_left hgap_top regime.mF_L2_const_nonneg
    exact hi_gap.trans (htop.trans (le_max_right _ _))
  have hdev := hE_bound ω hω i hi_diam
  have heval_sample :
      (Finset.univ.sum fun k : Fin n => B.F i (B.X (sample.Z k ω))) =
        ∑ k : Fin n, (S.m (sample.Z k ω) f₁ - S.m (sample.Z k ω) f₂) := by
    apply Finset.sum_congr rfl
    intro k _
    simpa [B, i] using regime.interp_mF_eval_pair f₁ f₂ hf₁ hf₂ (sample.Z k ω)
  have heval_pop :
      (fun ω' => B.F i (B.X (S.W ω'))) =
        fun ω' => S.m (S.W ω') f₁ - S.m (S.W ω') f₂ := by
    funext ω'
    simpa [B, i] using regime.interp_mF_eval_pair f₁ f₂ hf₁ hf₂ (S.W ω')
  have hdev_concrete :
      |(n : ℝ)⁻¹ * ∑ k : Fin n,
            (S.m (sample.Z k ω) f₁ - S.m (sample.Z k ω) f₂)
        - ∫ ω', (S.m (S.W ω') f₁ - S.m (S.W ω') f₂) ∂μ|
        ≤ 8 * δ_n * B.norm (B.F i) + 5 * δ_n ^ 2 := by
    simpa [B, i, heval_sample, heval_pop] using hdev
  have hrate :
      8 * δ_n * B.norm (B.F i) + 5 * δ_n ^ 2
        ≤ 8 * regime.mF_L2_const * δ_n * gap + 5 * δ_n ^ 2 := by
    have hlead := mul_le_mul_of_nonneg_left hi_gap
      (by nlinarith [hδn_nonneg] : 0 ≤ 8 * δ_n)
    nlinarith
  simpa [gap] using hdev_concrete.trans hrate


end Primal
end NPIV
end Estimation
end Causalean
