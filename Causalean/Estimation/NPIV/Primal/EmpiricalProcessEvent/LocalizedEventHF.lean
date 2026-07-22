/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.LocalizedEventsBase

/-! # Localized Deviation for Products from `H` and `F`

This file constructs the high-probability event controlling empirical
fluctuations of products of candidate primal functions and critic functions in
the primal NPIV analysis.  Here `HF` denotes the product class formed from
`h ∈ TC.H` and `f ∈ TC.F`; the result supplies the product-class component of
the localized empirical-process event used in the rate proof. -/

namespace Causalean
namespace Estimation
namespace NPIV
namespace Primal

open MeasureTheory Causalean.Stat Causalean.Stat.Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Ω-side localized deviation event for the product class
`star(H · F)` — controls
`|(1/n) Σ h(X_i) f(Z_i) − E[h(X) f(Z)]|` uniformly over
`h ∈ TC.H, f ∈ TC.F`. -/
lemma localized_omega_event_for_HF
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
      ∀ ω ∈ E, ∀ h ∈ TC.H, ∀ f ∈ TC.F,
        |(n : ℝ)⁻¹ * ∑ k : Fin n,
            h (S.xOf (sample.Z k ω)) * f (S.zOf (sample.Z k ω))
          - ∫ ω', h (S.xOf (S.W ω')) * f (S.zOf (S.W ω')) ∂μ|
          ≤ 4 * δ_n * criticalRadius (regime.bundle_HF.regime.ψ n)
            + regime.bundle_HF.regime.b *
                Real.sqrt (2 * Real.log (1 / δ) / n) := by
  classical
  let B := regime.bundle_HF
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
  · intro ω hω h hh f hf
    let i : B.ι := regime.interp_HF_idx h hh f hf
    have hω₀ : Ψ ω ∈ E₀ := by
      simpa [E, Ψ] using hω
    have hi_norm : B.norm (B.F i) ≤ δ_n := by
      simpa [B, i] using regime.interp_HF_norm h hh f hf
    have hdev := hE₀_bound (Ψ ω) hω₀ i hi_norm
    have hpop :
        ∫ w, B.F i (B.X w) ∂P_W =
          ∫ ω', B.F i (B.X (S.W ω')) ∂μ := by
      exact integral_comp_law_W regime.law_W ((B.F_meas i).comp B.X_meas)
    have heval_sample :
        (Finset.univ.sum fun k : Fin n => B.F i (B.X (sample.Z k ω))) =
          ∑ k : Fin n, h (S.xOf (sample.Z k ω)) * f (S.zOf (sample.Z k ω)) := by
      apply Finset.sum_congr rfl
      intro k _
      simpa [B, i] using regime.interp_HF_eval h hh f hf (sample.Z k ω)
    have heval_pop :
        (fun ω' => B.F i (B.X (S.W ω'))) =
          fun ω' => h (S.xOf (S.W ω')) * f (S.zOf (S.W ω')) := by
      funext ω'
      simpa [B, i] using regime.interp_HF_eval h hh f hf (S.W ω')
    simpa [Ψ, hpop, heval_sample, heval_pop] using hdev

/-- Ω-side fixed-diameter pair-form localized deviation event for the
cross class `star(H · F)` — produces a *single* μ-event simultaneously
valid for **every triple** `(h₁, h₂, f) ∈ TC.H × TC.H × TC.F`.

The radius is fixed at `HF_pair_const · H_diameter · δ_n + δ_n`, using
`regime.H_diameter_bound`, `regime.HF_pair_const_nonneg`,
`interp_HF_norm_pair`, and `H_diameter_lb`.  This mirrors the
fixed-diameter design of `localized_omega_event_for_H` and avoids the
dyadic peeling infrastructure required for a strict per-pair Foster
rate, at the cost of a worst-case (diameter-rate) leading term.

For every confidence level `δ ∈ (0,1]` there is a μ-event of mass
`≥ 1 − δ` such that for all `ω` in the event and all
`h₁, h₂ ∈ TC.H, f ∈ TC.F`,

    |(1/n) Σ_k (h₁ - h₂)(X_k) · f(Z_k) − E[(h₁ - h₂)(X) · f(Z)]|
      ≤ 4 · (HF_pair_const · H_diameter · δ_n + δ_n) · critRad
        + b · √(2 · log(1/δ) / n). -/
lemma localized_omega_event_for_HF_pair
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
        ∀ f, ∀ _hf : f ∈ TC.F,
        |(n : ℝ)⁻¹ * ∑ k : Fin n,
              (h₁ (S.xOf (sample.Z k ω)) - h₂ (S.xOf (sample.Z k ω)))
                * f (S.zOf (sample.Z k ω))
            - ∫ ω',
                (h₁ (S.xOf (S.W ω')) - h₂ (S.xOf (S.W ω')))
                  * f (S.zOf (S.W ω')) ∂μ|
          ≤ 4 *
              (regime.HF_pair_const * regime.H_diameter * δ_n + δ_n) *
                criticalRadius (regime.bundle_HF.regime.ψ n)
            + regime.bundle_HF.regime.b *
                Real.sqrt (2 * Real.log (1 / δ) / n) := by
  classical
  let B := regime.bundle_HF
  let r : ℝ := regime.HF_pair_const * regime.H_diameter * δ_n + δ_n
  haveI : IsProbabilityMeasure P_W := by
    rw [← regime.law_W]
    exact Measure.isProbabilityMeasure_map S.meas_W.aemeasurable
  have hδn_pos : 0 < δ_n := lt_of_lt_of_le B.crit_pos B.crit_le
  have hδn_nonneg : 0 ≤ δ_n := le_of_lt hδn_pos
  have hdiam_nonneg : 0 ≤ regime.H_diameter :=
    hδn_nonneg.trans regime.H_diameter_lb
  have hpair_nonneg : 0 ≤ regime.HF_pair_const :=
    regime.HF_pair_const_nonneg
  have hr_delta : δ_n ≤ r := by
    dsimp [r]
    have hpair_term_nonneg :
        0 ≤ regime.HF_pair_const * regime.H_diameter * δ_n := by
      positivity
    linarith
  have hr_lb : criticalRadius (B.regime.ψ n) ≤ r := by
    dsimp [r]
    nlinarith [B.crit_le, hr_delta]
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
  · intro ω hω h₁ hh₁ h₂ hh₂ f hf
    let i : B.ι := regime.interp_HF_idx_pair h₁ h₂ hh₁ hh₂ f hf
    have hω₀ : Ψ ω ∈ E₀ := by
      simpa [E, Ψ] using hω
    have hpair :
        S.strongNorm (S.hL2 (TC.H_subset hh₁) - S.hL2 (TC.H_subset hh₂))
          ≤ regime.H_diameter :=
      regime.H_diameter_bound h₁ h₂ hh₁ hh₂
    have hi_norm : B.norm (B.F i) ≤ r := by
      have hi_gap := regime.interp_HF_norm_pair h₁ h₂ hh₁ hh₂ f hf
      have hpair_mult : regime.HF_pair_const *
          S.strongNorm (S.hL2 (TC.H_subset hh₁) - S.hL2 (TC.H_subset hh₂)) *
          δ_n ≤
        regime.HF_pair_const * regime.H_diameter * δ_n := by
        have hmul : regime.HF_pair_const *
            S.strongNorm (S.hL2 (TC.H_subset hh₁) - S.hL2 (TC.H_subset hh₂))
            ≤ regime.HF_pair_const * regime.H_diameter :=
          mul_le_mul_of_nonneg_left hpair hpair_nonneg
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          (mul_le_mul_of_nonneg_left hmul hδn_nonneg)
      have hpair_nonneg' : 0 ≤ regime.HF_pair_const * regime.H_diameter * δ_n :=
        by positivity
      dsimp [r]
      have hpair_bound : B.norm (B.F i) ≤ regime.HF_pair_const * regime.H_diameter * δ_n :=
        le_trans hi_gap hpair_mult
      linarith [hpair_nonneg']
    have hdev := hE₀_bound (Ψ ω) hω₀ i hi_norm
    have hpop :
        ∫ w, B.F i (B.X w) ∂P_W =
          ∫ ω', B.F i (B.X (S.W ω')) ∂μ := by
      exact integral_comp_law_W regime.law_W ((B.F_meas i).comp B.X_meas)
    have heval_sample :
        (Finset.univ.sum fun k : Fin n => B.F i (B.X (sample.Z k ω))) =
          ∑ k : Fin n,
            (h₁ (S.xOf (sample.Z k ω)) - h₂ (S.xOf (sample.Z k ω)))
              * f (S.zOf (sample.Z k ω)) := by
      apply Finset.sum_congr rfl
      intro k _
      simpa [B, i] using
        regime.interp_HF_eval_pair h₁ h₂ hh₁ hh₂ f hf (sample.Z k ω)
    have heval_pop :
        (fun ω' => B.F i (B.X (S.W ω'))) =
          fun ω' =>
            (h₁ (S.xOf (S.W ω')) - h₂ (S.xOf (S.W ω')))
              * f (S.zOf (S.W ω')) := by
      funext ω'
      simpa [B, i] using
        regime.interp_HF_eval_pair h₁ h₂ hh₁ hh₂ f hf (S.W ω')
    simpa [Ψ, r, hpop, heval_sample, heval_pop] using hdev

/-- Ω-side peeled pair-form localized deviation event for the cross class
`star(H · F)`.

This is the Foster-style dyadic peeling upgrade of
`localized_omega_event_for_HF_pair`: the leading term scales with the
actual strong gap `‖h₁ - h₂‖`, while the per-shell McDiarmid slack is
absorbed into `δ_n²` using `regime.peeling_slack_HF`. -/
lemma localized_omega_event_for_HF_pair_peeled
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
      ∀ ω ∈ E, ∀ h₁, ∀ hh₁ : h₁ ∈ TC.H, ∀ h₂, ∀ hh₂ : h₂ ∈ TC.H,
        ∀ f, ∀ _hf : f ∈ TC.F,
        |(n : ℝ)⁻¹ * ∑ k : Fin n,
              (h₁ (S.xOf (sample.Z k ω)) - h₂ (S.xOf (sample.Z k ω)))
                * f (S.zOf (sample.Z k ω))
            - ∫ ω',
                (h₁ (S.xOf (S.W ω')) - h₂ (S.xOf (S.W ω')))
                  * f (S.zOf (S.W ω')) ∂μ|
          ≤ 8 * regime.HF_pair_const * δ_n ^ 2 *
              S.strongNorm (S.hL2 (TC.H_subset hh₁) - S.hL2 (TC.H_subset hh₂))
            + 5 * δ_n ^ 2 := by
  classical
  let B := regime.bundle_HF
  let Rmax : ℝ := max δ_n (regime.HF_pair_const * regime.H_diameter * δ_n)
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
    have htop : regime.HF_pair_const * regime.H_diameter * δ_n
        ≤ δ_n * (2 : ℝ) ^ K := by
      exact (le_max_right _ _).trans hK
    simpa [B] using regime.peeling_slack_HF K δ hδ_pos hδ_le hn htop
  obtain ⟨E, hE_meas, hE_prob, hE_bound⟩ :=
    localized_omega_event_sharp_for_bundle
      (S := S) (P_W := P_W) (sample := sample) (B := B)
      regime.law_W hn hδ_pos hδ_le hδn_pos hRmax_lb hslack
  refine ⟨E, hE_meas, hE_prob, ?_⟩
  intro ω hω h₁ hh₁ h₂ hh₂ f hf
  let i : B.ι := regime.interp_HF_idx_pair h₁ h₂ hh₁ hh₂ f hf
  let gap : ℝ :=
    S.strongNorm (S.hL2 (TC.H_subset hh₁) - S.hL2 (TC.H_subset hh₂))
  have hgap_diam : gap ≤ regime.H_diameter := by
    simpa [gap] using regime.H_diameter_bound h₁ h₂ hh₁ hh₂
  have hi_gap : B.norm (B.F i) ≤ regime.HF_pair_const * gap * δ_n := by
    simpa [B, i, gap] using regime.interp_HF_norm_pair h₁ h₂ hh₁ hh₂ f hf
  have hi_diam : B.norm (B.F i) ≤ Rmax := by
    have hpair_mult : regime.HF_pair_const * gap * δ_n
        ≤ regime.HF_pair_const * regime.H_diameter * δ_n := by
      have hmul : regime.HF_pair_const * gap
          ≤ regime.HF_pair_const * regime.H_diameter :=
        mul_le_mul_of_nonneg_left hgap_diam regime.HF_pair_const_nonneg
      exact mul_le_mul_of_nonneg_right hmul hδn_nonneg
    exact hi_gap.trans (hpair_mult.trans (le_max_right _ _))
  have hdev := hE_bound ω hω i hi_diam
  have heval_sample :
      (Finset.univ.sum fun k : Fin n => B.F i (B.X (sample.Z k ω))) =
        ∑ k : Fin n,
          (h₁ (S.xOf (sample.Z k ω)) - h₂ (S.xOf (sample.Z k ω)))
            * f (S.zOf (sample.Z k ω)) := by
    apply Finset.sum_congr rfl
    intro k _
    simpa [B, i] using
      regime.interp_HF_eval_pair h₁ h₂ hh₁ hh₂ f hf (sample.Z k ω)
  have heval_pop :
      (fun ω' => B.F i (B.X (S.W ω'))) =
        fun ω' =>
          (h₁ (S.xOf (S.W ω')) - h₂ (S.xOf (S.W ω')))
            * f (S.zOf (S.W ω')) := by
    funext ω'
    simpa [B, i] using
      regime.interp_HF_eval_pair h₁ h₂ hh₁ hh₂ f hf (S.W ω')
  have hdev_concrete :
      |(n : ℝ)⁻¹ * ∑ k : Fin n,
            (h₁ (S.xOf (sample.Z k ω)) - h₂ (S.xOf (sample.Z k ω)))
              * f (S.zOf (sample.Z k ω))
          - ∫ ω',
              (h₁ (S.xOf (S.W ω')) - h₂ (S.xOf (S.W ω')))
                * f (S.zOf (S.W ω')) ∂μ|
        ≤ 8 * δ_n * B.norm (B.F i) + 5 * δ_n ^ 2 := by
    simpa [B, i, heval_sample, heval_pop] using hdev
  have hrate :
      8 * δ_n * B.norm (B.F i) + 5 * δ_n ^ 2
        ≤ 8 * regime.HF_pair_const * δ_n ^ 2 * gap + 5 * δ_n ^ 2 := by
    have hlead := mul_le_mul_of_nonneg_left hi_gap
      (by nlinarith [hδn_nonneg] : 0 ≤ 8 * δ_n)
    nlinarith
  simpa [gap] using hdev_concrete.trans hrate


end Primal
end NPIV
end Estimation
end Causalean
