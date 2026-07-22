/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# A.e.-equality/inequality lifts under conditional independence and overlap

* `ae_eq_of_ae_eq_restrict_arm` — if two `m`-measurable functions agree on
  `μ.restrict {A=a}` and `P(A=a|m) > 0` a.e., they agree μ-a.e. globally.
* `ae_le_YofA_of_ae_le_Y` — `Y(a)` inherits `Y`'s a.e. upper bound under
  latent exchangeability and consistency.
* `ae_le_YofA_of_ae_le_Y_below` — mirror for the lower bound.

All three are Mathlib-contribution candidates.  Used in
`PO/ID/Partial/Proxy/Helpers/BridgeW.lean` and `BridgeWZ.lean`.
-/

import Causalean.Mathlib.CondIndep.Integrability
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Probability.Independence.Conditional

/-! # Almost-Everywhere Lifts Under Overlap

This file proves generic almost-everywhere equality and inequality lifting lemmas
under overlap and conditional-independence hypotheses. These tools transfer
restricted-arm statements and essential bounds to global potential-outcome
statements in partial-identification arguments.

The exported support lemmas convert between restricted a.e. equality and
indicator equality (`indicator_aeEq_of_aeEq_restrict`,
`aeEq_restrict_of_indicator_aeEq`) and propagate vanishing through conditional
expectation (`condExp_indicator_aeEq_zero`). The main public theorems are
`ae_eq_of_ae_eq_restrict_arm`, `ae_le_YofA_of_ae_le_Y`, and
`ae_le_YofA_of_ae_le_Y_below`. -/

namespace Causalean

open MeasureTheory
open scoped MeasureTheory ProbabilityTheory

/-- Push an a.e.-equality under `μ.restrict s` to a global equality of
`s`-indicators. -/
lemma indicator_aeEq_of_aeEq_restrict
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
    {s : Set Ω} (hs : MeasurableSet s) {f g : Ω → ℝ}
    (h : f =ᵐ[μ.restrict s] g) :
    s.indicator f =ᵐ[μ] s.indicator g := by
  have h_on : ∀ᵐ ω ∂(μ.restrict s), s.indicator f ω = s.indicator g ω := by
    filter_upwards [h, ae_restrict_mem hs] with ω hω hωs
    rw [Set.indicator_of_mem hωs, Set.indicator_of_mem hωs, hω]
  have h_off : ∀ᵐ ω ∂(μ.restrict sᶜ), s.indicator f ω = s.indicator g ω := by
    rw [ae_restrict_iff' hs.compl]
    filter_upwards with ω hωs
    rw [Set.indicator_of_notMem hωs, Set.indicator_of_notMem hωs]
  exact MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl s h_on h_off

/-- Recover a `μ.restrict s` a.e.-equality from a global equality of
`s`-indicators. -/
lemma aeEq_restrict_of_indicator_aeEq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
    {s : Set Ω} (hs : MeasurableSet s) {f g : Ω → ℝ}
    (h : s.indicator f =ᵐ[μ] s.indicator g) :
    f =ᵐ[μ.restrict s] g := by
  rw [Filter.EventuallyEq, ae_restrict_iff' hs]
  filter_upwards [h] with ω hω hωs
  have hf : s.indicator f ω = f ω := Set.indicator_of_mem hωs f
  have hg : s.indicator g ω = g ω := Set.indicator_of_mem hωs g
  simpa [hf, hg] using hω

/-- If an integrable function vanishes after restriction by an `m`-measurable
indicator, so does its conditional expectation. -/
lemma condExp_indicator_aeEq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
    {m : MeasurableSpace Ω} {s : Set Ω} (hs : MeasurableSet[m] s)
    {f : Ω → ℝ} (hf : MeasureTheory.Integrable f μ)
    (h : s.indicator f =ᵐ[μ] 0) :
    s.indicator (μ[f | m]) =ᵐ[μ] 0 := by
  have hCE_ind := MeasureTheory.condExp_indicator (m := m) hf hs
  have hLHS_zero : μ[s.indicator f | m] =ᵐ[μ] 0 := by
    refine (MeasureTheory.condExp_congr_ae (m := m) h).trans ?_
    rw [MeasureTheory.condExp_zero (m := m) (μ := μ) (E := ℝ)]
  exact hCE_ind.symm.trans hLHS_zero

/-- **Single-arm a.e.-equality lift for σ-measurable functions.**

If `f, g : Ω → ℝ` are both `m`-measurable and agree `μ.restrict {A=a}`-a.e., they
agree `μ`-a.e. globally, PROVIDED the conditional probability `P(A=a | m)` is
positive a.e. (`h_overlap`).

Without overlap the statement is false: σ_m-measurable functions can agree on
`{A=a}` while differing on `{A≠a}` if `{A=a}` is invisible to `m`. The overlap
condition exactly captures the "m sees {A=a}" requirement.

Proof sketch: let h = f - g (m-measurable). For any m-meas B,
  ∫_B h · 1_{A=a} dμ = 0  (from f =ᵐ[restrict {A=a}] g)
  = ∫_B h · E[1_{A=a} | m] dμ   (h is m-measurable, pull out of condExp)
So h · E[1_{A=a} | m] = 0 a.e. With E[1_{A=a}|m] > 0 a.e., h = 0 a.e.

Mathlib-contribution candidate. Used in `Proxy/Helpers/BridgeW.lean` and
`BridgeWZ.lean` for the `hKey` lift. -/
theorem ae_eq_of_ae_eq_restrict_arm
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {μ : @MeasureTheory.Measure Ω mΩ} [@MeasureTheory.IsFiniteMeasure Ω mΩ μ]
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {A : Ω → α} (a : α)
    {f g : Ω → ℝ}
    (_hfm : Measurable[m] f) (_hgm : Measurable[m] g)
    (_h : f =ᵐ[μ.restrict {ω | A ω = a}] g)
    (_h_overlap : ∀ s : Set Ω, MeasurableSet[m] s →
        μ (s ∩ {ω | A ω = a}) = 0 → μ s = 0) :
    f =ᵐ[μ] g := by
  let s : Set Ω := {ω | f ω ≠ g ω}
  have hs : MeasurableSet[m] s := by
    have heq : MeasurableSet[m] {ω | f ω = g ω} := measurableSet_eq_fun _hfm _hgm
    simpa [s, Set.compl_setOf] using heq.compl
  have hs_ambient : @MeasurableSet Ω mΩ s := hm _ hs
  have hs_arm_zero : μ (s ∩ {ω | A ω = a}) = 0 := by
    have hbad : (μ.restrict {ω | A ω = a}) s = 0 := by
      exact MeasureTheory.ae_iff.mp _h
    rwa [MeasureTheory.Measure.restrict_apply hs_ambient] at hbad
  have hs_zero : μ s = 0 := _h_overlap s hs hs_arm_zero
  exact MeasureTheory.ae_iff.mpr hs_zero

/-- **Y(a) inherits Y's a.e. upper bound under latent exchangeability + consistency.**

If `Y(a) ⟂ A | σ_UX` (latent exchangeability), `Y ≤ M` a.e., `Y =ᵐ[{A=a}] Y(a)`,
and `P(A=a | σ_UX) > 0` a.e. (overlap), then `Y(a) ≤ M` a.e. globally.

Proof sketch: by `CondIndepFun`, the conditional expectation of
`1_{Ya>M} * 1_{A=a}` factors into `E[1_{Ya>M}|σ_UX] * P(A=a|σ_UX)`.
Consistency and `Y ≤ M` make the intersection null, while overlap makes
`P(A=a|σ_UX)` positive a.e.; integrating then gives `μ{Ya > M} = 0`.

Mathlib-contribution candidate. -/
theorem ae_le_YofA_of_ae_le_Y
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    [@StandardBorelSpace Ω mΩ]
    {μ : @MeasureTheory.Measure Ω mΩ} [@MeasureTheory.IsFiniteMeasure Ω mΩ μ]
    {σ_UX : MeasurableSpace Ω} (_hσUX : σ_UX ≤ mΩ)
    {A : Ω → Bool} {Y Ya : Ω → ℝ}
    (_hA : @Measurable Ω Bool mΩ _ A)
    (_hY : @Measurable Ω ℝ mΩ _ Y)
    (_hYa : @Measurable Ω ℝ mΩ _ Ya)
    (a : Bool)
    (_latent_exch : ProbabilityTheory.CondIndepFun σ_UX _hσUX Ya A μ)
    (_consistency : Y =ᵐ[μ.restrict {ω | A ω = a}] Ya)
    (_h_overlap : ∀ s : Set Ω, MeasurableSet[σ_UX] s →
        μ (s ∩ {ω | A ω = a}) = 0 → μ s = 0)
    {M : ℝ} (_hY_le : ∀ᵐ ω ∂μ, Y ω ≤ M) :
    ∀ᵐ ω ∂μ, Ya ω ≤ M := by
  let E : Set Ω := {ω | A ω = a}
  let B : Set Ω := {ω | M < Ya ω}
  have hE : @MeasurableSet Ω mΩ E := by
    dsimp [E]
    exact _hA (measurableSet_singleton a)
  have hB : @MeasurableSet Ω mΩ B := by
    dsimp [B]
    exact _hYa measurableSet_Ioi
  have hYa_le_on_E : ∀ᵐ ω ∂μ.restrict E, Ya ω ≤ M := by
    filter_upwards [_consistency, MeasureTheory.ae_restrict_of_ae _hY_le] with ω hcons hYle
    rw [← hcons]
    exact hYle
  have hBE_zero : μ (B ∩ E) = 0 := by
    have hbad : (μ.restrict E) B = 0 := by
      have := MeasureTheory.ae_iff.mp hYa_le_on_E
      simpa [B, not_le] using this
    rwa [MeasureTheory.Measure.restrict_apply hB] at hbad
  have hCI :
      μ⟦B ∩ E | σ_UX⟧ =ᵐ[μ]
        fun ω => (μ⟦B | σ_UX⟧) ω * (μ⟦E | σ_UX⟧) ω := by
    have hraw :=
      (ProbabilityTheory.condIndepFun_iff_condExp_inter_preimage_eq_mul _hYa _hA).mp
        _latent_exch (Set.Ioi M) ({a} : Set Bool) measurableSet_Ioi
        (measurableSet_singleton a)
    simpa [B, E] using hraw
  have hBE_indicator_zero :
      Set.indicator (B ∩ E) (fun _ : Ω => (1 : ℝ)) =ᵐ[μ] 0 := by
    have hnot : ∀ᵐ ω ∂μ, ω ∉ B ∩ E := by
      rw [MeasureTheory.ae_iff]
      simpa using hBE_zero
    filter_upwards [hnot] with ω hω
    simp [Set.indicator_of_notMem, hω]
  have hCE_BE_zero : μ⟦B ∩ E | σ_UX⟧ =ᵐ[μ] 0 := by
    simpa using
      (MeasureTheory.condExp_congr_ae (m := σ_UX) (μ := μ) hBE_indicator_zero)
  have hE_pos : ∀ᵐ ω ∂μ, 0 < (μ⟦E | σ_UX⟧) ω := by
    simpa [E] using
      (ae_pos_condExp_indicator_of_le (mΩ := mΩ) (μ := μ)
        (m₁ := σ_UX) (m₂ := σ_UX) _hσUX _hσUX le_rfl _hA a _h_overlap)
  have hCE_B_zero : μ⟦B | σ_UX⟧ =ᵐ[μ] 0 := by
    have hprod_zero :
        (fun ω => (μ⟦B | σ_UX⟧) ω * (μ⟦E | σ_UX⟧) ω) =ᵐ[μ] 0 :=
      hCI.symm.trans hCE_BE_zero
    filter_upwards [hprod_zero, hE_pos] with ω hprod hpos
    exact (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hpos)
  haveI : MeasureTheory.IsFiniteMeasure (μ.trim _hσUX) :=
    MeasureTheory.isFiniteMeasure_trim _hσUX
  haveI : MeasureTheory.SigmaFinite (μ.trim _hσUX) := inferInstance
  have hB_zero : μ B = 0 := by
    have hInt_cond_zero : ∫ ω, (μ⟦B | σ_UX⟧) ω ∂μ = 0 := by
      simpa using MeasureTheory.integral_congr_ae hCE_B_zero
    have hInt_cond_eq :
        ∫ ω, (μ⟦B | σ_UX⟧) ω ∂μ
          = ∫ ω, Set.indicator B (fun _ : Ω => (1 : ℝ)) ω ∂μ := by
      exact MeasureTheory.integral_condExp _hσUX
    have hInt_B_zero :
        ∫ ω, Set.indicator B (fun _ : Ω => (1 : ℝ)) ω ∂μ = 0 :=
      hInt_cond_eq.symm.trans hInt_cond_zero
    have hB_real_zero : μ.real B = 0 := by
      rw [← MeasureTheory.integral_indicator_one (μ := μ) hB]
      exact hInt_B_zero
    exact (MeasureTheory.measureReal_eq_zero_iff (μ := μ) (s := B)).mp hB_real_zero
  rw [MeasureTheory.ae_iff]
  simpa [B, not_le] using hB_zero

/-- **Y(a) inherits Y's a.e. lower bound under latent exchangeability + consistency.**

Mirror of `ae_le_YofA_of_ae_le_Y` for the lower bound. Same overlap hypothesis required. -/
theorem ae_le_YofA_of_ae_le_Y_below
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    [@StandardBorelSpace Ω mΩ]
    {μ : @MeasureTheory.Measure Ω mΩ} [@MeasureTheory.IsFiniteMeasure Ω mΩ μ]
    {σ_UX : MeasurableSpace Ω} (_hσUX : σ_UX ≤ mΩ)
    {A : Ω → Bool} {Y Ya : Ω → ℝ}
    (_hA : @Measurable Ω Bool mΩ _ A)
    (_hY : @Measurable Ω ℝ mΩ _ Y)
    (_hYa : @Measurable Ω ℝ mΩ _ Ya)
    (a : Bool)
    (_latent_exch : ProbabilityTheory.CondIndepFun σ_UX _hσUX Ya A μ)
    (_consistency : Y =ᵐ[μ.restrict {ω | A ω = a}] Ya)
    (_h_overlap : ∀ s : Set Ω, MeasurableSet[σ_UX] s →
        μ (s ∩ {ω | A ω = a}) = 0 → μ s = 0)
    {M : ℝ} (_hY_ge : ∀ᵐ ω ∂μ, M ≤ Y ω) :
    ∀ᵐ ω ∂μ, M ≤ Ya ω := by
  have hneg : ∀ᵐ ω ∂μ, -Ya ω ≤ -M :=
    ae_le_YofA_of_ae_le_Y (mΩ := mΩ) (μ := μ) (σ_UX := σ_UX) _hσUX
      (A := A) (Y := fun ω => -Y ω) (Ya := fun ω => -Ya ω)
      _hA _hY.neg _hYa.neg a
      _latent_exch.neg_left
      (_consistency.mono fun ω hω => by simp [hω])
      _h_overlap
      (_hY_ge.mono fun ω hω => neg_le_neg hω)
  exact hneg.mono fun ω hω => neg_le_neg_iff.mp hω

end Causalean
