/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Likelihood-Ratio Arm Swap

This file proves `setIntegral_eq_setIntegral_mul_of_likelihoodRatio_swap`, an abstract
change-of-measure identity for replacing an integral over one treatment arm by an
integral over another arm with a likelihood-ratio weight. The result is used by proximal
partial-identification arguments and is formulated as a general measure-theoretic helper
independent of causal model structure. -/

namespace Causalean

open MeasureTheory ProbabilityTheory

/-- **Arm-swap via likelihood ratio.** For [a sub-σ-algebra `m` of the ambient σ-algebra on
`Ω`](hyp:hm), a finite measure `μ`, and [measurable sets `s` and `t`](hyp:hs_meas,ht_meas),
suppose [the product `f · L` is almost-everywhere strongly measurable relative to
`m`](hyp:hprod_m), [the integrand `f` itself is almost-everywhere strongly measurable relative
to `m`](hyp:hf_m), [`f` restricted to the source set `t` is integrable](hyp:hint), [the product
`f · L` restricted to the target set `s` is integrable](hyp:hint'), and [the likelihood ratio
`L` satisfies the change-of-measure relation: the conditional probability of `s` given `m`,
times `L`, agrees `μ`-almost everywhere with the conditional probability of `t` given
`m`](hyp:hSpec). Then [the integral of `f` over `t` equals the integral of `f · L` over
`s`](goal): `∫ₜ f dμ = ∫ₛ f · L dμ`.

Proof outline:
1. `integral_indicator` rewrites both set-integrals as
   `∫ 𝟙t · f dμ` and `∫ 𝟙s · (f · L) dμ`.
2. `integral_condExp` lifts each to `∫ μ[𝟙t · f | m] dμ` and
   `∫ μ[𝟙s · (f·L) | m] dμ`.
3. `condExp_mul_of_aestronglyMeasurable_left` pulls `f` (resp. `f · L`) out
   of the conditional expectation since both have the required a.e. measurability, leaving
   `f · μ[𝟙t | m]` and `(f · L) · μ[𝟙s | m]`.
4. The hypothesis `hSpec` rewrites `μ[𝟙t | m]` as
   `μ[𝟙s | m] · L`, identifying the two integrands μ-a.e.

Mathlib-contribution candidate. -/
lemma setIntegral_eq_setIntegral_mul_of_likelihoodRatio_swap
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (s t : Set Ω) (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t)
    {L f : Ω → ℝ}
    (hprod_m : AEStronglyMeasurable[m] (fun ω => f ω * L ω) μ)
    (hf_m : AEStronglyMeasurable[m] f μ)
    (hint : IntegrableOn f t μ)
    (hint' : IntegrableOn (fun ω => f ω * L ω) s μ)
    (hSpec :
      (fun ω =>
          (μ[Set.indicator s (fun _ => (1 : ℝ)) | m]) ω * L ω)
        =ᵐ[μ]
        (μ[Set.indicator t (fun _ => (1 : ℝ)) | m])) :
    ∫ ω in t, f ω ∂μ = ∫ ω in s, f ω * L ω ∂μ := by
  -- Set up the indicator notations (as functions, not via `set`, to avoid
  -- definitional unfolding issues with `condExp_mul_of_aestronglyMeasurable_left`).
  let Ia : Ω → ℝ := Set.indicator s (fun _ => (1 : ℝ))
  let Ia' : Ω → ℝ := Set.indicator t (fun _ => (1 : ℝ))
  have hIa_meas : Measurable Ia := by fun_prop
  have hIa'_meas : Measurable Ia' := by fun_prop
  have hIa_le : ∀ ω, ‖Ia ω‖ ≤ 1 := by
    intro ω; by_cases h : ω ∈ s
    · simp [Ia, Set.indicator_of_mem h]
    · simp [Ia, Set.indicator_of_notMem h]
  have hIa'_le : ∀ ω, ‖Ia' ω‖ ≤ 1 := by
    intro ω; by_cases h : ω ∈ t
    · simp [Ia', Set.indicator_of_mem h]
    · simp [Ia', Set.indicator_of_notMem h]
  -- σ-finiteness of the trim, needed for `integral_condExp`.
  haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  haveI : SigmaFinite (μ.trim hm) := inferInstance
  -- Integrability of indicators (against μ).
  have hIa_int : Integrable Ia μ := by
    refine (integrable_const (1 : ℝ)).mono' hIa_meas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (by intro ω; simpa using hIa_le ω)
  have hIa'_int : Integrable Ia' μ := by
    refine (integrable_const (1 : ℝ)).mono' hIa'_meas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (by intro ω; simpa using hIa'_le ω)
  -- Step A: `∫ₜ f dμ = ∫ f · Ia' dμ`.
  have hStepA : ∫ ω in t, f ω ∂μ
      = ∫ ω, f ω * Ia' ω ∂μ := by
    rw [← integral_indicator (μ := μ) ht_meas]
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro ω; by_cases h : ω ∈ t
    · simp [Ia', Set.indicator_of_mem h]
    · simp [Ia', Set.indicator_of_notMem h]
  -- Step B (symmetric): `∫ₛ f · L dμ = ∫ (f · L) · Ia dμ`.
  have hStepB : ∫ ω in s, f ω * L ω ∂μ
      = ∫ ω, (f ω * L ω) * Ia ω ∂μ := by
    rw [← integral_indicator (μ := μ) hs_meas]
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro ω; by_cases h : ω ∈ s
    · simp [Ia, Set.indicator_of_mem h]
    · simp [Ia, Set.indicator_of_notMem h]
  -- Integrability of pointwise products (f * Ia') and ((f*L) * Ia).
  -- These equal the indicator-times-f and indicator-times-(f·L) functions, so
  -- IntegrableOn-on-t (resp. s) gives global integrability.
  have hint_f_Ia' : Integrable (fun ω => f ω * Ia' ω) μ := by
    have h_eq : (fun ω => f ω * Ia' ω) = t.indicator f := by
      funext ω
      by_cases h : ω ∈ t
      · simp [Ia', Set.indicator_of_mem h]
      · simp [Ia', Set.indicator_of_notMem h]
    rw [h_eq]
    exact hint.integrable_indicator ht_meas
  have hint_fL_Ia : Integrable (fun ω => (f ω * L ω) * Ia ω) μ := by
    have h_eq : (fun ω => (f ω * L ω) * Ia ω)
        = s.indicator (fun ω => f ω * L ω) := by
      funext ω
      by_cases h : ω ∈ s
      · simp [Ia, Set.indicator_of_mem h]
      · simp [Ia, Set.indicator_of_notMem h]
    rw [h_eq]
    exact hint'.integrable_indicator hs_meas
  -- Pull-out: `μ[f * Ia' | m] =ᵐ f · μ[Ia' | m]`.
  have hpull' : (μ[fun ω => f ω * Ia' ω | m]) =ᵐ[μ]
      (fun ω => f ω * (μ[Ia' | m]) ω) := by
    have h := condExp_mul_of_aestronglyMeasurable_left (μ := μ) (m := m)
      (f := f) (g := Ia') hf_m hint_f_Ia' hIa'_int
    -- h : μ[f * Ia' | m] =ᵐ f * μ[Ia' | m]   (Pi product)
    exact h
  -- Pull-out: `μ[(f*L) * Ia | m] =ᵐ (f·L) · μ[Ia | m]`.
  have hpull : (μ[fun ω => (f ω * L ω) * Ia ω | m]) =ᵐ[μ]
      (fun ω => (f ω * L ω) * (μ[Ia | m]) ω) := by
    have h := condExp_mul_of_aestronglyMeasurable_left (μ := μ) (m := m)
      (f := fun ω => f ω * L ω) (g := Ia) hprod_m
      hint_fL_Ia hIa_int
    exact h
  -- Compute LHS: lift indicator integral, then condExp tower, then pull-out.
  have hLHS : ∫ ω in t, f ω ∂μ
      = ∫ ω, f ω * (μ[Ia' | m]) ω ∂μ := by
    rw [hStepA, ← integral_condExp hm (f := fun ω => f ω * Ia' ω)]
    exact integral_congr_ae hpull'
  -- Compute RHS.
  have hRHS : ∫ ω in s, f ω * L ω ∂μ
      = ∫ ω, (f ω * L ω) * (μ[Ia | m]) ω ∂μ := by
    rw [hStepB, ← integral_condExp hm (f := fun ω => (f ω * L ω) * Ia ω)]
    exact integral_congr_ae hpull
  -- Identify the two integrands via `hSpec`.
  rw [hLHS, hRHS]
  refine integral_congr_ae ?_
  filter_upwards [hSpec] with ω hω
  -- hω : (μ[Ia | m]) ω * L ω = (μ[Ia' | m]) ω
  -- Goal: f ω * (μ[Ia' | m]) ω = (f ω * L ω) * (μ[Ia | m]) ω
  rw [← hω]; ring

end Causalean
