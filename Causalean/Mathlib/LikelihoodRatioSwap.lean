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

/-- **Arm-swap via likelihood ratio.**

If `L : Ω → ℝ` is `m`-measurable and satisfies the change-of-measure
relation

    (μ[𝟙{A=a} | m]) · L  =ᵐ[μ]  (μ[𝟙{A=a'} | m]),

then for any `m`-measurable real-valued integrand `f` whose restriction to
the source arm `{A = a'}` is integrable and whose product `f · L` restricted
to the target arm `{A = a}` is integrable,

    ∫_{A=a'} f dμ  =  ∫_{A=a} f · L dμ.

Proof outline:
1. `integral_indicator` rewrites both set-integrals as
   `∫ 𝟙_{A=...} · f dμ` and `∫ 𝟙_{A=a} · (f · L) dμ`.
2. `integral_condExp` lifts each to `∫ μ[𝟙_{...} · f | m] dμ` and
   `∫ μ[𝟙_{A=a} · (f·L) | m] dμ`.
3. `condExp_mul_of_stronglyMeasurable_right` pulls `f` (resp. `f · L`) out
   of the conditional expectation since both are `m`-measurable, leaving
   `f · μ[𝟙_{A=a'} | m]` and `(f · L) · μ[𝟙_{A=a} | m]`.
4. The hypothesis `hSpec` rewrites `μ[𝟙_{A=a'} | m]` as
   `μ[𝟙_{A=a} | m] · L`, identifying the two integrands μ-a.e.

Mathlib-contribution candidate. -/
lemma setIntegral_eq_setIntegral_mul_of_likelihoodRatio_swap
    {Ω α : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {A : Ω → α} (hA : Measurable A) (a a' : α)
    {L f : Ω → ℝ}
    (hL_m : Measurable[m] L) (hf_m : Measurable[m] f)
    (hint : IntegrableOn f {ω | A ω = a'} μ)
    (hint' : IntegrableOn (fun ω => f ω * L ω) {ω | A ω = a} μ)
    (hSpec :
      (fun ω =>
          (μ[Set.indicator {ω' | A ω' = a} (fun _ => (1 : ℝ)) | m]) ω * L ω)
        =ᵐ[μ]
        (μ[Set.indicator {ω' | A ω' = a'} (fun _ => (1 : ℝ)) | m])) :
    ∫ ω in {ω | A ω = a'}, f ω ∂μ
      = ∫ ω in {ω | A ω = a}, f ω * L ω ∂μ := by
  -- Set up the indicator notations (as functions, not via `set`, to avoid
  -- definitional unfolding issues with `condExp_mul_of_stronglyMeasurable_left`).
  let Ia : Ω → ℝ := Set.indicator {ω' | A ω' = a} (fun _ => (1 : ℝ))
  let Ia' : Ω → ℝ := Set.indicator {ω' | A ω' = a'} (fun _ => (1 : ℝ))
  have hsa_meas : MeasurableSet {ω | A ω = a} := hA (measurableSet_singleton a)
  have hsa'_meas : MeasurableSet {ω | A ω = a'} := hA (measurableSet_singleton a')
  have hIa_meas : Measurable Ia :=
    (measurable_const).indicator hsa_meas
  have hIa'_meas : Measurable Ia' :=
    (measurable_const).indicator hsa'_meas
  have hIa_le : ∀ ω, ‖Ia ω‖ ≤ 1 := by
    intro ω; by_cases h : A ω = a
    · simp [Ia, Set.indicator_of_mem (show ω ∈ {ω' | A ω' = a} from h)]
    · simp [Ia, Set.indicator_of_notMem (show ω ∉ {ω' | A ω' = a} from h)]
  have hIa'_le : ∀ ω, ‖Ia' ω‖ ≤ 1 := by
    intro ω; by_cases h : A ω = a'
    · simp [Ia', Set.indicator_of_mem (show ω ∈ {ω' | A ω' = a'} from h)]
    · simp [Ia', Set.indicator_of_notMem (show ω ∉ {ω' | A ω' = a'} from h)]
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
  -- Step A: `∫_{A=a'} f dμ = ∫ f · Ia' dμ`.
  have hStepA : ∫ ω in {ω | A ω = a'}, f ω ∂μ
      = ∫ ω, f ω * Ia' ω ∂μ := by
    rw [← integral_indicator (μ := μ) hsa'_meas]
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro ω; by_cases h : A ω = a'
    · simp [Ia', Set.indicator_of_mem (show ω ∈ {ω' | A ω' = a'} from h)]
    · simp [Ia', Set.indicator_of_notMem (show ω ∉ {ω' | A ω' = a'} from h)]
  -- Step B (symmetric): `∫_{A=a} f · L dμ = ∫ (f · L) · Ia dμ`.
  have hStepB : ∫ ω in {ω | A ω = a}, f ω * L ω ∂μ
      = ∫ ω, (f ω * L ω) * Ia ω ∂μ := by
    rw [← integral_indicator (μ := μ) hsa_meas]
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro ω; by_cases h : A ω = a
    · simp [Ia, Set.indicator_of_mem (show ω ∈ {ω' | A ω' = a} from h)]
    · simp [Ia, Set.indicator_of_notMem (show ω ∉ {ω' | A ω' = a} from h)]
  -- Lift m-measurability to mΩ-measurability.
  have hf_mΩ : Measurable f := hf_m.mono hm le_rfl
  have hL_mΩ : Measurable L := hL_m.mono hm le_rfl
  have hfL_mΩ : Measurable (fun ω => f ω * L ω) := hf_mΩ.mul hL_mΩ
  -- Integrability of pointwise products (f * Ia') and ((f*L) * Ia).
  -- These equal the indicator-times-f and indicator-times-(f·L) functions, so
  -- IntegrableOn-on-{A=a'} (resp. {A=a}) gives global integrability.
  have hint_f_Ia' : Integrable (fun ω => f ω * Ia' ω) μ := by
    have h_eq : (fun ω => f ω * Ia' ω) = ({ω' | A ω' = a'}).indicator f := by
      funext ω
      by_cases h : ω ∈ {ω' | A ω' = a'}
      · simp [Ia', Set.indicator_of_mem h]
      · simp [Ia', Set.indicator_of_notMem h]
    rw [h_eq]
    exact hint.integrable_indicator hsa'_meas
  have hint_fL_Ia : Integrable (fun ω => (f ω * L ω) * Ia ω) μ := by
    have h_eq : (fun ω => (f ω * L ω) * Ia ω)
        = ({ω' | A ω' = a}).indicator (fun ω => f ω * L ω) := by
      funext ω
      by_cases h : ω ∈ {ω' | A ω' = a}
      · simp [Ia, Set.indicator_of_mem h]
      · simp [Ia, Set.indicator_of_notMem h]
    rw [h_eq]
    exact hint'.integrable_indicator hsa_meas
  -- Pull-out: `μ[f * Ia' | m] =ᵐ f · μ[Ia' | m]` (f is m-measurable).
  have hpull' : (μ[fun ω => f ω * Ia' ω | m]) =ᵐ[μ]
      (fun ω => f ω * (μ[Ia' | m]) ω) := by
    have h := condExp_mul_of_stronglyMeasurable_left (μ := μ) (m := m)
      (f := f) (g := Ia') hf_m.stronglyMeasurable hint_f_Ia' hIa'_int
    -- h : μ[f * Ia' | m] =ᵐ f * μ[Ia' | m]   (Pi product)
    exact h
  -- Pull-out: `μ[(f*L) * Ia | m] =ᵐ (f·L) · μ[Ia | m]`.
  have hpull : (μ[fun ω => (f ω * L ω) * Ia ω | m]) =ᵐ[μ]
      (fun ω => (f ω * L ω) * (μ[Ia | m]) ω) := by
    have h := condExp_mul_of_stronglyMeasurable_left (μ := μ) (m := m)
      (f := fun ω => f ω * L ω) (g := Ia) (hf_m.mul hL_m).stronglyMeasurable
      hint_fL_Ia hIa_int
    exact h
  -- Compute LHS: lift indicator integral, then condExp tower, then pull-out.
  have hLHS : ∫ ω in {ω | A ω = a'}, f ω ∂μ
      = ∫ ω, f ω * (μ[Ia' | m]) ω ∂μ := by
    rw [hStepA, ← integral_condExp hm (f := fun ω => f ω * Ia' ω)]
    exact integral_congr_ae hpull'
  -- Compute RHS.
  have hRHS : ∫ ω in {ω | A ω = a}, f ω * L ω ∂μ
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
