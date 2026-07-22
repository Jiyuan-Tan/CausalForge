/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Integrals Under Independent Variables

This file proves a drop-of-conditioning identity for independent random
variables: integrating a function of one variable over an event determined by
an independent variable factors into the event probability times the full
integral. The helper supports instrumental-variable identification arguments
while remaining a general measure-theoretic result. -/

namespace ProbabilityTheory

open MeasureTheory

/-- **Drop of conditioning.** If `f` and `g` are independent, then under Lean's
    unrestricted Bochner-integral convention the integral of `h ∘ g` restricted
    to `f ⁻¹' E` equals
    `μ(f ⁻¹' E).toReal * ∫ h ∘ g ∂μ`.  This is the core identity behind the
    IV first-stage and reduced-form derivations: conditioning on an event in
    the `f`-fiber drops out as a scalar factor when `g` is independent of `f`.

    The proof rewrites the set integral as an indicator-weighted integral,
    factors it via `IndepFun.integral_fun_comp_mul_comp`, and evaluates
    `∫ indicator_{f ⁻¹' E} 1` via `integral_indicator_one`. -/
theorem IndepFun.integral_restrict_preimage_eq_mul
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω}
    {f : Ω → α} {g : Ω → β} (hfg : IndepFun f g μ)
    (hf : Measurable f) (hg : Measurable g)
    {E : Set α} (hE : MeasurableSet E)
    {h : β → ℝ} (hh_meas : Measurable h) :
    ∫ ω in f ⁻¹' E, h (g ω) ∂μ
      = (μ (f ⁻¹' E)).toReal * ∫ ω, h (g ω) ∂μ := by
  classical
  -- `φ : α → ℝ` is the indicator of `E` as a plain function.
  set φ : α → ℝ := fun a => if a ∈ E then (1 : ℝ) else 0 with hφ_def
  have hφ_meas : Measurable φ :=
    Measurable.ite hE measurable_const measurable_const
  -- Pointwise: `φ (f ω) = (f ⁻¹' E).indicator 1 ω`.
  have hφ_indicator : ∀ ω,
      φ (f ω) = (f ⁻¹' E).indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ f ⁻¹' E
    · have hfE : f ω ∈ E := hω
      simp [hφ_def, hfE]
    · have hfE : f ω ∉ E := hω
      simp [hφ_def, hfE]
  -- Rewrite `∫ in f ⁻¹' E, ...` as `∫ φ(f) * h(g) dμ`.
  have heq_int : ∫ ω in f ⁻¹' E, h (g ω) ∂μ
      = ∫ ω, φ (f ω) * h (g ω) ∂μ := by
    rw [← MeasureTheory.integral_indicator (hf hE)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro ω
    by_cases hω : ω ∈ f ⁻¹' E
    · have hfE : f ω ∈ E := hω
      simp [hφ_def, hfE]
    · have hfE : f ω ∉ E := hω
      simp [hφ_def, hfE]
  -- Apply independence to factor the product integral.
  have hfAE : AEMeasurable f μ := hf.aemeasurable
  have hgAE : AEMeasurable g μ := hg.aemeasurable
  have hφAEStr : MeasureTheory.AEStronglyMeasurable φ (μ.map f) :=
    hφ_meas.aestronglyMeasurable
  have hhAEStr : MeasureTheory.AEStronglyMeasurable h (μ.map g) :=
    hh_meas.aestronglyMeasurable
  have hmul : ∫ ω, φ (f ω) * h (g ω) ∂μ
      = (∫ ω, φ (f ω) ∂μ) * ∫ ω, h (g ω) ∂μ :=
    hfg.integral_fun_comp_mul_comp hfAE hgAE hφAEStr hhAEStr
  -- `∫ φ(f) dμ = μ(f ⁻¹' E).toReal`.
  have hφint : ∫ ω, φ (f ω) ∂μ = (μ (f ⁻¹' E)).toReal := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hφ_indicator)]
    rw [MeasureTheory.integral_indicator_const (1 : ℝ) (hf hE)]
    simp [MeasureTheory.measureReal_def]
  rw [heq_int, hmul, hφint]

end ProbabilityTheory
