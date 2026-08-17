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

/-- **Drop of conditioning.** For [random elements `f` and `g` that are independent](hyp:hfg),
    with [`f` almost-everywhere measurable](hyp:hf_ae) and [`g` almost-everywhere
    measurable](hyp:hg), given [a measurable set `E`](hyp:hE) whose preimage
    [`f ⁻¹' E` is measurable](hyp:hpre), and [a function `h` that is almost-everywhere strongly
    measurable with respect to the pushforward measure of `g`](hyp:hh), then [restricting the
    integral of `h ∘ g` to the event `f ⁻¹' E` equals the probability of that event times the
    unrestricted integral of `h ∘ g`](goal).

    This is the core identity behind the
    IV first-stage and reduced-form derivations: conditioning on an event in
    the `f`-fiber drops out as a scalar factor when `g` is independent of `f`.

    The proof rewrites the set integral as an indicator-weighted integral,
    factors it via `IndepFun.integral_fun_comp_mul_comp`, and evaluates
    `∫ indicator_{f ⁻¹' E} 1` via `integral_indicator_one`. -/
theorem IndepFun.integral_restrict_preimage_eq_mul
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω}
    {f : Ω → α} {g : Ω → β} (hfg : IndepFun f g μ)
    (hf_ae : AEMeasurable f μ) (hg : AEMeasurable g μ)
    {E : Set α} (hE : MeasurableSet E)
    (hpre : MeasurableSet (f ⁻¹' E))
    {h : β → ℝ} (hh : AEStronglyMeasurable h (μ.map g)) :
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
    rw [← MeasureTheory.integral_indicator hpre]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro ω
    by_cases hω : ω ∈ f ⁻¹' E
    · have hfE : f ω ∈ E := hω
      simp [hφ_def, hfE]
    · have hfE : f ω ∉ E := hω
      simp [hφ_def, hfE]
  -- Apply independence to factor the product integral.
  have hfAE : AEMeasurable f μ := hf_ae
  have hgAE : AEMeasurable g μ := hg
  have hφAEStr : MeasureTheory.AEStronglyMeasurable φ (μ.map f) :=
    hφ_meas.aestronglyMeasurable
  have hmul : ∫ ω, φ (f ω) * h (g ω) ∂μ
      = (∫ ω, φ (f ω) ∂μ) * ∫ ω, h (g ω) ∂μ :=
    hfg.integral_fun_comp_mul_comp hfAE hgAE hφAEStr hh
  -- `∫ φ(f) dμ = μ(f ⁻¹' E).toReal`.
  have hφint : ∫ ω, φ (f ω) ∂μ = (μ (f ⁻¹' E)).toReal := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hφ_indicator)]
    rw [MeasureTheory.integral_indicator_const (1 : ℝ) hpre]
    simp [MeasureTheory.measureReal_def]
  rw [heq_int, hmul, hφint]

end ProbabilityTheory
