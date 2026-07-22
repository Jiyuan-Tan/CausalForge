/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.Core

/-!
# Base Localized Events for Primal NPIV

This file supplies the shared Ω-side infrastructure for turning product-space
localized deviation inequalities into events on the ambient sample space.  The
law bridge `integral_comp_law_W` rewrites population means under the observation
law as integrals over `S.W`, and `localized_omega_event_sharp_for_bundle`
pulls the sharp localized event for an abstract `LocalizedRegimeBundle` back
along an IID sample.  The class-specific event files for `H`, `F`, `H · F`, and
`m ∘ F` instantiate this wrapper through their `LocalizedRegimes`
interpretation fields.
-/

namespace Causalean
namespace Estimation
namespace NPIV
namespace Primal

open MeasureTheory Causalean.Stat Causalean.Stat.Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Per-class Ω-side localized deviation helpers

The four helpers below isolate the deferred infrastructure obligation:
each takes a `LocalizedRegimes` value at sample size `n` and produces an
Ω-event of mass `≥ 1 - δ` on which the empirical-vs-population deviation
along the **first `n` observations of the IID sample** is bounded by the
localized rate, *for the relevant concrete function class*.

The helpers are stated abstractly in `n`: callers in the public theorems
below instantiate `n := split.n₁ horizon` so the deviation is on the
fold-A subsample.  This works because the IID sample restricted to any
finite index set is again IID with marginal `P_W`.

The concrete helpers are routine applications of
`localized_uniform_deviation`, followed by the IID-sample joint
pushforward identity, the per-bundle interpretation fields linking the
abstract class to the concrete NPIV losses, and the law bridge
`regime.law_W`.  The shared wrapper pulls the product-space sharp event back along
the IID sample and keeps the diameter obligation available for each concrete index. -/

/-- Integrating a measurable function under the law of the observed variable is the same as
integrating its pullback over the ambient sample space. -/
lemma integral_comp_law_W
    {S : OperatorSystem Ω μ} {P_W : Measure S.𝒲}
    (hlaw : μ.map S.W = P_W)
    {g : S.𝒲 → ℝ} (hg : Measurable g) :
    ∫ w, g w ∂P_W = ∫ ω, g (S.W ω) ∂μ := by
  rw [← hlaw]
  exact MeasureTheory.integral_map S.meas_W.aemeasurable hg.aestronglyMeasurable

/-- Ω-side Foster--Syrgkanis sharp localized event for a single NPIV
`LocalizedRegimeBundle`.

This is the NPIV-facing wrapper around
`localized_uniform_deviation_sharp`: it transports the product-space event
for `(Fin n → S.𝒲)` back to the ambient sample space through `sample` and
rewrites the population mean under `P_W` as an integral over `S.W`.
Concrete HF/mF/F/H event lemmas can instantiate the abstract index `i`
through their interpretation fields. -/
lemma localized_omega_event_sharp_for_bundle
    {S : OperatorSystem Ω μ} {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    [IsProbabilityMeasure μ]
    {n : ℕ} {δ_n Rmax : ℝ}
    (B : LocalizedRegimeBundle S.𝒲 P_W n δ_n)
    (h_law_W : μ.map S.W = P_W)
    (hn : 0 < n)
    {ζ : ℝ} (hζ_pos : 0 < ζ) (hζ_le : ζ ≤ 1)
    (hδn_pos : 0 < δ_n)
    (hRmax_lb : δ_n ≤ Rmax)
    (hslack : ∀ K : ℕ,
      Rmax ≤ δ_n * (2 : ℝ) ^ K →
      B.regime.b * Real.sqrt
          (2 * Real.log (2 * ((K : ℝ) + 1) / ζ) / n)
        ≤ δ_n ^ 2) :
    ∃ E : Set Ω,
      MeasurableSet E ∧ μ E ≥ 1 - ENNReal.ofReal ζ ∧
      ∀ ω ∈ E, ∀ i : B.ι,
        B.norm (B.F i) ≤ Rmax →
        |(n : ℝ)⁻¹ * ∑ k : Fin n, B.F i (B.X (sample.Z k ω))
            - ∫ ω', B.F i (B.X (S.W ω')) ∂μ|
          ≤ 8 * δ_n * B.norm (B.F i) + 5 * δ_n ^ 2 := by
  classical
  haveI : IsProbabilityMeasure P_W := by
    rw [← h_law_W]
    exact Measure.isProbabilityMeasure_map S.meas_W.aemeasurable
  obtain ⟨E₀, hE₀_meas, hE₀_prob, hE₀_bound⟩ :=
    localized_uniform_deviation_sharp B.F B.norm P_W B.X B.X_meas B.F_meas
      B.regime hζ_pos hζ_le n hn (ρ := δ_n) (Rmax := Rmax)
      B.crit_le hδn_pos hRmax_lb B.crit_pos B.crit_fp
      B.rad_bdd B.rad_int hslack
  let Ψ : Ω → (Fin n → S.𝒲) := fun ω k => sample.Z k ω
  let E : Set Ω := Ψ ⁻¹' E₀
  have hpull :=
    Causalean.Stat.event_pullback_along_iidSample sample n hE₀_meas hE₀_prob
  refine ⟨E, ?_, ?_, ?_⟩
  · simpa [E, Ψ] using hpull.1
  · simpa [E, Ψ] using hpull.2
  · intro ω hω i hi_diam
    have hω₀ : Ψ ω ∈ E₀ := by
      simpa [E, Ψ] using hω
    have hdev := hE₀_bound (Ψ ω) hω₀ i (B.norm_nonneg i) hi_diam
    have hpop :
        ∫ w, B.F i (B.X w) ∂P_W =
          ∫ ω', B.F i (B.X (S.W ω')) ∂μ := by
      exact integral_comp_law_W h_law_W ((B.F_meas i).comp B.X_meas)
    simpa [Ψ, hpop] using hdev

end Primal
end NPIV
end Estimation
end Causalean
