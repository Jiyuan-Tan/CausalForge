/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.RadonNikodym
import Mathlib.Probability.Kernel.RadonNikodym

/-!
# Radon–Nikodym derivative of a composition-product against a σ-finite fibre reference

Mathlib's `ProbabilityTheory.rnDeriv_compProd`
(`Mathlib/Probability/Kernel/Composition/RadonNikodym.lean`) computes
`(μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η)` but leaves the conditional factor as
`(μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η)` rather than the fibre derivative `∂κ/∂η`, and its
kernel Radon–Nikodym API requires the reference **kernel** to be finite.

This file proves the product-reference formula used when a composition product is
compared against a product reference `ν ×ₘ ρ`.  It takes product
a.e.-measurability of the raw per-slice fibre derivative
`(a, b) ↦ (dκ_a/dρ)(b)` as an explicit hypothesis; with that representative in
hand the fibre reference `ρ` need only be **σ-finite**, so the public theorem
`rnDeriv_compProd_prod_sigmaFinite` covers continuous references (Lebesgue), not
just finite/discrete ones.  It takes the μ-a.e. fibre domination `κ_a ≪ ρ`
directly as a hypothesis (rather than re-deriving it from joint domination, which
would route through the finite kernel `Kernel.const α ρ`), and assembles the
formula by `withDensity` bookkeeping that never needs `ρ` to be finite.

The remaining Mathlib gap is only in *constructing* that measurable fibre density
automatically: when `ρ` is infinite, `Kernel.const α ρ` is not a finite kernel, so
the current kernel RN API cannot build a jointly measurable σ-finite
representative.  Callers that already possess such a representative (for instance
from a stepwise fibre Radon–Nikodym assumption) obtain the full σ-finite formula
here.
-/


open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

private lemma compProd_eq_prod_withDensity_fiber
    (μ : Measure α) (ρ : Measure β) (κ : Kernel α β)
    [SFinite μ] [SigmaFinite ρ] [IsSFiniteKernel κ]
    (hfiber : ∀ᵐ a ∂μ, κ a ≪ ρ)
    (hmeas : AEMeasurable (fun p : α × β => (κ p.1).rnDeriv ρ p.2) (μ.prod ρ)) :
    μ ⊗ₘ κ = (μ.prod ρ).withDensity
      (fun p : α × β => (κ p.1).rnDeriv ρ p.2) := by
  ext s hs
  rw [Measure.compProd_apply hs, withDensity_apply _ hs]
  rw [← lintegral_indicator hs]
  rw [lintegral_prod]
  · refine lintegral_congr_ae ?_
    filter_upwards [hfiber] with a ha
    have hsec : MeasurableSet (Prod.mk a ⁻¹' s) := measurable_prodMk_left hs
    change (κ a) (Prod.mk a ⁻¹' s) =
      ∫⁻ y, (Prod.mk a ⁻¹' s).indicator (fun y => (κ a).rnDeriv ρ y) y ∂ρ
    rw [lintegral_indicator hsec]
    rw [← Measure.setLIntegral_rnDeriv ha (Prod.mk a ⁻¹' s)]
  · exact hmeas.indicator hs

/-- **σ-finite-reference Radon–Nikodym derivative of a composition-product.**

For a finite measure `μ`, a σ-finite base reference `ν`, a **σ-finite** fibre
reference `ρ`, and a finite kernel `κ`, assume base domination `μ ≪ ν`, μ-a.e.
fibre domination `κ_a ≪ ρ`, and product a.e.-measurability of the raw per-slice
fibre derivative.  Then the Radon–Nikodym derivative of the composition-product
`μ ⊗ₘ κ` with respect to the product reference `ν ×ₘ ρ` is, almost everywhere, the
product of the base derivative and the fibre derivative:
`d(μ ⊗ₘ κ)/d(ν ×ₘ ρ)(a, b) = f(a) · (dκ_a/dρ)(b)` for any `f =ᵐ[ν] dμ/dν`. -/
lemma rnDeriv_compProd_prod_sigmaFinite
    (μ ν : Measure α) (ρ : Measure β) (κ : Kernel α β) (f : α → ℝ≥0∞)
    [IsFiniteMeasure μ] [SigmaFinite ν] [SigmaFinite ρ] [IsFiniteKernel κ]
    (hμν : μ ≪ ν) (hfiber : ∀ᵐ a ∂μ, κ a ≪ ρ)
    (hfiber_meas :
      AEMeasurable (fun p : α × β => (κ p.1).rnDeriv ρ p.2) (ν.prod ρ))
    (hf : μ.rnDeriv ν =ᵐ[ν] f) :
    (μ ⊗ₘ κ).rnDeriv (ν.prod ρ)
      =ᵐ[ν.prod ρ] fun p => f p.1 * (κ p.1).rnDeriv ρ p.2 := by
  have hprod_ac : μ.prod ρ ≪ ν.prod ρ := hμν.prod Measure.AbsolutelyContinuous.rfl
  have hfiber_meas_mu :
      AEMeasurable (fun p : α × β => (κ p.1).rnDeriv ρ p.2) (μ.prod ρ) :=
    hfiber_meas.mono_ac hprod_ac
  have hcomp :
      μ ⊗ₘ κ =
        (μ.prod ρ).withDensity (fun p : α × β => (κ p.1).rnDeriv ρ p.2) :=
    compProd_eq_prod_withDensity_fiber (μ := μ) (ρ := ρ) (κ := κ)
      hfiber hfiber_meas_mu
  have hbase :
      μ.prod ρ = (ν.prod ρ).withDensity (fun p : α × β => μ.rnDeriv ν p.1) := by
    calc
      μ.prod ρ = (ν.withDensity (μ.rnDeriv ν)).prod ρ := by
        rw [Measure.withDensity_rnDeriv_eq μ ν hμν]
      _ = (ν.prod ρ).withDensity (fun p : α × β => μ.rnDeriv ν p.1) := by
        exact prod_withDensity_left₀ (Measure.measurable_rnDeriv μ ν).aemeasurable
  have hmain :
      μ ⊗ₘ κ = (ν.prod ρ).withDensity
        (fun p : α × β => μ.rnDeriv ν p.1 * (κ p.1).rnDeriv ρ p.2) := by
    rw [hcomp, hbase]
    rw [← withDensity_mul₀]
    · rfl
    · exact (Measure.measurable_rnDeriv μ ν).aemeasurable.comp_fst
    · exact hfiber_meas
  have hmeas_main :
      AEMeasurable
        (fun p : α × β => μ.rnDeriv ν p.1 * (κ p.1).rnDeriv ρ p.2)
        (ν.prod ρ) := by
    exact ((Measure.measurable_rnDeriv μ ν).aemeasurable.comp_fst).mul hfiber_meas
  have hμrn :
      (μ ⊗ₘ κ).rnDeriv (ν.prod ρ)
        =ᵐ[ν.prod ρ]
          fun p : α × β => μ.rnDeriv ν p.1 * (κ p.1).rnDeriv ρ p.2 := by
    rw [hmain]
    exact Measure.rnDeriv_withDensity₀ (ν.prod ρ) hmeas_main
  have hf_fst : (fun p : α × β => μ.rnDeriv ν p.1) =ᵐ[ν.prod ρ] fun p => f p.1 := by
    simpa [Function.comp_def] using
      (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := ρ)).ae_eq_comp hf
  have h_prod :
      (fun p : α × β => μ.rnDeriv ν p.1 * (κ p.1).rnDeriv ρ p.2)
        =ᵐ[ν.prod ρ] fun p => f p.1 * (κ p.1).rnDeriv ρ p.2 := by
    filter_upwards [hf_fst] with p hp
    rw [hp]
  exact hμrn.trans h_prod

end MeasureTheory
