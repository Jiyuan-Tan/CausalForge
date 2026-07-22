/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Disintegration.Basic
import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# Composition-product assembly lemmas

This file packages recurring measure-kernel assembly steps for composition products.
The main lemmas turn an almost-everywhere equality of inner kernels on a product space
into equality of the resulting outer composition products:

* `compProd_eq_of_inner_ae`: the inner kernels are mixed against a fixed finite measure;
* `compProd_eq_of_inner_ae_kernel`: the inner kernels are mixed against an indexed finite
  kernel;
* `compProd_map_snd_apply`: the second-coordinate marginal of a kernel composition product
  is the bind of the section of the inner kernel against the outer kernel value.

These results isolate the Fubini-style steps that otherwise require repeating
`Measure.ext_prod`, `compProd_apply_prod`, `ae_ae_of_ae_compProd`, and
`lintegral_congr_ae`.
-/

namespace Causalean.Mathlib.CompProdAssembly

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory

/-- **CompProd assembly from an a.e. inner equality.**

    If `KL`/`KR` are the `μ`-mixtures of the `a`-sections of `fL`/`fR`
    (`KL a = (fL.sectR a) ∘ₘ μ`), and `fL = fR` holds `(ν ⊗ₘ const μ)`-a.e., then
    `ν ⊗ₘ KL = ν ⊗ₘ KR`. -/
theorem compProd_eq_of_inner_ae
    {α γ β : Type*} [MeasurableSpace α] [MeasurableSpace γ] [MeasurableSpace β]
    (ν : Measure α) [IsFiniteMeasure ν] (μ : Measure γ) [IsFiniteMeasure μ]
    (KL KR : Kernel α β) [IsFiniteKernel KL] [IsSFiniteKernel KR]
    (fL fR : Kernel (α × γ) β)
    (hL : ∀ a, KL a = (fL.sectR a) ∘ₘ μ)
    (hR : ∀ a, KR a = (fR.sectR a) ∘ₘ μ)
    (hae : ∀ᵐ p ∂(ν ⊗ₘ Kernel.const α μ), fL p = fR p) :
    ν ⊗ₘ KL = ν ⊗ₘ KR := by
  refine MeasureTheory.Measure.ext_prod (fun {A B} hA hB => ?_)
  rw [MeasureTheory.Measure.compProd_apply_prod hA hB,
      MeasureTheory.Measure.compProd_apply_prod hA hB]
  have hInnerL : ∀ a, (KL a) B = ∫⁻ c, (fL (a, c)) B ∂μ := by
    intro a
    rw [hL a, MeasureTheory.Measure.bind_apply hB
        (ProbabilityTheory.Kernel.aemeasurable _)]
    simp only [ProbabilityTheory.Kernel.sectR_apply]
  have hInnerR : ∀ a, (KR a) B = ∫⁻ c, (fR (a, c)) B ∂μ := by
    intro a
    rw [hR a, MeasureTheory.Measure.bind_apply hB
        (ProbabilityTheory.Kernel.aemeasurable _)]
    simp only [ProbabilityTheory.Kernel.sectR_apply]
  simp only [hInnerL, hInnerR]
  have hae' := MeasureTheory.Measure.ae_ae_of_ae_compProd hae
  have hInnerAE :
      ∀ᵐ a ∂ν, (∫⁻ c, (fL (a, c)) B ∂μ) = ∫⁻ c, (fR (a, c)) B ∂μ := by
    filter_upwards [hae'] with a ha
    refine MeasureTheory.lintegral_congr_ae ?_
    have ha' : ∀ᵐ c ∂μ, fL (a, c) = fR (a, c) := by
      simpa only [ProbabilityTheory.Kernel.const_apply] using ha
    filter_upwards [ha'] with c hc
    rw [hc]
  exact MeasureTheory.lintegral_congr_ae (MeasureTheory.ae_restrict_of_ae hInnerAE)

/-- **CompProd assembly from an a.e. inner equality, indexed-integrator form.**

    If `KL`/`KR` are mixtures of the `a`-sections of `fL`/`fR` against an
    `a`-indexed kernel `κ`, and `fL = fR` holds `(ν ⊗ₘ κ)`-a.e., then
    `ν ⊗ₘ KL = ν ⊗ₘ KR`.  This is the indexed analogue of
    `compProd_eq_of_inner_ae`; it is useful when the inner integration law is a
    conditional kernel rather than a fixed marginal. -/
theorem compProd_eq_of_inner_ae_kernel
    {α γ β : Type*} [MeasurableSpace α] [MeasurableSpace γ] [MeasurableSpace β]
    (ν : Measure α) [IsFiniteMeasure ν] (κ : Kernel α γ) [IsFiniteKernel κ]
    (KL KR : Kernel α β) [IsFiniteKernel KL] [IsSFiniteKernel KR]
    (fL fR : Kernel (α × γ) β)
    (hL : ∀ a, KL a = (fL.sectR a) ∘ₘ κ a)
    (hR : ∀ a, KR a = (fR.sectR a) ∘ₘ κ a)
    (hae : ∀ᵐ p ∂(ν ⊗ₘ κ), fL p = fR p) :
    ν ⊗ₘ KL = ν ⊗ₘ KR := by
  refine MeasureTheory.Measure.ext_prod (fun {A B} hA hB => ?_)
  rw [MeasureTheory.Measure.compProd_apply_prod hA hB,
      MeasureTheory.Measure.compProd_apply_prod hA hB]
  have hInnerL : ∀ a, (KL a) B = ∫⁻ c, (fL (a, c)) B ∂(κ a) := by
    intro a
    rw [hL a, MeasureTheory.Measure.bind_apply hB
        (ProbabilityTheory.Kernel.aemeasurable _)]
    simp only [ProbabilityTheory.Kernel.sectR_apply]
  have hInnerR : ∀ a, (KR a) B = ∫⁻ c, (fR (a, c)) B ∂(κ a) := by
    intro a
    rw [hR a, MeasureTheory.Measure.bind_apply hB
        (ProbabilityTheory.Kernel.aemeasurable _)]
    simp only [ProbabilityTheory.Kernel.sectR_apply]
  simp only [hInnerL, hInnerR]
  have hae' := MeasureTheory.Measure.ae_ae_of_ae_compProd hae
  have hInnerAE :
      ∀ᵐ a ∂ν, (∫⁻ c, (fL (a, c)) B ∂(κ a)) = ∫⁻ c, (fR (a, c)) B ∂(κ a) := by
    filter_upwards [hae'] with a ha
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [ha] with c hc
    rw [hc]
  exact MeasureTheory.lintegral_congr_ae (MeasureTheory.ae_restrict_of_ae hInnerAE)

/-- **Snd-marginal of a composition product, pointwise (disintegration backbone).**

    The `Prod.snd`-pushforward of a kernel composition product, evaluated at `a`, is the
    mixture of the `a`-section of the inner kernel against the outer kernel's value:
    `((κ₁ ⊗ₖ κ₂).map Prod.snd) a = (κ₂.sectR a) ∘ₘ (κ₁ a)`.  This is the "adjustment /
    bind unfold" that every do-calculus identification factor performs by hand; naming it
    turns the recurring four-line `map_apply / compProd_apply_eq_compProd_sectR /
    Measure.snd / snd_compProd` rewrite chain into a single step. -/
theorem compProd_map_snd_apply
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (κ₁ : Kernel α β) (κ₂ : Kernel (α × β) γ)
    [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] (a : α) :
    ((κ₁ ⊗ₖ κ₂).map Prod.snd) a = (κ₂.sectR a) ∘ₘ (κ₁ a) := by
  rw [Kernel.map_apply _ measurable_snd,
      Kernel.compProd_apply_eq_compProd_sectR,
      ← Measure.snd, Measure.snd_compProd]

end Causalean.Mathlib.CompProdAssembly
