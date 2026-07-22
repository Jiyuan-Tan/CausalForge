/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# The graph push-forward of a product measure is a composition product

If `νₗ` is a probability measure on `γ` and `Φ : β × γ → δ` is measurable, then
pushing a product measure `α ⊗ νₗ` forward along the *graph map*
`(o, l) ↦ (o, Φ (o, l))` produces a composition product `α.compProd κ`, where the
disintegration kernel `κ o = νₗ.map (fun l => Φ (o, l))` reads the first
coordinate as a parameter and pushes the `γ`-marginal through the slice of `Φ`.

This is the abstract measure-theoretic core of "exogenous noise plus a structural
mechanism gives an environment-invariant conditional law": the predictor marginal
is `α`, the exogenous-noise law is `νₗ`, the mechanism is `Φ`, and the resulting
conditional law of the response given the predictor is the kernel `κ`.
-/

namespace Causalean.Mathlib.GraphMapProd

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {β γ δ : Type*} [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

/-- The structural-mechanism kernel `κ o = νₗ.map (Φ (o, ·))`: at each value `o` of
the first coordinate, push the `γ`-marginal `νₗ` through the slice `l ↦ Φ (o, l)`.
Built as the deterministic-times-constant product kernel
`(Kernel.id ×ₖ Kernel.const β νₗ)` mapped through `Φ`. -/
noncomputable def mechanismKernel (νₗ : Measure γ) (Φ : β × γ → δ) :
    ProbabilityTheory.Kernel β δ :=
  ((ProbabilityTheory.Kernel.id : ProbabilityTheory.Kernel β β).prod
    (ProbabilityTheory.Kernel.const β νₗ)).map Φ

/-- Pointwise value of `mechanismKernel`: `κ o = νₗ.map (fun l => Φ (o, l))`. -/
theorem mechanismKernel_apply (νₗ : Measure γ) [SFinite νₗ]
    {Φ : β × γ → δ} (hΦ : Measurable Φ) (o : β) :
    mechanismKernel νₗ Φ o = νₗ.map (fun l => Φ (o, l)) := by
  unfold mechanismKernel
  rw [ProbabilityTheory.Kernel.map_apply _ hΦ,
      ProbabilityTheory.Kernel.prod_apply,
      ProbabilityTheory.Kernel.id_apply,
      ProbabilityTheory.Kernel.const_apply,
      MeasureTheory.Measure.dirac_prod, MeasureTheory.Measure.map_map hΦ measurable_prodMk_left]
  rfl

/-- The mechanism kernel is Markov when the exogenous-noise law is a probability measure and
the mechanism is measurable. -/
instance instIsMarkovKernelMechanismKernel (νₗ : Measure γ)
    [IsProbabilityMeasure νₗ] {Φ : β × γ → δ} (hΦ : Measurable Φ) :
    IsMarkovKernel (mechanismKernel νₗ Φ) := by
  unfold mechanismKernel
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _ hΦ

/-- **Graph push-forward of a product measure is a composition product.**

For a finite first marginal `α`, a probability measure `νₗ` on the second factor,
and a measurable mechanism `Φ : β × γ → δ`, pushing `α.prod νₗ` forward along the
graph map `(o, l) ↦ (o, Φ (o, l))` equals `α.compProd (mechanismKernel νₗ Φ)`. -/
theorem map_graph_prod_eq_compProd
    (α : Measure β) [SFinite α] (νₗ : Measure γ) [IsProbabilityMeasure νₗ]
    {Φ : β × γ → δ} (hΦ : Measurable Φ) :
    Measure.map (fun p : β × γ => (p.1, Φ p)) (α.prod νₗ)
      = α.compProd (mechanismKernel νₗ Φ) := by
  -- `mechanismKernel = η.map Φ` with `η = Kernel.id ×ₖ Kernel.const β νₗ`.
  set η : ProbabilityTheory.Kernel β (β × γ) :=
    (ProbabilityTheory.Kernel.id : ProbabilityTheory.Kernel β β).prod
      (ProbabilityTheory.Kernel.const β νₗ) with hη
  have hΦ' : Measurable (fun p : β × γ => (p.1, Φ p)) := measurable_fst.prodMk hΦ
  -- Step 1: `α.compProd (η.map Φ) = map (Prod.map id Φ) (α.compProd η)`.
  have h1 : α.compProd (mechanismKernel νₗ Φ)
      = Measure.map (Prod.map id Φ) (α.compProd η) := by
    unfold mechanismKernel
    rw [← hη]
    exact MeasureTheory.Measure.compProd_map (μ := α) (κ := η) hΦ
  -- Step 2: `α.compProd η = map (fun o => (o, (o, ·)))`-style; concretely
  -- `α.compProd (id ×ₖ const νₗ) = map (fun p => (p.1, (p.1, p.2))) (α.prod νₗ)`.
  have h2 : α.compProd η
      = Measure.map (fun p : β × γ => (p.1, (p.1, p.2))) (α.prod νₗ) := by
    ext s hs
    rw [MeasureTheory.Measure.compProd_apply hs,
        MeasureTheory.Measure.map_apply
          ((measurable_fst.prodMk (measurable_fst.prodMk measurable_snd))) hs]
    rw [MeasureTheory.Measure.prod_apply
          (measurable_fst.prodMk (measurable_fst.prodMk measurable_snd) hs)]
    apply MeasureTheory.lintegral_congr
    intro o
    rw [hη, ProbabilityTheory.Kernel.prod_apply, ProbabilityTheory.Kernel.id_apply,
        ProbabilityTheory.Kernel.const_apply, MeasureTheory.Measure.dirac_prod]
    rw [MeasureTheory.Measure.map_apply measurable_prodMk_left
          (measurable_prodMk_left hs)]
    congr 1
  -- Step 3: combine.  `(Prod.map id Φ) ∘ (fun p => (p.1, p.1, p.2)) = fun p => (p.1, Φ p)`.
  rw [h1, h2, MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end Causalean.Mathlib.GraphMapProd
