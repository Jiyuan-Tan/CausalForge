/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Finite-partition integral algebra

Causal-agnostic measure-theory utilities for decomposing an integral over the
*fibers* of a finite-valued measurable map `H : Ω → ι` (a finite partition of the sample
space). They live in `Causalean/Mathlib/MeasureTheory/` so any layer (estimation, panel
cell algebra, partial-ID) can use them without pulling in the statistics or
potential-outcome layers.

The companion lemma `Causalean.PO.integral_eq_sum_measure_mul_eventCondExp`
(file `Causalean/PO/Conditioning/EventCondExp.lean`) gives the *measure-weighted /
`eventCondExp`* form for an explicit `Fintype`-indexed set family; the lemmas
here are the *measurable-map / set-integral* form, plus the **cell-constant
pull-out** that the eventCondExp file does not provide:

* `integral_eq_sum_setIntegral_fiber` : `∫ f = ∑ h, ∫_{H⁻¹{h}} f`.
* `integral_cellConst_mul` : `∫ c(H ω)·f ω = ∑ h, c h · ∫_{H⁻¹{h}} f`.
* `integral_cellConst` : `∫ c(H ω) = ∑ h, c h · μ(H⁻¹{h})` (finite measure).

The index type carries `[Fintype ι] [MeasurableSpace ι]
[MeasurableSingletonClass ι]`, so the fibers `H⁻¹{h}` are measurable, pairwise
disjoint, and cover `univ`.  No measurability of `c : ι → ℝ` is required: on
each fiber `c ∘ H` is the *constant* `c h`, pulled out per cell.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Finite-partition integral algebra

This file decomposes integrals over the fibres of a finite-valued measurable map and
proves that cell-constant weights can be pulled out fibre by fibre. The public lemmas
are `integral_eq_sum_setIntegral_fiber`, `integral_cellConst_mul`, and
`integral_cellConst`, which turn a finite partition of a sample space into finite sums
of set integrals or cell weights.
-/

-- `open` BEFORE the namespace: inside `namespace Causalean.Mathlib.MeasureTheory`
-- the token `MeasureTheory` would resolve to this local namespace and shadow the
-- real one, so open the root MeasureTheory here at top level (cf. IntegralBind).
open MeasureTheory

namespace Causalean.Mathlib.MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Fiber partition of `univ` -/

/-- The fibers of `H` are measurable. -/
private theorem measurableSet_fiber {ι : Type*} [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {H : Ω → ι} (hH : Measurable H) (h : ι) :
    MeasurableSet (H ⁻¹' {h}) :=
  hH (measurableSet_singleton h)

omit [MeasurableSpace Ω] in
/-- The fibers of `H` are pairwise disjoint. -/
private theorem pairwise_disjoint_fiber {ι : Type*} (H : Ω → ι) :
    Pairwise (Function.onFun Disjoint (fun h => H ⁻¹' {h})) := by
  intro a b hab
  simp only [Function.onFun]
  rw [Set.disjoint_left]
  intro ω ha hb
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha hb
  exact hab (ha.symm.trans hb)

omit [MeasurableSpace Ω] in
/-- The fibers of `H` cover the whole space. -/
private theorem iUnion_fiber {ι : Type*} (H : Ω → ι) : (⋃ h, H ⁻¹' {h}) = Set.univ := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  exact ⟨H ω, rfl⟩

/-! ## Integral decomposition over fibers -/

/-- **Fiber decomposition.**  For an integrable `f` and a finite-valued
measurable map `H`, the integral of `f` splits as the sum of its set-integrals
over the fibers `H⁻¹{h}`. -/
theorem integral_eq_sum_setIntegral_fiber {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {H : Ω → ι} (hH : Measurable H) {f : Ω → ℝ} (hf : Integrable f μ) :
    ∫ ω, f ω ∂μ = ∑ h : ι, ∫ ω in H ⁻¹' {h}, f ω ∂μ := by
  have hsplit :
      ∫ ω in ⋃ h, H ⁻¹' {h}, f ω ∂μ = ∑ h : ι, ∫ ω in H ⁻¹' {h}, f ω ∂μ :=
    MeasureTheory.integral_iUnion_fintype (measurableSet_fiber hH)
      (pairwise_disjoint_fiber H) (fun _ => hf.integrableOn)
  calc
    ∫ ω, f ω ∂μ = ∫ ω in (Set.univ : Set Ω), f ω ∂μ := by rw [setIntegral_univ]
    _ = ∫ ω in ⋃ h, H ⁻¹' {h}, f ω ∂μ := by rw [iUnion_fiber]
    _ = ∑ h : ι, ∫ ω in H ⁻¹' {h}, f ω ∂μ := hsplit

/-- **Cell-constant pull-out.**  If the integrand is a function `f` weighted by
a value `c (H ω)` that depends on `ω` only through the cell `H ω`, the integral
decomposes as `∑ h, c h · ∫_{H⁻¹{h}} f`.  No measurability of `c` is needed:
on each fiber `c (H ω)` is the constant `c h`.

This is the workhorse for panel cell-by-cell regression algebra and for
estimands written as cell-weighted averages. -/
theorem integral_cellConst_mul {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {H : Ω → ι} (hH : Measurable H) (c : ι → ℝ)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    ∫ ω, c (H ω) * f ω ∂μ = ∑ h : ι, c h * ∫ ω in H ⁻¹' {h}, f ω ∂μ := by
  -- On each fiber the integrand equals the constant-multiple `c h • f`.
  have hgint : ∀ h : ι, IntegrableOn (fun ω => c (H ω) * f ω) (H ⁻¹' {h}) μ := by
    intro h
    refine ((hf.const_mul (c h)).integrableOn).congr_fun ?_ (measurableSet_fiber hH h)
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
    simp [hω]
  have hsplit :
      ∫ ω in ⋃ h, H ⁻¹' {h}, c (H ω) * f ω ∂μ
        = ∑ h : ι, ∫ ω in H ⁻¹' {h}, c (H ω) * f ω ∂μ :=
    MeasureTheory.integral_iUnion_fintype (measurableSet_fiber hH)
      (pairwise_disjoint_fiber H) hgint
  calc
    ∫ ω, c (H ω) * f ω ∂μ
        = ∫ ω in (Set.univ : Set Ω), c (H ω) * f ω ∂μ := by rw [setIntegral_univ]
    _ = ∫ ω in ⋃ h, H ⁻¹' {h}, c (H ω) * f ω ∂μ := by rw [iUnion_fiber]
    _ = ∑ h : ι, ∫ ω in H ⁻¹' {h}, c (H ω) * f ω ∂μ := hsplit
    _ = ∑ h : ι, c h * ∫ ω in H ⁻¹' {h}, f ω ∂μ := by
        refine Finset.sum_congr rfl fun h _ => ?_
        have hcell :
            ∫ ω in H ⁻¹' {h}, c (H ω) * f ω ∂μ = ∫ ω in H ⁻¹' {h}, c h * f ω ∂μ := by
          refine setIntegral_congr_fun (measurableSet_fiber hH h) ?_
          intro ω hω
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
          simp [hω]
        rw [hcell, integral_const_mul]

/-- **Cell-weight aggregation.**  For a finite measure, the integral of a
cell-constant function `c (H ω)` is the cell-weighted sum `∑ h, c h · μ(H⁻¹{h})`.
Special case of `integral_cellConst_mul` with `f ≡ 1`. -/
theorem integral_cellConst {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [IsFiniteMeasure μ]
    {H : Ω → ι} (hH : Measurable H) (c : ι → ℝ) :
    ∫ ω, c (H ω) ∂μ = ∑ h : ι, c h * (μ (H ⁻¹' {h})).toReal := by
  have h := integral_cellConst_mul hH c
    (f := fun _ => (1 : ℝ)) (hf := (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ))
  simpa [mul_one, setIntegral_const, smul_eq_mul] using h

end Causalean.Mathlib.MeasureTheory
