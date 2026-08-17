/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Concentration.Covering.Separable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Countable reduction of empirical suprema

This file gives a paper-neutral criterion reducing an uncountable empirical
supremum to a fixed countable, pointwise-dense subfamily under every finite
product law.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Causalean.Stat.Concentration

/-- The centered empirical average is the sample average of a function minus
its population integral. -/
noncomputable def centeredEmpiricalAverage {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (w : Fin n → Ω) (g : Ω → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, g (w i) - ∫ z, g z ∂μ

/-- A countable subfamily realizes the continuum empirical-process supremum
almost surely under every finite product law. -/
def HasCountableEmpiricalSupReduction {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g : ι → Ω → ℝ) : Prop :=
  (∀ i, Measurable (g i)) ∧
  ∃ g0 : ℕ → ι, ∀ n,
    (∀ᵐ w ∂Measure.pi (fun _ : Fin n => μ),
      (⨆ i : ι, ENNReal.ofReal |centeredEmpiricalAverage μ w (g i)|) =
        ⨆ k : ℕ, ENNReal.ofReal |centeredEmpiricalAverage μ w (g (g0 k))|)

/-- **Countable supremum reduction from pointwise density.** Let `μ` be a σ-finite measure on
`Ω`, `g : ι → Ω → ℝ` a family of functions, and `g0 : ℕ → ι` a countable subfamily. Suppose
[`S` is a `μ`-conull subset of `Ω`](hyp:hS), [on `S`, every `g i` is the pointwise limit, along
some subsequence, of the countable subfamily `g ∘ g0`](hyp:hdense), [each `g i` is
measurable](hyp:hmeas), and [there is a single `μ`-integrable envelope `G` dominating `|g i|`
uniformly in `i`](hyp:hdom). Then [the countable subfamily indexed by `g0` realizes the full
continuum empirical-process supremum of `g` almost surely under every finite product law of
`μ`](goal). -/
-- @node: hasCountableEmpiricalSupReduction_of_pointwise_dense
lemma hasCountableEmpiricalSupReduction_of_pointwise_dense
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
    (g : ι → Ω → ℝ)
    (g0 : ℕ → ι)
    (S : Set Ω) (hS : ∀ᵐ z ∂μ, z ∈ S)
    (hdense : ∀ i, ∃ kseq : ℕ → ℕ,
      ∀ z ∈ S, Tendsto (fun m => g (g0 (kseq m)) z) atTop (nhds (g i z)))
    (hmeas : ∀ i, Measurable (g i))
    (hdom : ∃ G : Ω → ℝ, Integrable G μ ∧ ∀ i z, |g i z| ≤ G z) :
    HasCountableEmpiricalSupReduction μ g := by
  rcases hdom with ⟨G, hG, hbound⟩
  refine ⟨hmeas, g0, ?_⟩
  intro n
  have hsampleS : ∀ᵐ w ∂Measure.pi (fun _ : Fin n => μ), ∀ j, w j ∈ S :=
    eventually_all.2 fun j =>
      Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => μ) (i := j) hS
  filter_upwards [hsampleS] with w hw
  apply le_antisymm
  · refine iSup_le fun i => ?_
    obtain ⟨kseq, hseq⟩ := hdense i
    have hint : Tendsto
        (fun m => ∫ z, g (g0 (kseq m)) z ∂μ) atTop
        (nhds (∫ z, g i z ∂μ)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence G
        (fun m => (hmeas _).aestronglyMeasurable) hG ?_ ?_
      · intro m
        exact Eventually.of_forall fun z => by
          simpa only [Real.norm_eq_abs] using hbound (g0 (kseq m)) z
      · exact hS.mono fun z hz => hseq z hz
    have havg : Tendsto
        (fun m => centeredEmpiricalAverage μ w (g (g0 (kseq m)))) atTop
        (nhds (centeredEmpiricalAverage μ w (g i))) := by
      unfold centeredEmpiricalAverage
      apply Tendsto.sub
      · apply Tendsto.const_mul
        apply tendsto_finset_sum
        intro j _hj
        exact hseq (w j) (hw j)
      · exact hint
    have hval : Tendsto
        (fun m => ENNReal.ofReal
          |centeredEmpiricalAverage μ w (g (g0 (kseq m)))|) atTop
        (nhds (ENNReal.ofReal |centeredEmpiricalAverage μ w (g i)|)) :=
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (continuous_abs.continuousAt.tendsto.comp havg)
    apply le_of_tendsto hval
    exact Eventually.of_forall fun m =>
      le_iSup (fun k : ℕ => ENNReal.ofReal
        |centeredEmpiricalAverage μ w (g (g0 k))|) (kseq m)
  · refine iSup_le fun k => ?_
    exact le_iSup (fun i : ι => ENNReal.ofReal
      |centeredEmpiricalAverage μ w (g i)|) (g0 k)

-- @node: winsorizedScore_boundary_volume_zero

end Causalean.Stat.Concentration
