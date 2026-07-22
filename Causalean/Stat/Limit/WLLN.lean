/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Weak law of large numbers for the i.i.d. sample type

Generic weak law of large numbers (WLLN) for `Causalean.Stat.IIDSample`: under
plain integrability, the sample mean of a real-valued statistic converges in
probability to its population integral.  This generalizes the Panel-specific
a.s. convergence lemma `iidPanel_sampleMean_ae` (which required boundedness) to
arbitrary integrable statistics and converts almost-everywhere convergence to
convergence in probability via `tendstoInMeasure_of_tendsto_ae` on the finite
(probability) space `μ`.

A second-moment corollary specializes the WLLN to `ψ²` for a known influence
function `ψ`, giving consistency of the empirical second moment.
-/

import Causalean.Stat.Sample
import Causalean.Stat.Limit.Convergence
import Mathlib.Probability.StrongLaw
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Weak laws for sample means

This module proves weak laws of large numbers for real-valued statistics of
`IIDSample`.  The measurability helper `IIDSample.measurable_sampleMean` supports
sample means of measurable functions, `IIDSample.sampleMean_tendsto_inProb`
converts the strong law into convergence in probability for any integrable
statistic, and `IIDSample.sampleSecondMoment_tendsto_inProb` records the
second-moment specialization used by variance-estimation arguments. -/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

namespace IIDSample

/-- `S.sampleMean g N` is measurable for measurable `g`: it is a finite sum of
`g ∘ Z i` scaled by a constant. -/
theorem measurable_sampleMean (S : IIDSample Ω X μ P) {g : X → ℝ}
    (hg_meas : Measurable g) (N : ℕ) :
    Measurable (S.sampleMean g N) := by
  unfold IIDSample.sampleMean
  exact (Finset.measurable_sum _ (fun i _hi => hg_meas.comp (S.meas i))).const_mul _

/-- **Generic weak law of large numbers.**  For an integrable real-valued
statistic `g` of an i.i.d. sample, the sample mean `S.sampleMean g N` converges
in probability to the population integral `∫ x, g x ∂P` as `N → ∞`.

This weakens the boundedness hypothesis of the Panel a.s. lemma
`iidPanel_sampleMean_ae` to plain integrability (all the strong law needs) and
converts almost-everywhere convergence to convergence in probability on the
finite probability space `μ`. -/
theorem sampleMean_tendsto_inProb
    (S : IIDSample Ω X μ P) {g : X → ℝ}
    [IsProbabilityMeasure P]
    (hg_meas : Measurable g)
    (hg_int : Integrable (fun ω => g (S.Z 0 ω)) μ) :
    Tendsto_inProb (S.sampleMean g) (fun _ => ∫ x, g x ∂P) μ := by
  haveI : IsProbabilityMeasure μ := by
    haveI : IsProbabilityMeasure (μ.map (S.Z 0)) := by
      rw [S.law]; infer_instance
    exact Measure.isProbabilityMeasure_of_map (S.Z 0)
  -- i.i.d. family of the transformed sample points
  have hindep_iid :
      Pairwise (Function.onFun (fun x1 x2 => IndepFun x1 x2 μ)
        (fun i ω => g (S.Z i ω))) := by
    have hi : iIndepFun (fun i => g ∘ S.Z i) μ :=
      S.indep.comp (fun _ => g) (fun _ => hg_meas)
    intro i j hij
    exact hi.indepFun hij
  have hident :
      ∀ i, IdentDistrib (fun ω => g (S.Z i ω)) (fun ω => g (S.Z 0 ω)) μ μ := by
    intro i
    exact ((S.identDist i).symm.comp hg_meas)
  have hslln := ProbabilityTheory.strong_law_ae_real
    (fun i ω => g (S.Z i ω)) hg_int hindep_iid hident
  -- transfer the limiting integral through the law of `Z 0`
  have hint_eq : (∫ ω, g (S.Z 0 ω) ∂μ) = ∫ x, g x ∂P := by
    rw [← integral_map (S.meas 0).aemeasurable hg_meas.aestronglyMeasurable, S.law]
  -- a.s. convergence of the sample mean to `∫ x, g x ∂P`
  have hae : ∀ᵐ ω ∂μ,
      Tendsto (fun N : ℕ => S.sampleMean g N ω) atTop
        (𝓝 (∫ x, g x ∂P)) := by
    filter_upwards [hslln] with ω hω
    unfold IIDSample.sampleMean
    simpa [hint_eq, div_eq_mul_inv, mul_comm] using hω
  -- a.e. ⟹ in-measure on the finite (probability) space `μ`
  unfold Tendsto_inProb
  refine tendstoInMeasure_of_tendsto_ae ?_ hae
  intro N
  exact (S.measurable_sampleMean hg_meas N).aestronglyMeasurable

/-- **Second-moment consistency.**  For a known influence function `ψ` with
square-integrable values, the empirical second moment `S.sampleMean (ψ²) N`
converges in probability to `∫ x, (ψ x)² ∂P`.  Direct application of the WLLN
to `g := ψ²`. -/
theorem sampleSecondMoment_tendsto_inProb
    (S : IIDSample Ω X μ P) [IsProbabilityMeasure P] {ψ : X → ℝ}
    (hψ_meas : Measurable ψ)
    (hψ_sq_int : Integrable (fun ω => (ψ (S.Z 0 ω)) ^ 2) μ) :
    Tendsto_inProb (S.sampleMean (fun x => (ψ x) ^ 2))
      (fun _ => ∫ x, (ψ x) ^ 2 ∂P) μ :=
  S.sampleMean_tendsto_inProb (hψ_meas.pow_const 2) hψ_sq_int

end IIDSample

end Causalean.Stat
