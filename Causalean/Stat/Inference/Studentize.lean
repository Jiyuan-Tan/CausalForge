/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Generic studentized CLT and Wald coverage

Estimator-agnostic versions of the studentized-CLT and Wald-coverage
arguments.  These abstract the concrete TRAE-DR estimator
(`Causalean/Estimation/NPIV/DR/AsymptoticNormal.lean`) into an arbitrary
sequence `Xn` (the rescaled estimator) together with a variance-estimator
sequence `σ_hat`, and into an arbitrary studentized statistic `Sn` for the
Wald-coverage half.

* `Tendsto_dist.tendsto_measure_of_null_frontier` — continuity-set form of
  portmanteau for the project's `Tendsto_dist` wrapper.
* `gaussianMeasure_zero_one_singleton` / `gaussianMeasure_zero_one_frontier_Icc`
  — the standard normal has no atoms and gives zero mass to the boundary of a
  symmetric closed interval.
* `Tendsto_dist.div_tendsto_inProb_gaussian` — generic studentized CLT:
  if `Xn ⇒ N(0, σ₀²)` and `σ̂ →_p σ₀ > 0`, then `Xn / σ̂ ⇒ N(0, 1)`.
* `Tendsto_dist.wald_coverage` — generic Wald coverage: if `Sn ⇒ N(0, 1)`
  and a real sequence `coverProb` is asymptotically equivalent to the
  studentized interval event, then `coverProb → N(0,1)(Icc (-z) z)`.
-/

import Causalean.Stat.CLT.AsymptoticLinearity
import Causalean.Stat.Limit.ContinuousMapping
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
This file provides estimator-agnostic studentized CLT and Wald-interval coverage
results.  The portmanteau helper
`Tendsto_dist.tendsto_measure_of_null_frontier` converts convergence in
distribution into convergence of probabilities for continuity sets, while
`gaussianMeasure_zero_one_singleton` and
`gaussianMeasure_zero_one_frontier_Icc` record the boundary-null facts needed for
standard-normal intervals.

The main studentization theorem
`Tendsto_dist.div_tendsto_inProb_gaussian` proves that `Xn / σ_hat ⇒ N(0,1)`
from `Xn ⇒ N(0, σ₀ ^ 2)` and `σ_hat →ₚ σ₀ > 0`.  The coverage theorem
`Tendsto_dist.wald_coverage` then transfers the limiting probability of
`Sn ∈ Icc (-z) z` to an abstract coverage sequence via a bridge hypothesis.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

/-! ## Portmanteau + Gaussian-boundary helpers -/

/-- Continuity-set form of portmanteau for the project's `Tendsto_dist`
wrapper. -/
theorem Tendsto_dist.tendsto_measure_of_null_frontier
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Xn : ℕ → Ω → ℝ} {Q : Measure ℝ} [IsProbabilityMeasure Q]
    (hXn : ∀ n, AEMeasurable (Xn n) μ)
    (hX : Tendsto_dist Xn Q μ hXn)
    {E : Set ℝ} (hE : Q (frontier E) = 0) :
    Tendsto (fun n => ((μ.map (Xn n)) E).toReal) atTop (𝓝 (Q E).toReal) := by
  unfold Tendsto_dist at hX
  let μs : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨μ.map (Xn n), Measure.isProbabilityMeasure_map (hXn n)⟩
  let ν : ProbabilityMeasure ℝ := ⟨Q, inferInstance⟩
  have hE' : ν (frontier E) = 0 := by
    change (Q (frontier E)).toNNReal = 0
    simp [hE]
  have hpm := MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
      (μs := μs) (μ := ν) hX (E := E) hE'
  have hreal := NNReal.continuous_coe.tendsto _ |>.comp hpm
  simpa [μs, ν, ENNReal.coe_toNNReal_eq_toReal] using hreal

/-- The standard normal has no atom at any real point. -/
theorem gaussianMeasure_zero_one_singleton (x : ℝ) :
    gaussianMeasure 0 1 ({x} : Set ℝ) = 0 := by
  haveI : NoAtoms (gaussianMeasure 0 1) := by
    unfold gaussianMeasure
    exact ProbabilityTheory.noAtoms_gaussianReal (by norm_num)
  exact MeasureTheory.NoAtoms.measure_singleton x

/-- The standard normal gives zero mass to the boundary of a symmetric
closed interval. -/
theorem gaussianMeasure_zero_one_frontier_Icc
    {z : ℝ} (hz : 0 < z) :
    gaussianMeasure 0 1 (frontier (Set.Icc (-z) z)) = 0 := by
  have hle : -z ≤ z := by linarith
  rw [frontier_Icc hle]
  rw [show ({-z, z} : Set ℝ) = {-z} ∪ {z} by ext x; simp [or_comm]]
  exact le_antisymm
    (by
      calc
        gaussianMeasure 0 1 (({-z} : Set ℝ) ∪ {z})
            ≤ gaussianMeasure 0 1 ({-z} : Set ℝ) + gaussianMeasure 0 1 ({z} : Set ℝ) :=
              measure_union_le _ _
        _ = 0 := by simp [gaussianMeasure_zero_one_singleton])
    (zero_le _)

/-! ## Generic studentized CLT -/

/-- **Generic studentized convergence.**

Given an abstract rescaled-estimator sequence `Xn ⇒ N(0, σ₀²)` and a
variance-estimator sequence `σ_hat` with `σ̂ →_p σ₀` and `σ₀ > 0`,

    Xn / σ̂  ⇒  N(0, 1).

The argument scales `Xn` by the constant `1/σ₀` (giving
`N(0, (1/σ₀)²·σ₀²) = N(0,1)`) and absorbs the Slutsky remainder
`Xn · (1/σ̂ - 1/σ₀)`, which is `O_p(1)·o_p(1) = o_p(1)`. -/
theorem Tendsto_dist.div_tendsto_inProb_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Xn : ℕ → Ω → ℝ} {σ_hat : ℕ → Ω → ℝ} {σ₀ : ℝ}
    (hσ₀_pos : 0 < σ₀)
    (hXn : ∀ n, AEMeasurable (Xn n) μ)
    (hX : Tendsto_dist Xn (gaussianMeasure 0 (σ₀ ^ 2)) μ hXn)
    (hσ : Tendsto_inProb σ_hat (fun _ => σ₀) μ)
    (hdiv : ∀ n, AEMeasurable (fun ω => Xn n ω / σ_hat n ω) μ) :
    Tendsto_dist (fun n ω => Xn n ω / σ_hat n ω) (gaussianMeasure 0 1) μ hdiv := by
  have hσ₀_ne : σ₀ ≠ 0 := ne_of_gt hσ₀_pos
  have hscaled_meas : ∀ n, AEMeasurable (fun ω => (1 / σ₀) * Xn n ω) μ := by
    intro n
    exact aemeasurable_const.mul (hXn n)
  have hscaled :
      Tendsto_dist (fun n ω => (1 / σ₀) * Xn n ω)
        (gaussianMeasure 0 1) μ hscaled_meas := by
    have h :=
      Tendsto_dist.const_mul_tendsto_gaussian
        (Xn := Xn) (a := fun _ : ℕ => 1 / σ₀) (a₀ := 1 / σ₀)
        (v := σ₀ ^ 2) hXn hscaled_meas hX tendsto_const_nhds
    have hvar : ((σ₀ ^ 2)⁻¹ * σ₀ ^ 2) = 1 := by
      have hσsq_ne : σ₀ ^ 2 ≠ 0 := pow_ne_zero 2 hσ₀_ne
      field_simp [hσsq_ne]
    simpa [hvar] using h
  have hXbig : IsBigOp Xn (fun _ => (1 : ℝ)) μ :=
    Tendsto_dist.tightness hXn hX
  have hinv_little :
      IsLittleOp (fun n ω => 1 / σ_hat n ω - 1 / σ₀)
        (fun _ => (1 : ℝ)) μ := by
    exact Tendsto_inProb.isLittleOp_one
      (Tendsto_inProb.sub_const (Tendsto_inProb.inv hσ hσ₀_ne))
  have hrem_prod :
      IsLittleOp
        (fun n ω => Xn n ω * (1 / σ_hat n ω - 1 / σ₀))
        (fun _ => (1 : ℝ)) μ :=
    IsBigOp.mul_isLittleOp_one_isLittleOp hXbig hinv_little
  have hrem :
      IsLittleOp
        (fun n ω => Xn n ω / σ_hat n ω - (1 / σ₀) * Xn n ω)
        (fun _ => (1 : ℝ)) μ := by
    convert hrem_prod using 1
    funext n ω
    ring
  exact Tendsto_dist.add_isLittleOp_one hscaled_meas hdiv hscaled hrem

/-! ## Generic Wald-interval asymptotic coverage -/

/-- **Generic Wald asymptotic coverage.**

If a studentized statistic sequence `Sn ⇒ N(0, 1)`, then for any `z > 0`
and any real sequence `coverProb` asymptotically equivalent to the
studentized interval event (hypothesis `h_bridge`),

    coverProb n  →  N(0,1)(Icc (-z) z).

The studentized-interval probability limit comes from portmanteau
(`Tendsto_dist.tendsto_measure_of_null_frontier` with the null-boundary fact
`gaussianMeasure_zero_one_frontier_Icc`); `h_bridge` then carries it to
`coverProb`. -/
theorem Tendsto_dist.wald_coverage
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Sn : ℕ → Ω → ℝ} (hSn : ∀ n, AEMeasurable (Sn n) μ)
    (hS : Tendsto_dist Sn (gaussianMeasure 0 1) μ hSn)
    {z : ℝ} (hz : 0 < z)
    (coverProb : ℕ → ℝ)
    (h_bridge : Tendsto
      (fun n => coverProb n - (μ {ω | Sn n ω ∈ Set.Icc (-z) z}).toReal) atTop (𝓝 0)) :
    Tendsto coverProb atTop (𝓝 ((gaussianMeasure 0 1) (Set.Icc (-z) z)).toReal) := by
  let studProb : ℕ → ℝ := fun n =>
    (μ {ω | Sn n ω ∈ Set.Icc (-z) z}).toReal
  change Tendsto (fun n => coverProb n - studProb n) atTop (𝓝 0) at h_bridge
  have hpm :
      Tendsto
        (fun n => ((μ.map (Sn n)) (Set.Icc (-z) z)).toReal)
        atTop
        (𝓝 ((gaussianMeasure 0 1) (Set.Icc (-z) z)).toReal) := by
    exact Tendsto_dist.tendsto_measure_of_null_frontier
      hSn hS
      (gaussianMeasure_zero_one_frontier_Icc hz)
  have hstudent_event :
      Tendsto studProb atTop
        (𝓝 ((gaussianMeasure 0 1) (Set.Icc (-z) z)).toReal) := by
    refine hpm.congr' ?_
    filter_upwards with n
    rw [Measure.map_apply_of_aemeasurable (hSn n) measurableSet_Icc]
    rfl
  have hsum := hstudent_event.add h_bridge
  have hsum' : Tendsto (fun n => studProb n + (coverProb n - studProb n)) atTop
      (𝓝 ((gaussianMeasure 0 1) (Set.Icc (-z) z)).toReal) := by
    simpa using hsum
  refine hsum'.congr' ?_
  filter_upwards with n
  ring

end Causalean.Stat
