/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Multivariate Wald / confidence-ellipsoid coverage

The vector analogue of the scalar Wald-coverage theorem
`Tendsto_dist.wald_coverage` (`Causalean/Stat/Inference/Studentize.lean`).

For a multivariate estimator the Wald statistic is the quadratic form
`Wₙ = (√n (θ̂ₙ − θ₀))ᵀ Σ̂ₙ⁻¹ (√n (θ̂ₙ − θ₀))`, an `ℝ`-valued random variable.
A confidence *ellipsoid* `{θ : Wald(θ) ≤ c}` has asymptotic coverage
`χ(Iic c)` where `χ` is the limit law of `Wₙ` — the `χ²_d` distribution when
the rescaled estimator is asymptotically `N(0, Σ)` and `Σ̂ₙ →ₚ Σ` (so that
`Σ̂ₙ⁻¹` whitens the Gaussian into a standard one whose squared norm is `χ²_d`).

Because `Wₙ` is already scalar, the coverage statement reduces to the
one-sided portmanteau on `Set.Iic c` (`Tendsto_dist.tendsto_measure_of_null_frontier`),
exactly mirroring the scalar `wald_coverage`.  This file provides that
reduction; the *construction* of `Wₙ` from `(θ̂ₙ, Σ̂ₙ)` and the proof that
`Wₙ ⇒ χ` (continuous mapping of the joint limit through `(t, S) ↦ tᵀS⁻¹t`) is
the caller's input — just as the scalar `wald_coverage` takes `Sₙ ⇒ N(0,1)` as
a hypothesis rather than proving it.

## On the χ² closed form

Identifying the limit `χ` as the `χ²_d` distribution (and hence reading off the
critical value `c = χ²_{d,1−α}`) requires pushing the *concrete* multivariate
Gaussian limit (`Causalean/Stat/CLT/GaussianLimit.lean`, `gaussianLimit`) through the
quadratic form `S ↦ Sᵀ Σ⁻¹ S` and recognising the result as `χ²_d`.  This step
is now **closed** in `Causalean/Stat/Inference/ChiSquaredWald.lean`
(`gaussianLimit_waldForm_map`): under a non-degenerate asymptotic variance the
whitened quadratic form has the χ²_d law `chiSqDist (finrank E)`
(`Causalean/Stat/CLT/ChiSquared.lean`), and `Tendsto_dist.wald_coverage_chiSq`
specialises the coverage theorem below to that limit.  We still keep `χ` abstract
*here* so that the reduction holds against an arbitrary limit law of `Wₙ`.

Key declarations:

* `Tendsto_dist.wald_coverage_Iic` : one-sided/ellipsoid coverage for a scalar
  statistic `Wₙ ⇒ χ` with `χ` null on the boundary `{c}`.
* `Tendsto_dist.wald_coverage_Iic_of_noAtoms` : the boundary-null hypothesis is
  automatic when the limit law `χ` has no atoms (e.g. any non-degenerate `χ²`).
-/

import Causalean.Stat.Inference.Studentize
import Causalean.Stat.CLT.MultivariateCLT
import Causalean.Stat.Inference.VarianceEstimation

/-!
This file reduces multivariate Wald ellipsoid coverage to scalar convergence of
the Wald statistic.  The theorem `Tendsto_dist.wald_coverage_Iic` says that if
`Wn ⇒ χ`, the limit has zero mass on the boundary of `Iic c`, and a coverage
sequence is asymptotically equivalent to the event `{ω | Wn n ω ≤ c}`, then the
coverage sequence converges to `χ (Iic c)`.

The variant `Tendsto_dist.wald_coverage_Iic_of_noAtoms` discharges the
boundary-null hypothesis when the Wald-statistic limit law has no atoms.  The
chi-squared specialization lives in `Causalean.Stat.Inference.ChiSquaredWald`,
which identifies the Gaussian quadratic-form limit.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

/-! ## One-sided Wald / ellipsoid coverage -/

/-- **Wald / confidence-ellipsoid asymptotic coverage.**

If the (scalar) Wald statistic sequence `Wₙ ⇒ χ` in distribution, `χ` has zero
mass on the boundary `frontier (Iic c) = {c}`, and a real sequence `coverProb`
is asymptotically equivalent to the ellipsoid event `{ω | Wₙ ω ≤ c}` (the bridge
hypothesis), then

    coverProb n  →  χ(Iic c).

For `Wₙ = (√n(θ̂ₙ−θ₀))ᵀ Σ̂ₙ⁻¹ (√n(θ̂ₙ−θ₀)) ⇒ χ²_d` and `c = χ²_{d,1−α}` this is
the `1 − α` asymptotic coverage of the Wald confidence ellipsoid.  Reduces the
ellipsoid event to the one-sided portmanteau on `Set.Iic c`; vector analogue of
`Tendsto_dist.wald_coverage`. -/
theorem Tendsto_dist.wald_coverage_Iic
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Wn : ℕ → Ω → ℝ} (hWn : ∀ n, AEMeasurable (Wn n) μ)
    {χ : Measure ℝ} [IsProbabilityMeasure χ]
    (hW : Tendsto_dist Wn χ μ hWn)
    {c : ℝ} (hfront : χ (frontier (Set.Iic c)) = 0)
    (coverProb : ℕ → ℝ)
    (h_bridge : Tendsto
      (fun n => coverProb n - (μ {ω | Wn n ω ≤ c}).toReal) atTop (𝓝 0)) :
    Tendsto coverProb atTop (𝓝 ((χ (Set.Iic c)).toReal)) := by
  let ellProb : ℕ → ℝ := fun n => (μ {ω | Wn n ω ≤ c}).toReal
  change Tendsto (fun n => coverProb n - ellProb n) atTop (𝓝 0) at h_bridge
  have hpm :
      Tendsto (fun n => ((μ.map (Wn n)) (Set.Iic c)).toReal) atTop
        (𝓝 ((χ (Set.Iic c)).toReal)) :=
    Tendsto_dist.tendsto_measure_of_null_frontier hWn hW hfront
  have hell : Tendsto ellProb atTop (𝓝 ((χ (Set.Iic c)).toReal)) := by
    refine hpm.congr' ?_
    filter_upwards with n
    rw [Measure.map_apply_of_aemeasurable (hWn n) measurableSet_Iic]
    rfl
  have hsum := hell.add h_bridge
  have hsum' :
      Tendsto (fun n => ellProb n + (coverProb n - ellProb n)) atTop
        (𝓝 ((χ (Set.Iic c)).toReal)) := by simpa using hsum
  refine hsum'.congr' ?_
  filter_upwards with n
  ring

/-- **Wald / ellipsoid coverage with an atomless limit.**  When the limit law
`χ` of the Wald statistic has no atoms (which holds for any non-degenerate
`χ²_d`, and more generally for any continuous limit), the boundary-null
hypothesis of `wald_coverage_Iic` is automatic: `frontier (Iic c) = {c}` and
`χ {c} = 0`. -/
theorem Tendsto_dist.wald_coverage_Iic_of_noAtoms
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Wn : ℕ → Ω → ℝ} (hWn : ∀ n, AEMeasurable (Wn n) μ)
    {χ : Measure ℝ} [IsProbabilityMeasure χ] [NoAtoms χ]
    (hW : Tendsto_dist Wn χ μ hWn)
    (c : ℝ)
    (coverProb : ℕ → ℝ)
    (h_bridge : Tendsto
      (fun n => coverProb n - (μ {ω | Wn n ω ≤ c}).toReal) atTop (𝓝 0)) :
    Tendsto coverProb atTop (𝓝 ((χ (Set.Iic c)).toReal)) := by
  refine Tendsto_dist.wald_coverage_Iic hWn hW ?_ coverProb h_bridge
  rw [frontier_Iic]
  exact measure_singleton c

end Causalean.Stat
