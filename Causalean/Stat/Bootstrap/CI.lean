/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bootstrap standard error: studentized CLT and Wald coverage

The econometric workhorse use of the nonparametric bootstrap (`vce(bootstrap)`):
estimate the standard error of an asymptotically-linear estimator by the
bootstrap, then form a studentized / Wald confidence interval.  This file closes
the loop by routing the *consistent* bootstrap standard error
(`Stat/Bootstrap/Variance.lean`) through the generic studentized-CLT and
Wald-coverage machinery (`Stat/Inference/Studentize.lean`).

* `bootstrapSE` — `√(bootstrapVar)`, the bootstrap standard error of `√n θ̂`.
* `bootstrapSE_tendsto_inProb` — `bootstrapSE →ₚ σ₀ := √(∫ ψ² dP)`.
* `bootstrapStudentized` — the studentized statistic `√n(θ̂ − θ₀) / σ̂ₙ`.
* `bootstrap_studentized_tendsto` — `√n(θ̂ − θ₀) / σ̂ₙ ⇒ N(0, 1)` for an
  asymptotically-linear estimator with nondegenerate influence function.
* `bootstrap_wald_coverage` — asymptotic `N(0,1)(Icc (-z) z)` coverage of the
  bootstrap studentized interval.

Only the bootstrap-standard-error route is formalized.  Distributional
(Bickel–Freedman) consistency and the percentile / percentile-t refinements are
out of scope here — they need conditional weak convergence, which this argument
does not.
-/

import Causalean.Stat.Bootstrap.Variance
import Causalean.Stat.Inference.Studentize

/-! # Bootstrap Wald Intervals

This file turns the nonparametric bootstrap variance into a bootstrap standard
error and then uses studentized central-limit and Wald-coverage results. It
formalizes the standard route in which a consistent bootstrap standard error
validates a studentized confidence interval for an asymptotically linear
estimator.

The main declarations are `IIDSample.bootstrapSE`, its consistency theorem
`IIDSample.bootstrapSE_tendsto_inProb`, the studentized statistic
`IIDSample.bootstrapStudentized`, the distributional limit
`bootstrap_studentized_tendsto`, and the Wald coverage theorem
`bootstrap_wald_coverage`. The file does not prove percentile-bootstrap or
conditional weak-convergence results; it uses only the bootstrap standard-error
route. -/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

namespace IIDSample

/-- **Bootstrap standard error** of `√n θ̂`: the square root of the bootstrap
variance.  Since the bootstrap variance of `√n (X̄* − X̄)` is exactly the
empirical variance, `bootstrapSE` is the bootstrap estimate of the asymptotic
standard deviation `√(∫ ψ² dP)`. -/
noncomputable def bootstrapSE (S : IIDSample Ω X μ P) (ψ : X → ℝ) (n : ℕ) :
    Ω → ℝ :=
  fun ω => Real.sqrt (bootstrapVar S ψ n ω)

/-- **Consistency of the bootstrap standard error.** Along an i.i.d. sample `S`, if the
influence function `ψ` is [measurable](hyp:hψ_meas), [integrable](hyp:hψ_int),
[square-integrable](hyp:hψ_sq_int), and [has population mean zero](hyp:hmean), then [the
bootstrap standard error of `√n θ̂` converges in probability to the asymptotic standard
deviation $\sqrt{\int \psi^2\,dP}$](goal).

    Square root (continuous) applied to `bootstrapVar_tendsto_inProb`. -/
theorem bootstrapSE_tendsto_inProb (S : IIDSample Ω X μ P)
    [IsProbabilityMeasure P] {ψ : X → ℝ}
    (hψ_meas : Measurable ψ)
    (hψ_int : Integrable (fun ω => ψ (S.Z 0 ω)) μ)
    (hψ_sq_int : Integrable (fun ω => (ψ (S.Z 0 ω)) ^ 2) μ)
    (hmean : ∫ x, ψ x ∂P = 0) :
    Tendsto_inProb (bootstrapSE S ψ)
      (fun _ => Real.sqrt (∫ x, (ψ x) ^ 2 ∂P)) μ :=
  Tendsto_inProb.sqrt
    (bootstrapVar_tendsto_inProb S hψ_meas hψ_int hψ_sq_int hmean)

/-- **Bootstrap studentized statistic** `√n (θ̂ − θ₀) / σ̂ₙ`, where
`σ̂ₙ = bootstrapSE` is the bootstrap standard error.  The full-sample index
family `I n = Finset.range n` is used. -/
noncomputable def bootstrapStudentized (θn : ℕ → Ω → ℝ) (θ₀ : ℝ)
    (S : IIDSample Ω X μ P) (ψ : X → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω =>
    IsAsymLinear.rescaledEstimator θn θ₀ (fun m => Finset.range m) n ω
      / bootstrapSE S ψ n ω

end IIDSample

/-! ## Studentized CLT and Wald coverage -/

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
  {θn : ℕ → Ω → ℝ} {θ₀ : ℝ} {ψ : X → ℝ} {S : IIDSample Ω X μ P}

/-- **Bootstrap studentized CLT.** Let [`θ̂ₙ` be asymptotically linear at `θ₀` with influence
function `ψ` along the i.i.d. sample `S`](hyp:h), where `ψ` is [measurable](hyp:hψ_meas),
[integrable](hyp:hψ_int), and [square-integrable](hyp:hψ_sq_int); suppose further that [the
influence function is nondegenerate, $\int \psi^2\,dP > 0$](hyp:hpos), [the rescaled estimator
is a.e. measurable at every sample size](hyp:hθn_meas), and [the bootstrap studentized
statistic is a.e. measurable at every sample size](hyp:hStud_meas). Then [the
bootstrap-studentized statistic $\sqrt n(\hat\theta_n-\theta_0)/\hat\sigma_n$ converges in
distribution to the standard normal law](goal), where $\hat\sigma_n$ is the bootstrap standard
error.

    Combines `IsAsymLinear.tendsto_normal` (numerator `⇒ N(0, ∫ ψ²)`),
`bootstrapSE_tendsto_inProb` (`σ̂ₙ →ₚ √(∫ ψ²)`), and the generic studentized CLT
`Tendsto_dist.div_tendsto_inProb_gaussian`. -/
theorem bootstrap_studentized_tendsto
    (h : IsAsymLinear θn θ₀ ψ S (fun m => Finset.range m))
    (hψ_meas : Measurable ψ)
    (hψ_int : Integrable (fun ω => ψ (S.Z 0 ω)) μ)
    (hψ_sq_int : Integrable (fun ω => (ψ (S.Z 0 ω)) ^ 2) μ)
    (hpos : 0 < ∫ x, (ψ x) ^ 2 ∂P)
    (hθn_meas : ∀ n, AEMeasurable
      (IsAsymLinear.rescaledEstimator θn θ₀ (fun m => Finset.range m) n) μ)
    (hStud_meas : ∀ n,
      AEMeasurable (IIDSample.bootstrapStudentized θn θ₀ S ψ n) μ) :
    Tendsto_dist (IIDSample.bootstrapStudentized θn θ₀ S ψ)
      (gaussianMeasure 0 1) μ hStud_meas := by
  set σ₀ : ℝ := Real.sqrt (∫ x, (ψ x) ^ 2 ∂P) with hσ₀
  have hσ₀_pos : 0 < σ₀ := Real.sqrt_pos.mpr hpos
  have hσ₀sq : σ₀ ^ 2 = ∫ x, (ψ x) ^ 2 ∂P := Real.sq_sqrt (le_of_lt hpos)
  -- numerator ⇒ N(0, σ₀²)
  have hXn :
      Tendsto_dist (IsAsymLinear.rescaledEstimator θn θ₀ (fun m => Finset.range m))
        (gaussianMeasure 0 (σ₀ ^ 2)) μ hθn_meas := by
    rw [hσ₀sq]
    exact IsAsymLinear.tendsto_normal h hψ_meas hθn_meas
  -- bootstrap SE ⇒ σ₀ in probability
  have hSE : Tendsto_inProb (IIDSample.bootstrapSE S ψ) (fun _ => σ₀) μ :=
    IIDSample.bootstrapSE_tendsto_inProb S hψ_meas hψ_int hψ_sq_int h.mean_zero
  -- generic studentized CLT
  exact Tendsto_dist.div_tendsto_inProb_gaussian hσ₀_pos hθn_meas hXn hSE hStud_meas

/-- **Bootstrap Wald asymptotic coverage.** Under [the asymptotic-linearity
hypothesis](hyp:h), [measurability](hyp:hψ_meas), [integrability](hyp:hψ_int), and
[square-integrability](hyp:hψ_sq_int) of `ψ`, [influence-function nondegeneracy](hyp:hpos), and
[measurability of the rescaled estimator](hyp:hθn_meas) and [of the studentized
statistic](hyp:hStud_meas) at every sample size — the hypotheses of
`bootstrap_studentized_tendsto` — fix [a positive critical value `z`](hyp:hz) and a
coverage-probability sequence `coverProb` that [asymptotically tracks the studentized
interval's true coverage event](hyp:h_bridge); then [`coverProb` converges to the standard
normal probability of the interval `[-z, z]`](goal), so the bootstrap studentized interval has
asymptotic $N(0,1)$-coverage.

    Specializing `z = z_{1-α/2}` gives the `1 − α` bootstrap confidence interval
`θ̂ₙ ± z_{1-α/2} · σ̂ₙ / √n`.  The bridge hypothesis isolates the event-rewrite /
exceptional-set step (matching `trae_dr_wald_coverage`); it holds with `coverProb`
the natural interval-coverage probability whenever `σ̂ₙ > 0` a.e. -/
theorem bootstrap_wald_coverage
    (h : IsAsymLinear θn θ₀ ψ S (fun m => Finset.range m))
    (hψ_meas : Measurable ψ)
    (hψ_int : Integrable (fun ω => ψ (S.Z 0 ω)) μ)
    (hψ_sq_int : Integrable (fun ω => (ψ (S.Z 0 ω)) ^ 2) μ)
    (hpos : 0 < ∫ x, (ψ x) ^ 2 ∂P)
    (hθn_meas : ∀ n, AEMeasurable
      (IsAsymLinear.rescaledEstimator θn θ₀ (fun m => Finset.range m) n) μ)
    (hStud_meas : ∀ n,
      AEMeasurable (IIDSample.bootstrapStudentized θn θ₀ S ψ n) μ)
    {z : ℝ} (hz : 0 < z) (coverProb : ℕ → ℝ)
    (h_bridge : Tendsto
      (fun n => coverProb n
        - (μ {ω | IIDSample.bootstrapStudentized θn θ₀ S ψ n ω
            ∈ Set.Icc (-z) z}).toReal) atTop (𝓝 0)) :
    Tendsto coverProb atTop
      (𝓝 ((gaussianMeasure 0 1) (Set.Icc (-z) z)).toReal) := by
  have hStud := bootstrap_studentized_tendsto h hψ_meas hψ_int hψ_sq_int hpos
    hθn_meas hStud_meas
  exact Tendsto_dist.wald_coverage hStud_meas hStud hz coverProb h_bridge

end Causalean.Stat
