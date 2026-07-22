/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sample-quantile asymptotics (Bahadur representation)

Causal-agnostic inference layer for the `τ`-quantile of an i.i.d. real sample.
For a sequence of quantile estimators `q̂ₙ` (e.g. the empirical-cdf generalized
inverse of `Stat/Quantile.lean`, or an IPW-reweighted variant for the QTE) the
**Bahadur representation** says

    q̂ₙ − q₀  =  (1/n) Σ ψ_τ(Z_i)  +  o_p(n^{-1/2}),
    ψ_τ(z)   =  (τ − 1{z ≤ q₀}) / f₀,

where `q₀` is the population `τ`-quantile (`F(q₀) = τ`) and `f₀ = F'(q₀) > 0`
the density at the quantile.  The influence function `ψ_τ` is mean-zero with
variance

    ∫ ψ_τ² dP  =  τ(1 − τ) / f₀²,

the classical sample-quantile asymptotic variance.  Consequently

    √n (q̂ₙ − q₀)  ⇒  N(0, τ(1 − τ) / f₀²).

## Design: the one exposed hypothesis

The genuinely hard analytic content — the empirical-process oscillation
(Donsker / asymptotic-equicontinuity) step that produces the `o_p(n^{-1/2})`
Bahadur remainder — is **exposed as a hypothesis** (`QuantileRegularity.bahadur`),
exactly mirroring the established `StochEquicontAt` pattern of
`Stat/EmpiricalExpansion.lean`.
Everything downstream — the influence function, its mean and variance, and the
resulting `√n`-asymptotic normality — is proved.  This makes the layer reusable
by *any* quantile estimator satisfying the expansion (plain sample quantile,
IPW-weighted QTE quantile, …): instantiate `QuantileRegularity` and read off
the limit law.

The remainder field is literally the `IsAsymLinear.remainder` of `(q̂ₙ, q₀, ψ_τ)`,
so `QuantileRegularity.isAsymLinear` packages the bundle into the project's
generic asymptotic-linearity engine, and `QuantileRegularity.tendsto_normal`
specializes `IsAsymLinear.tendsto_normal` with the closed-form variance.

For the ordinary empirical sample quantile, the companion
`SampleQuantileBahadur` modules prove the Bahadur remainder directly and expose
`sampleQuantile_quantileRegularity`. The generic bundle here deliberately keeps
`bahadur` as an assumption so it can also be reused for other quantile estimators,
such as reweighted or causal quantile estimators, once their own expansion has
been proved.

References: Bahadur (1966); van der Vaart (1998) §21; Koenker (2005) §4.
-/

import Causalean.Stat.Quantile.EmpiricalCDF

/-! # Sample Quantile Asymptotics

This file develops the influence-function and asymptotic-normality layer for
sample quantiles of an i.i.d. real sample. It assumes the Bahadur representation
as the regularity input and then derives the classical variance and Gaussian
limit for the quantile estimator. -/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {P : Measure ℝ}

/-- The sample-quantile influence function
`ψ_τ(z) = (τ − 1{z ≤ q₀}) / f₀`. -/
noncomputable def quantileIF (τ q₀ f₀ : ℝ) : ℝ → ℝ :=
  fun z => (τ - cdfStat q₀ z) / f₀

/-- The sample-quantile influence function is measurable. -/
lemma measurable_quantileIF (τ q₀ f₀ : ℝ) : Measurable (quantileIF τ q₀ f₀) :=
  (measurable_const.sub (measurable_cdfStat q₀)).div_const f₀

/-- The quantile influence function has mean zero under `P`, given that `q₀`
is the population `τ`-quantile (`F(q₀) = τ`). -/
lemma quantileIF_mean_zero [IsProbabilityMeasure P] {τ q₀ f₀ : ℝ}
    (hcdf : cdf P q₀ = τ) :
    ∫ z, quantileIF τ q₀ f₀ z ∂P = 0 := by
  unfold quantileIF
  rw [integral_div, integral_sub (integrable_const _) (integrable_cdfStat q₀),
    integral_const, probReal_univ, one_smul, integral_cdfStat, hcdf,
    sub_self, zero_div]

/-- The quantile influence function is square-integrable (it is bounded). -/
lemma quantileIF_sq_integrable [IsProbabilityMeasure P] {τ q₀ f₀ : ℝ} :
    Integrable (fun z => (quantileIF τ q₀ f₀ z) ^ 2) P := by
  refine (integrable_const (((|τ| + 1) / |f₀|) ^ 2)).mono'
    ((measurable_quantileIF τ q₀ f₀).pow_const 2).aestronglyMeasurable ?_
  filter_upwards with z
  have hc0 : 0 ≤ cdfStat q₀ z := cdfStat_nonneg q₀ z
  have hc1 : cdfStat q₀ z ≤ 1 := cdfStat_le_one q₀ z
  have hnum : |τ - cdfStat q₀ z| ≤ |τ| + 1 := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have := neg_abs_le τ; linarith
    · have := le_abs_self τ; linarith
  have hbound : |quantileIF τ q₀ f₀ z| ≤ (|τ| + 1) / |f₀| := by
    unfold quantileIF
    rw [abs_div, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr (abs_nonneg _))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc (quantileIF τ q₀ f₀ z) ^ 2 = |quantileIF τ q₀ f₀ z| ^ 2 := (sq_abs _).symm
    _ ≤ ((|τ| + 1) / |f₀|) ^ 2 := by gcongr

/-- **Variance of the quantile influence function.**
`∫ ψ_τ² dP = τ(1 − τ) / f₀²`, the classical sample-quantile asymptotic
variance. -/
lemma quantileIF_variance [IsProbabilityMeasure P] {τ q₀ f₀ : ℝ}
    (hcdf : cdf P q₀ = τ) :
    ∫ z, (quantileIF τ q₀ f₀ z) ^ 2 ∂P = τ * (1 - τ) / f₀ ^ 2 := by
  have hstat : Integrable (cdfStat q₀) P := integrable_cdfStat q₀
  have hexpand : (fun z => (quantileIF τ q₀ f₀ z) ^ 2)
      = (fun z => (τ ^ 2 - 2 * τ * cdfStat q₀ z + cdfStat q₀ z) / f₀ ^ 2) := by
    funext z
    unfold quantileIF
    rw [div_pow]
    congr 1
    rw [show (τ - cdfStat q₀ z) ^ 2
          = τ ^ 2 - 2 * τ * cdfStat q₀ z + (cdfStat q₀ z) ^ 2 from by ring, cdfStat_sq]
  rw [hexpand, integral_div]
  have h1 : Integrable (fun z => τ ^ 2 - 2 * τ * cdfStat q₀ z) P :=
    (integrable_const (τ ^ 2)).sub (hstat.const_mul (2 * τ))
  have hinner : ∫ z, (τ ^ 2 - 2 * τ * cdfStat q₀ z + cdfStat q₀ z) ∂P = τ - τ ^ 2 := by
    rw [integral_add h1 hstat,
      integral_sub (integrable_const _) (hstat.const_mul (2 * τ)), integral_const_mul]
    simp only [integral_cdfStat, integral_const, probReal_univ, one_smul]
    rw [hcdf]; ring
  rw [hinner]; congr 1; ring

/-! ## Regularity bundle and asymptotic normality -/

/-- **Quantile-estimator regularity.**  Bundles the analytic facts plus the one
exposed empirical-process hypothesis (the Bahadur remainder) needed to conclude
`√n`-asymptotic normality of a quantile-estimator sequence `q̂ₙ` for the
`τ`-quantile of `P`:

* `tau_pos`, `tau_lt_one` — interior level `τ ∈ (0, 1)`.
* `density_pos` — positive density `f₀ > 0` at the quantile.
* `cdf_eq` — `q₀` is the population `τ`-quantile: `F(q₀) = τ`.
* `hasDeriv` — `f₀` is the density at `q₀`: `HasDerivAt F f₀ q₀` (records that the
  variance `τ(1−τ)/f₀²` is the genuine asymptotic variance).
* `bahadur` — the exposed Donsker/equicontinuity content: the rescaled estimator
  matches the normalized influence-function sum up to `o_p(1)`.  This is exactly
  the `IsAsymLinear.remainder` for `(q̂ₙ, q₀, ψ_τ)`.

For the ordinary empirical sample quantile this field is supplied by
`sampleQuantile_quantileRegularity` in the companion `SampleQuantileBahadur`
modules. It remains a hypothesis here because the same bundle is meant to cover
other quantile-estimator sequences once their Bahadur expansion is available. -/
structure QuantileRegularity (S : IIDSample Ω ℝ μ P) (qn : ℕ → Ω → ℝ)
    (τ q₀ f₀ : ℝ) : Prop where
  tau_pos : 0 < τ
  tau_lt_one : τ < 1
  density_pos : 0 < f₀
  cdf_eq : cdf P q₀ = τ
  hasDeriv : HasDerivAt (fun y => cdf P y) f₀ q₀
  bahadur : IsLittleOp
    (fun n ω => Real.sqrt ((Finset.range n).card : ℝ) * (qn n ω - q₀)
      - (Real.sqrt ((Finset.range n).card : ℝ))⁻¹
        * ∑ i ∈ Finset.range n, quantileIF τ q₀ f₀ (S.Z i ω))
    (fun _ => (1 : ℝ)) μ

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

/-- A `QuantileRegularity` bundle is an `IsAsymLinear` witness for `q̂ₙ` at `q₀`
with influence function `ψ_τ`. -/
lemma QuantileRegularity.isAsymLinear {S : IIDSample Ω ℝ μ P} {qn : ℕ → Ω → ℝ}
    {τ q₀ f₀ : ℝ} (h : QuantileRegularity S qn τ q₀ f₀) :
    IsAsymLinear qn q₀ (quantileIF τ q₀ f₀) S (fun m => Finset.range m) where
  mean_zero := quantileIF_mean_zero h.cdf_eq
  finite_var := quantileIF_sq_integrable
  remainder := h.bahadur

/-- **Sample-quantile asymptotic normality.**  Under `QuantileRegularity`,
`√n (q̂ₙ − q₀) ⇒ N(0, τ(1 − τ) / f₀²)`.

Measurability obligations on the rescaled estimator and the normalized sum are
imposed at the call site, matching `IsAsymLinear.tendsto_normal`. -/
theorem QuantileRegularity.tendsto_normal {S : IIDSample Ω ℝ μ P} {qn : ℕ → Ω → ℝ}
    {τ q₀ f₀ : ℝ} (h : QuantileRegularity S qn τ q₀ f₀)
    (hθn_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.rescaledEstimator qn q₀ (fun m => Finset.range m) n) μ)
    (hSum_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.normalizedSum S (quantileIF τ q₀ f₀) (fun m => Finset.range m) n) μ) :
    Tendsto_dist
      (IsAsymLinear.rescaledEstimator qn q₀ (fun m => Finset.range m))
      (gaussianMeasure 0 (τ * (1 - τ) / f₀ ^ 2))
      μ
      hθn_meas := by
  have hAL := h.isAsymLinear.tendsto_normal (measurable_quantileIF τ q₀ f₀) hθn_meas hSum_meas
  rwa [quantileIF_variance h.cdf_eq] at hAL

end Causalean.Stat
