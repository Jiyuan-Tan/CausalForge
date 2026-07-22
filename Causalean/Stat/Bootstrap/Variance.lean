/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Nonparametric bootstrap variance for the i.i.d. sample type

The nonparametric (multinomial / Efron) bootstrap resamples `n` points with
replacement from the observed sample `{Z₀ ω, …, Z_{n-1} ω}`, i.e. draws i.i.d.
from the *empirical distribution* `P̂ₙ(ω)` that puts mass `1/n` on each observed
point.  For a real influence statistic `ψ`, the conditional variance of a single
bootstrap draw `ψ(Z*₁)` given the data is the **plug-in (empirical) variance**

    bootstrapVar S ψ n ω
      = (1/n) Σ_{i<n} ψ(Zᵢ ω)²  −  ((1/n) Σ_{i<n} ψ(Zᵢ ω))²
      = (1/n) Σ_{i<n} (ψ(Zᵢ ω) − ψ̄ₙ(ω))²            (`bootstrapVar_eq_centered`).

This is an *exact* identity (not an asymptotic statement): under multinomial
resampling the bootstrap mean `√n (X̄* − X̄)` has conditional variance exactly
`bootstrapVar`.  Consequently the bootstrap standard error feeds the generic
studentized CLT / Wald-coverage machinery (`Stat/Inference/Studentize.lean`),
which is the econometric workhorse use of the bootstrap (`vce(bootstrap)`):
a *consistent* bootstrap standard error yields a valid studentized / Wald
confidence interval.  Consistency `bootstrapVar →ₚ ∫ ψ² dP` follows from the
WLLN second-moment lemmas of `Stat/Limit/WLLN.lean`.

The distributional (Bickel–Freedman, percentile / percentile-t) refinements are
deliberately *not* claimed here; only the bootstrap-standard-error route, which
needs nothing beyond consistency of `σ̂` plus asymptotic normality of the
estimator.
-/

import Causalean.Stat.Limit.WLLN
import Causalean.Stat.Limit.ContinuousMapping
import Causalean.Stat.Inference.VarianceEstimation

/-! # Bootstrap Variance

This file defines the nonparametric bootstrap variance for a statistic of an
i.i.d. sample as the empirical second moment minus the square of the empirical
mean. It proves the exact centered-variance identity and the consistency result
needed by bootstrap standard-error and Wald-inference arguments.

The public API is `IIDSample.bootstrapVar` for the plug-in bootstrap variance,
`IIDSample.bootstrapVar_eq_centered` for the exact centered empirical-variance
identity, `IIDSample.bootstrapVar_nonneg` for nonnegativity, and
`IIDSample.bootstrapVar_tendsto_inProb` for convergence in probability to the
population second moment under the usual mean-zero influence-function
hypotheses. -/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

namespace IIDSample

/-- **Nonparametric bootstrap variance.**  The conditional variance of a single
multinomial-bootstrap draw `ψ(Z*₁)` given the first `n` sample points: the
plug-in (empirical) variance of `ψ` over the empirical distribution
`P̂ₙ(ω) = (1/n) Σ_{i<n} δ_{Zᵢ ω}`,

    bootstrapVar S ψ n ω = E*[ψ²] − (E*[ψ])²
      = S.sampleMean (ψ²) n ω − (S.sampleMean ψ n ω)².

Here `E*[g] = S.sampleMean g n ω` is expectation under the uniform empirical
pmf.  Equals the centered empirical second moment `(1/n) Σ (ψ(Zᵢ) − ψ̄ₙ)²`
(`bootstrapVar_eq_centered`), hence is nonnegative. -/
noncomputable def bootstrapVar (S : IIDSample Ω X μ P) (ψ : X → ℝ) (n : ℕ) :
    Ω → ℝ :=
  fun ω => S.sampleMean (fun x => (ψ x) ^ 2) n ω - (S.sampleMean ψ n ω) ^ 2

/-- **Exact bootstrap-variance identity** (`E*[ψ²] − (E*ψ)² = E*[(ψ − E*ψ)²]`).
The plug-in variance equals the centered empirical second moment: the
conditional variance of a single uniform draw from the observed sample.  This is
the standard `mean-of-squares minus square-of-mean` identity for the empirical
expectation, valid for every `n` (the `n = 0` case is `0 = 0`). -/
theorem bootstrapVar_eq_centered (S : IIDSample Ω X μ P) (ψ : X → ℝ) (n : ℕ)
    (ω : Ω) :
    bootstrapVar S ψ n ω
      = (n : ℝ)⁻¹ *
          ∑ i ∈ Finset.range n, (ψ (S.Z i ω) - S.sampleMean ψ n ω) ^ 2 := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn; simp [bootstrapVar, IIDSample.sampleMean]
  · have hncast : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp only [bootstrapVar, IIDSample.sampleMean]
    set f : ℕ → ℝ := fun i => ψ (S.Z i ω) with hf
    have hA : ∑ i ∈ Finset.range n,
          (f i - (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f j) ^ 2
        = (∑ i ∈ Finset.range n, (f i) ^ 2)
          - 2 * ((n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f j)
              * (∑ i ∈ Finset.range n, f i)
          + (n : ℝ) * ((n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f j) ^ 2 := by
      have hpt : ∀ i,
          (f i - (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f j) ^ 2
            = (f i) ^ 2
              - 2 * ((n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f j) * (f i)
              + ((n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f j) ^ 2 :=
        fun i => by ring
      simp_rw [hpt]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hA]
    field_simp
    ring

/-- The bootstrap variance is nonnegative: it is a centered empirical second
moment (`bootstrapVar_eq_centered`). -/
theorem bootstrapVar_nonneg (S : IIDSample Ω X μ P) (ψ : X → ℝ) (n : ℕ)
    (ω : Ω) : 0 ≤ bootstrapVar S ψ n ω := by
  rw [bootstrapVar_eq_centered]
  apply mul_nonneg
  · positivity
  · exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- **Consistency of the bootstrap variance.**  Along an i.i.d. sample with a
measurable, integrable, square-integrable, mean-zero influence function `ψ`
(`∫ ψ dP = 0`), the bootstrap variance converges in probability to the
population second moment:

    bootstrapVar S ψ n  →ₚ  ∫ x, (ψ x)² ∂P.

Proof: `S.sampleMean (ψ²) →ₚ ∫ ψ² dP` (second-moment WLLN) and
`(S.sampleMean ψ)² →ₚ (∫ ψ dP)² = 0` (WLLN + continuous mapping); subtract via
`Tendsto_inProb.sub` and use `∫ ψ dP = 0`. -/
theorem bootstrapVar_tendsto_inProb (S : IIDSample Ω X μ P)
    [IsProbabilityMeasure P] {ψ : X → ℝ}
    (hψ_meas : Measurable ψ)
    (hψ_int : Integrable (fun ω => ψ (S.Z 0 ω)) μ)
    (hψ_sq_int : Integrable (fun ω => (ψ (S.Z 0 ω)) ^ 2) μ)
    (hmean : ∫ x, ψ x ∂P = 0) :
    Tendsto_inProb (bootstrapVar S ψ) (fun _ => ∫ x, (ψ x) ^ 2 ∂P) μ := by
  have h2 : Tendsto_inProb (S.sampleMean (fun x => (ψ x) ^ 2))
      (fun _ => ∫ x, (ψ x) ^ 2 ∂P) μ :=
    S.sampleSecondMoment_tendsto_inProb hψ_meas hψ_sq_int
  have h1 : Tendsto_inProb (S.sampleMean ψ) (fun _ => ∫ x, ψ x ∂P) μ :=
    S.sampleMean_tendsto_inProb hψ_meas hψ_int
  have h1sq : Tendsto_inProb (fun n ω => (S.sampleMean ψ n ω) ^ 2)
      (fun _ => (∫ x, ψ x ∂P) ^ 2) μ := by
    have hcont : ContinuousAt (fun x : ℝ => x ^ 2) (∫ x, ψ x ∂P) :=
      (continuous_pow 2).continuousAt
    simpa using Tendsto_inProb.comp_continuousAt hcont h1
  have hsub := Tendsto_inProb.sub h2 h1sq
  have heq : (fun _ : Ω => (∫ x, (ψ x) ^ 2 ∂P) - (∫ x, ψ x ∂P) ^ 2)
      = (fun _ : Ω => ∫ x, (ψ x) ^ 2 ∂P) := by
    funext _; rw [hmean]; ring
  rw [heq] at hsub
  exact hsub

end IIDSample

end Causalean.Stat
