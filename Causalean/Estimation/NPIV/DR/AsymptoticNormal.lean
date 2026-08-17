/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# TRAE-DR asymptotic normality

This file states `thm:est-trae-dr-asymp-normal` from
`doc/basic_concepts/po/estimation/trae_inverse_problems.tex`:

* the rescaled TRAE-DR estimator converges in distribution to
  `N(0, σ₀²)` along the estimation fold, where
  `σ₀² := ∫ ρ₀(w)² dP_W`;
* under a consistent variance estimator `σ̂_n`, the studentized statistic
  converges to `N(0, 1)`;
* the Wald interval `θ̂_n ± z_{1-α/2} σ̂_n / √|B(n)|` has asymptotic
  coverage `1 − α`.

The first theorem is a direct composition of `trae_dr_isAsymLinear`
(`thm:est-trae-dr-al-criterion`) with
`IsAsymLinear.tendsto_normal_foldB` (`Causalean/Stat/PartialFoldCLT.lean`).

The studentized and Wald-coverage statements are pragmatic: they
parameterize over a variance-estimator sequence `σ_hat_n` together with
its `Tendsto_inProb` consistency hypothesis.
-/

import Causalean.Estimation.NPIV.DR.AsymptoticLinear
import Causalean.Stat.SampleSplit.PartialFoldCLT
import Causalean.Stat.Inference.Studentize

/-!
Derives asymptotic normality for the doubly robust NPIV estimator from
asymptotic linearity, Gaussian score limits, and
studentization/continuous-mapping inputs.
-/

namespace Causalean
namespace Estimation
namespace NPIV
namespace DR

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat

/-! ## Headline asymptotic-normality theorem

The portmanteau / Gaussian-boundary helpers and the convergence-in-probability
primitives used below now live in `Causalean/Stat/Studentize.lean` and
`Causalean/Stat/ContinuousMapping.lean` (public, estimator-agnostic). -/

/-- **TRAE-DR asymptotic normality** — `thm:est-trae-dr-asymp-normal`. Under [the dual-solution
hypothesis on `q₀`](hyp:hq₀), [primal nuisance estimators `ĥ_n`, indexed by sample size and
outcome, satisfying — together with the paired dual estimators — the bundled TRAE-DR remainder
conditions](hyp:h_hat), and [the law bridge identifying the pushforward of `μ` along the
observation map `W` with the observation law `P_W`](hyp:h_law_W), suppose further that [the
√n-rescaled estimator sequence is almost-everywhere measurable at every sample
size](hyp:h_meas_θ) and [the normalized influence-function partial sum is almost-everywhere
measurable at every sample size](hyp:_h_meas_sum). Then [the rescaled TRAE-DR estimator
converges in distribution, along the estimation-fold sizes, to the centered Gaussian law with
variance `σ₀² := ∫ ρ₀(w)² dP_W`](goal).

Under the hypotheses of `trae_dr_isAsymLinear`, the rescaled estimator
converges in distribution to `N(0, σ₀²)` along the estimation-fold
horizon, where `σ₀² := ∫ ρ₀(w)² dP_W`.

This is the direct composition of `trae_dr_isAsymLinear` with
`IsAsymLinear.tendsto_normal_foldB`.  The conclusion is at the fold-B
rate `√|B(n)|`; for the √n form under a fixed split ratio
`|B(n)|/n → c`, the variance inflates to `σ₀²/c` (apply
`IsAsymLinear.tendsto_normal_foldB_sqrt_n` instead). -/
theorem trae_dr_asymp_normal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (S : InverseProblemSystem Ω μ) {q₀ : S.𝒵 → ℝ}
    (hq₀ : S.DualSolution q₀)
    {P_W : Measure S.𝒲} [IsProbabilityMeasure P_W]
    (sample : IIDSample Ω S.𝒲 μ P_W)
    (split : OneShotSplit sample)
    (h_hat : ℕ → Ω → (S.𝒳 → ℝ))
    (q_hat : ℕ → Ω → (S.𝒵 → ℝ))
    (_hyps : TRAEDRRemainderHyps S hq₀ sample split h_hat q_hat)
    (h_law_W : μ.map S.W = P_W)
    (_h_ρ₀_meas : Measurable (ρ₀ S q₀))
    (h_meas_θ : ∀ n, AEMeasurable
      (IsAsymLinear.rescaledEstimator
        (trae_dr_estimator S sample split h_hat q_hat) S.θ₀ split.foldB n) μ)
    (_h_meas_sum : ∀ n, AEMeasurable
      (IsAsymLinear.normalizedSum sample (ρ₀ S q₀) split.foldB n) μ) :
    Tendsto_dist
      (IsAsymLinear.rescaledEstimator
        (trae_dr_estimator S sample split h_hat q_hat) S.θ₀ split.foldB)
      (gaussianMeasure 0 (∫ w, (ρ₀ S q₀ w) ^ 2 ∂P_W))
      μ
      h_meas_θ := by
  have hAL : IsAsymLinear
      (trae_dr_estimator S sample split h_hat q_hat)
      S.θ₀
      (ρ₀ S q₀)
      sample
      split.foldB := by
    exact trae_dr_isAsymLinear S hq₀ sample split h_hat q_hat _hyps h_law_W _h_ρ₀_meas
  exact hAL.tendsto_normal_foldB split _h_ρ₀_meas h_meas_θ _h_meas_sum

/-! ## Studentized convergence -/

/-- **Studentized TRAE-DR convergence.** Fix [a dual solution `q₀` of the inverse-problem
system `S`](hyp:hq₀) together with [a first-stage nuisance-estimator sequence `ĥ_n`](hyp:h_hat),
and suppose [the sample's `W`-marginal is identified as `P_W`](hyp:h_law_W). Assume [the
efficient influence function `ρ₀` is measurable](hyp:h_ρ₀_meas) and [the rescaled estimator
sequence, its normalized-sum representation, and the studentized statistic itself are all
almost-everywhere measurable at every sample
size](hyp:h_meas_θ,h_meas_sum,h_studentized_meas). If [the asymptotic standard deviation
`σ₀` is strictly positive with `σ₀² = ∫ ρ₀(w)² dP_W`](hyp:_hσ₀_pos,_hσ_eq) and [a
variance-estimator sequence `σ̂_n` converges to `σ₀` in probability](hyp:_hσ_consistent), then
[the studentized statistic `√|B(n)| · (θ̂_n − θ₀) / σ̂_n` converges in distribution to the
standard normal law `N(0, 1)`](goal).

Given any variance-estimator sequence `σ_hat_n : ℕ → Ω → ℝ` satisfying
`σ̂_n →_p σ₀` and `σ₀ > 0`,

    √|B(n)| · (θ̂_n − θ₀) / σ̂_n  ⇒  N(0, 1).

A direct application of `Tendsto_dist.const_mul_tendsto_gaussian` to
`trae_dr_asymp_normal` plus Slutsky absorption of `1/σ̂_n` against the
constant `1/σ₀`. -/
theorem trae_dr_studentized
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (S : InverseProblemSystem Ω μ) {q₀ : S.𝒵 → ℝ}
    (hq₀ : S.DualSolution q₀)
    {P_W : Measure S.𝒲} [IsProbabilityMeasure P_W]
    (sample : IIDSample Ω S.𝒲 μ P_W)
    (split : OneShotSplit sample)
    (h_hat : ℕ → Ω → (S.𝒳 → ℝ))
    (q_hat : ℕ → Ω → (S.𝒵 → ℝ))
    (_hyps : TRAEDRRemainderHyps S hq₀ sample split h_hat q_hat)
    (h_law_W : μ.map S.W = P_W)
    (σ_hat_n : ℕ → Ω → ℝ) (σ₀ : ℝ)
    (_hσ₀_pos : 0 < σ₀)
    (_hσ_eq : σ₀ ^ 2 = ∫ w, (ρ₀ S q₀ w) ^ 2 ∂P_W)
    (_hσ_consistent : Tendsto_inProb σ_hat_n (fun _ => σ₀) μ)
    (h_ρ₀_meas : Measurable (ρ₀ S q₀))
    (h_meas_θ : ∀ n, AEMeasurable
      (IsAsymLinear.rescaledEstimator
        (trae_dr_estimator S sample split h_hat q_hat) S.θ₀ split.foldB n) μ)
    (h_meas_sum : ∀ n, AEMeasurable
      (IsAsymLinear.normalizedSum sample (ρ₀ S q₀) split.foldB n) μ)
    (h_studentized_meas : ∀ n, AEMeasurable
      (fun ω =>
        Real.sqrt ((split.foldB n).card : ℝ) *
          (trae_dr_estimator S sample split h_hat q_hat n ω - S.θ₀)
          / σ_hat_n n ω) μ) :
    Tendsto_dist
      (fun n ω =>
        Real.sqrt ((split.foldB n).card : ℝ) *
          (trae_dr_estimator S sample split h_hat q_hat n ω - S.θ₀)
          / σ_hat_n n ω)
      (gaussianMeasure 0 1)
      μ
      h_studentized_meas := by
  let Xn : ℕ → Ω → ℝ :=
    IsAsymLinear.rescaledEstimator
      (trae_dr_estimator S sample split h_hat q_hat) S.θ₀ split.foldB
  have hAN : Tendsto_dist Xn (gaussianMeasure 0 (σ₀ ^ 2)) μ h_meas_θ := by
    have h :=
      trae_dr_asymp_normal S hq₀ sample split h_hat q_hat _hyps h_law_W
        h_ρ₀_meas h_meas_θ h_meas_sum
    simpa [Xn, _hσ_eq] using h
  -- The studentized statistic is `Xn / σ̂ₙ`; apply the generic studentized CLT
  -- (`Tendsto_dist.div_tendsto_inProb_gaussian` in `Causalean/Stat/Studentize.lean`).
  have hdiv : ∀ n, AEMeasurable (fun ω => Xn n ω / σ_hat_n n ω) μ := by
    intro n
    simpa [Xn, IsAsymLinear.rescaledEstimator] using h_studentized_meas n
  have hres :=
    Tendsto_dist.div_tendsto_inProb_gaussian _hσ₀_pos h_meas_θ hAN
      _hσ_consistent hdiv
  simpa [Xn, IsAsymLinear.rescaledEstimator] using hres

/-! ## Wald-interval asymptotic coverage -/

/-- **Wald asymptotic coverage** — `thm:est-trae-dr-asymp-normal`. Under the same setup as
`trae_dr_studentized` — [a dual solution `q₀` of the inverse-problem system `S`](hyp:hq₀),
[a first-stage nuisance-estimator sequence `ĥ_n`](hyp:h_hat), [the sample's `W`-marginal
identified as `P_W`](hyp:h_law_W), [measurability of `ρ₀`, of the rescaled estimator, of its
normalized-sum representation, and of the studentized
statistic](hyp:h_ρ₀_meas,h_meas_θ,h_meas_sum,h_studentized_meas), and [a variance-estimator
sequence `σ̂_n` that is consistent in probability for a strictly positive `σ₀` satisfying
`σ₀² = ∫ ρ₀(w)² dP_W`](hyp:_hσ₀_pos,_hσ_eq,_hσ_consistent) — fix any [strictly positive real
number `z`](hyp:_hz_pos). Then [provided the coverage probability of the Wald interval
`θ̂_n ± z · σ̂_n / √|B(n)|` and the probability that the studentized statistic lands in
`[-z, z]` become asymptotically equal, the Wald-interval coverage probability converges to
the standard-normal mass `2 Φ(z) − 1` on `[-z, z]`](goal).

The hypothesis `h_wald_studentized` is the event-rewrite/exceptional-set
bridge: it says the Wald coverage event and the studentized interval event
have asymptotically equal probabilities.  It is separated from the
distributional argument so callers can discharge it from positivity of
`σ̂_n` and the fold-B cardinality in the concrete estimator setup.

In particular, taking `z = z_{1-α/2}` gives asymptotic coverage `1 − α`
for the Wald interval

    θ̂_n ± z_{1-α/2} · σ̂_n / √|B(n)|.

The conclusion is phrased as a `Tendsto` on the coverage probability;
plugging in the standard-normal quantile is left to the user. -/
theorem trae_dr_wald_coverage
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (S : InverseProblemSystem Ω μ) {q₀ : S.𝒵 → ℝ}
    (hq₀ : S.DualSolution q₀)
    {P_W : Measure S.𝒲} [IsProbabilityMeasure P_W]
    (sample : IIDSample Ω S.𝒲 μ P_W)
    (split : OneShotSplit sample)
    (h_hat : ℕ → Ω → (S.𝒳 → ℝ))
    (q_hat : ℕ → Ω → (S.𝒵 → ℝ))
    (_hyps : TRAEDRRemainderHyps S hq₀ sample split h_hat q_hat)
    (h_law_W : μ.map S.W = P_W)
    (σ_hat_n : ℕ → Ω → ℝ) (σ₀ : ℝ)
    (_hσ₀_pos : 0 < σ₀)
    (_hσ_eq : σ₀ ^ 2 = ∫ w, (ρ₀ S q₀ w) ^ 2 ∂P_W)
    (_hσ_consistent : Tendsto_inProb σ_hat_n (fun _ => σ₀) μ)
    (h_ρ₀_meas : Measurable (ρ₀ S q₀))
    (h_meas_θ : ∀ n, AEMeasurable
      (IsAsymLinear.rescaledEstimator
        (trae_dr_estimator S sample split h_hat q_hat) S.θ₀ split.foldB n) μ)
    (h_meas_sum : ∀ n, AEMeasurable
      (IsAsymLinear.normalizedSum sample (ρ₀ S q₀) split.foldB n) μ)
    (h_studentized_meas : ∀ n, AEMeasurable
      (fun ω =>
        Real.sqrt ((split.foldB n).card : ℝ) *
          (trae_dr_estimator S sample split h_hat q_hat n ω - S.θ₀)
          / σ_hat_n n ω) μ)
    (z : ℝ) (_hz_pos : 0 < z) :
    Tendsto
      (fun n =>
        (μ {ω | |trae_dr_estimator S sample split h_hat q_hat n ω - S.θ₀|
            ≤ z * σ_hat_n n ω / Real.sqrt ((split.foldB n).card : ℝ)}).toReal
        -
        (μ {ω |
          Real.sqrt ((split.foldB n).card : ℝ) *
            (trae_dr_estimator S sample split h_hat q_hat n ω - S.θ₀)
            / σ_hat_n n ω ∈ Set.Icc (-z) z}).toReal)
      atTop
      (𝓝 0) →
    Tendsto
      (fun n =>
        (μ {ω | |trae_dr_estimator S sample split h_hat q_hat n ω - S.θ₀|
            ≤ z * σ_hat_n n ω / Real.sqrt ((split.foldB n).card : ℝ)}).toReal)
      atTop
      (𝓝 ((gaussianMeasure 0 1) (Set.Icc (-z) z)).toReal) := by
  intro h_wald_studentized
  let studentized : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((split.foldB n).card : ℝ) *
      (trae_dr_estimator S sample split h_hat q_hat n ω - S.θ₀)
      / σ_hat_n n ω
  let coverProb : ℕ → ℝ := fun n =>
    (μ {ω | |trae_dr_estimator S sample split h_hat q_hat n ω - S.θ₀|
        ≤ z * σ_hat_n n ω / Real.sqrt ((split.foldB n).card : ℝ)}).toReal
  let studProb : ℕ → ℝ := fun n =>
    (μ {ω | studentized n ω ∈ Set.Icc (-z) z}).toReal
  change Tendsto (fun n => coverProb n - studProb n) atTop (𝓝 0) at h_wald_studentized
  have hStud :
      Tendsto_dist studentized (gaussianMeasure 0 1) μ h_studentized_meas := by
    simpa [studentized] using
      trae_dr_studentized S hq₀ sample split h_hat q_hat _hyps
        h_law_W σ_hat_n σ₀ _hσ₀_pos _hσ_eq _hσ_consistent
        h_ρ₀_meas h_meas_θ h_meas_sum h_studentized_meas
  -- The portmanteau argument is now the generic `Tendsto_dist.wald_coverage`
  -- (in `Causalean/Stat/Studentize.lean`); the studentized limit `hStud` and the
  -- event-equivalence bridge `h_wald_studentized` are the only inputs.
  have hcover :=
    Tendsto_dist.wald_coverage h_studentized_meas hStud _hz_pos coverProb
      h_wald_studentized
  simpa [coverProb] using hcover

end DR
end NPIV
end Estimation
end Causalean
