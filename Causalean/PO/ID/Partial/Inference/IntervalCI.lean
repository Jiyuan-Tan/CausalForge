/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Finite-sample honest confidence intervals for interval-identified parameters

Instantiating the abstract honest-CI lemma `Inference/Basic.lean` with the
finite-sample concentration intervals of `Stat/Concentration/ConfidenceInterval`.

The setup is the *plug-in Manski sandwich*: the partially identified scalar `θ₀`
is bracketed by two population means

    L = ∫ f_L ∂P  ≤  θ₀  ≤  ∫ f_U ∂P = U,

where `f_L`, `f_U` are observable lower/upper bounding statistics (e.g. the
worst-case / best-case imputations behind a Manski, Lee, or Balke–Pearl bound).  We
estimate each endpoint by its sample mean and *widen* by an absolute-deviation
concentration half-width.  The resulting random interval

    [ X̄ₙ(f_L) − w_L ,  X̄ₙ(f_U) + w_U ]

covers the whole identified set `[L, U]` — and hence the true `θ₀` — with
probability at least `1 − δ_L − δ_U`, at *every* sample size `n` (no asymptotics).
This is the finite-sample, plug-in form of the Horowitz–Manski (2000) honest
confidence region.

## Main results

* `hoeffding_honest_ci_set_cover` / `hoeffding_honest_ci_point_cover` — honest CI
  with Hoeffding half-widths, valid for bounded statistics `f_L ∈ [aL,bL]`,
  `f_U ∈ [aU,bU]`.
* `bernstein_honest_ci_point_cover` — variance-adaptive Bernstein version, tighter
  when the bounding statistics have small variance.

All half-widths are explicit; the conservativeness `δ_L + δ_U` is the Bonferroni
price of protecting both endpoints.  The sharper Imbens–Manski refinement (which,
when `U − L > 0`, replaces the two-sided half-widths by *one-sided* critical
values to recover `1 − α` rather than `1 − 2·(α/2)` parameter coverage) is the
asymptotic statement in `Inference/ImbensManski.lean`.
-/

import Causalean.PO.ID.Partial.Inference.Basic
import Causalean.Stat.Concentration.UniformDeviation.ConfidenceInterval
import Causalean.Stat.Limit.WLLN

/-! # Finite-Sample Confidence Intervals for Interval Bounds

This file turns plug-in estimates of lower and upper population bounds into
finite-sample confidence intervals for an interval-identified scalar parameter.
Given observable bounding statistics `fL` and `fU`, the lower and upper
population bounds are their means, and the random interval widens the two sample
means by concentration half-widths.

The theorem `hoeffding_honest_ci_set_cover` proves finite-sample coverage of the
whole identified interval using Hoeffding half-widths. Its corollary
`hoeffding_honest_ci_point_cover` gives parameter coverage for any
`theta0` in the population sandwich. The theorem
`bernstein_honest_ci_point_cover` gives the corresponding variance-adaptive
Bernstein version. All results are conservative two-endpoint guarantees based on
the abstract union-bound lemma in `Inference.Basic`; the one-sided asymptotic
Imbens-Manski refinement is developed separately in `Inference.ImbensManski`. -/

namespace Causalean.PartialID.Inference

open MeasureTheory ProbabilityTheory Real Causalean.Stat Causalean.Stat.Concentration

variable {Ω X' : Type*} [MeasurableSpace Ω] [MeasurableSpace X']
  {μ : Measure Ω} {P : Measure X'}

/-- **Finite-sample honest CI for the identified set (Hoeffding).** Given lower and upper
bounding statistics `f_L`, `f_U` that are [measurable](hyp:hfL,hfU), each [confined a.s. to a
known bounded range — `f_L ∈ [aL, bL]` with `aL < bL`, `f_U ∈ [aU, bU]` with
`aU < bU`](hyp:habL,habU,hbL,hbU) — at [any positive sample size `n`](hyp:hn) and [any pair of
failure probabilities `δ_L`, `δ_U` in `(0, 1]`](hyp:hδL0,hδL1,hδU0,hδU1), [widening the sample
means `X̄ₙ(f_L)` and `X̄ₙ(f_U)` outward by the matching Hoeffding half-widths produces a random
interval that covers the whole identified interval `[∫ f_L dP, ∫ f_U dP]` with probability at
least `1 − δ_L − δ_U`](goal). -/
theorem hoeffding_honest_ci_set_cover (S : IIDSample Ω X' μ P)
    {fL fU : X' → ℝ} (hfL : Measurable fL) (hfU : Measurable fU)
    {aL bL aU bU : ℝ} (habL : aL < bL) (habU : aU < bU)
    (hbL : ∀ᵐ x ∂P, fL x ∈ Set.Icc aL bL) (hbU : ∀ᵐ x ∂P, fU x ∈ Set.Icc aU bU)
    (n : ℕ) (hn : 0 < n) {δL δU : ℝ} (hδL0 : 0 < δL) (hδL1 : δL ≤ 1)
    (hδU0 : 0 < δU) (hδU1 : δU ≤ 1) :
    1 - δL - δU ≤
      μ.real (RandomCoversIcc
        (fun ω => S.sampleMean fL n ω - hoeffdingCIHalfWidth aL bL n δL)
        (fun ω => S.sampleMean fU n ω + hoeffdingCIHalfWidth aU bU n δU)
        (∫ x, fL x ∂P) (∫ x, fU x ∂P)) := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  have hL_one :
      μ.real {ω | (∫ x, fL x ∂P) < S.sampleMean fL n ω - hoeffdingCIHalfWidth aL bL n δL}
        ≤ δL :=
    le_trans (measureReal_mono lowerOvershoot_subset_absMiss)
      (hoeffding_ci_miss S hfL habL hbL n hn hδL0 hδL1)
  have hU_one :
      μ.real {ω | S.sampleMean fU n ω + hoeffdingCIHalfWidth aU bU n δU < (∫ x, fU x ∂P)}
        ≤ δU :=
    le_trans (measureReal_mono upperUndershoot_subset_absMiss)
      (hoeffding_ci_miss S hfU habU hbU n hn hδU0 hδU1)
  exact honest_ci_set_cover (S.measurable_sampleMean hfL n) (S.measurable_sampleMean hfU n)
    hL_one hU_one

/-- **Finite-sample honest CI for the parameter (Hoeffding).** The parameter-coverage corollary
of `hoeffding_honest_ci_set_cover`: under the same setup — [measurable](hyp:hfL,hfU) bounding
statistics `f_L`, `f_U` [a.s. confined to `[aL, bL]` and `[aU, bU]`
respectively](hyp:habL,habU,hbL,hbU), [a positive sample size `n`](hyp:hn), and [failure
probabilities `δ_L`, `δ_U` in `(0, 1]`](hyp:hδL0,hδL1,hδU0,hδU1) — if [the true scalar
parameter `θ₀` lies in the population sandwich `[∫ f_L dP, ∫ f_U dP]`](hyp:hsand), then [the same
widened random interval covers `θ₀` with probability at least `1 − δ_L − δ_U`](goal). -/
theorem hoeffding_honest_ci_point_cover (S : IIDSample Ω X' μ P)
    {fL fU : X' → ℝ} (hfL : Measurable fL) (hfU : Measurable fU)
    {aL bL aU bU : ℝ} (habL : aL < bL) (habU : aU < bU)
    (hbL : ∀ᵐ x ∂P, fL x ∈ Set.Icc aL bL) (hbU : ∀ᵐ x ∂P, fU x ∈ Set.Icc aU bU)
    (n : ℕ) (hn : 0 < n) {δL δU : ℝ} (hδL0 : 0 < δL) (hδL1 : δL ≤ 1)
    (hδU0 : 0 < δU) (hδU1 : δU ≤ 1)
    {θ₀ : ℝ} (hsand : θ₀ ∈ Set.Icc (∫ x, fL x ∂P) (∫ x, fU x ∂P)) :
    1 - δL - δU ≤
      μ.real (RandomCoversPoint
        (fun ω => S.sampleMean fL n ω - hoeffdingCIHalfWidth aL bL n δL)
        (fun ω => S.sampleMean fU n ω + hoeffdingCIHalfWidth aU bU n δU) θ₀) := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  have hL_one :
      μ.real {ω | (∫ x, fL x ∂P) < S.sampleMean fL n ω - hoeffdingCIHalfWidth aL bL n δL}
        ≤ δL :=
    le_trans (measureReal_mono lowerOvershoot_subset_absMiss)
      (hoeffding_ci_miss S hfL habL hbL n hn hδL0 hδL1)
  have hU_one :
      μ.real {ω | S.sampleMean fU n ω + hoeffdingCIHalfWidth aU bU n δU < (∫ x, fU x ∂P)}
        ≤ δU :=
    le_trans (measureReal_mono upperUndershoot_subset_absMiss)
      (hoeffding_ci_miss S hfU habU hbU n hn hδU0 hδU1)
  exact honest_ci_point_cover (S.measurable_sampleMean hfL n) (S.measurable_sampleMean hfU n)
    hsand hL_one hU_one

/-- **Finite-sample honest CI for the parameter (Bernstein).** Variance-adaptive version: with
[measurable](hyp:hfL,hfU) and [integrable](hyp:hfLint,hfUint) bounding statistics `f_L`, `f_U`,
[deviation bounds `|f_L − ∫f_L| ≤ cL` and `|f_U − ∫f_U| ≤ cU` holding a.s. for nonnegative
constants `cL, cU`](hyp:hcL,hcU,hbL,hbU), and [variance proxies `σL, σU > 0` dominating the
respective second central moments](hyp:hσL,hσU,hvL,hvU), for [a positive sample size
`n`](hyp:hn) and [failure probabilities `δ_L`, `δ_U` in `(0, 1]`](hyp:hδL0,hδL1,hδU0,hδU1), if
[the true parameter `θ₀` lies in the population sandwich `[∫ f_L dP, ∫ f_U dP]`](hyp:hsand), then
[widening the sample means by the corresponding Bernstein half-widths yields a random interval
covering `θ₀` with probability at least `1 − δ_L − δ_U`](goal).

When the bounding statistics have small variance this interval is far tighter than the Hoeffding
one (leading term `2σ√(log(2/δ)/n)` rather than `(b−a)√(log(2/δ)/2n)`). -/
theorem bernstein_honest_ci_point_cover (S : IIDSample Ω X' μ P)
    {fL fU : X' → ℝ} (hfL : Measurable fL) (hfU : Measurable fU)
    (hfLint : Integrable fL P) (hfUint : Integrable fU P)
    {cL σL cU σU : ℝ} (hcL : 0 ≤ cL) (hσL : 0 < σL) (hcU : 0 ≤ cU) (hσU : 0 < σU)
    (hbL : ∀ᵐ x ∂P, |fL x - ∫ y, fL y ∂P| ≤ cL)
    (hbU : ∀ᵐ x ∂P, |fU x - ∫ y, fU y ∂P| ≤ cU)
    (hvL : ∫ x, (fL x - ∫ y, fL y ∂P) ^ 2 ∂P ≤ σL ^ 2)
    (hvU : ∫ x, (fU x - ∫ y, fU y ∂P) ^ 2 ∂P ≤ σU ^ 2)
    (n : ℕ) (hn : 0 < n) {δL δU : ℝ} (hδL0 : 0 < δL) (hδL1 : δL ≤ 1)
    (hδU0 : 0 < δU) (hδU1 : δU ≤ 1)
    {θ₀ : ℝ} (hsand : θ₀ ∈ Set.Icc (∫ x, fL x ∂P) (∫ x, fU x ∂P)) :
    1 - δL - δU ≤
      μ.real (RandomCoversPoint
        (fun ω => S.sampleMean fL n ω - bernsteinCIHalfWidth cL σL n δL)
        (fun ω => S.sampleMean fU n ω + bernsteinCIHalfWidth cU σU n δU) θ₀) := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  have hL_one :
      μ.real {ω | (∫ x, fL x ∂P) < S.sampleMean fL n ω - bernsteinCIHalfWidth cL σL n δL}
        ≤ δL :=
    le_trans (measureReal_mono lowerOvershoot_subset_absMiss)
      (bernstein_ci_miss S hfL hfLint hcL hσL hbL hvL n hn hδL0 hδL1)
  have hU_one :
      μ.real {ω | S.sampleMean fU n ω + bernsteinCIHalfWidth cU σU n δU < (∫ x, fU x ∂P)}
        ≤ δU :=
    le_trans (measureReal_mono upperUndershoot_subset_absMiss)
      (bernstein_ci_miss S hfU hfUint hcU hσU hbU hvU n hn hδU0 hδU1)
  exact honest_ci_point_cover (S.measurable_sampleMean hfL n) (S.measurable_sampleMean hfU n)
    hsand hL_one hU_one

end Causalean.PartialID.Inference
