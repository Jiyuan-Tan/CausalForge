/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Coupling.ProductLossMonotoneCoupling.Hoeffding
import Causalean.Stat.Coupling.ProductLossMonotoneCoupling.FrechetHoeffdingAttainment

/-!
# Optimality of the monotone couplings (capstone)

Over the Fréchet class `Π(μ, ν)` of couplings of two `L²` real probability
measures, the product expectation `E_π[XY] = ∫ p, p.1 * p.2 ∂π` is:

* **maximised** by the comonotone (quantile) coupling, and
* **minimised** by the countermonotone coupling.

The argument: by Hoeffding's identity `E_π[XY] = E[X]E[Y] + ∫∫ (H_π - F·G)`.
The term `E[X]E[Y]` depends only on the marginals `μ, ν`, hence is **constant**
across `Π(μ, ν)`; so extremising `E_π[XY]` is the same as extremising
`∫∫ H_π`. The Fréchet–Hoeffding bounds give this pointwise: `H_π ≤ H_comonotone`
and `H_countermonotone ≤ H_π`, and monotonicity of the double integral lifts the
pointwise ordering to the integrals.

A closed form for the optimum is also recorded:
`E[XY]` under the comonotone coupling equals `∫_(0,1) quantile μ · quantile ν`.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Set
open Causalean.Stat

variable {π : Measure (ℝ × ℝ)} {μ ν : Measure ℝ}

/-- **Upper optimality.** For every coupling `π` of `(μ, ν)` with `L²`
marginals, the product expectation is at most that of the comonotone coupling:

    `∫ p, p.1 * p.2 ∂π ≤ ∫ p, p.1 * p.2 ∂(comonotoneCoupling μ ν)`.

Proof: apply `hoeffding_cov_identity` to both `π` and the comonotone coupling;
the `E[X]E[Y]` terms coincide (same marginals), and the double integrals are
ordered by the pointwise bound `jointCdf_le_comonotone` together with
monotonicity of the integral (`integrable_frechet_gap` supplies integrability). -/
theorem product_expectation_le_comonotone (h : IsCoupling π μ ν)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun x : ℝ => x) 2 μ) (hν : MemLp (fun y : ℝ => y) 2 ν) :
    (∫ p, p.1 * p.2 ∂π) ≤ ∫ p, p.1 * p.2 ∂(comonotoneCoupling μ ν) := by
  let hc : IsCoupling (comonotoneCoupling μ ν) μ ν := isCoupling_comonotoneCoupling μ ν
  have hπid := hoeffding_cov_identity h hμ hν
  have hcid := hoeffding_cov_identity hc hμ hν
  have hπint := integrable_frechet_gap h hμ hν
  have hcint := integrable_frechet_gap hc hμ hν
  have hgap :
      (∫ x, ∫ y, (jointCdf π x y - cdf μ x * cdf ν y) ∂volume ∂volume) ≤
        ∫ x, ∫ y, (jointCdf (comonotoneCoupling μ ν) x y -
          cdf μ x * cdf ν y) ∂volume ∂volume := by
    rw [← MeasureTheory.integral_prod
        (fun p : ℝ × ℝ => jointCdf π p.1 p.2 - cdf μ p.1 * cdf ν p.2) hπint,
      ← MeasureTheory.integral_prod
        (fun p : ℝ × ℝ => jointCdf (comonotoneCoupling μ ν) p.1 p.2 -
          cdf μ p.1 * cdf ν p.2) hcint]
    refine MeasureTheory.integral_mono hπint hcint ?_
    intro p
    exact sub_le_sub_right (jointCdf_le_comonotone h p.1 p.2) _
  nlinarith [hπid, hcid, hgap]

/-- **Lower optimality.** For every coupling `π` of `(μ, ν)` with `L²`
marginals, the product expectation is at least that of the countermonotone
coupling:

    `∫ p, p.1 * p.2 ∂(countermonotoneCoupling μ ν) ≤ ∫ p, p.1 * p.2 ∂π`.

Proof mirrors the upper bound, using `countermonotone_le_jointCdf`. -/
theorem countermonotone_le_product_expectation (h : IsCoupling π μ ν)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun x : ℝ => x) 2 μ) (hν : MemLp (fun y : ℝ => y) 2 ν) :
    (∫ p, p.1 * p.2 ∂(countermonotoneCoupling μ ν)) ≤ ∫ p, p.1 * p.2 ∂π := by
  let hc : IsCoupling (countermonotoneCoupling μ ν) μ ν := isCoupling_countermonotoneCoupling μ ν
  have hcid := hoeffding_cov_identity hc hμ hν
  have hπid := hoeffding_cov_identity h hμ hν
  have hcint := integrable_frechet_gap hc hμ hν
  have hπint := integrable_frechet_gap h hμ hν
  have hgap :
      (∫ x, ∫ y, (jointCdf (countermonotoneCoupling μ ν) x y -
        cdf μ x * cdf ν y) ∂volume ∂volume) ≤
        ∫ x, ∫ y, (jointCdf π x y - cdf μ x * cdf ν y) ∂volume ∂volume := by
    rw [← MeasureTheory.integral_prod
        (fun p : ℝ × ℝ => jointCdf (countermonotoneCoupling μ ν) p.1 p.2 -
          cdf μ p.1 * cdf ν p.2) hcint,
      ← MeasureTheory.integral_prod
        (fun p : ℝ × ℝ => jointCdf π p.1 p.2 - cdf μ p.1 * cdf ν p.2) hπint]
    refine MeasureTheory.integral_mono hcint hπint ?_
    intro p
    exact sub_le_sub_right (countermonotone_le_jointCdf h p.1 p.2) _
  nlinarith [hcid, hπid, hgap]

/-- **Closed form of the optimum.** The product expectation under the comonotone
coupling is the integral of the product of quantile functions over `(0,1)`:

    `∫ p, p.1 * p.2 ∂(comonotoneCoupling μ ν)
       = ∫ u in Ioo 0 1, quantile μ u * quantile ν u`.

Immediate from the change-of-variables formula for pushforward measures applied
to `f p = p.1 * p.2` and `g u = (quantile μ u, quantile ν u)`. -/
theorem product_expectation_comonotoneCoupling (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun x : ℝ => x) 2 μ) (hν : MemLp (fun y : ℝ => y) 2 ν) :
    (∫ p, p.1 * p.2 ∂(comonotoneCoupling μ ν))
      = ∫ u in Ioo (0 : ℝ) 1, quantile μ u * quantile ν u := by
  unfold comonotoneCoupling
  rw [MeasureTheory.integral_map]
  · rfl
  · exact (aemeasurable_quantile_unifOI μ).prodMk (aemeasurable_quantile_unifOI ν)
  · fun_prop

end Causalean.Stat
