/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.HOIF.DegenerateUStatVariance
import Causalean.Stat.Nonparametric.HOIF.ProductRemainder
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Order-`m` HOIF projection-risk decomposition (capstone)

Risk decompositions for localized HOIF estimators, combining first-order variance, projection bias,
degenerate U-statistic variance, and higher-order product remainders.

The mean-squared error of an order-`m` HOIF estimator, using a `J`-dimensional projection space and
bandwidth `h`, splits into three statistically distinct pieces plus the higher-order estimation
remainder:

* **localized first-order variance** `V₁ = O((nh)^{-1})` — the AIPW/plug-in stochastic term;
* **projection product bias²** `B² = O(J^{-4s/d})` — the squared series/sieve approximation error of
  the `J`-term projection (`Causalean.Stat.Nonparametric.SeriesSieve`);
* **degenerate U-statistic variance** `V₂ = Var[Uₙ] ≤ 4C·J/(nh)²` — the second-order projected
  stochastic term, controlled by `HOIF.DegenerateUStatVariance` from the supplied localized
  L²-energy hypothesis `ζ ≤ C·J/h²` (the sibling `HOIF.ProjectedKernelTrace` proves the inverse-Gram
  identity `ζ = J` in the unlocalized case);
* **order-`m` product remainder** `R² ≤ |T|²·δ^{2(m+1)}` — the HOIF estimation bias, a finite sum of
  products of `m+1` nuisance `L²`-errors (`HOIF.ProductRemainder`), made `o(ρ_n)` by choosing `m`
  large enough (`hoif_order_choice_negligible`).

`hoif_projection_risk_bound` assembles these into a single explicit upper bound on the risk: it
takes the bias-variance decomposition as input and discharges the second-order variance term and
the product remainder from the Causalean theorems, leaving only `V₁` and `B²` (supplied by the
sibling local-polynomial / series-sieve substrates) as hypotheses.
-/

namespace Causalean.Stat.Nonparametric.HOIF

open MeasureTheory ProbabilityTheory
open Causalean.Stat

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
  {g : X → X → ℝ}

/-- **Order-`m` HOIF projection-risk bound.** For an i.i.d. sample `S` and a projection
kernel `g`, suppose [`g` is symmetric, square-integrable, and doubly degenerate](hyp:hg),
[the sample size `n` is at least `2`](hyp:hn), and [the bandwidth `h` is positive, the
projection dimension `J` and trace constant `C` are nonnegative, and the kernel's
L²-energy `ζ` obeys the trace bound `ζ ≤ C·J/h²`](hyp:hh,hJ,hC,hzeta). Suppose further
that [the first-order variance `V1` obeys the rate `V1 ≤ Cv1/(nh)`](hyp:hV1) and [the
projection bias² `Bsq` obeys the rate `Bsq ≤ Cb·J^{-4s/d}`](hyp:hB), and that the
order-`m` estimation remainder `R` is controlled, over a finite index set `T`, by a sum of
products of `m+1` nuisance-error factors: [every such factor is nonnegative](hyp:hnn),
[every factor is at most the largest nuisance error `δ`](hyp:hle), and [the absolute value
of `R` is bounded by that sum of products](hyp:hRbd). If, finally, [the estimator's risk
decomposes as `risk ≤ V1 + Bsq + Var[Uₙ] + R²`](hyp:hdecomp), then [the risk is bounded by
the explicit sum `Cv1/(nh) + Cb·J^{-4s/d} + 4C·J/(nh)² + |T|²·δ^{2(m+1)}`](goal).

The degenerate U-statistic variance term and the product-remainder term are discharged from the
Causalean theorems `degenerate_uStatistic_variance_le` and `hoif_remainder_sq_le`; the remaining two
terms are the first-order-variance / projection-bias inputs from the sibling substrates. -/
theorem hoif_projection_risk_bound (S : IIDSample Ω X μ P) (hg : DegenKernel P g)
    {ι : Type*} (T : Finset ι) (e : ι → ℕ → ℝ) (R : ℝ)
    {risk V1 Bsq Cv1 Cb C J h s d δ : ℝ} {n m : ℕ}
    (hn : 2 ≤ n) (hh : 0 < h) (hJ : 0 ≤ J) (hC : 0 ≤ C)
    (hzeta : IIDSample.zeta P g ≤ C * J / h ^ 2)
    (hV1 : V1 ≤ Cv1 / ((n : ℝ) * h))
    (hB : Bsq ≤ Cb * J ^ (-(4 * s / d)))
    (hnn : ∀ t ∈ T, ∀ k ∈ Finset.range (m + 1), 0 ≤ e t k)
    (hle : ∀ t ∈ T, ∀ k ∈ Finset.range (m + 1), e t k ≤ δ)
    (hRbd : |R| ≤ ∑ t ∈ T, ∏ k ∈ Finset.range (m + 1), e t k)
    (hdecomp : risk ≤ V1 + Bsq + variance (uStatistic S g n) μ + R ^ 2) :
    risk ≤ Cv1 / ((n : ℝ) * h) + Cb * J ^ (-(4 * s / d))
            + 4 * C * J / ((n : ℝ) * h) ^ 2 + (T.card : ℝ) ^ 2 * δ ^ (2 * (m + 1)) := by
  have hV2 : variance (uStatistic S g n) μ ≤ 4 * C * J / ((n : ℝ) * h) ^ 2 :=
    degenerate_uStatistic_variance_le S hg hn hh hJ hC hzeta
  have hRem : R ^ 2 ≤ (T.card : ℝ) ^ 2 * δ ^ (2 * (m + 1)) :=
    hoif_remainder_sq_le T e m δ R hnn hle hRbd
  calc risk ≤ V1 + Bsq + variance (uStatistic S g n) μ + R ^ 2 := hdecomp
    _ ≤ Cv1 / ((n : ℝ) * h) + Cb * J ^ (-(4 * s / d))
          + 4 * C * J / ((n : ℝ) * h) ^ 2 + (T.card : ℝ) ^ 2 * δ ^ (2 * (m + 1)) :=
        add_le_add (add_le_add (add_le_add hV1 hB) hV2) hRem

end Causalean.Stat.Nonparametric.HOIF
