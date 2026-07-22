/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The fixed-order U-statistic central limit theorem

This is the headline of the order-`m` U-statistic development: a symmetric,
square-integrable order-`m` U-statistic is `√n`-asymptotically normal with the
Hájek variance `∫ ψ² dP`, where `ψ = Σⱼ uProjOrderAt j h P` is the summed
coordinatewise first Hoeffding projection.

Two forms:

* `uStatisticOrder_clt` — the primitive CLT, taking the higher-order remainder
  negligibility `OrderDegenerateNegligible S h` as an explicit hypothesis.  Use
  this when negligibility is available from some other route.
* `uStatisticOrder_clt_of_regular` — the end-to-end CLT: it discharges
  negligibility internally (via `orderDegenerateNegligible_of_residual`,
  `OrderM.RemainderNegligible`) from the residual's regularity, so the caller
  supplies no negligibility hypothesis.  This is the order-`m` analogue of the
  order-2 `uStatistic_clt_of_symmetric`.

The `m = 2` specialization back onto the classical order-2 CLT lives in
`OrderM.OrderTwo`.
-/

import Causalean.Stat.UStatistic.OrderM.Hajek
import Causalean.Stat.UStatistic.OrderM.RemainderNegligible

/-!
# Fixed-order U-statistic CLTs

This module states the asymptotic-normality interface for fixed-order
U-statistics.  `uStatisticOrder_clt` converts a centered, square-integrable
summed first projection and an explicit higher-order remainder-negligibility
hypothesis into the Gaussian limit of the `√n`-rescaled statistic.

The end-to-end theorem `uStatisticOrder_clt_of_regular` discharges the
negligibility hypothesis from regularity of the residual kernel via
`orderDegenerateNegligible_of_residual`.  Together these declarations are the
public CLT endpoint for the `OrderM` U-statistic development.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X} [IsProbabilityMeasure μ]

/-- **Fixed-order U-statistic CLT.**  If the first-order influence function is
measurable, centered, square-integrable, and the higher-order residual is
negligible at the `√n` scale, then the U-statistic is asymptotically normal with
variance `∫ ψ² dP`, where `ψ` is the sum of coordinatewise first projections. -/
theorem uStatisticOrder_clt (S : IIDSample Ω X μ P)
    {m : ℕ} [NeZero m] (h : (Fin m → X) → ℝ)
    (hψ_meas : Measurable (uInfluenceOrder h P))
    (hψ_mean : ∫ x, uInfluenceOrder h P x ∂P = 0)
    (hψ_sq : Integrable (fun x => (uInfluenceOrder h P x) ^ 2) P)
    (hneg : OrderDegenerateNegligible S h)
    (hθn_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.rescaledEstimator (uStatisticOrder S h) (uMeanOrder h P)
        (fun r => Finset.range r) n) μ)
    (hSum_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.normalizedSum S (uInfluenceOrder h P)
        (fun r => Finset.range r) n) μ) :
    Tendsto_dist
      (IsAsymLinear.rescaledEstimator (uStatisticOrder S h) (uMeanOrder h P)
        (fun r => Finset.range r))
      (gaussianMeasure 0 (∫ x, (uInfluenceOrder h P x) ^ 2 ∂P))
      μ
      hθn_meas := by
  have hAL : IsAsymLinear (uStatisticOrder S h) (uMeanOrder h P)
      (uInfluenceOrder h P) S (fun r => Finset.range r) :=
    uStatisticOrder_isAsymLinear S h hψ_mean hψ_sq hneg
  exact hAL.tendsto_normal hψ_meas hθn_meas hSum_meas

/-- **Fixed-order U-statistic CLT (end-to-end).**  For an order-`m` kernel `h`
whose residual is regular (measurable, square-integrable, with the slice/Fubini
side conditions) and whose summed first projection is measurable, centered, and
square-integrable, the fixed-order U-statistic is `√n`-asymptotically normal with
variance `∫ ψ² dP`, `ψ = Σⱼ uProjOrderAt j h P`.  This composes
`uStatisticOrder_clt` with `orderDegenerateNegligible_of_residual`, so no
negligibility hypothesis is required from the caller — the order-`m` analogue of
`uStatistic_clt_of_symmetric`. -/
theorem uStatisticOrder_clt_of_regular
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {P : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (S : IIDSample Ω X μ P) {m : ℕ} [NeZero m] (h : (Fin m → X) → ℝ)
    (hmeas : Measurable (uDegenOrder h P))
    (hL2 : Integrable (fun z => (uDegenOrder h P z) ^ 2)
      (Measure.pi fun _ : Fin m => P))
    (hslice_int : ∀ j : Fin m, Integrable
      (fun x => ∫ tail : ({k : Fin m // k ≠ j}) → X,
        h (insertCoord j x tail) ∂(Measure.pi fun _ : {k : Fin m // k ≠ j} => P)) P)
    (hmean : ∀ j : Fin m,
      ∫ x, (∫ tail : ({k : Fin m // k ≠ j}) → X,
        h (insertCoord j x tail) ∂(Measure.pi fun _ : {k : Fin m // k ≠ j} => P)) ∂P
        = uMeanOrder h P)
    (hrow : ∀ (j : Fin m) (x : X),
      Integrable (fun tail : ({k : Fin m // k ≠ j}) → X =>
        h (insertCoord j x tail))
        (Measure.pi fun _ : {k : Fin m // k ≠ j} => P))
    (hψ_meas : Measurable (uInfluenceOrder h P))
    (hψ_mean : ∫ x, uInfluenceOrder h P x ∂P = 0)
    (hψ_sq : Integrable (fun x => (uInfluenceOrder h P x) ^ 2) P)
    (hθn_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.rescaledEstimator (uStatisticOrder S h) (uMeanOrder h P)
        (fun r => Finset.range r) n) μ)
    (hSum_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.normalizedSum S (uInfluenceOrder h P)
        (fun r => Finset.range r) n) μ) :
    Tendsto_dist
      (IsAsymLinear.rescaledEstimator (uStatisticOrder S h) (uMeanOrder h P)
        (fun r => Finset.range r))
      (gaussianMeasure 0 (∫ x, (uInfluenceOrder h P x) ^ 2 ∂P))
      μ
      hθn_meas := by
  have hneg : OrderDegenerateNegligible S h :=
    orderDegenerateNegligible_of_residual S h hmeas hL2 hslice_int hmean hrow
  exact uStatisticOrder_clt S h hψ_meas hψ_mean hψ_sq hneg hθn_meas hSum_meas

end Causalean.Stat
