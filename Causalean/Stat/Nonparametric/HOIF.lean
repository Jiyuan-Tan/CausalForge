/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.HOIF.ProductRemainder
import Causalean.Stat.Nonparametric.HOIF.DegenerateUStatVariance
import Causalean.Stat.Nonparametric.HOIF.ProjectedKernelTrace
import Causalean.Stat.Nonparametric.HOIF.ProjectionRisk

/-!
# Order-`m` higher-order influence function (HOIF) projection-risk substrate

Higher-order influence-function machinery for localized nonparametric functionals: product
remainders, degenerate U-statistic variance, projected-kernel trace identities, and projection-risk
assembly.

This barrel collects the Causalean substrate for the order-`m` HOIF projection-risk analysis with a
`J`-dimensional projection space and bandwidth `h`:

* `HOIF/ProductRemainder.lean` — the order-`m` estimation-bias remainder is a finite sum of products
  of `m+1` nuisance `L²`-errors, so its squared contribution is `R² ≤ |T|²·δ^{2(m+1)}`
  (`hoif_remainder_sq_le`); choosing the order so that `2(m+1)λ_* > κ` makes it `o(ρ_n)`
  (`hoif_order_choice_negligible`).
* `HOIF/DegenerateUStatVariance.lean` — the exact degenerate order-2 U-statistic variance
  `Var[Uₙ] = 2ζ/(n(n−1))` (`degenerate_uStatistic_variance`) and the consequence
  `Var[Uₙ] ≤ 4C·J/(nh)²` (`degenerate_uStatistic_variance_le`) under an L²-energy
  hypothesis `ζ ≤ C·J/h²`. Built on the order-2 degenerate-kernel machinery of
  `Causalean.Stat.UStatistic.Variance`.
* `HOIF/ProjectedKernelTrace.lean` — the projected degenerate kernel
  `g(x,y) = ⟨c(x), Σ⁻¹ c(y)⟩` has L²-energy `ζ = ∬ g² dP dP = J` (`projKernel_L2_eq_dim`), the trace
  identity `tr(Σ Σ⁻¹ Σ Σ⁻¹) = J`; plus its degeneracy (`projKernel_degen`).
* `HOIF/ProjectionRisk.lean` — the capstone assembling localized first-order variance
  `O((nh)^{-1})`, projection bias² `O(J^{-4s/d})`, degenerate U-statistic variance
  `O(J/(nh)²)`, and the order-`m` product remainder into a single risk bound
  (`hoif_projection_risk_bound`).
-/
