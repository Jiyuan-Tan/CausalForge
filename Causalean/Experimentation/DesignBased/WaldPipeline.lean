/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The design-based Wald-interval pipeline, in one theorem

`DependencyCLT` supplies the studentized CLT and `WaldCoverage` turns a studentized CLT plus a
conservative variance into interval coverage.  This file composes them: from primitive
dependency-graph inputs — bounded, mean-zero, bounded-degree unit contributions whose standardized
sum is the centered, scaled estimator, together with a deterministic conservative variance — the
two-sided Wald interval has asymptotic coverage at least `1 − α`.  A design-based interference paper
instantiates this single theorem instead of separately building a CLT, a Slutsky/coverage argument,
and their composition.
-/

import Causalean.Experimentation.DesignBased.DependencyCLT
import Causalean.Experimentation.DesignBased.WaldCoverage

/-! # Design-based Wald-interval pipeline

`dependency_wald_coverage` chains the design-based dependency CLT (`dependency_studentized_cdf`)
into the conservative Wald-coverage transfer (`conservative_wald_liminf_of_studentized_cdf`).  Given
unit
contributions `X n` whose standardized sum `depSum(X n)` equals the scaled centered estimator
`√(m n)·(est n − θ n)`, and a deterministic conservative variance `vhat n ≥ v n`, the Wald interval
`|θ n − est n| ≤ z·√(vhat n / m n)` has liminf coverage at least `1 − α`.
-/

open MeasureTheory ProbabilityTheory Filter
open Causalean.SteinMethod
open scoped Topology BigOperators

namespace Causalean
namespace Experimentation
namespace DesignBased

/-- **Design-based Wald-interval coverage from dependency-graph primitives.** Consider a sequence of
finite designs `D n` with an estimator `est n` of a target `θ n`.  Suppose the centered, `√(m n)`-
scaled estimator `√(m n)·(est n − θ n)` is the sum `depSum(X n)` of unit contributions `X n i` that
are uniformly bounded, have design mean `0`, and depend only across a graph of degree at most
`Dmax`, with standardizing variance `v n = E[depSum(X n)²]` bounded below by `c` times the number of
units, and the number of units diverging.  Then, for a deterministic conservative variance
`vhat n ≥ v n`, the two-sided Wald interval `|θ n − est n| ≤ z·√(vhat n / m n)` (with `z` the upper
`1 − α/2` normal quantile) has asymptotic (liminf) coverage at least `1 − α`.

This is the complete design-based inference pipeline: it obtains the studentized CLT from the
dependency-graph engine and feeds it, with the conservative variance, into the Wald-coverage
transfer, so a paper supplies only its unit-contribution decomposition and a conservative variance
bound. -/
theorem dependency_wald_coverage
    {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)] [∀ n, MeasurableSpace (Ω n)]
    [∀ n, MeasurableSingletonClass (Ω n)]
    (D : ∀ n, FiniteDesign (Ω n))
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (X : ∀ n, ι n → Ω n → ℝ) (Dep : ∀ n, DepGraph (X n) (D n).toMeasure)
    (Dmax : ℕ) (hdeg : ∀ n i, ((Dep n).nbhd i).card ≤ Dmax)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ n i ω, |X n i ω| ≤ M)
    (hmean : ∀ n i, (D n).E (X n i) = 0)
    (v : ℕ → ℝ) (hv : ∀ n, (D n).E (fun ω => depSum (X n) ω ^ 2) = v n)
    (c : ℝ) (hc : 0 < c)
    (hvc : ∀ᶠ n in atTop, c * (Fintype.card (ι n) : ℝ) ≤ v n)
    (hcard : Tendsto (fun n => Fintype.card (ι n)) atTop atTop)
    (est : ∀ n, Ω n → ℝ) (θ m : ℕ → ℝ)
    (hlink : ∀ n ω, depSum (X n) ω = Real.sqrt (m n) * (est n ω - θ n))
    (hmpos : ∀ᶠ n in atTop, 0 < m n) (hvarpos : ∀ᶠ n in atTop, 0 < v n)
    (vhat : ℕ → ℝ) (hvar_le : ∀ n, v n ≤ vhat n)
    (α z : ℝ) (hz0 : 0 ≤ z) (hz : stdNormalCdf z = 1 - α / 2) :
    1 - α ≤ liminf (fun n =>
        (D n).Pr (fun ω => |θ n - est n ω| ≤ z * Real.sqrt (vhat n / m n))) atTop := by
  have hclt : ∀ s : ℝ, Tendsto (fun n =>
      (D n).Pr (fun ω =>
        Real.sqrt (m n) * (est n ω - θ n) / Real.sqrt (v n) ≤ s))
      atTop (𝓝 (stdNormalCdf s)) := by
    intro s
    have h := dependency_studentized_cdf D X Dep Dmax hdeg M hM hbound hmean v hv c hc hvc hcard s
    refine Tendsto.congr (fun n => ?_) h
    refine (D n).Pr_congr _ _ (fun ω => ?_)
    rw [hlink n ω]
  exact conservative_wald_liminf_of_studentized_cdf D est θ v vhat m hmpos hvarpos hvar_le hclt
    α z hz0 hz

end DesignBased
end Experimentation
end Causalean
