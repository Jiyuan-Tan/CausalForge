/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.SuperPopulation.Basic

/-!
# m-dependent CLT for a super-population network field

For a sequence of super-population network fields (one per population size `n`) with bounded
degree `m`, uniformly bounded summands `|X i| ≤ Bₙ` shrinking with `Bₙ → 0` and `N·Bₙ³ → 0`,
mean-zero summands, and unit total variance, the network sum `∑ᵢ Xᵢ` converges in distribution
to the standard normal.  This is the model-based (super-population, network-dependence) analog of
the design-based `prodDesign_clt`, and is obtained by viewing the field as a Stein dependency
graph (`NetworkDependence.toDepGraph`) and invoking the proved bounded-degree dependency-graph CLT
`stein_cdf_clt_of_depGraph` — the m-dependence (exact independence beyond the network) is exactly
its leave-out independence hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology BigOperators

namespace Causalean.Experimentation.SuperPopulation

open Causalean.SteinMethod

/-- **m-dependent network CLT (super-population).** For network fields `F n` with bounded degree
`m`, uniformly bounded mean-zero summands `|F n .X i| ≤ B n` with `B n → 0` and
`card(Vₙ)·(B n)³ → 0`, and unit total variance of the network sum, the network sum converges in
distribution to the standard normal: `P[∑ᵢ (F n).X i ≤ s] → Φ(s)`.

The randomness is the super-population draw `μ n`; the dependence is the network `(F n).adj`.
The proof reads off the dependency-graph hypotheses from the field and applies
`stein_cdf_clt_of_depGraph`. -/
theorem networkSum_clt
    {V : ℕ → Type*} [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (F : ∀ n, NetworkDependence (V n) (Ω n) (μ n))
    (m : ℕ) (hdeg : ∀ n i, ((F n).toDepGraph.nbhd i).card ≤ m)
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n) (hbound : ∀ n i ω, |(F n).X i ω| ≤ B n)
    (hB0 : Tendsto B atTop (𝓝 0))
    (hNB3 : Tendsto (fun n => (Fintype.card (V n) : ℝ) * (B n) ^ 3) atTop (𝓝 0))
    (hmean : ∀ n i, ∫ ω, (F n).X i ω ∂(μ n) = 0)
    (hvar : ∀ n, ∫ ω, (depSum (F n).X ω) ^ 2 ∂(μ n) = 1)
    (s : ℝ) :
    Tendsto (fun n => ((μ n).map (depSum (F n).X)).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) :=
  stein_cdf_clt_of_depGraph μ (fun n => (F n).X) (fun n => (F n).toDepGraph)
    (fun n i => (F n).meas i) m hdeg B hB hbound hB0 hNB3 hmean hvar s

end Causalean.Experimentation.SuperPopulation
