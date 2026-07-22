/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bounded-degree dependency-graph CLT wrapper (re-export)

The standardization wrapper around the abstract Stein dependency-graph CLT
(`depGraph_div_const`, `bounded_degree_dependency_clt`, `bounded_degree_dependency_clt_eventually_bounded`,
`bounded_degree_dependency_clt_of_variance_floor_all`) was promoted to
`Causalean.Mathlib.Probability.SteinMethod.StandardizedDepGraphCLT`. This file re-exports it so the
bipartite experiment sees it under the `Causalean.SteinMethod` namespace it already opens.
-/

import Causalean.Mathlib.Probability.SteinMethod.StandardizedDepGraphCLT

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

-- @node: lem:bounded-degree-dependency-clt
/-- Centered, uniformly bounded triangular arrays with a dependency graph of fixed
maximum degree and an eventual linear variance lower bound satisfy the
variance-standardized central limit theorem. -/
lemma bounded_degree_dependency_clt
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (X : ∀ n, ι n → Ω n → ℝ)
    (Dep : ∀ n, Causalean.SteinMethod.DepGraph (X n) (μ n))
    (Dmax : ℕ) (hdeg : ∀ n i, ((Dep n).nbhd i).card ≤ Dmax)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ n i ω, |X n i ω| ≤ M)
    (hmean : ∀ n i, ∫ ω, X n i ω ∂(μ n) = 0)
    (v : ℕ → ℝ)
    (hv : ∀ n, ∫ ω, (Causalean.SteinMethod.depSum (X n) ω) ^ 2 ∂(μ n) = v n)
    (c : ℝ) (hc : 0 < c)
    (hcard : ∀ n, Fintype.card (ι n) = n)
    (hvc : ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ≤ v n)
    (s : ℝ) :
    Tendsto (fun n =>
        ((μ n).map (fun ω => Causalean.SteinMethod.depSum (X n) ω / Real.sqrt (v n))).real
          (Set.Iic s))
      atTop (nhds ((gaussianReal 0 1).real (Set.Iic s))) := by
  classical
  apply Causalean.SteinMethod.bounded_degree_dependency_clt
    μ X Dep Dmax hdeg M hM hbound hmean v hv c hc
  · simpa only [hcard] using hvc
  · simpa only [hcard] using
      (tendsto_id : Tendsto (fun n : ℕ => n) atTop atTop)

end CausalSmith.Experimentation.BipartiteMinimaxDesign
