/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Design-based central limit theorem from a bounded-degree dependency graph

The Stein dependency-graph CLT engine (`Causalean.SteinMethod.bounded_degree_dependency_clt`) is
stated over abstract probability measures.  Feeding it the design measure `D.toMeasure` through the
measure bridge specialises it to the finite-design layer, yielding the studentized
CDF-convergence statement `Pr[ depSum(X)/√v ≤ s ] → Φ(s)` in the native `FiniteDesign.Pr` form.

This is the general design-based CLT behind every interference paper: express the centered,
standardized estimator as `depSum` of bounded, mean-zero, bounded-degree-dependent unit
contributions with a variance floor, and its studentized statistic is asymptotically standard
normal.  Its conclusion is exactly the `hclt` hypothesis of
`conservative_wald_liminf_of_studentized_cdf`, so the two compose into a complete design-based
Wald-interval pipeline.
-/

import Causalean.Experimentation.DesignBased.MeasureBridge
import Causalean.Experimentation.DesignBased.GaussianCDF
import Causalean.Mathlib.Probability.SteinMethod.StandardizedDepGraphCLT

/-! # Design-based dependency-graph CLT

`dependency_studentized_cdf` transports the bounded-degree dependency-graph CLT to the finite-design
layer: for a sequence of designs whose unit contributions `X n` are uniformly bounded, mean-zero,
and dependent only across a bounded-degree graph, with the standardizing variance `v n` bounded
below by a constant multiple of the number of units, the studentized statistic
`depSum(X n)/√(v n)` has standard-normal limiting CDF under `D n`.  It is stated in the
`FiniteDesign.Pr` form so it plugs directly into `conservative_wald_liminf_of_studentized_cdf`.
-/

open MeasureTheory ProbabilityTheory Filter
open Causalean.SteinMethod
open scoped Topology BigOperators

namespace Causalean
namespace Experimentation
namespace DesignBased

/-- **Design-based dependency-graph CLT (studentized CDF form).** Consider a sequence of finite
designs `D n` with a triangular array of unit contributions `X n i`, uniformly bounded by `M`, each
with design mean `0`, whose statistical dependence is captured by a graph of degree at most `Dmax`.
If the standardizing variance `v n = E[depSum(X n)²]` is bounded below by `c` times the number of
units and the number of units diverges, then the studentized sum `depSum(X n)/√(v n)` has, under the
design `D n`, a limiting standard-normal CDF at every point `s`.

Obtained by feeding the design measure `D n .toMeasure` to the abstract Stein dependency-graph CLT
through the measure bridge; the conclusion is in the native `FiniteDesign.Pr` presentation so it can
be handed straight to `conservative_wald_liminf_of_studentized_cdf`. -/
theorem dependency_studentized_cdf
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
    (s : ℝ) :
    Tendsto (fun n => (D n).Pr (fun ω => depSum (X n) ω / Real.sqrt (v n) ≤ s))
      atTop (𝓝 (stdNormalCdf s)) := by
  classical
  have hmean' : ∀ n i, ∫ ω, X n i ω ∂((D n).toMeasure) = 0 := by
    intro n i
    exact ((D n).integral_toMeasure (X n i)).trans (hmean n i)
  have hv' : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂((D n).toMeasure) = v n := by
    intro n
    exact ((D n).integral_toMeasure (fun ω => (depSum (X n) ω) ^ 2)).trans (hv n)
  have hengine :=
    bounded_degree_dependency_clt (fun n => (D n).toMeasure) X Dep Dmax hdeg M hM hbound
      hmean' v hv' c hc hvc hcard s
  rw [show stdNormalCdf s = (gaussianReal 0 1).real (Set.Iic s) from rfl]
  refine hengine.congr (fun n => ?_)
  rw [← (D n).toMeasure_real_setOf,
    MeasureTheory.map_measureReal_apply (measurable_of_finite _) measurableSet_Iic]
  rfl

end DesignBased
end Experimentation
end Causalean
