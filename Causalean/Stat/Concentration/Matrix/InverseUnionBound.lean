/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Concentration.Matrix.IidSums

/-!
# Union bound for entrywise design-matrix concentration

The random design moment matrix has entries `M_{jk}(ω) = ∑ᵢ h_{jk}(ωᵢ)` with
`h_{jk}(a) = K((a−t)/h)·(a−t)^{j+k}` — each entry is an iid sum, so it concentrates around its
mean `N·𝔼[h_{jk}]` by `iid_sum_chebyshev`. To control the whole `(p+1)²`-entry matrix at once
(the "good event" on which the inverse perturbation bound applies) we union-bound over the
finite index set: the probability that *some* coordinate sum deviates from its mean by at least
`η` is at most the sum of the per-coordinate Chebyshev bounds.

This is the probabilistic half of the matrix-inverse concentration: combined with the
deterministic entrywise perturbation bound (`designInv00_perturb`), it shows that on an event of
probability `≥ 1 − ∑ Var/η²` the empirical moment matrix is invertible with controlled leverage.
-/

namespace Causalean.Stat.Concentration

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- **Union bound for iid coordinate sums.** For a finite family `g : ι → Ω → ℝ` of `L²`
statistics evaluated on an iid sample of size `N` (product law `Measure.pi`), the probability
that *some* index `a` has its sum `∑ᵢ g a (ωᵢ)` deviate from its mean `N·𝔼[g a]` by at least `η`
is bounded by the sum of the per-index Chebyshev bounds `N·Var[g a]/η²`. Specialising `ι` to the
`(p+1)²` matrix-entry indices and `g` to the design statistics `h_{jk}` controls every entry of
the design moment matrix simultaneously on the complementary good event. -/
theorem iid_sum_union_bound {N : ℕ} {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : ι → Ω → ℝ) (hg : ∀ a, MemLp (g a) 2 μ)
    {η : ℝ} (hη : 0 < η) :
    (Measure.pi (fun _ : Fin N => μ))
        {ω : Fin N → Ω | ∃ a, η ≤ |(∑ i, g a (ω i)) - N * ∫ x, g a x ∂μ|}
      ≤ ∑ a, ENNReal.ofReal (N * Var[g a; μ] / η ^ 2) := by
  rw [Set.setOf_exists]
  refine le_trans (measure_iUnion_le
    (fun a : ι =>
      {ω : Fin N → Ω | η ≤ |(∑ i, g a (ω i)) - N * ∫ x, g a x ∂μ|})) ?_
  rw [tsum_fintype]
  refine Finset.sum_le_sum ?_
  intro a _
  exact iid_sum_chebyshev μ (g a) (hg a) hη

end Causalean.Stat.Concentration
