/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic

/-!
# Concentration building blocks for the random design

The interior nonparametric rates (`(Nh)^{−1/2}` variance, leverage `O(1)`) come from the
behaviour of the random design moment sums `∑ᵢ K((Aᵢ−t)/h) (Aᵢ−t)ᵐ` under an iid sample.
This file develops the elementary expectation/variance facts for such sums under the
product (iid) law `Measure.pi`, starting with linearity of expectation across the iid
coordinates:

`𝔼[∑ᵢ g(Xᵢ)] = N · 𝔼[g]`.

These are the building blocks that turn the algebraic reductions (bias `≤ √(M₀₀(M⁻¹)₀₀)`,
variance `≤ σ² W (M⁻¹)₀₀`) into rate statements via the design density.
-/

namespace Causalean.Stat.Concentration

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- **Expectation of an iid sum.** For an iid sample of size `N` drawn from a probability
measure `μ` (modelled by the product measure `Measure.pi`), the expectation of the sum
`∑ᵢ g(Xᵢ)` of a fixed integrable statistic `g` equals `N · 𝔼[g]`. -/
theorem integral_sum_pi_eq {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : Ω → ℝ) (hg : Integrable g μ) :
    ∫ ω, (∑ i : Fin N, g (ω i)) ∂(Measure.pi (fun _ : Fin N => μ))
      = N * ∫ ω, g ω ∂μ := by
  let π : Measure (Fin N → Ω) := Measure.pi (fun _ : Fin N => μ)
  have hπ : ∀ i : Fin N, MeasurePreserving (Function.eval i) π μ := by
    intro i
    simpa [π] using measurePreserving_eval (fun _ : Fin N => μ) i
  change ∫ ω, (∑ i : Fin N, g (ω i)) ∂π = N * ∫ ω, g ω ∂μ
  calc
    ∫ ω, (∑ i : Fin N, g (ω i)) ∂π
        = ∑ i : Fin N, ∫ ω, g (ω i) ∂π := by
          rw [integral_finset_sum]
          intro i _
          simpa [Function.comp_def] using (hπ i).integrable_comp_of_integrable hg
    _ = ∑ _i : Fin N, ∫ ω, g ω ∂μ := by
          apply Finset.sum_congr rfl
          intro i _
          calc
            ∫ ω, g (ω i) ∂π = ∫ ω, g ω ∂Measure.map (Function.eval i) π := by
              refine (integral_map (hπ i).measurable.aemeasurable ?_).symm
              simpa [(hπ i).map_eq] using hg.aestronglyMeasurable
            _ = ∫ ω, g ω ∂μ := by
              rw [(hπ i).map_eq]
    _ = N * ∫ ω, g ω ∂μ := by
          simp [Finset.sum_const, nsmul_eq_mul]

/-- **Variance of an iid sum.** For an iid sample of size `N` from `μ` (the product measure
`Measure.pi`), the variance of the sum `∑ᵢ g(Xᵢ)` of a fixed `L²` statistic `g` equals
`N · Var[g]` — the coordinate copies are independent, so cross-covariances vanish. -/
theorem variance_sum_pi_eq {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : Ω → ℝ) (hg : MemLp g 2 μ) :
    Var[fun ω => ∑ i : Fin N, g (ω i); Measure.pi (fun _ : Fin N => μ)]
      = N * Var[g; μ] := by
  rw [show (fun ω : Fin N → Ω => ∑ i : Fin N, g (ω i))
      = (∑ i : Fin N, fun ω : Fin N → Ω => g (ω i)) by
        ext ω
        simp [Finset.sum_apply]]
  simpa [Finset.sum_const, nsmul_eq_mul] using
    (ProbabilityTheory.variance_sum_pi
      (μ := fun _ : Fin N => μ)
      (X := fun _ : Fin N => g)
      (fun _ : Fin N => hg))

/-- **Chebyshev concentration of an iid sum.** Combining the iid expectation and variance laws
with Chebyshev's inequality: the sum `∑ᵢ g(Xᵢ)` of a fixed `L²` statistic over an iid sample of
size `N` deviates from its mean `N·𝔼[g]` by at least `ε` with probability at most
`N·Var[g]/ε²`. For the design weight `g = K((·−t)/h)` this is the concentration of the total
kernel weight `M₀₀` around `N·𝔼[K((A−t)/h)] = Θ(Nh)`. -/
theorem iid_sum_chebyshev {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : Ω → ℝ) (hg : MemLp g 2 μ)
    {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin N => μ))
        {ω : Fin N → Ω | ε ≤ |(∑ i, g (ω i)) - N * ∫ x, g x ∂μ|}
      ≤ ENNReal.ofReal (N * Var[g; μ] / ε ^ 2) := by
  let π : Measure (Fin N → Ω) := Measure.pi (fun _ : Fin N => μ)
  let S : (Fin N → Ω) → ℝ := fun ω => ∑ i : Fin N, g (ω i)
  have hS : MemLp S 2 π := by
    change MemLp (fun ω : Fin N → Ω => ∑ i : Fin N, g (ω i)) 2 π
    rw [show (fun ω : Fin N → Ω => ∑ i : Fin N, g (ω i))
        = (∑ i : Fin N, fun ω : Fin N → Ω => g (ω i)) by
          ext ω
          simp [Finset.sum_apply]]
    refine MeasureTheory.memLp_finset_sum'
      (s := Finset.univ) (f := fun i : Fin N => fun ω : Fin N → Ω => g (ω i)) ?_
    intro i _hi
    simpa [Function.comp_def, π] using
      hg.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => μ) i)
  have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq (μ := π) hS hε
  have hmean : ∫ ω, S ω ∂π = N * ∫ x, g x ∂μ := by
    simpa [S, π] using
      integral_sum_pi_eq (N := N) μ g (hg.integrable (by norm_num))
  have hvar : Var[S; π] = N * Var[g; μ] := by
    simpa [S, π] using variance_sum_pi_eq (N := N) μ g hg
  simpa [S, π, hmean, hvar] using hcheb

end Causalean.Stat.Concentration
