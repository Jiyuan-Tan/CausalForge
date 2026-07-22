/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.SuperPopulation.HACConsistency.VarianceBound
import Mathlib.Probability.Moments.Variance

/-!
# Consistency of the network-HAC variance estimator

This file proves the variance-estimator consistency input for feasible inference with
super-population network dependence: the network-HAC estimator `V̂ = ∑ᵢ ∑_{j ∈ N i} Xᵢ Xⱼ`
converges in probability to the variance of the network sum under bounded-degree and shrinking
summand conditions.  It supplies a consistency ingredient for future Wald-style conclusions, but
does not itself prove a Wald statistic or coverage theorem.

The argument is Chebyshev:

* the estimator is *unbiased*, `E[V̂] = Var(∑ᵢ Xᵢ)` (the proved identity
  `NetworkDependence.netHACVarEst_integral_eq_variance`), and
* its *variance* tends to zero (`netHACVarEst_variance_tendsto_zero`),

so for every `ε > 0` the deviation probability
`(μ n)({ω | ε ≤ |V̂ ω − Var(∑ᵢ Xᵢ)|}) ≤ Var(V̂)/ε² → 0`.

`netHAC_consistent` is the resulting convergence-in-probability statement, stated with the
real-valued measure `Measure.real` to match the convergence-mode convention used elsewhere in the
library.  The bounded-summand `MemLp` anchor is the auxiliary `netHACVarEst_memLp`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology BigOperators

namespace Causalean.Experimentation.SuperPopulation.HACConsistency

open Causalean.Experimentation.SuperPopulation Causalean.SteinMethod

variable {V Ω : Type*} [Fintype V] [DecidableEq V] [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The network-HAC estimator is in `L²`.** With summands bounded by `B` and degree `≤ m`, the
estimator `V̂` is pointwise bounded by `card(V)·m·B²`, hence square-integrable; this is the moment
hypothesis Chebyshev's inequality needs. -/
theorem netHACVarEst_memLp (F : NetworkDependence V Ω μ) [IsProbabilityMeasure μ]
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ i ω, |F.X i ω| ≤ B)
    {m : ℕ} (hdeg : ∀ i, (F.toDepGraph.nbhd i).card ≤ m) :
    MemLp (fun ω => F.netHACVarEst ω) 2 μ := by
  classical
  have hmeas : Measurable (fun ω => F.netHACVarEst ω) := by
    simp only [NetworkDependence.netHACVarEst]
    exact Finset.measurable_sum _ (fun i _ =>
      Finset.measurable_sum _ (fun j _ => (F.meas i).mul (F.meas j)))
  have hpt : ∀ ω, |F.netHACVarEst ω| ≤ (Fintype.card V : ℝ) * ((m : ℝ) * B ^ 2) := by
    intro ω
    calc
      |F.netHACVarEst ω|
          = |∑ i, ∑ j ∈ F.nbhd i, F.X i ω * F.X j ω| := rfl
      _ ≤ ∑ i, |∑ j ∈ F.nbhd i, F.X i ω * F.X j ω| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j ∈ F.nbhd i, |F.X i ω * F.X j ω| :=
          Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i, ∑ j ∈ F.nbhd i, B * B :=
          Finset.sum_le_sum (fun i _ =>
            Finset.sum_le_sum (fun j _ => by
              rw [abs_mul]
              exact mul_le_mul (hbound i ω) (hbound j ω) (abs_nonneg _) hB))
      _ = ∑ i, ((F.nbhd i).card : ℝ) * (B * B) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ _i : V, (m : ℝ) * (B * B) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          change ((F.toDepGraph.nbhd i).card : ℝ) ≤ (m : ℝ)
          exact_mod_cast hdeg i
      _ = (Fintype.card V : ℝ) * ((m : ℝ) * B ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  exact MemLp.of_bound hmeas.aestronglyMeasurable
    ((Fintype.card V : ℝ) * ((m : ℝ) * B ^ 2))
    (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs]
      exact hpt ω))

/-- **HAC consistency (convergence in probability).** Along a sequence of super-population network
fields `F n` in the CLT regime — bounded degree `m`, summands bounded by `B n` with `B n → 0` and
`card(V n)·(B n)³ → 0`, square-integrable mean-zero summands — the network-HAC estimator converges
in probability to the variance of the network sum: for every `ε > 0`,

  `(μ n)({ω | ε ≤ |(F n).netHACVarEst ω − variance (depSum (F n).X) (μ n)|}) → 0`.

By unbiasedness (`netHACVarEst_integral_eq_variance`) the target `variance (depSum (F n).X)` is the
mean `E[V̂]`, so this is Chebyshev's inequality `(μ n).real {…} ≤ Var(V̂)/ε²` together with the
variance limit `netHACVarEst_variance_tendsto_zero`. -/
theorem netHAC_consistent
    {V : ℕ → Type*} [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (F : ∀ n, NetworkDependence (V n) (Ω n) (μ n))
    (m : ℕ) (hdeg : ∀ n i, ((F n).toDepGraph.nbhd i).card ≤ m)
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n) (hbound : ∀ n i ω, |(F n).X i ω| ≤ B n)
    (hB0 : Tendsto B atTop (𝓝 0))
    (hNB3 : Tendsto (fun n => (Fintype.card (V n) : ℝ) * (B n) ^ 3) atTop (𝓝 0))
    (hL2 : ∀ n i, MemLp ((F n).X i) 2 (μ n))
    (hmean : ∀ n i, ∫ ω, (F n).X i ω ∂(μ n) = 0)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (μ n).real
        {ω | ε ≤ |(F n).netHACVarEst ω - variance (depSum (F n).X) (μ n)|})
      atTop (𝓝 0) := by
  have hmemLp : ∀ n, MemLp (fun ω => (F n).netHACVarEst ω) 2 (μ n) :=
    fun n => netHACVarEst_memLp (F n) (hB n) (hbound n) (hdeg n)
  have hEq : ∀ n, ∫ ω, (F n).netHACVarEst ω ∂(μ n) =
      variance (depSum (F n).X) (μ n) :=
    fun n => (F n).netHACVarEst_integral_eq_variance (hL2 n) (hmean n)
  have hupper : Tendsto
      (fun n => variance (fun ω => (F n).netHACVarEst ω) (μ n) / ε ^ 2) atTop (𝓝 0) := by
    simpa using
      (netHACVarEst_variance_tendsto_zero μ F m hdeg B hB hbound hB0 hNB3).div_const (ε ^ 2)
  refine squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_) hupper
  have hcheb := meas_ge_le_variance_div_sq (hmemLp n) hε
  rw [hEq n] at hcheb
  have hnn : (0 : ℝ) ≤ variance (fun ω => (F n).netHACVarEst ω) (μ n) / ε ^ 2 := by
    exact div_nonneg (variance_nonneg _ _) (sq_nonneg ε)
  rw [measureReal_def]
  calc
    ((μ n) {ω | ε ≤ |(F n).netHACVarEst ω -
        variance (depSum (F n).X) (μ n)|}).toReal
        ≤ (ENNReal.ofReal (variance (fun ω => (F n).netHACVarEst ω) (μ n) / ε ^ 2)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
    _ = variance (fun ω => (F n).netHACVarEst ω) (μ n) / ε ^ 2 :=
        ENNReal.toReal_ofReal hnn

end Causalean.Experimentation.SuperPopulation.HACConsistency
