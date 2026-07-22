/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.SuperPopulation.Basic

/-!
# Network-HAC variance estimator

Inference for a super-population network field needs a variance estimator that is robust to the
network dependence — the analog of a HAC / cluster-robust estimator.  Because far-apart units are
independent (m-dependence beyond the network), the variance of the network sum collapses to a sum
of within-neighborhood cross-products, so the natural estimator is

  `V̂ = ∑ᵢ ∑_{j ∈ N i} Xᵢ Xⱼ`,

i.e. the empirical sum of products over network-adjacent pairs.  This file defines that estimator
and records its **unbiasedness** anchor: under mean-zero summands its expectation is exactly the
variance of the network sum.  Sequence-level consistency of `V̂` for the true variance along a
growing network is developed in the `HACConsistency` modules.
-/

open MeasureTheory ProbabilityTheory

namespace Causalean.Experimentation.SuperPopulation

open Causalean.SteinMethod

variable {V Ω : Type*} [Fintype V] [DecidableEq V] [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **network-HAC variance estimator** for a network field: the empirical sum of summand
products over network-adjacent pairs, `V̂(ω) = ∑ᵢ ∑_{j ∈ N i} Xᵢ(ω)·Xⱼ(ω)`.  It targets the
variance of the network sum, whose cross-terms vanish outside the network neighborhoods. -/
noncomputable def NetworkDependence.netHACVarEst (F : NetworkDependence V Ω μ) (ω : Ω) : ℝ :=
  ∑ i, ∑ j ∈ F.nbhd i, F.X i ω * F.X j ω

/-- **Unbiasedness of the network-HAC estimator.** Under a probability measure with mean-zero,
square-integrable summands, the expectation of the network-HAC estimator equals the variance of
the network sum: `E[V̂] = Var(∑ᵢ Xᵢ)`.  The off-neighborhood cross-covariances vanish by the
m-dependence (non-adjacent summands are independent, hence uncorrelated), so summing products over
the neighborhoods recovers the full covariance double sum. -/
theorem NetworkDependence.netHACVarEst_integral_eq_variance
    (F : NetworkDependence V Ω μ) [IsProbabilityMeasure μ]
    (hL2 : ∀ i, MemLp (F.X i) 2 μ)
    (hmean : ∀ i, ∫ ω, F.X i ω ∂μ = 0) :
    ∫ ω, F.netHACVarEst ω ∂μ = variance (depSum F.X) μ := by
  classical
  have hvar : variance (depSum F.X) μ = ∑ i, ∑ j, covariance (F.X i) (F.X j) μ := by
    simpa [depSum] using variance_fun_sum hL2
  have hprod : ∀ i j, ∫ ω, F.X i ω * F.X j ω ∂μ = covariance (F.X i) (F.X j) μ := by
    intro i j
    rw [covariance_eq_sub (hL2 i) (hL2 j)]
    simp [hmean i, hmean j]
  have hint : ∀ i j, Integrable (fun ω => F.X i ω * F.X j ω) μ := by
    intro i j
    exact (hL2 i).integrable_mul (hL2 j)
  have hzero : ∀ i j, j ∉ F.nbhd i → covariance (F.X i) (F.X j) μ = 0 := by
    intro i j hj
    have hsep : ∀ a ∈ ({i} : Finset V), ∀ b ∈ ({j} : Finset V), ¬ F.adj a b := by
      intro a ha b hb hab
      rw [Finset.mem_singleton] at ha
      rw [Finset.mem_singleton] at hb
      subst a
      subst b
      exact hj ((F.mem_nbhd_iff).mpr hab)
    have hind := F.indep ({i} : Finset V) ({j} : Finset V) hsep
    let φ : (({i} : Finset V) → ℝ) → ℝ :=
      fun t => t ⟨i, Finset.mem_singleton.mpr rfl⟩
    let ψ : (({j} : Finset V) → ℝ) → ℝ :=
      fun t => t ⟨j, Finset.mem_singleton.mpr rfl⟩
    have hφ : Measurable φ := measurable_pi_apply _
    have hψ : Measurable ψ := measurable_pi_apply _
    have hcomp := hind.comp hφ hψ
    have h1 : φ ∘ (fun ω => fun k : ({i} : Finset V) => F.X k ω) = F.X i := rfl
    have h2 : ψ ∘ (fun ω => fun k : ({j} : Finset V) => F.X k ω) = F.X j := rfl
    rw [h1, h2] at hcomp
    exact hcomp.covariance_eq_zero (hL2 i) (hL2 j)
  have hinner :
      ∀ i, ∑ j ∈ F.nbhd i, covariance (F.X i) (F.X j) μ =
        ∑ j, covariance (F.X i) (F.X j) μ := by
    intro i
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    exact hzero i j hj
  calc
    ∫ ω, F.netHACVarEst ω ∂μ
        = ∫ ω, (∑ i, ∑ j ∈ F.nbhd i, F.X i ω * F.X j ω) ∂μ := rfl
    _ = ∑ i, ∑ j ∈ F.nbhd i, ∫ ω, F.X i ω * F.X j ω ∂μ := by
          rw [MeasureTheory.integral_finset_sum Finset.univ]
          · congr with i
            rw [MeasureTheory.integral_finset_sum (F.nbhd i)]
            intro j _
            exact hint i j
          · intro i _
            exact integrable_finset_sum (F.nbhd i) (fun j _ => hint i j)
    _ = ∑ i, ∑ j ∈ F.nbhd i, covariance (F.X i) (F.X j) μ := by
          refine Finset.sum_congr rfl ?_
          intro i _
          refine Finset.sum_congr rfl ?_
          intro j _
          exact hprod i j
    _ = ∑ i, ∑ j, covariance (F.X i) (F.X j) μ := by
          refine Finset.sum_congr rfl ?_
          intro i _
          exact hinner i
    _ = variance (depSum F.X) μ := hvar.symm

end Causalean.Experimentation.SuperPopulation
