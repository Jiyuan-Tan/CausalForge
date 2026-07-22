/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.SuperPopulation.HAC
import Causalean.Experimentation.SuperPopulation.CLT

/-!
# Variance bound for the network-HAC variance estimator

The network-HAC estimator `V̂ = ∑ᵢ ∑_{j ∈ N i} Xᵢ Xⱼ` of a super-population locally-dependent
network field (`Causalean.Experimentation.SuperPopulation.NetworkDependence.netHACVarEst`) is
*itself* a sum of products over network-adjacent pairs.  Rewritten with `Finset.mul_sum` it is
exactly the localized double sum `∑ᵢ Xᵢ · (∑_{j ∈ N i} Xⱼ)` whose variance the proved
dependency-graph pair-counting bound `Causalean.SteinMethod.DepGraph.var_nbhd_prod_le` controls.

This file records two facts.

* `netHACVarEst_variance_le` — the **estimator-variance bound**: for a single field with bounded
  summands `|Xᵢ| ≤ B` and bounded degree `m`, the variance of `V̂` is at most a polynomial in `m`
  times `card(V)·B⁴`, namely `2·m⁵·card(V)·B⁴`.  This is the substantive lemma: it is *derived*
  from the m-dependence (covariances of separated localized products vanish) and the
  bounded-degree pair counting, not assumed.

* `netHACVarEst_variance_tendsto_zero` — the **variance → 0** corollary: along a CLT-regime sequence
  with `B n → 0` and `card(V n)·(B n)³ → 0`, the estimator variance tends to zero (squeeze the
  bound, using `card·B⁴ = (card·B³)·B → 0`).

The consistency-in-probability statement is assembled in `Consistency.lean` from this variance
limit and the unbiasedness identity `netHACVarEst_integral_eq_variance` via Chebyshev.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology BigOperators

namespace Causalean.Experimentation.SuperPopulation.HACConsistency

open Causalean.Experimentation.SuperPopulation Causalean.SteinMethod

variable {V Ω : Type*} [Fintype V] [DecidableEq V] [MeasurableSpace Ω] {μ : Measure Ω}

/-- The network-HAC estimator equals the localized double sum `∑ᵢ Xᵢ · (∑_{j ∈ N i} Xⱼ)`: the
pointwise identity that lets the dependency-graph variance bound apply to `V̂` verbatim. -/
theorem netHACVarEst_eq_locProd (F : NetworkDependence V Ω μ) (ω : Ω) :
    F.netHACVarEst ω = ∑ i, F.X i ω * ∑ k ∈ F.toDepGraph.nbhd i, F.X k ω := by
  simp only [NetworkDependence.netHACVarEst, NetworkDependence.nbhd, Finset.mul_sum]

/-- **Estimator-variance bound.** For a super-population network field `F` with summands bounded by
`B` (`|Xᵢ| ≤ B`) and bounded degree `m` (each network neighborhood has at most `m` units), the
variance of the network-HAC estimator `V̂ = ∑ᵢ ∑_{j∈N i} Xᵢ Xⱼ` is at most `2·m⁵·card(V)·B⁴`.

This is the genuine content of the consistency argument: because non-adjacent summand tuples are
independent (the m-dependence `NetworkDependence.indep`), the covariance between two localized
products `Xᵢ·Tᵢ` and `Xⱼ·Tⱼ` vanishes unless `i, j` are within graph distance two; there are at
most `card(V)·m³` such pairs, each covariance bounded by `2(m·B²)²`.  Proved by reducing to the
dependency-graph pair-counting bound `var_nbhd_prod_le` on `F.toDepGraph`. -/
theorem netHACVarEst_variance_le (F : NetworkDependence V Ω μ) [IsProbabilityMeasure μ]
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ i ω, |F.X i ω| ≤ B)
    {m : ℕ} (hdeg : ∀ i, (F.toDepGraph.nbhd i).card ≤ m) :
    variance (fun ω => F.netHACVarEst ω) μ ≤ 2 * (m : ℝ) ^ 5 * (Fintype.card V : ℝ) * B ^ 4 := by
  have hrw : (fun ω => F.netHACVarEst ω)
      = (fun ω => ∑ i, F.X i ω * ∑ k ∈ F.toDepGraph.nbhd i, F.X k ω) := by
    funext ω; exact netHACVarEst_eq_locProd F ω
  rw [hrw]
  exact F.toDepGraph.var_nbhd_prod_le hB hbound hdeg

/-- **Estimator variance tends to zero.** Along a sequence of super-population network fields `F n`
in the CLT regime — bounded degree `m`, summands bounded by `B n` with `B n → 0`, and
`card(V n)·(B n)³ → 0` — the variance of the network-HAC estimator tends to zero.

Squeeze the bound `2·m⁵·card(V n)·(B n)⁴` from `netHACVarEst_variance_le`, which tends to zero
because `card(V n)·(B n)⁴ = (card(V n)·(B n)³)·(B n) → 0·0`.  This is the variance half of the
HAC-consistency statement (`netHAC_consistent`). -/
theorem netHACVarEst_variance_tendsto_zero
    {V : ℕ → Type*} [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (F : ∀ n, NetworkDependence (V n) (Ω n) (μ n))
    (m : ℕ) (hdeg : ∀ n i, ((F n).toDepGraph.nbhd i).card ≤ m)
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n) (hbound : ∀ n i ω, |(F n).X i ω| ≤ B n)
    (hB0 : Tendsto B atTop (𝓝 0))
    (hNB3 : Tendsto (fun n => (Fintype.card (V n) : ℝ) * (B n) ^ 3) atTop (𝓝 0)) :
    Tendsto (fun n => variance (fun ω => (F n).netHACVarEst ω) (μ n)) atTop (𝓝 0) := by
  have hub : Tendsto (fun n => 2 * (m : ℝ) ^ 5 * (Fintype.card (V n) : ℝ) * (B n) ^ 4)
      atTop (𝓝 0) := by
    have hfac : (fun n => 2 * (m : ℝ) ^ 5 * (Fintype.card (V n) : ℝ) * (B n) ^ 4)
        = (fun n => (2 * (m : ℝ) ^ 5) *
            (((Fintype.card (V n) : ℝ) * (B n) ^ 3) * B n)) := by
      funext n; ring
    rw [hfac]
    have h := (hNB3.mul hB0)
    simpa using (h.const_mul (2 * (m : ℝ) ^ 5)).congr (fun n => by ring)
  refine squeeze_zero (fun n => variance_nonneg _ _) (fun n => ?_) hub
  exact netHACVarEst_variance_le (F n) (hB n) (hbound n) (hdeg n)

end Causalean.Experimentation.SuperPopulation.HACConsistency
