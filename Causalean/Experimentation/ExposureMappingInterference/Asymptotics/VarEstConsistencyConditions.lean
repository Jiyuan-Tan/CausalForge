/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.ExposureMappingInterference.Asymptotics.VarEstQuadBound
import Causalean.Experimentation.ExposureMappingInterference.Asymptotics.VarianceConsistency
import Causalean.Experimentation.ExposureMappingInterference.Asymptotics.SteinInstance
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Variance-estimator consistency from boundedness and dependency-graph conditions

Assembles the per-population quadruple-sum bound (`var_htEdgeStat_le`) into the asymptotic limit
`N²·Var[V̂_n] → 0` along a sequence of growing experiments, under uniform boundedness,
single-propensity overlap, inverse joint-propensity bounds, and dependency-graph covariance
conditions.  Combined with the Stein dependency-graph CLT discharge, the Chebyshev reduction
(`relVar_of_NsqVar_tendsto`), and the feasible-coverage capstone
(`wald_coverage_feasible_of_relVar`), this proves feasible Wald coverage from primitive
boundedness, overlap, dependency-graph, and variance-growth conditions.

`N²·Var[V̂_n] = N⁻²·Var[V̂_raw,n] ≤ N⁻²·(8·M²·m³·N) = 8·M²·m³/N → 0` as `N → ∞`.
-/


open scoped BigOperators Topology Classical
open Filter

namespace Causalean
namespace Experimentation
namespace ExposureMappingInterference

open Causalean.Experimentation.DesignBased

variable {Ω : Type*} [Fintype Ω]
variable {ι Θ Δ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq Δ]

/-- The finite-design variance is nonnegative. -/
private lemma Var_nonneg (D : FiniteDesign Ω) (X : Ω → ℝ) : 0 ≤ D.Var X :=
  D.E_nonneg (fun _ => sq_nonneg _)

/-- **Per-population scaled-variance bound.** Under the stated boundedness, overlap, dependency,
and covariance-vanishing hypotheses, `N²·Var[V̂] ≤ 8·M²·m³·N⁻¹`, where `M = vbBound`.
The scaling `V̂ = N⁻²·V̂_raw` converts the linear-in-`N` bound on `Var[V̂_raw]` into an
`O(N⁻¹)` bound on `N²·Var[V̂]`. -/
private lemma NsqVar_htEffectVarEst_le (D : FiniteDesign Ω) (y : ι → Δ → ℝ) (f : Ω → Θ → Δ)
    (θ : ι → Θ) (dk dl : Δ) (hne : dk ≠ dl)
    {c₁ c₂ c₃ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hy : ∀ i d, |y i d| ≤ c₁)
    (hπk : ∀ i, 0 < prop D f θ i dk) (hπl : ∀ i, 0 < prop D f θ i dl)
    (hπinvk : ∀ i, 1 / prop D f θ i dk ≤ c₂) (hπinvl : ∀ i, 1 / prop D f θ i dl ≤ c₂)
    (hjk : ∀ i j, 1 / propPairSame D f θ i j dk ≤ c₃)
    (hjl : ∀ i j, 1 / propPairSame D f θ i j dl ≤ c₃)
    (hjc : ∀ i j, 1 / propPairCross D f θ i j dk dl ≤ c₃)
    (G : ι → ι → Prop) [DecidableRel G] (hrefl : ∀ i, G i i) (hsymm : ∀ i j, G i j → G j i)
    {m : ℕ} (hdeg : ∀ i, (Finset.univ.filter (fun j => G i j)).card ≤ m)
    (hGindep : ∀ i j, ¬ G i j →
        propPairSame D f θ i j dk = prop D f θ i dk * prop D f θ j dk ∧
        propPairSame D f θ i j dl = prop D f θ i dl * prop D f θ j dl ∧
        propPairCross D f θ i j dk dl = prop D f θ i dk * prop D f θ j dl)
    (hcov0 : ∀ i j k l, ¬ (G i k ∨ G i l ∨ G j k ∨ G j l) →
        D.Cov (vb D y f θ dk dl i j) (vb D y f θ dk dl k l) = 0) :
    (Fintype.card ι : ℝ) ^ 2 * D.Var (htEffectVarEst D y f θ dk dl)
      ≤ 8 * vbBound c₁ c₂ c₃ ^ 2 * (m : ℝ) ^ 3 * (Fintype.card ι : ℝ)⁻¹ := by
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  by_cases hN0 : N = 0
  · -- Degenerate `N = 0`: the estimator divides by `0`, so it is identically `0`.
    have hzero : htEffectVarEst D y f θ dk dl = fun _ => 0 := by
      funext z; unfold htEffectVarEst; rw [← hNdef, hN0]; simp
    rw [hzero, hN0]; simp
  · have hNpos : 0 < N := lt_of_le_of_ne (by rw [hNdef]; positivity) (Ne.symm hN0)
    -- `V̂ = (N⁻¹)²·V̂_raw`.
    have hform : htEffectVarEst D y f θ dk dl
        = fun z => (N⁻¹) ^ 2 * (htVarEst D y f θ dk z + htVarEst D y f θ dl z
            - 2 * htCovEst D y f θ dk dl z) := by
      funext z; unfold htEffectVarEst; rw [← hNdef, inv_pow]; ring
    rw [hform, FiniteDesign.Var_const_mul]
    -- `Var[V̂_raw] ≤ 8·vbBound²·(m³·N)`.
    have hVraw := var_htEdgeStat_le D y f θ dk dl hne hc₁ hc₂ hc₃ hy hπk hπl hπinvk hπinvl
      hjk hjl hjc G hrefl hsymm hdeg hGindep hcov0
    set V : ℝ := D.Var (fun z => htVarEst D y f θ dk z + htVarEst D y f θ dl z
        - 2 * htCovEst D y f θ dk dl z) with hVdef
    set C : ℝ := 8 * vbBound c₁ c₂ c₃ ^ 2 * (m : ℝ) ^ 3 with hCdef
    have hVle : V ≤ C * N := by
      rw [hCdef]; calc V ≤ 8 * vbBound c₁ c₂ c₃ ^ 2 * ((m : ℝ) ^ 3 * N) := hVraw
        _ = 8 * vbBound c₁ c₂ c₃ ^ 2 * (m : ℝ) ^ 3 * N := by ring
    calc N ^ 2 * (((N⁻¹) ^ 2) ^ 2 * V)
        ≤ N ^ 2 * (((N⁻¹) ^ 2) ^ 2 * (C * N)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hVle (by positivity)
      _ = C * N⁻¹ := by field_simp

/-- **Scaled variance-estimator variance vanishes (Aronow–Samii Prop 6.6 core).** Along a sequence
of growing experiments (`hN : N → ∞`) with uniformly bounded outcomes, positive and uniformly
bounded inverse marginal exposure propensities, positive off-diagonal joint exposure
propensities with uniformly bounded inverses, and a bounded-degree dependency graph whose nonedges
give the stated independence and covariance cancellations, the scaled variance of the conservative
variance estimator vanishes: `N²·Var[V̂_n] → 0`. -/
theorem var_NsqVhat_tendsto_zero_of_conditions
    (Exp : ℕ → Experiment) (dk dl : ∀ n, (Exp n).Δ) (hne : ∀ n, dk n ≠ dl n)
    {c₁ c₂ c₃ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hy : ∀ n i d, |(Exp n).y i d| ≤ c₁)
    (hπk : ∀ n i, 0 < prop (Exp n).D (Exp n).f (Exp n).θ i (dk n))
    (hπl : ∀ n i, 0 < prop (Exp n).D (Exp n).f (Exp n).θ i (dl n))
    (hπinvk : ∀ n i, 1 / prop (Exp n).D (Exp n).f (Exp n).θ i (dk n) ≤ c₂)
    (hπinvl : ∀ n i, 1 / prop (Exp n).D (Exp n).f (Exp n).θ i (dl n) ≤ c₂)
    (hjk : ∀ n i j, 1 / propPairSame (Exp n).D (Exp n).f (Exp n).θ i j (dk n) ≤ c₃)
    (hjl : ∀ n i j, 1 / propPairSame (Exp n).D (Exp n).f (Exp n).θ i j (dl n) ≤ c₃)
    (hjc : ∀ n i j, 1 / propPairCross (Exp n).D (Exp n).f (Exp n).θ i j (dk n) (dl n) ≤ c₃)
    (hjointk : ∀ n i j, i ≠ j →
      0 < propPairSame (Exp n).D (Exp n).f (Exp n).θ i j (dk n))
    (hjointl : ∀ n i j, i ≠ j →
      0 < propPairSame (Exp n).D (Exp n).f (Exp n).θ i j (dl n))
    (hjointc : ∀ n i j, i ≠ j →
      0 < propPairCross (Exp n).D (Exp n).f (Exp n).θ i j (dk n) (dl n))
    (G : ∀ n, (Exp n).ι → (Exp n).ι → Prop) (decG : ∀ n, DecidableRel (G n))
    (hrefl : ∀ n i, G n i i) (hsymm : ∀ n i j, G n i j → G n j i)
    {m : ℕ} (hdeg : ∀ n i, (Finset.univ.filter (fun j => G n i j)).card ≤ m)
    (hGindep : ∀ n i j, ¬ G n i j →
        propPairSame (Exp n).D (Exp n).f (Exp n).θ i j (dk n)
            = prop (Exp n).D (Exp n).f (Exp n).θ i (dk n)
              * prop (Exp n).D (Exp n).f (Exp n).θ j (dk n) ∧
        propPairSame (Exp n).D (Exp n).f (Exp n).θ i j (dl n)
            = prop (Exp n).D (Exp n).f (Exp n).θ i (dl n)
              * prop (Exp n).D (Exp n).f (Exp n).θ j (dl n) ∧
        propPairCross (Exp n).D (Exp n).f (Exp n).θ i j (dk n) (dl n)
            = prop (Exp n).D (Exp n).f (Exp n).θ i (dk n)
              * prop (Exp n).D (Exp n).f (Exp n).θ j (dl n))
    (hcov0 : ∀ n i j k l, ¬ (G n i k ∨ G n i l ∨ G n j k ∨ G n j l) →
        (Exp n).D.Cov (vb (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) i j)
          (vb (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) k l) = 0)
    (hN : Tendsto (fun n => (Fintype.card (Exp n).ι : ℝ)) atTop atTop) :
    Tendsto (fun n => (Fintype.card (Exp n).ι : ℝ) ^ 2 *
        (Exp n).D.Var (htEffectVarEst (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)))
      atTop (𝓝 0) := by
  set C : ℝ := 8 * vbBound c₁ c₂ c₃ ^ 2 * (m : ℝ) ^ 3 with hCdef
  refine squeeze_zero (g := fun n => C * (Fintype.card (Exp n).ι : ℝ)⁻¹)
    (fun n => ?_) (fun n => ?_) ?_
  · exact mul_nonneg (sq_nonneg _) (Var_nonneg _ _)
  · letI := decG n
    exact NsqVar_htEffectVarEst_le (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)
      (hne n) hc₁ hc₂ hc₃ (hy n) (hπk n) (hπl n) (hπinvk n) (hπinvl n)
      (hjk n) (hjl n) (hjc n) (G n) (hrefl n) (hsymm n) (hdeg n) (hGindep n) (hcov0 n)
  · have hinv : Tendsto (fun n => (Fintype.card (Exp n).ι : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hN
    have := tendsto_const_nhds (x := C) |>.mul hinv
    simpa using this

/-- **Feasible Wald coverage from primitive boundedness, overlap, dependency-graph, and
variance-growth conditions.** If outcomes are uniformly bounded, marginal propensities are
positive and uniformly bounded away from zero, off-diagonal joint propensities are positive with
bounded inverses, the exposure dependency graph supplies the required independence and covariance
cancellations, the Stein dependency-graph conditions hold, and population size times the true
effect-estimator variance converges to a positive constant, then the feasible Wald interval
`τ̂ ± z_{1−α/2}·√V̂` has asymptotic coverage at least `1 − α`. -/
theorem wald_coverage_feasible_of_conditions
    (Exp : ℕ → Experiment) (dk dl : ∀ n, (Exp n).Δ)
    {m : ℕ}
    (Dg : ∀ n, SteinMethod.DepGraph (fun i => (Exp n).effSummand (dk n) (dl n) i)
      (Exp n).D.toMeasure)
    (hSteinDeg : ∀ n i, ((Dg n).nbhd i).card ≤ m)
    (hne : ∀ n, dk n ≠ dl n)
    {c₁ c₂ c₃ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hc₂pos : 0 < c₂)
    (hy : ∀ n i d, |(Exp n).y i d| ≤ c₁)
    (hπk : ∀ n i, 0 < prop (Exp n).D (Exp n).f (Exp n).θ i (dk n))
    (hπl : ∀ n i, 0 < prop (Exp n).D (Exp n).f (Exp n).θ i (dl n))
    (hπinvk : ∀ n i, 1 / prop (Exp n).D (Exp n).f (Exp n).θ i (dk n) ≤ c₂)
    (hπinvl : ∀ n i, 1 / prop (Exp n).D (Exp n).f (Exp n).θ i (dl n) ≤ c₂)
    (hjk : ∀ n i j, 1 / propPairSame (Exp n).D (Exp n).f (Exp n).θ i j (dk n) ≤ c₃)
    (hjl : ∀ n i j, 1 / propPairSame (Exp n).D (Exp n).f (Exp n).θ i j (dl n) ≤ c₃)
    (hjc : ∀ n i j, 1 / propPairCross (Exp n).D (Exp n).f (Exp n).θ i j (dk n) (dl n) ≤ c₃)
    (G : ∀ n, (Exp n).ι → (Exp n).ι → Prop) (decG : ∀ n, DecidableRel (G n))
    (hrefl : ∀ n i, G n i i) (hsymm : ∀ n i j, G n i j → G n j i)
    (hdeg : ∀ n i, (Finset.univ.filter (fun j => G n i j)).card ≤ m)
    (hGindep : ∀ n i j, ¬ G n i j →
        propPairSame (Exp n).D (Exp n).f (Exp n).θ i j (dk n)
            = prop (Exp n).D (Exp n).f (Exp n).θ i (dk n)
              * prop (Exp n).D (Exp n).f (Exp n).θ j (dk n) ∧
        propPairSame (Exp n).D (Exp n).f (Exp n).θ i j (dl n)
            = prop (Exp n).D (Exp n).f (Exp n).θ i (dl n)
              * prop (Exp n).D (Exp n).f (Exp n).θ j (dl n) ∧
        propPairCross (Exp n).D (Exp n).f (Exp n).θ i j (dk n) (dl n)
            = prop (Exp n).D (Exp n).f (Exp n).θ i (dk n)
              * prop (Exp n).D (Exp n).f (Exp n).θ j (dl n))
    (hcov0 : ∀ n i j k l, ¬ (G n i k ∨ G n i l ∨ G n j k ∨ G n j l) →
        (Exp n).D.Cov (vb (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) i j)
          (vb (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) k l) = 0)
    (hN : Tendsto (fun n => (Fintype.card (Exp n).ι : ℝ)) atTop atTop)
    (hjointk : ∀ n i j, i ≠ j →
      0 < propPairSame (Exp n).D (Exp n).f (Exp n).θ i j (dk n))
    (hjointl : ∀ n i j, i ≠ j →
      0 < propPairSame (Exp n).D (Exp n).f (Exp n).θ i j (dl n))
    (hjointc : ∀ n i j, i ≠ j →
      0 < propPairCross (Exp n).D (Exp n).f (Exp n).θ i j (dk n) (dl n))
    {cVar : ℝ} (hcVar : 0 < cVar)
    (hCond4 : Tendsto (fun n => (Fintype.card (Exp n).ι : ℝ)
        * (Exp n).D.Var (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)))
      atTop (𝓝 cVar))
    (hVar : ∀ n, 0 < (Exp n).D.Var
      (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)))
    {α : ℝ} (zq : ℝ) (hzq0 : 0 ≤ zq) (hzq : stdNormalCdf zq = 1 - α / 2) :
    1 - α ≤ Filter.liminf
      (fun n => (Exp n).D.Pr (fun z =>
        |htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) z
            - tauTrue (Exp n).y (dk n) (dl n)|
          ≤ zq * Real.sqrt
              (htEffectVarEst (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) z)))
      Filter.atTop := by
  have hclt : LocalDependenceCLT Exp dk dl :=
    localDependenceCLT_of_paper_conditions Exp dk dl Dg m hSteinDeg c₁
      (fun n i => hy n i (dk n)) (fun n i => hy n i (dl n)) c₂ hc₂pos
      (fun n i => by
        have hπinv := hπinvk n i
        rw [one_div] at hπinv
        rw [one_div]
        exact (inv_le_comm₀ hc₂pos (hπk n i)).mpr hπinv)
      (fun n i => by
        have hπinv := hπinvl n i
        rw [one_div] at hπinv
        rw [one_div]
        exact (inv_le_comm₀ hc₂pos (hπl n i)).mpr hπinv)
      hN hVar cVar hcVar hCond4
  have hVN := var_NsqVhat_tendsto_zero_of_conditions Exp dk dl hne hc₁ hc₂ hc₃ hy hπk hπl
    hπinvk hπinvl hjk hjl hjc hjointk hjointl hjointc G decG hrefl hsymm hdeg hGindep hcov0 hN
  have hrel := relVar_of_NsqVar_tendsto Exp dk dl hcVar hCond4 hVN
  exact wald_coverage_feasible_of_relVar Exp dk dl hclt hne
    (fun n i => (hπk n i).ne') (fun n i => (hπl n i).ne')
    (fun n i j hij => (hjointk n i j hij).ne')
    (fun n i j hij => (hjointl n i j hij).ne')
    (fun n i j hij => (hjointc n i j hij).ne') hVar hrel
    zq hzq0 hzq

end ExposureMappingInterference
end Experimentation
end Causalean
