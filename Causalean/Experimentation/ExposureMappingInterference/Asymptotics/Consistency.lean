/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.DesignBased.HT.Variance
import Causalean.Experimentation.DesignBased.HT.Unbiased
import Causalean.Experimentation.DesignBased.Chebyshev
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Consistency of the Horvitz–Thompson effect estimator (Aronow–Samii 2017, Prop 6.4)

Along a sequence of nested finite-population experiments, the HT mean (hence effect)
estimator converges in probability to its estimand under two conditions:

* **Condition 1 (boundedness):** outcomes and inverse exposure probabilities are bounded,
  so each weighted summand `y_i(d)/π_i(d)` is bounded by a constant `c`.
* **Condition 2 (pairwise dependence):** `∑_{i,j} g_{ij} = o(N²)`, where `g_{ij}=0`
  whenever the exposure indicators of `i` and `j` are uncorrelated.

The proof is the lightweight-layer Chebyshev inequality applied to the `O((N+∑g)/N²)`
variance bound; no central limit theorem is needed.
-/


open scoped BigOperators Topology Classical
open Finset Filter

namespace Causalean
namespace Experimentation
namespace ExposureMappingInterference

open Causalean.Experimentation.DesignBased

/-- A design-based experiment on a finite population. -/
structure Experiment where
  /-- Finite assignment space. -/
  Ω : Type
  [fintypeΩ : Fintype Ω]
  /-- Finite population of units. -/
  ι : Type
  [fintypeι : Fintype ι]
  [decι : DecidableEq ι]
  /-- Unit-trait space. -/
  Θ : Type
  /-- Exposure space. -/
  Δ : Type
  [decΔ : DecidableEq Δ]
  /-- Randomization design. -/
  D : FiniteDesign Ω
  /-- Exposure-indexed potential outcomes. -/
  y : ι → Δ → ℝ
  /-- Exposure mapping. -/
  f : Ω → Θ → Δ
  /-- Unit traits. -/
  θ : ι → Θ

attribute [instance] Experiment.fintypeΩ Experiment.fintypeι Experiment.decι Experiment.decΔ

namespace Experiment

variable (E : Experiment)

/-- Pairwise dependency indicator: `0` when the exposure indicators of `i` and `j` for
exposure `d` are uncorrelated, `1` otherwise. -/
noncomputable def gdep (d : E.Δ) (i j : E.ι) : ℝ := by
  classical
  exact if E.D.Cov (expoInd E.f E.θ i d) (expoInd E.f E.θ j d) = 0 then 0 else 1

/-- Population size. -/
def N : ℕ := Fintype.card E.ι

/-- Covariance of two `[0,1]`-valued random variables is bounded by `1` in absolute value. -/
private lemma abs_Cov_le_one_of_mem_unit {Ω : Type*} [Fintype Ω] (D : FiniteDesign Ω)
    (X Y : Ω → ℝ) (hX0 : ∀ z, 0 ≤ X z) (hX1 : ∀ z, X z ≤ 1)
    (hY0 : ∀ z, 0 ≤ Y z) (hY1 : ∀ z, Y z ≤ 1) :
    |D.Cov X Y| ≤ 1 := by
  rw [FiniteDesign.Cov_eq]
  have ha0 : 0 ≤ D.E (fun z => X z * Y z) :=
    D.E_nonneg (fun z => mul_nonneg (hX0 z) (hY0 z))
  have ha1 : D.E (fun z => X z * Y z) ≤ 1 :=
    D.E_le_one (fun z => by nlinarith [hX0 z, hX1 z, hY0 z, hY1 z])
  have hb0 : 0 ≤ D.E X := D.E_nonneg hX0
  have hb1 : D.E X ≤ 1 := D.E_le_one hX1
  have he0 : 0 ≤ D.E Y := D.E_nonneg hY0
  have he1 : D.E Y ≤ 1 := D.E_le_one hY1
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hb0 he0, mul_le_one₀ hb1 he0 he1]

/-- **Variance bound.** Under a uniform bound `c` on `|y_i(d)/π_i(d)|`, the variance of the
HT mean estimator is `O((N + ∑_{i,j} g_{ij})/N²)`. -/
theorem Var_htMean_le (d : E.Δ) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ i, |E.y i d / prop E.D E.f E.θ i d| ≤ c) :
    E.D.Var (htMean E.D E.y E.f E.θ d)
      ≤ c ^ 2 * ((E.N : ℝ) + ∑ i, ∑ j ∈ Finset.univ.erase i, E.gdep d i j) / (E.N : ℝ) ^ 2 := by
  classical
  -- Abbreviations.
  set w : E.ι → ℝ := fun i => E.y i d / prop E.D E.f E.θ i d with hw
  set Cov : E.ι → E.ι → ℝ :=
    fun i j => E.D.Cov (expoInd E.f E.θ i d) (expoInd E.f E.θ j d) with hCov
  -- Covariance bound: `|Cov i j| ≤ 1` for all `i, j`.
  have hCovBound : ∀ i j, |Cov i j| ≤ 1 := by
    intro i j
    exact abs_Cov_le_one_of_mem_unit E.D _ _
      (fun z => FiniteDesign.ind_nonneg _ z) (fun z => FiniteDesign.ind_le_one _ z)
      (fun z => FiniteDesign.ind_nonneg _ z) (fun z => FiniteDesign.ind_le_one _ z)
  -- Termwise bound: `|w i * w j * Cov i j| ≤ c ^ 2`.
  have hTerm : ∀ i j, |w i * w j * Cov i j| ≤ c ^ 2 := by
    intro i j
    rw [abs_mul, abs_mul]
    have h1 : |w i| * |w j| ≤ c * c :=
      mul_le_mul (hbound i) (hbound j) (abs_nonneg _) hc
    calc |w i| * |w j| * |Cov i j|
        ≤ (c * c) * 1 :=
          mul_le_mul h1 (hCovBound i j) (abs_nonneg _) (by positivity)
      _ = c ^ 2 := by ring
  -- Off-diagonal termwise bound: `w i * w j * Cov i j ≤ c ^ 2 * gdep d i j`.
  have hOff : ∀ i, ∀ j ∈ Finset.univ.erase i,
      w i * w j * Cov i j ≤ c ^ 2 * E.gdep d i j := by
    intro i j _
    unfold Experiment.gdep
    by_cases hz : E.D.Cov (expoInd E.f E.θ i d) (expoInd E.f E.θ j d) = 0
    · rw [if_pos hz, mul_zero]
      have : Cov i j = 0 := hz
      rw [this, mul_zero]
    · rw [if_neg hz, mul_one]
      exact le_trans (le_abs_self _) (hTerm i j)
  -- Diagonal termwise bound: `w i * w i * Cov i i ≤ c ^ 2`.
  have hDiag : ∀ i, w i * w i * Cov i i ≤ c ^ 2 :=
    fun i => le_trans (le_abs_self _) (hTerm i i)
  -- Bound `Var (htTotal) ≤ c ^ 2 * (N + S)`.
  set S : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i, E.gdep d i j with hS
  have hTotal : E.D.Var (htTotal E.D E.y E.f E.θ d) ≤ c ^ 2 * ((E.N : ℝ) + S) := by
    rw [Var_htTotal_cov]
    -- Split each inner sum into the diagonal `j = i` plus the `erase i` remainder.
    have hsplit : (∑ i, ∑ j, w i * w j * Cov i j)
        = (∑ i, w i * w i * Cov i i)
          + ∑ i, ∑ j ∈ Finset.univ.erase i, w i * w j * Cov i j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.add_sum_erase Finset.univ (fun j => w i * w j * Cov i j)
        (Finset.mem_univ i)]
    rw [hsplit]
    have hDiagSum : (∑ i, w i * w i * Cov i i) ≤ c ^ 2 * (E.N : ℝ) := by
      calc (∑ i, w i * w i * Cov i i)
          ≤ ∑ _i : E.ι, c ^ 2 := Finset.sum_le_sum (fun i _ => hDiag i)
        _ = c ^ 2 * (E.N : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, Experiment.N, Finset.card_univ, mul_comm]
    have hOffSum : (∑ i, ∑ j ∈ Finset.univ.erase i, w i * w j * Cov i j) ≤ c ^ 2 * S := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun j hj => hOff i j hj)
    rw [mul_add]
    exact add_le_add hDiagSum hOffSum
  -- Reduce the HT mean variance to the HT total variance.
  have hmean : htMean E.D E.y E.f E.θ d
      = fun z => (Fintype.card E.ι : ℝ)⁻¹ * htTotal E.D E.y E.f E.θ d z := by
    funext z; rw [htMean, div_eq_inv_mul]
  rw [hmean, FiniteDesign.Var_const_mul]
  -- Now: `(card)⁻¹ ^ 2 * Var(htTotal) ≤ c ^ 2 * (N + S) / N ^ 2`.
  have hNdef : (E.N : ℝ) = (Fintype.card E.ι : ℝ) := by rw [Experiment.N]
  rw [hNdef]
  by_cases hN0 : (Fintype.card E.ι : ℝ) = 0
  · rw [hN0]; simp
  · have hpos2 : (0 : ℝ) ≤ ((Fintype.card E.ι : ℝ)⁻¹) ^ 2 := by positivity
    have hVarNonneg := mul_le_mul_of_nonneg_left hTotal hpos2
    refine le_trans hVarNonneg ?_
    rw [hNdef] at hTotal ⊢
    -- `(card)⁻² * (c²(N+S)) = c²(N+S)/N²`.
    rw [div_eq_mul_inv, inv_pow]
    ring_nf
    rfl

end Experiment

/-- **Chebyshev consistency.** If the variance of the HT mean estimator tends to `0` along a
sequence of experiments (with positive exposure probabilities throughout), then the estimator
is consistent: `Pr[|μ̂ − μ| ≥ ε] → 0`. -/
theorem htMean_consistent_of_var (Exp : ℕ → Experiment) (d : ∀ n, (Exp n).Δ)
    (hpos : ∀ n i, prop (Exp n).D (Exp n).f (Exp n).θ i (d n) ≠ 0)
    (hvar : Tendsto (fun n => (Exp n).D.Var (htMean (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (d n)))
      atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (Exp n).D.Pr
        (fun z => ε ≤ |htMean (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (d n) z
            - muTrue (Exp n).y (d n)|))
      atTop (𝓝 (0 : ℝ)) := by
  have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
  -- Upper bound: `Var_n / ε²`, which tends to `0` by Chebyshev + `hvar`.
  refine squeeze_zero (g := fun n =>
      (Exp n).D.Var (htMean (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (d n)) / ε ^ 2)
      (fun n => ?_) (fun n => ?_) ?_
  · -- `0 ≤ Pr_n`: a sum of nonnegative terms.
    unfold FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind
    refine Finset.sum_nonneg (fun z _ => ?_)
    exact mul_nonneg ((Exp n).D.p_nonneg z) (by positivity)
  · -- `Pr_n ≤ Var_n / ε²` by Chebyshev, using unbiasedness to recenter.
    have hcenter : muTrue (Exp n).y (d n)
        = (Exp n).D.E (htMean (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (d n)) :=
      (E_htMean (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (d n) (hpos n)).symm
    rw [hcenter]
    exact (Exp n).D.chebyshev (htMean (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (d n)) hε
  · -- `Var_n / ε² → 0 / ε² = 0`.
    have := hvar.div_const (ε ^ 2)
    simpa using this

end ExposureMappingInterference
end Experimentation
end Causalean
