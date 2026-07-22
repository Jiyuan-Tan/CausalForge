/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.DesignBased.Designs.CompleteRandomization
import Causalean.Experimentation.DesignBased.Estimators.DifferenceInMeans
import Mathlib.Tactic.NormNum

/-!
# Li & Ding (2017): finite-population moments of the simple-random-sampling mean

Worked application of the complete-randomization design to Li & Ding (2017), "General Forms of
Finite Population Central Limit Theorems with Applications to Causal Inference" (JASA).  Their
foundational object (Theorem 1, after Hájek 1960) is the average `ȳ_S = (1/n) ∑_{i∈S} y_i` of a
**simple random sample** `S` of size `n` drawn from a fixed finite population `Π_N = {y_1,…,y_N}` —
which is exactly the `completeRandomization` design on size-`n` subsets.  This file proves the two
exact finite-sample moments that the Hájek central limit theorem is stated about:

* the sample mean is **unbiased** for the population mean, `E[ȳ_S] = ȳ_N`; and
* its randomization variance is the classical sampling-without-replacement (Cochran) formula
  `Var(ȳ_S) = (1/n − 1/N)·v_N`, where `v_N = (1/(N−1)) ∑ (y_i − ȳ_N)²` is the finite-population
  variance.

The Hájek CLT itself — `(ȳ_S − ȳ_N)/√Var(ȳ_S) ⇝ N(0,1)` under the Lindeberg-type condition
`m_N/(v_N·min(n,N−n)) → 0`, where `m_N = maxᵢ (y_i − ȳ_N)²` — is the asymptotic result built on
these moments.  This module formalizes the finite-population moments and the maximal-deviation
quantity `popMaxSqDev`; it does not formalize the sequence-level convergence-in-distribution
statement.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace FinitePopulationMoments

open DesignBased

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The **finite-population mean** `ȳ_N = (1/N) ∑ y_i`. -/
noncomputable def popMean (y : U → ℝ) : ℝ := (∑ i, y i) / (Fintype.card U : ℝ)

/-- The **finite-population variance** `v_N = (1/(N−1)) ∑ (y_i − ȳ_N)²`. -/
noncomputable def popVar (y : U → ℝ) : ℝ :=
  (∑ i, (y i - popMean y) ^ 2) / ((Fintype.card U : ℝ) - 1)

/-- The **maximum squared deviation** `m_N = maxᵢ (y_i − ȳ_N)²` driving the Hájek CLT condition. -/
noncomputable def popMaxSqDev [Nonempty U] (y : U → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => (y i - popMean y) ^ 2)

/-- The **simple-random-sample mean** `ȳ_S = (1/n) ∑_{i∈S} y_i` of a size-`n` sample `S`. -/
noncomputable def sampleMean (n : ℕ) (y : U → ℝ) (S : {S : Finset U // S.card = n}) : ℝ :=
  (∑ i, (if i ∈ S.val then y i else 0)) / (n : ℝ)

/-- **Unbiasedness of the sample mean** (Li & Ding 2017, Thm 1 moments). The simple-random-sample
mean is unbiased for the population mean: each unit is sampled with probability `n/N`, which the
`1/n` weight averages to `1/N`. -/
theorem E_sampleMean (n : ℕ) (hn : n ≤ Fintype.card U) (hn0 : 0 < n) (y : U → ℝ) :
    (completeRandomization n hn).E (sampleMean n y) = popMean y :=
  -- `sampleMean n y` is definitionally the treated-arm mean of `y`, already proved unbiased.
  E_treatedMean n hn hn0 y

/-- **Variance of the sample mean** (Li & Ding 2017, Thm 1 / Cochran). The randomization variance of
the simple-random-sample mean is `(1/n − 1/N)·v_N`, the sampling-without-replacement variance. -/
theorem Var_sampleMean (n : ℕ) (hn : n ≤ Fintype.card U) (hn0 : 0 < n) (hN : 2 ≤ Fintype.card U)
    (y : U → ℝ) :
    (completeRandomization n hn).Var (sampleMean n y)
      = (1 / (n : ℝ) - 1 / (Fintype.card U : ℝ)) * popVar y := by
  classical
  set D := completeRandomization n hn with hDdef
  -- the per-unit sampling indicator `1(i ∈ S)`
  set I : U → ({S : Finset U // S.card = n}) → ℝ :=
    fun i => FiniteDesign.ind (fun S => i ∈ S.val) with hIdef
  have hNnat : 0 < Fintype.card U := lt_of_lt_of_le (by norm_num) hN
  have hNR : (Fintype.card U : ℝ) ≠ 0 := by exact_mod_cast hNnat.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hN1R : (Fintype.card U : ℝ) - 1 ≠ 0 := by
    have h1 : (1 : ℝ) < Fintype.card U := by exact_mod_cast hN
    exact sub_ne_zero.mpr h1.ne'
  -- first-order and second-order inclusion probabilities
  have hπ : ∀ i, D.Pr (fun S => i ∈ S.val) = (n : ℝ) / Fintype.card U := fun i =>
    completeRandomization_incl n hn i
  -- diagonal covariance: `Var(1ᵢ) = π(1−π)`
  have hdiag : ∀ i, D.Cov (I i) (I i)
      = (n : ℝ) / Fintype.card U * (1 - (n : ℝ) / Fintype.card U) := by
    intro i; rw [hIdef, FiniteDesign.Cov_self, FiniteDesign.Var_ind, hπ i]
  -- off-diagonal covariance: `Cov(1ᵢ,1ⱼ) = π_ij − π²`  (i ≠ j)
  have hoff : ∀ i j, i ≠ j → D.Cov (I i) (I j)
      = (n : ℝ) * ((n : ℝ) - 1) / (Fintype.card U * ((Fintype.card U : ℝ) - 1))
          - (n : ℝ) / Fintype.card U * ((n : ℝ) / Fintype.card U) := by
    intro i j hij
    rw [hIdef, FiniteDesign.Cov_eq]
    have hprod : (fun S : {S : Finset U // S.card = n} =>
          FiniteDesign.ind (fun S => i ∈ S.val) S * FiniteDesign.ind (fun S => j ∈ S.val) S)
        = FiniteDesign.ind (fun S : {S : Finset U // S.card = n} => i ∈ S.val ∧ j ∈ S.val) := by
      funext S; simp only [FiniteDesign.ind]
      by_cases hi : i ∈ S.val <;> by_cases hj : j ∈ S.val <;> simp [hi, hj]
    rw [hprod, FiniteDesign.E_ind, FiniteDesign.E_ind, FiniteDesign.E_ind,
      completeRandomization_incl_pair n hn hij, hπ i, hπ j]
  -- `sampleMean = (1/n) · ∑ᵢ yᵢ · 1ᵢ`
  have hsm : sampleMean n y = fun S => (1 / (n : ℝ)) * ∑ i, y i * I i S := by
    funext S
    have hterm : (∑ i, if i ∈ S.val then y i else 0) = ∑ i, y i * I i S := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hIdef]; simp only [FiniteDesign.ind]; by_cases h : i ∈ S.val <;> simp [h]
    change (∑ i, if i ∈ S.val then y i else 0) / (n : ℝ)
      = (1 / (n : ℝ)) * ∑ i, y i * I i S
    rw [hterm]; ring
  rw [hsm]
  rw [show (D.Var (fun S => 1 / (n : ℝ) * ∑ i, y i * I i S))
        = (1 / (n : ℝ)) ^ 2 * D.Var (fun S => ∑ i, y i * I i S)
      from D.Var_const_mul (1 / (n : ℝ)) (fun S => ∑ i, y i * I i S)]
  rw [D.Var_linear_comb Finset.univ y I]
  -- collapse the double sum using `Cov(1ᵢ,1ⱼ) = off + 1{i=j}(diag − off)`
  set off : ℝ := (n : ℝ) * ((n : ℝ) - 1) / (Fintype.card U * ((Fintype.card U : ℝ) - 1))
      - (n : ℝ) / Fintype.card U * ((n : ℝ) / Fintype.card U) with hoffdef
  set diag : ℝ := (n : ℝ) / Fintype.card U * (1 - (n : ℝ) / Fintype.card U) with hdiagdef
  have hcov : ∀ i j, y i * y j * D.Cov (I i) (I j)
      = y i * y j * off + (if i = j then y i * y j * (diag - off) else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij; rw [hdiag i, if_pos rfl]; ring
    · rw [hoff i j hij, if_neg hij]; ring
  simp_rw [hcov]
  -- collapse the double sum: `off·(∑y)² + (diag−off)·∑y²`
  have hsumsq : (∑ i, ∑ j, y i * y j) = (∑ i, y i) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  have hsplit :
      (∑ i, ∑ j, (y i * y j * off + if i = j then y i * y j * (diag - off) else 0))
        = off * (∑ i, y i) ^ 2 + (diag - off) * ∑ i, (y i) ^ 2 := by
    rw [show (∑ i, ∑ j, (y i * y j * off + if i = j then y i * y j * (diag - off) else 0))
          = (∑ i, ∑ j, y i * y j * off)
            + (∑ i, ∑ j, (if i = j then y i * y j * (diag - off) else 0)) from by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib]
    have hA : (∑ i, ∑ j, y i * y j * off) = off * (∑ i, y i) ^ 2 := by
      rw [← hsumsq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    have hB : (∑ i, ∑ j, (if i = j then y i * y j * (diag - off) else 0))
        = (diag - off) * ∑ i, (y i) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_ite_eq Finset.univ i (fun j => y i * y j * (diag - off))]
      simp only [Finset.mem_univ, if_true]; ring
    rw [hA, hB]
  rw [hsplit, hoffdef, hdiagdef, popVar, popMean]
  -- computational variance formula `∑(yᵢ−ȳ)² = ∑yᵢ² − (∑y)²/N`
  have hexp : (∑ i, (y i - (∑ k, y k) / (Fintype.card U : ℝ)) ^ 2)
      = (∑ i, (y i) ^ 2) - (∑ i, y i) ^ 2 / (Fintype.card U : ℝ) := by
    have hpt : ∀ i, (y i - (∑ k, y k) / (Fintype.card U : ℝ)) ^ 2
        = (y i) ^ 2 - 2 * ((∑ k, y k) / (Fintype.card U : ℝ)) * y i
          + ((∑ k, y k) / (Fintype.card U : ℝ)) ^ 2 := fun i => by ring
    simp_rw [hpt]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  rw [hexp]
  field_simp
  ring

end FinitePopulationMoments
end Experimentation
end Causalean
