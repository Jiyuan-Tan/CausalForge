/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Hudgens–Halloran (2008): stage-1 simple-random-sampling sample-mean variance

The variance of the mean of a simple random sample of `m` of `N` fixed numbers is `(1 − m/N)/m`
times their population variance — the finite-population correction.  This is the between-group
variance term in Hudgens & Halloran's two-stage variance decomposition (Theorems 4 and 6).  Concretely,
given a design `D₁` with a family of `{0,1}` selection indicators `U i` that pick out a simple
random sample of size `m` from the `N := card ι` groups (so each indicator has mean `m/N`, each
distinct pair has joint mean `m(m−1)/(N(N−1))`, and each indicator has the Bernoulli variance
`(m/N)(1−m/N)`), the sampling variance of the sample mean `(∑ᵢ Uᵢ·μᵢ)/m` of the group-level
quantities `μ i` equals `(1 − m/N)/m · Sμ²`, where `Sμ² = (∑ᵢ(μᵢ − μ̄)²)/(N−1)` is the population
sample variance of `μ` (with an `N−1` denominator).  The result is proved abstractly: the SRS
first- and second-order selection moments are taken as hypotheses, so the lemma is design-agnostic
and reusable.
-/

import Causalean.Experimentation.TwoStageInterference.Variance

/-! # Stage-one sampling variance

Simple-random-sampling selection contributes the finite-population between-group variance term.

This file defines `SmuVar`, the `N - 1` sample variance of group-level quantities, and proves
`Var_srs_mean`: under simple-random-sampling first- and second-order selection moments, the
variance of the selected group mean is `(1 - m/N) / m * SmuVar`.  The result is design-agnostic
and is used as the between-group term in the two-stage variance decompositions.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace TwoStageInterference

open DesignBased

section StageOne

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω₁ : Type*} [Fintype Ω₁]

/-- The population sample variance (Neyman `N−1` denominator) of the group-level quantities `μ`,
`Sμ² = (∑ᵢ(μᵢ − μ̄)²)/(N−1)`, where `N := card ι` and `μ̄ = (∑ μ)/N`. -/
noncomputable def SmuVar (μ : ι → ℝ) : ℝ :=
  (∑ i, (μ i - (∑ i, μ i) / (Fintype.card ι : ℝ)) ^ 2) / ((Fintype.card ι : ℝ) - 1)

variable (D₁ : FiniteDesign Ω₁) (U : ι → Ω₁ → ℝ) (μ : ι → ℝ) (m : ℝ)
variable (hmean : ∀ i, D₁.E (U i) = m / (Fintype.card ι : ℝ))
variable (hpair : ∀ i j, i ≠ j →
  D₁.E (fun s => U i s * U j s)
    = (m * (m - 1)) / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1)))
variable (hvar : ∀ i,
  D₁.Var (U i) = (m / (Fintype.card ι : ℝ)) * (1 - m / (Fintype.card ι : ℝ)))
variable (hm : m ≠ 0) (hN1 : ((Fintype.card ι : ℝ) - 1) ≠ 0) (hN : (Fintype.card ι : ℝ) ≠ 0)

include hmean hpair hvar hm hN1 hN in
set_option linter.unusedDecidableInType false in
/-- **Stage-1 / between-group SRS variance term** (Hudgens–Halloran 2008, the between-group term of
Theorems 4 and 6).  Under simple
random sampling of `m` of the `N := card ι` groups, with `{0,1}` selection indicators `U`
satisfying the SRS first- and second-order selection moments (`hmean`, `hpair`) and the Bernoulli
diagonal variance (`hvar`), the sampling variance of the sample mean `(∑ᵢ Uᵢ·μᵢ)/m` of the
group-level quantities `μ` equals `(1 − m/N)/m` times the population sample variance `SmuVar μ`. -/
theorem Var_srs_mean :
    D₁.Var (fun s => (∑ i, U i s * μ i) / m)
      = (1 - m / (Fintype.card ι : ℝ)) / m * SmuVar μ := by
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  -- Step 1: write the mean as `(1/m) · ∑ᵢ μᵢ · Uᵢ` and pull the constant out of the variance.
  have hmeanform : (fun s => (∑ i, U i s * μ i) / m)
      = (fun s => (1 / m) * (∑ i, μ i * U i s)) := by
    funext s
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_comm (μ i) (U i s)]; ring
  rw [hmeanform, FiniteDesign.Var_const_mul]
  -- Step 2: `Var(∑ μᵢ Uᵢ) = ∑ᵢ∑ⱼ μᵢμⱼ Cov(Uᵢ,Uⱼ)`.
  rw [FiniteDesign.Var_linear_comb]
  -- Step 3: the covariances are two-valued — `vd` on the diagonal, `vo` off it.
  set vd : ℝ := (m / N) * (1 - m / N) with hvd
  set vo : ℝ := (m * (m - 1)) / (N * (N - 1)) - (m / N) * (m / N) with hvo
  have hcov : ∀ i j, D₁.Cov (U i) (U j) = if i = j then vd else vo := by
    intro i j
    by_cases h : i = j
    · subst h; rw [if_pos rfl, hvd, FiniteDesign.Cov_self, hvar i]
    · rw [if_neg h, hvo, FiniteDesign.Cov_eq, hpair i j h, hmean i, hmean j]
  have hrw : ∀ i j, μ i * μ j * D₁.Cov (U i) (U j)
      = μ i * μ j * (if i = j then vd else vo) := fun i j => by rw [hcov i j]
  simp only [hrw]
  -- Step 4: collapse the double sum to `vo·(∑μ)² + (vd−vo)·∑μ²`.
  rw [sum_sum_ite_quadratic Finset.univ μ vd vo]
  -- Step 5: rewrite `∑μ² − (∑μ)²/N` as `∑(μ−μ̄)²` and finish by field algebra.
  unfold SmuVar
  rw [← hNdef]
  -- `∑ᵢ(μᵢ − μ̄)² = ∑μ² − (∑μ)²/N`, the population deviation-sum identity over `ι`.
  have hNne : N ≠ 0 := hN
  have hcardN : (∑ _i : ι, ((∑ i, μ i) / N) ^ 2) = (∑ i, μ i) ^ 2 / N := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hNdef]
    field_simp
  have hdev : (∑ i, (μ i - (∑ i, μ i) / N) ^ 2)
      = (∑ i, (μ i) ^ 2) - (∑ i, μ i) ^ 2 / N := by
    have hexp : ∀ i, (μ i - (∑ i, μ i) / N) ^ 2
        = (μ i) ^ 2 - 2 * ((∑ i, μ i) / N) * (μ i) + ((∑ i, μ i) / N) ^ 2 := fun i => by ring
    simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hcardN, ← Finset.mul_sum]
    field_simp
    ring
  rw [hdev, hvd, hvo]
  -- Pure field algebra over the raw moment sums; constant `(1−m/N)/m` verified symbolically.
  have hNsub : N - 1 ≠ 0 := hN1
  clear_value N
  field_simp [hm, hNne, hNsub]
  ring

end StageOne

end TwoStageInterference
end Experimentation
end Causalean
