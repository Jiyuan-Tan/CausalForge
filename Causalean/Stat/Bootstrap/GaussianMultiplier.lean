/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Gaussian multiplier (wild) bootstrap for the sample mean

The multiplier (wild) bootstrap (van der Vaart §23, Mammen) attaches i.i.d.
mean-zero multipliers `ξᵢ` to the *recentred* data `aᵢ = xᵢ − x̄ₙ` and studies
the perturbed statistic `∑ᵢ aᵢ ξᵢ`.  With **standard Gaussian** multipliers the
distribution of this statistic is, on a *fixed* data vector, **exactly** a
centred Gaussian — no CLT and no conditional-distribution machinery are needed,
because a linear combination of independent Gaussians is Gaussian with variances
adding.

* `map_weighted_sum_gaussian` — the core algebraic fact: for fixed weights
  `a : Fin n → ℝ` and an i.i.d. standard-Gaussian multiplier family `ξ`, the law
  of `ω ↦ ∑ i, a i * ξ i ω` is `gaussianReal 0 ⟨∑ i, (a i)², _⟩`.  Proved by
  `Finset` induction peeling one summand at a time: each `a i * ξ i` is Gaussian
  via `gaussianReal_map_const_mul`, and the independent sum's law is the
  convolution via `gaussianReal_add_gaussianReal_of_indepFun`.
* `multiplierBootstrap_law` — specialisation to the √n-scaled multiplier mean
  `Tₙ*(ω) = n^{-1/2} ∑ i, (xᵢ − x̄) ξᵢ`, whose law is exactly the centred
  Gaussian with variance the fixed sample variance `sₙ² = (1/n) ∑ (xᵢ − x̄)²`.

This is the *distributional* analogue of the bootstrap-standard-error route in
`Stat/Bootstrap/Variance.lean` / `CI.lean`: there the bootstrap is used only
through a consistent SE; here the multiplier construction delivers the exact
sampling law of the bootstrap statistic on the conditioned sample.
-/

import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Gaussian Multiplier Bootstrap

This file proves the exact Gaussian law of multiplier-bootstrap weighted sums with
standard Gaussian multipliers. It specializes that law to the recentered sample mean,
where the fixed-data variance is the empirical variance of the recentered sample.

The core theorem `map_weighted_sum_gaussian` says that a fixed linear
combination of independent standard Gaussian multipliers is Gaussian with
variance equal to the sum of squared weights. The specialization
`multiplierBootstrap_law` applies this to
`n^{-1/2} Σ_i (x_i - xbar) ξ_i`, giving the exact centered Gaussian law with
the empirical recentered variance. -/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Core multiplier lemma.**  Let `ξ : Fin n → Ω → ℝ` be a mutually
independent family of measurable random variables, each with law
`gaussianReal 0 1` (standard Gaussian).  Then for any fixed weights
`a : Fin n → ℝ`, the weighted sum `ω ↦ ∑ i, a i * ξ i ω` has law

    gaussianReal 0 ⟨∑ i, (a i)², _⟩,

i.e. it is exactly a centred Gaussian whose variance is the sum of the squared
weights.  No CLT — a linear combination of independent Gaussians is Gaussian.

The proof peels one summand at a time over a `Finset`: each `a i * ξ i` is
Gaussian with variance `(a i)²` (`gaussianReal_map_const_mul`), and the partial
sum is independent of the new term
(`iIndepFun.indepFun_finset_sum_of_notMem`), so their laws convolve to a
Gaussian with variances adding (`gaussianReal_add_gaussianReal_of_indepFun`). -/
theorem map_weighted_sum_gaussian {n : ℕ} (ξ : Fin n → Ω → ℝ)
    (hindep : iIndepFun ξ μ) (hmeas : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, μ.map (ξ i) = gaussianReal 0 1) (a : Fin n → ℝ) :
    μ.map (fun ω => ∑ i, a i * ξ i ω)
      = gaussianReal 0 ⟨∑ i, (a i) ^ 2, by positivity⟩ := by
  -- The summands `g i ω = a i * ξ i ω`.
  set g : Fin n → Ω → ℝ := fun i ω => a i * ξ i ω with hg
  -- Each summand is measurable, independent, and Gaussian with variance `(a i)²`.
  have hg_meas : ∀ i, Measurable (g i) := fun i => (hmeas i).const_mul (a i)
  have hg_indep : iIndepFun g μ := by
    have : g = fun i => (fun x => a i * x) ∘ ξ i := by
      funext i ω; simp [hg, Function.comp]
    rw [this]
    exact hindep.comp _ (fun i => measurable_const_mul (a i))
  have hg_law : ∀ i, μ.map (g i) = gaussianReal 0 ⟨(a i) ^ 2, sq_nonneg _⟩ := by
    intro i
    have hgi : g i = (fun x => a i * x) ∘ ξ i := rfl
    have hmap : μ.map (g i) = (gaussianReal 0 1).map (fun x => a i * x) := by
      rw [hgi, ← Measure.map_map (measurable_const_mul (a i)) (hmeas i), hlaw i]
    rw [hmap, gaussianReal_map_const_mul (a i)]
    congr 1
    · ring
    · ext; simp
  -- General `Finset`-indexed statement, then specialise to `Finset.univ`.
  have key : ∀ s : Finset (Fin n),
      μ.map (fun ω => ∑ i ∈ s, g i ω)
        = gaussianReal 0 ⟨∑ i ∈ s, (a i) ^ 2, by positivity⟩ := by
    intro s
    induction s using Finset.induction with
    | empty =>
        simp only [Finset.sum_empty]
        rw [Measure.map_const]
        simp only [measure_univ, one_smul]
        rw [show (⟨(0 : ℝ), by positivity⟩ : NNReal) = 0 from rfl]
        exact (gaussianReal_zero_var 0).symm
    | insert j s hj ih =>
        -- Split off the `j`-th summand: rewrite as the Pi-sum `(partial sum) + g j`.
        have hsum : (fun ω => ∑ i ∈ insert j s, g i ω)
            = (fun ω => ∑ i ∈ s, g i ω) + g j := by
          funext ω; rw [Finset.sum_insert hj]; simp [Pi.add_apply]; ring
        rw [hsum]
        -- Independence of the partial sum and the new term.
        have hindepFun : IndepFun (fun ω => ∑ i ∈ s, g i ω) (g j) μ := by
          have h := hg_indep.indepFun_finset_sum_of_notMem hg_meas (s := s) (i := j) hj
          have heq : (∑ i ∈ s, g i) = (fun ω => ∑ i ∈ s, g i ω) := by
            funext ω; simp [Finset.sum_apply]
          rwa [heq] at h
        -- Convolution of the two Gaussian laws.
        have hconv :=
          gaussianReal_add_gaussianReal_of_indepFun hindepFun ih (hg_law j)
        rw [hconv]
        congr 1
        · simp
        · ext
          simp only [NNReal.coe_add, NNReal.coe_mk]
          rw [Finset.sum_insert hj]
          ring
  have := key Finset.univ
  simpa using this

/-- **Exact law of the √n-scaled multiplier-bootstrap mean.** Fix data
`x : Fin n → ℝ` with sample mean `x̄ = n⁻¹ ∑ i, x i`, and let `ξ` be an i.i.d.
standard-Gaussian multiplier family. The scaled bootstrap statistic

    Tₙ*(ω) = n^{-1/2} ∑ i, (x i − x̄) · ξ i ω

has law exactly `gaussianReal 0 sₙ²`, where the variance argument is the fixed
sample variance `sₙ² = (1/n) ∑ i, (x i − x̄)²` (packaged as a nonnegative real).
Immediate from `map_weighted_sum_gaussian` with weights
`aᵢ = n^{-1/2} (xᵢ − x̄)`, using `∑ aᵢ² = n⁻¹ ∑ (xᵢ − x̄)² = sₙ²`. -/
theorem multiplierBootstrap_law {n : ℕ} (ξ : Fin n → Ω → ℝ)
    (hindep : iIndepFun ξ μ) (hmeas : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, μ.map (ξ i) = gaussianReal 0 1) (x : Fin n → ℝ) :
    μ.map (fun ω =>
        (Real.sqrt n)⁻¹ * ∑ i, (x i - (n : ℝ)⁻¹ * ∑ j, x j) * ξ i ω)
      = gaussianReal 0
          ⟨(n : ℝ)⁻¹ * ∑ i, (x i - (n : ℝ)⁻¹ * ∑ j, x j) ^ 2,
            by positivity⟩ := by
  set xbar : ℝ := (n : ℝ)⁻¹ * ∑ j, x j with hxbar
  set a : Fin n → ℝ := fun i => (Real.sqrt n)⁻¹ * (x i - xbar) with ha
  -- Rewrite the statistic as `∑ i, a i * ξ i`.
  have hstat : (fun ω => (Real.sqrt n)⁻¹ * ∑ i, (x i - xbar) * ξ i ω)
      = (fun ω => ∑ i, a i * ξ i ω) := by
    funext ω
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [ha]; ring
  rw [hstat, map_weighted_sum_gaussian ξ hindep hmeas hlaw a]
  -- Match the variance: `∑ aᵢ² = n⁻¹ ∑ (xᵢ − x̄)²`.
  congr 1
  ext
  simp only [ha]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hsq : ((Real.sqrt n)⁻¹) ^ 2 = (n : ℝ)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (le_of_lt hnpos)]
    have hpt : ∀ i, ((Real.sqrt n)⁻¹ * (x i - xbar)) ^ 2
        = (n : ℝ)⁻¹ * (x i - xbar) ^ 2 := by
      intro i; rw [mul_pow, hsq]
    push_cast
    rw [Finset.sum_congr rfl (fun i _ => hpt i), ← Finset.mul_sum]

end Causalean.Stat
