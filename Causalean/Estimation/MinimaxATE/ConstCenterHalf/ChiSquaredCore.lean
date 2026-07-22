/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: the χ² indistinguishability core

This file discharges the one remaining hypothesis of `ExplicitWitness.lean`, the
total-variation bound `tvDist (Qfalse) (Qtrue) ≤ 1/2`, by the Ingster χ²
second-moment method, turning `explicit_minimax_lower_bound` into an
**unconditional** minimax lower bound.

The chain is:

* `one_add_chiSqDiv_Qtrue_Qfalse` — the **mixture second-moment identity**: on the
  finite product space, `1 + χ²(Qtrue‖Qfalse) = ∑_{λ,λ'} w² · overlap(λ,λ')ⁿ`, the
  weighted average over Rademacher sign pairs of the single-observation overlap
  raised to the sample size.  Proved from the finite χ² formula
  (`finite_one_add_chiSqDiv`), the product point mass (`pi_real_singleton`), and
  the combinatorial identity `Fintype.sum_pow`.
* `chiSqOverlap_eq` (sibling) gives the closed form `overlap = 1 + (2γ/K)Σ_j s_j s'_j`
  with `γ = α²+2αβ+3β²`, so the sum is exactly the LHS of `ingster_bound`.
* `ingster_bound` (sibling) bounds it by `2` in the regime `2n²γ² ≤ K·log 2`.

Hence `χ²(Qtrue‖Qfalse) ≤ 1`, so `tvDist ≤ ½√χ² ≤ 1/2`
(`tvDist_le_half_sqrt_chiSqDiv` + `tvDist_symm`), and
`minimax_lower_bound` concludes `1/4 ≤ minimaxMiss`.
-/

import Causalean.Estimation.MinimaxATE.ConstCenterHalf.ExplicitWitness
import Causalean.Estimation.MinimaxATE.ConstCenterHalf.ChiSqOverlap
import Causalean.Estimation.MinimaxATE.ConstCenterHalf.Ingster
import Causalean.Stat.Minimax.ChiSquaredFinite

/-! # Chi-Squared Core

This file proves the statistical indistinguishability bound for the baseline structure-agnostic
ATE construction. It first supplies finite-support facts such as
`absolutelyContinuous_of_singleton_pos`, `productLaw_real_singleton`, `Qfalse_singleton_ne_zero`,
and `Qtrue_real_singleton`.

The core identity `one_add_chiSqDiv_Qtrue_Qfalse` evaluates the mixture second moment. The
theorem `chiSqDiv_Qtrue_Qfalse_le_one` applies `ingster_bound`, and
`tvDist_Qfalse_Qtrue_le_half` converts that chi-squared bound into total-variation
indistinguishability. The final theorem `minimax_lower_bound` discharges the abstract
two-point witness and gives the unconditional finite-cell minimax lower bound. -/

namespace Causalean.Estimation.MinimaxATE

open MeasureTheory
open Causalean.Stat
open scoped ENNReal BigOperators

variable {K n : ℕ} {α β εg εm : ℝ}

/-- **Absolute continuity from full support.** If `ν` charges every singleton, every
measure is absolutely continuous w.r.t. `ν` (a `ν`-null set must be empty). -/
theorem absolutelyContinuous_of_singleton_pos {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) (hν : ∀ x, ν {x} ≠ 0) : μ ≪ ν := by
  intro s hs
  have hempty : s = ∅ := by
    by_contra hne
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
    exact hν x (le_antisymm (hs ▸ measure_mono (Set.singleton_subset_iff.mpr hx)) (zero_le _))
  rw [hempty]; exact measure_empty

/-- The `.real` product point mass of an `n`-sample DGP law factorizes over draws. -/
theorem productLaw_real_singleton [NeZero K] {m : Fin K × Bool → ℝ}
    {g : Bool → Fin K × Bool → ℝ} (hv : ValidDGP m g) (ω : Fin n → Obs (Fin K × Bool)) :
    (productLaw hv n).real {ω} = ∏ i, obsReal m g (ω i) := by
  rw [productLaw, pi_real_singleton]
  exact Finset.prod_congr rfl fun i _ => obsLaw_real_singleton hv (ω i)

/-- The null `n`-sample law charges every point (its mass is `(8K)⁻ⁿ > 0`). -/
theorem Qfalse_singleton_ne_zero [NeZero K] (ω : Fin n → Obs (Fin K × Bool)) :
    Qfalse K n {ω} ≠ 0 := by
  have hpos : 0 < (Qfalse K n).real {ω} := by
    rw [Qfalse, productLaw_real_singleton]
    apply Finset.prod_pos
    intro i _
    have hC : (0 : ℝ) < (Fintype.card (Fin K × Bool) : ℝ) := by
      have := Fintype.card_pos (α := Fin K × Bool)
      exact_mod_cast this
    simp only [obsReal, mhat, ghat]
    rcases (ω i).2.1 with _ | _ <;> rcases (ω i).2.2 with _ | _ <;>
      · simp only [Bool.false_eq_true, if_false, if_true]; positivity
  intro h
  rw [Measure.real, h, ENNReal.toReal_zero] at hpos
  exact lt_irrefl _ hpos

/-- The real-valued uniform sign weight `(2^K)⁻¹`. -/
theorem signWeight_toReal (lam : Fin K → Bool) :
    (signWeight K lam).toReal = ((2 : ℝ) ^ K)⁻¹ := by
  have hcard : (Fintype.card (Fin K → Bool) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ K := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; push_cast; ring
  rw [signWeight, hcard, ENNReal.toReal_inv, ENNReal.toReal_pow]
  norm_num

/-- The alternative law's `.real` point mass: a uniform mixture over sign vectors. -/
theorem Qtrue_real_singleton [NeZero K]
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + 2 * β ≤ 1 / 2)
    (ω : Fin n → Obs (Fin K × Bool)) :
    (Qtrue hα hβ hαβ n).real {ω}
      = ∑ lam : Fin K → Bool, ((2 : ℝ) ^ K)⁻¹
          * ∏ i, obsReal (mPerturbed β lam) (gPerturbed α β lam) (ω i) := by
  haveI : ∀ lam : Fin K → Bool, IsProbabilityMeasure (Qpert hα hβ hαβ n lam) :=
    fun lam => Qpert_isProb hα hβ hαβ n lam
  rw [Qtrue, Measure.real, mixture_apply]
  rw [ENNReal.toReal_sum (fun lam _ => ENNReal.mul_ne_top
    (by rw [signWeight]; exact ENNReal.inv_ne_top.2 (by simp)) (measure_ne_top _ _))]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [ENNReal.toReal_mul, signWeight_toReal]
  congr 1
  exact productLaw_real_singleton (validDGP_perturbed hα hβ hαβ lam) ω

/-- **Mixture second-moment identity.**  On the finite product space,
`1 + χ²(Qtrue‖Qfalse)` is the uniform average over Rademacher sign pairs of the
single-observation overlap raised to the sample size `n`. -/
theorem one_add_chiSqDiv_Qtrue_Qfalse [NeZero K]
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + 2 * β ≤ 1 / 2) :
    1 + chiSqDiv (Qtrue hα hβ hαβ n) (Qfalse K n)
      = ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
          ((2 : ℝ) ^ K)⁻¹ * ((2 : ℝ) ^ K)⁻¹ * (chiSqOverlap α β lam lam') ^ n := by
  haveI : IsProbabilityMeasure (Qtrue (K := K) hα hβ hαβ n) := Qtrue_isProb hα hβ hαβ n
  haveI : IsProbabilityMeasure (Qfalse K n) := Qfalse_isProb K n
  have hac : Qtrue (K := K) hα hβ hαβ n ≪ Qfalse K n :=
    absolutelyContinuous_of_singleton_pos _ _ Qfalse_singleton_ne_zero
  rw [finite_one_add_chiSqDiv (Qtrue hα hβ hαβ n) (Qfalse K n) hac]
  -- expand each summand
  have hstep : ∀ ω : Fin n → Obs (Fin K × Bool),
      ((Qtrue hα hβ hαβ n).real {ω}) ^ 2 / (Qfalse K n).real {ω}
        = ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
            ((2 : ℝ) ^ K)⁻¹ * ((2 : ℝ) ^ K)⁻¹
              * ∏ i, (obsReal (mPerturbed β lam) (gPerturbed α β lam) (ω i)
                    * obsReal (mPerturbed β lam') (gPerturbed α β lam') (ω i)
                    / obsReal mhat ghat (ω i)) := by
    intro ω
    rw [Qtrue_real_singleton hα hβ hαβ ω, Qfalse,
      productLaw_real_singleton (validDGP_hat (K := K)) ω, sq, Finset.sum_mul_sum]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun lam _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun lam' _ => ?_
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
    ring
  rw [Finset.sum_congr rfl fun ω _ => hstep ω]
  -- swap sums and apply Fintype.sum_pow
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun lam' _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  unfold chiSqOverlap
  rw [Fintype.sum_pow]

/-- **The χ² indistinguishability bound.**  In the regime `2n²γ² ≤ K·log 2` (with
`γ = α²+2αβ+3β²`, `2γ ≤ 1`), the χ²-divergence of the alternative mixture from the
null is at most `1`. -/
theorem chiSqDiv_Qtrue_Qfalse_le_one [NeZero K]
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + 2 * β ≤ 1 / 2)
    (hγ : 2 * (α ^ 2 + 2 * α * β + 3 * β ^ 2) ≤ 1)
    (hreg : 2 * (n : ℝ) ^ 2 * (α ^ 2 + 2 * α * β + 3 * β ^ 2) ^ 2 ≤ (K : ℝ) * Real.log 2) :
    chiSqDiv (Qtrue hα hβ hαβ n) (Qfalse K n) ≤ 1 := by
  have hγ0 : 0 ≤ α ^ 2 + 2 * α * β + 3 * β ^ 2 := by positivity
  have hid := one_add_chiSqDiv_Qtrue_Qfalse (K := K) (n := n) hα hβ hαβ
  -- rewrite overlap by its closed form
  have hov : ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
        ((2 : ℝ) ^ K)⁻¹ * ((2 : ℝ) ^ K)⁻¹ * (chiSqOverlap α β lam lam') ^ n
      = ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
        ((2 : ℝ) ^ K)⁻¹ * ((2 : ℝ) ^ K)⁻¹
          * (1 + (2 * (α ^ 2 + 2 * α * β + 3 * β ^ 2) / (K : ℝ))
              * ∑ j, signOf (lam j) * signOf (lam' j)) ^ n := by
    refine Finset.sum_congr rfl fun lam _ => ?_
    refine Finset.sum_congr rfl fun lam' _ => ?_
    rw [chiSqOverlap_eq hα hβ hαβ lam lam']
  have hbound := ingster_bound K n hγ0 hγ hreg
  rw [← hov] at hbound
  rw [← hid] at hbound
  linarith

/-- **Total-variation indistinguishability.**  In the same regime, the null and
alternative `n`-sample laws are statistically `1/2`-close in total variation —
discharging the hypothesis carried abstractly in `ExplicitWitness.lean`. -/
theorem tvDist_Qfalse_Qtrue_le_half [NeZero K]
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + 2 * β ≤ 1 / 2)
    (hγ : 2 * (α ^ 2 + 2 * α * β + 3 * β ^ 2) ≤ 1)
    (hreg : 2 * (n : ℝ) ^ 2 * (α ^ 2 + 2 * α * β + 3 * β ^ 2) ^ 2 ≤ (K : ℝ) * Real.log 2) :
    tvDist (Qfalse K n) (Qtrue hα hβ hαβ n) ≤ 1 / 2 := by
  haveI : IsProbabilityMeasure (Qtrue (K := K) hα hβ hαβ n) := Qtrue_isProb hα hβ hαβ n
  haveI : IsProbabilityMeasure (Qfalse K n) := Qfalse_isProb K n
  have hac : Qtrue (K := K) hα hβ hαβ n ≪ Qfalse K n :=
    absolutelyContinuous_of_singleton_pos _ _ Qfalse_singleton_ne_zero
  have hchi := chiSqDiv_Qtrue_Qfalse_le_one (K := K) (n := n) hα hβ hαβ hγ hreg
  rw [tvDist_symm]
  calc tvDist (Qtrue hα hβ hαβ n) (Qfalse K n)
      ≤ (1 / 2) * Real.sqrt (chiSqDiv (Qtrue hα hβ hαβ n) (Qfalse K n)) :=
        tvDist_le_half_sqrt_chiSqDiv _ _ hac (Integrable.of_finite)
    _ ≤ (1 / 2) * Real.sqrt 1 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.sqrt_le_sqrt hchi
    _ = 1 / 2 := by rw [Real.sqrt_one]; ring

/-- **Structure-agnostic minimax lower bound (unconditional).**  For the centered
estimates `(m̂, ĝ) = (1/2, 1/2)` on the paired-cell covariate `Fin K × Bool`, with
the Rademacher bump budgets met (`β² ≤ εm`, `(α+β)²/(1−2β)² ≤ εg`) and the
sample-size regime `2n²γ² ≤ K·log 2` (`γ = α²+2αβ+3β²`, `2γ ≤ 1`), **every**
measurable estimator misses the true ATE by `s = β(α+β)/(1−4β²)` with probability at
least `1/4` somewhere in the class.  The doubly-robust product rate is unbeatable. -/
theorem minimax_lower_bound [NeZero K]
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + 2 * β ≤ 1 / 2)
    (hm : β ^ 2 ≤ εm) (hg : (α + β) ^ 2 / (1 - 2 * β) ^ 2 ≤ εg)
    (hεg : 0 ≤ εg) (hεm : 0 ≤ εm)
    (hγ : 2 * (α ^ 2 + 2 * α * β + 3 * β ^ 2) ≤ 1)
    (hreg : 2 * (n : ℝ) ^ 2 * (α ^ 2 + 2 * α * β + 3 * β ^ 2) ^ 2 ≤ (K : ℝ) * Real.log 2)
    {est : (Fin n → Obs (Fin K × Bool)) → ℝ} (hest : Measurable est) :
    1 / 4 ≤ minimaxMiss mhat ghat εg εm n est (β * (α + β) / (1 - 4 * β ^ 2)) :=
  explicit_minimax_lower_bound hα hβ hαβ hm hg hεg hεm
    (tvDist_Qfalse_Qtrue_le_half hα hβ hαβ hγ hreg) hest

end Causalean.Estimation.MinimaxATE
