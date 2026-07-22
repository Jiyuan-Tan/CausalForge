/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Sample
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Probability.Moments.Basic

/-! # Multiplicative tails for Bernoulli counts

This file gives the two one-sided multiplicative Chernoff estimates used for
pilot-sample counts.  The interface is an `IIDSample` together with a
measurable `{0,1}`-valued statistic, whose population integral is the Bernoulli
mean.  `bernoulliCount_measurable` records measurability of the sample count,
while `bernoulliCount_upper_tail` and `bernoulliCount_lower_tail` bound the
probability that the count exceeds, respectively falls below, a multiplicative
deviation from its mean.
-/

namespace Causalean.Stat.Concentration

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
  {μ : Measure Ω} {P : Measure 𝒳}

/-- The number of the first `m` observations on which `f` is one. -/
noncomputable def bernoulliCount
    (S : Causalean.Stat.IIDSample Ω 𝒳 μ P) (f : 𝒳 → ℝ) (m : ℕ) : Ω → ℝ :=
  fun ω ↦ ∑ i ∈ Finset.range m, f (S.Z i ω)

lemma bernoulliCount_measurable
    (S : Causalean.Stat.IIDSample Ω 𝒳 μ P) {f : 𝒳 → ℝ}
    (hf : Measurable f) (m : ℕ) : Measurable (bernoulliCount S f m) := by
  unfold bernoulliCount
  exact Finset.measurable_fun_sum _ fun i _ ↦ hf.comp (S.meas i)

private lemma bernoulli_mgf
    [IsProbabilityMeasure P] {f : 𝒳 → ℝ} (hf : Measurable f)
    (h01 : ∀ x, f x = 0 ∨ f x = 1) (p s : ℝ)
    (hmean : ∫ x, f x ∂P = p) :
    mgf f P s = 1 + p * (exp s - 1) := by
  have hf_int : Integrable f P := by
    refine Integrable.of_bound hf.aestronglyMeasurable 1 (ae_of_all _ fun x ↦ ?_)
    rcases h01 x with hx | hx <;> simp [hx]
  rw [mgf]
  calc
    (∫ x, exp (s * f x) ∂P) = ∫ x, (1 + f x * (exp s - 1)) ∂P := by
      refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
      rcases h01 x with hx | hx
      · simp [hx]
      · simp [hx]
    _ = 1 + p * (exp s - 1) := by
      rw [integral_add (integrable_const 1) (hf_int.mul_const _), integral_const,
        integral_mul_const, hmean]
      simp

private lemma bernoulliCount_mgf_le
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (S : Causalean.Stat.IIDSample Ω 𝒳 μ P) {f : 𝒳 → ℝ}
    (hf : Measurable f) (h01 : ∀ x, f x = 0 ∨ f x = 1)
    {p : ℝ} (hmean : ∫ x, f x ∂P = p) (m : ℕ) (s : ℝ) :
    mgf (bernoulliCount S f m) μ s ≤ exp ((m : ℝ) * (p * (exp s - 1))) := by
  let X : ℕ → Ω → ℝ := fun i ↦ f ∘ S.Z i
  have hX_meas : ∀ i, Measurable (X i) := fun i ↦ hf.comp (S.meas i)
  have hX_indep : iIndepFun X μ := S.indep.comp (fun _ ↦ f) (fun _ ↦ hf)
  have hmgf_one : ∀ i, mgf (X i) μ s = 1 + p * (exp s - 1) := by
    intro i
    rw [← mgf_map (S.meas i).aemeasurable (by fun_prop), S.map_eq]
    exact bernoulli_mgf hf h01 p s hmean
  have hsum : bernoulliCount S f m = ∑ i ∈ Finset.range m, X i := by
    ext ω
    simp [bernoulliCount, X, Function.comp_apply]
  rw [hsum, hX_indep.mgf_sum hX_meas]
  simp_rw [hmgf_one]
  rw [Finset.prod_const, Finset.card_range]
  calc
    (1 + p * (exp s - 1)) ^ m
        ≤ (exp (p * (exp s - 1))) ^ m := by
      apply pow_le_pow_left₀
      · rw [← bernoulli_mgf hf h01 p s hmean]
        exact mgf_nonneg
      · simpa [add_comm] using Real.add_one_le_exp (p * (exp s - 1))
    _ = exp ((m : ℝ) * (p * (exp s - 1))) := by
      rw [← Real.exp_nat_mul]

/-- Upper multiplicative tail for an i.i.d. Bernoulli count.  If its mean
`m * p` is below half the threshold `a`, then the probability of exceeding
`a` is at most `exp (-a * (log 2 - 1/2))`. -/
theorem bernoulliCount_upper_tail
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (S : Causalean.Stat.IIDSample Ω 𝒳 μ P) {f : 𝒳 → ℝ}
    (hf : Measurable f) (h01 : ∀ x, f x = 0 ∨ f x = 1)
    {p a : ℝ} (hmean : ∫ x, f x ∂P = p)
    {m : ℕ} (hmean_lt : (m : ℝ) * p < a / 2) :
    μ.real {ω | a < bernoulliCount S f m ω}
      ≤ exp (-a * (log 2 - 1 / 2)) := by
  have hlog : 0 ≤ log (2 : ℝ) := (log_pos (by norm_num)).le
  have hint : Integrable (fun ω ↦ exp (log 2 * bernoulliCount S f m ω)) μ := by
    refine Integrable.of_bound
      ((bernoulliCount_measurable S hf m).const_mul _ |>.exp.aestronglyMeasurable)
      (exp (log 2 * m)) (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    have hcount_le : bernoulliCount S f m ω ≤ m := by
      simp only [bernoulliCount]
      calc
        (∑ i ∈ Finset.range m, f (S.Z i ω)) ≤ ∑ _i ∈ Finset.range m, (1 : ℝ) := by
          gcongr with i hi
          rcases h01 (S.Z i ω) with h | h <;> simp [h]
        _ = m := by simp
    exact mul_le_mul_of_nonneg_left hcount_le hlog
  calc
    μ.real {ω | a < bernoulliCount S f m ω}
        ≤ μ.real {ω | a ≤ bernoulliCount S f m ω} :=
      measureReal_mono (by
        intro ω hω
        change a < bernoulliCount S f m ω at hω
        change a ≤ bernoulliCount S f m ω
        exact hω.le)
    _ ≤ exp (-log 2 * a) * mgf (bernoulliCount S f m) μ (log 2) :=
      measure_ge_le_exp_mul_mgf a hlog hint
    _ ≤ exp (-log 2 * a) * exp ((m : ℝ) * p) := by
      have hm := bernoulliCount_mgf_le S hf h01 hmean m (log 2)
      rw [exp_log (by norm_num : (0 : ℝ) < 2)] at hm
      have heq : (m : ℝ) * (p * ((2 : ℝ) - 1)) = (m : ℝ) * p := by ring
      rw [heq] at hm
      have hm' : mgf (bernoulliCount S f m) μ (log 2) ≤ exp ((m : ℝ) * p) := by
        exact hm
      exact mul_le_mul_of_nonneg_left hm' (exp_pos _).le
    _ ≤ exp (-a * (log 2 - 1 / 2)) := by
      rw [← exp_add]
      apply exp_le_exp.mpr
      nlinarith

/-- Lower multiplicative tail for an i.i.d. Bernoulli count.  If its mean
`m * p` is more than twice the threshold `a`, then the probability of being
at most `a` is at most `exp (-(m*p)/8)`. -/
theorem bernoulliCount_lower_tail
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (S : Causalean.Stat.IIDSample Ω 𝒳 μ P) {f : 𝒳 → ℝ}
    (hf : Measurable f) (h01 : ∀ x, f x = 0 ∨ f x = 1)
    {p a : ℝ} (hp : 0 ≤ p) (hmean : ∫ x, f x ∂P = p)
    {m : ℕ} (hmean_gt : 2 * a < (m : ℝ) * p) :
    μ.real {ω | bernoulliCount S f m ω ≤ a}
      ≤ exp (-((m : ℝ) * p) / 8) := by
  have hlog : -log (2 : ℝ) ≤ 0 := neg_nonpos.mpr (log_pos (by norm_num)).le
  have hint : Integrable (fun ω ↦ exp (-log 2 * bernoulliCount S f m ω)) μ := by
    refine Integrable.of_bound
      ((bernoulliCount_measurable S hf m).const_mul _ |>.exp.aestronglyMeasurable)
      1 (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    calc
      exp (-log 2 * bernoulliCount S f m ω) ≤ exp 0 := by
        apply exp_le_exp.mpr
        have hcount_nonneg : 0 ≤ bernoulliCount S f m ω := by
          apply Finset.sum_nonneg
          intro i hi
          rcases h01 (S.Z i ω) with h | h <;> simp [h]
        exact mul_nonpos_of_nonpos_of_nonneg hlog hcount_nonneg
      _ = 1 := exp_zero
  calc
    μ.real {ω | bernoulliCount S f m ω ≤ a}
        ≤ exp (-(-log 2) * a) * mgf (bernoulliCount S f m) μ (-log 2) :=
      measure_le_le_exp_mul_mgf a hlog hint
    _ ≤ exp (-(-log 2) * a) * exp (-((m : ℝ) * p) / 2) := by
      have hm := bernoulliCount_mgf_le S hf h01 hmean m (-log 2)
      have hexp : exp (-log (2 : ℝ)) = 1 / 2 := by
        rw [exp_neg, exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
      rw [hexp] at hm
      have hm' : mgf (bernoulliCount S f m) μ (-log 2) ≤ exp (-((m : ℝ) * p) / 2) := by
        convert hm using 1
        norm_num
        ring
      exact mul_le_mul_of_nonneg_left hm' (exp_pos _).le
    _ ≤ exp (-((m : ℝ) * p) / 8) := by
      rw [← exp_add]
      apply exp_le_exp.mpr
      have hlog_lt : log (2 : ℝ) < 3 / 4 :=
        Real.log_two_lt_d9.trans (by norm_num)
      have hmp_nonneg : 0 ≤ (m : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
      nlinarith

end Causalean.Stat.Concentration
