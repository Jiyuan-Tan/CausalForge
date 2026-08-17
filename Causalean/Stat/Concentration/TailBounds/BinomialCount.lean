/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Sample
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Probability.Moments.Basic

/-! # Multiplicative tails for bounded i.i.d. counts

This file develops the Chernoff chain for the sum of the first `m` observations
of a measurable `[0,1]`-valued statistic along an `IIDSample`.  The chain is
exposed one step at a time so that downstream work can enter at whatever level
it needs and can pick its own exponential tilt:

* `exp_mul_le_secant` — the chord bound for `exp` on the unit interval;
* `mgf_le_of_mem_Icc_zero_one` — the one-observation moment generating
  function bound `mgf ≤ exp (mean * (exp s - 1))`;
* `boundedCount_mgf_le_integral` / `boundedCount_mgf_le` — the same bound for
  the `m`-fold count, in terms of the population integral respectively an
  upper bound `p` for it;
* `boundedCount_upper_tail_of_tilt` / `boundedCount_lower_tail_of_tilt` — the
  resulting one-sided tails at an arbitrary tilt `s`.

`bernoulliCount_upper_tail` and `bernoulliCount_lower_tail` are the historical
`{0,1}`-valued specializations at the tilt `s = ± log 2`; `mgf_eq_of_mem_zero_one`
records that for a `{0,1}`-valued statistic the one-observation bound is an
equality.  `bernoulliCount_measurable`, `bernoulliCount_nonneg` and
`bernoulliCount_le` record the basic properties of the count itself.
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

/-- A count built from a nonnegative statistic is nonnegative. -/
lemma bernoulliCount_nonneg
    (S : Causalean.Stat.IIDSample Ω 𝒳 μ P) {f : 𝒳 → ℝ}
    (h0 : ∀ x, 0 ≤ f x) (m : ℕ) (ω : Ω) : 0 ≤ bernoulliCount S f m ω := by
  simp only [bernoulliCount]
  exact Finset.sum_nonneg fun i _ ↦ h0 _

/-- A count of `m` observations of a statistic bounded by one never exceeds `m`. -/
lemma bernoulliCount_le
    (S : Causalean.Stat.IIDSample Ω 𝒳 μ P) {f : 𝒳 → ℝ}
    (h1 : ∀ x, f x ≤ 1) (m : ℕ) (ω : Ω) : bernoulliCount S f m ω ≤ m := by
  simp only [bernoulliCount]
  calc
    (∑ i ∈ Finset.range m, f (S.Z i ω)) ≤ ∑ _i ∈ Finset.range m, (1 : ℝ) := by
      gcongr with i hi
      exact h1 _
    _ = m := by simp

/-- On the unit interval the exponential function stays below the chord joining
its values at the two endpoints: for a number `x` between zero and one and any
tilt `s`, `exp (s * x)` is at most `1 + x * (exp s - 1)`.  This is the convexity
step behind every Bernoulli-type Chernoff bound. -/
lemma exp_mul_le_secant {x s : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    exp (s * x) ≤ 1 + x * (exp s - 1) := by
  calc
    exp (s * x) = exp (x * s + (1 - x) * 0) := by ring_nf
    _ ≤ x * exp s + (1 - x) * exp 0 :=
      convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _)
        hx.1 (by linarith [hx.2]) (by ring)
    _ = 1 + x * (exp s - 1) := by rw [exp_zero]; ring

/-- The moment generating function of a measurable statistic taking values in
the unit interval is at most `exp (mean * (exp s - 1))`, where `mean` is the
statistic's population mean.  This holds at every tilt `s`, positive or
negative. -/
lemma mgf_le_of_mem_Icc_zero_one [IsProbabilityMeasure P] {f : 𝒳 → ℝ}
    (hf : AEMeasurable f P) (h01 : ∀ᵐ x ∂P, f x ∈ Set.Icc (0 : ℝ) 1) (s : ℝ) :
    mgf f P s ≤ exp ((∫ x, f x ∂P) * (exp s - 1)) := by
  have hfint : Integrable f P := by
    refine Integrable.of_bound hf.aestronglyMeasurable 1 (h01.mono fun x hx ↦ ?_)
    rw [Real.norm_eq_abs]
    exact abs_le.2 ⟨by linarith [hx.1], hx.2⟩
  have hexpint : Integrable (fun x ↦ exp (s * f x)) P := by
    refine Integrable.of_bound ((hf.const_mul s).exp.aestronglyMeasurable)
      (exp |s|) (h01.mono fun x hx ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    calc
      s * f x ≤ |s * f x| := le_abs_self _
      _ = |s| * |f x| := abs_mul _ _
      _ ≤ |s| * 1 := by
        gcongr
        exact abs_le.2 ⟨by linarith [hx.1], hx.2⟩
      _ = |s| := mul_one _
  rw [mgf]
  calc
    (∫ x, exp (s * f x) ∂P) ≤ ∫ x, (1 + f x * (exp s - 1)) ∂P :=
      integral_mono_ae hexpint ((integrable_const 1).add (hfint.mul_const _))
        (h01.mono fun x hx ↦ exp_mul_le_secant hx)
    _ = 1 + (∫ x, f x ∂P) * (exp s - 1) := by
      rw [integral_add (integrable_const 1) (hfint.mul_const _), integral_const,
        integral_mul_const]
      simp
    _ ≤ exp ((∫ x, f x ∂P) * (exp s - 1)) := by
      simpa [add_comm] using Real.add_one_le_exp ((∫ x, f x ∂P) * (exp s - 1))

/-- For a statistic that only takes the values zero and one, the moment
generating function is exactly `1 + p * (exp s - 1)`, where `p` is the
probability that the statistic equals one. -/
lemma mgf_eq_of_mem_zero_one
    [IsProbabilityMeasure P] {f : 𝒳 → ℝ} (hf : AEMeasurable f P)
    (h01 : ∀ᵐ x ∂P, f x = 0 ∨ f x = 1) (p s : ℝ)
    (hmean : ∫ x, f x ∂P = p) :
    mgf f P s = 1 + p * (exp s - 1) := by
  have hf_int : Integrable f P := by
    refine Integrable.of_bound hf.aestronglyMeasurable 1 (h01.mono fun x hx ↦ ?_)
    rcases hx with hx | hx <;> simp [hx]
  rw [mgf]
  calc
    (∫ x, exp (s * f x) ∂P) = ∫ x, (1 + f x * (exp s - 1)) ∂P := by
      refine integral_congr_ae (h01.mono fun x hx ↦ ?_)
      rcases hx with hx | hx
      · simp [hx]
      · simp [hx]
    _ = 1 + p * (exp s - 1) := by
      rw [integral_add (integrable_const 1) (hf_int.mul_const _), integral_const,
        integral_mul_const, hmean]
      simp

/-- The moment generating function of the count of the first `m` observations of
a measurable `[0,1]`-valued statistic is at most `exp (m * mean * (exp s - 1))`,
where `mean` is the statistic's population mean.  This is the i.i.d. tensorisation
of the one-observation bound and holds at every tilt `s`. -/
theorem boundedCount_mgf_le_integral
    (S : Causalean.Stat.IIDSample Ω 𝒳 μ P) {f : 𝒳 → ℝ}
    (hf : Measurable f) (h01 : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (m : ℕ) (s : ℝ) :
    mgf (bernoulliCount S f m) μ s
      ≤ exp ((m : ℝ) * ((∫ x, f x ∂P) * (exp s - 1))) := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  haveI : IsProbabilityMeasure P := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  let X : ℕ → Ω → ℝ := fun i ↦ f ∘ S.Z i
  have hX_meas : ∀ i, Measurable (X i) := fun i ↦ hf.comp (S.meas i)
  have hX_indep : iIndepFun X μ := S.indep.comp (fun _ ↦ f) (fun _ ↦ hf)
  have hmgf_one : ∀ i, mgf (X i) μ s ≤ exp ((∫ x, f x ∂P) * (exp s - 1)) := by
    intro i
    rw [← mgf_map (S.meas i).aemeasurable (by fun_prop), S.map_eq]
    exact mgf_le_of_mem_Icc_zero_one hf.aemeasurable (ae_of_all _ h01) s
  have hsum : bernoulliCount S f m = ∑ i ∈ Finset.range m, X i := by
    ext ω
    simp [bernoulliCount, X, Function.comp_apply]
  rw [hsum, hX_indep.mgf_sum hX_meas]
  calc
    (∏ i ∈ Finset.range m, mgf (X i) μ s)
        ≤ ∏ _i ∈ Finset.range m, exp ((∫ x, f x ∂P) * (exp s - 1)) :=
      Finset.prod_le_prod (fun i _ ↦ mgf_nonneg) (fun i _ ↦ hmgf_one i)
    _ = exp ((m : ℝ) * ((∫ x, f x ∂P) * (exp s - 1))) := by
      rw [Finset.prod_const, Finset.card_range, ← Real.exp_nat_mul]

/-- If the population mean of a measurable `[0,1]`-valued statistic is at most
`p`, then at every nonnegative tilt `s` the moment generating function of the
count of the first `m` observations is at most `exp (m * p * (exp s - 1))`. -/
theorem boundedCount_mgf_le
    (S : Causalean.Stat.IIDSample Ω 𝒳 μ P) {f : 𝒳 → ℝ}
    (hf : Measurable f) (h01 : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    {p : ℝ} (hmean : ∫ x, f x ∂P ≤ p) (m : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    mgf (bernoulliCount S f m) μ s ≤ exp ((m : ℝ) * (p * (exp s - 1))) := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  haveI : IsProbabilityMeasure P := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  refine (boundedCount_mgf_le_integral S hf h01 m s).trans (exp_le_exp.mpr ?_)
  have hexp : 0 ≤ exp s - 1 := by
    have := Real.one_le_exp hs
    linarith
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmean hexp)
    (Nat.cast_nonneg m)

/-- Chernoff upper tail at an arbitrary nonnegative tilt.  For a measurable
`[0,1]`-valued statistic with population mean at most `p`, the probability that the
count of the first `m` observations exceeds a level `a` is at most
`exp (-s * a + m * p * (exp s - 1))`, for every nonnegative `s`.  Optimising
over `s` recovers the usual multiplicative Chernoff bounds. -/
theorem boundedCount_upper_tail_of_tilt
    (S : Causalean.Stat.IIDSample Ω 𝒳 μ P) {f : 𝒳 → ℝ}
    (hf : Measurable f) (h01 : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    {p a : ℝ} (hmean : ∫ x, f x ∂P ≤ p) (m : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    μ.real {ω | a < bernoulliCount S f m ω}
      ≤ exp (-s * a + (m : ℝ) * (p * (exp s - 1))) := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  haveI : IsProbabilityMeasure P := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hint : Integrable (fun ω ↦ exp (s * bernoulliCount S f m ω)) μ := by
    refine Integrable.of_bound
      ((bernoulliCount_measurable S hf m).const_mul _ |>.exp.aestronglyMeasurable)
      (exp (s * m)) (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (bernoulliCount_le S (fun x ↦ (h01 x).2) m ω) hs)
  have hmgf := boundedCount_mgf_le S hf h01 hmean m s hs
  calc
    μ.real {ω | a < bernoulliCount S f m ω}
        ≤ μ.real {ω | a ≤ bernoulliCount S f m ω} :=
      measureReal_mono (by
        intro ω hω
        change a < bernoulliCount S f m ω at hω
        exact hω.le)
    _ ≤ exp (-s * a) * mgf (bernoulliCount S f m) μ s :=
      measure_ge_le_exp_mul_mgf a hs hint
    _ ≤ exp (-s * a) * exp ((m : ℝ) * (p * (exp s - 1))) :=
      mul_le_mul_of_nonneg_left hmgf (exp_pos _).le
    _ = exp (-s * a + (m : ℝ) * (p * (exp s - 1))) := (exp_add _ _).symm

/-- Chernoff lower tail at an arbitrary nonpositive tilt.  For a measurable
`[0,1]`-valued statistic with population mean at least `p`, the probability that the
count of the first `m` observations falls at or below a level `a` is at most
`exp (-s * a + m * p * (exp s - 1))`, for every nonpositive `s`.  Optimising
over `s` recovers the usual multiplicative Chernoff bounds. -/
theorem boundedCount_lower_tail_of_tilt
    (S : Causalean.Stat.IIDSample Ω 𝒳 μ P) {f : 𝒳 → ℝ}
    (hf : Measurable f) (h01 : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    {p a : ℝ} (hmean : p ≤ ∫ x, f x ∂P) (m : ℕ) (s : ℝ) (hs : s ≤ 0) :
    μ.real {ω | bernoulliCount S f m ω ≤ a}
      ≤ exp (-s * a + (m : ℝ) * (p * (exp s - 1))) := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  haveI : IsProbabilityMeasure P := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hint : Integrable (fun ω ↦ exp (s * bernoulliCount S f m ω)) μ := by
    refine Integrable.of_bound
      ((bernoulliCount_measurable S hf m).const_mul _ |>.exp.aestronglyMeasurable)
      1 (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    calc
      exp (s * bernoulliCount S f m ω) ≤ exp 0 :=
        exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg hs
          (bernoulliCount_nonneg S (fun x ↦ (h01 x).1) m ω))
      _ = 1 := exp_zero
  have hbase := boundedCount_mgf_le_integral S hf h01 m s
  have hcoef : exp s - 1 ≤ 0 := by
    have := Real.exp_le_one_iff.mpr hs
    linarith
  have hmgf : mgf (bernoulliCount S f m) μ s
      ≤ exp ((m : ℝ) * (p * (exp s - 1))) :=
    hbase.trans (exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonpos_right hmean hcoef) (Nat.cast_nonneg m)))
  calc
    μ.real {ω | bernoulliCount S f m ω ≤ a}
        ≤ exp (-s * a) * mgf (bernoulliCount S f m) μ s :=
      measure_le_le_exp_mul_mgf a hs hint
    _ ≤ exp (-s * a) * exp ((m : ℝ) * (p * (exp s - 1))) :=
      mul_le_mul_of_nonneg_left hmgf (exp_pos _).le
    _ = exp (-s * a + (m : ℝ) * (p * (exp s - 1))) := (exp_add _ _).symm

/-- **Upper multiplicative tail** for the count of an i.i.d. `[0,1]`-valued statistic. Let `S` be an
i.i.d. sample and let `f` be [a measurable statistic taking values in the unit
interval](hyp:hf,h01). If [the population mean of `f` is at most `p`](hyp:hmean) and [`m` times
`p` is less than half the threshold `a`](hyp:hmean_lt), then [the probability that the sum of
`f` over the first `m` draws exceeds `a` is at most $\exp(-a(\log 2 - 1/2))$](goal). -/
theorem bernoulliCount_upper_tail
    (S : Causalean.Stat.IIDSample Ω 𝒳 μ P) {f : 𝒳 → ℝ}
    (hf : Measurable f) (h01 : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    {p a : ℝ} (hmean : ∫ x, f x ∂P ≤ p)
    {m : ℕ} (hmean_lt : (m : ℝ) * p < a / 2) :
    μ.real {ω | a < bernoulliCount S f m ω}
      ≤ exp (-a * (log 2 - 1 / 2)) := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  haveI : IsProbabilityMeasure P := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hlog : 0 ≤ log (2 : ℝ) := (log_pos (by norm_num)).le
  refine (boundedCount_upper_tail_of_tilt S hf h01 hmean m (log 2) hlog).trans ?_
  rw [exp_log (by norm_num : (0 : ℝ) < 2)]
  refine exp_le_exp.mpr ?_
  have hmul : (m : ℝ) * (p * ((2 : ℝ) - 1)) = (m : ℝ) * p := by ring
  have hrhs : -a * (log 2 - 1 / 2) = -log 2 * a + a / 2 := by ring
  rw [hmul, hrhs]
  linarith

/-- **Lower multiplicative tail** for the count of an i.i.d. `[0,1]`-valued statistic. Let `S` be an
i.i.d. sample and let `f` be [a measurable statistic taking values in the unit
interval](hyp:hf,h01). If [`p` is nonnegative](hyp:hp), [the population mean of `f` is at least
`p`](hyp:hmean), and [twice the threshold `a` is less than `m` times `p`](hyp:hmean_gt), then
[the probability that the sum of `f` over the first `m` draws is at most `a` is at most
$\exp(-mp/8)$](goal). -/
theorem bernoulliCount_lower_tail
    (S : Causalean.Stat.IIDSample Ω 𝒳 μ P) {f : 𝒳 → ℝ}
    (hf : Measurable f) (h01 : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    {p a : ℝ} (hp : 0 ≤ p) (hmean : p ≤ ∫ x, f x ∂P)
    {m : ℕ} (hmean_gt : 2 * a < (m : ℝ) * p) :
    μ.real {ω | bernoulliCount S f m ω ≤ a}
      ≤ exp (-((m : ℝ) * p) / 8) := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  haveI : IsProbabilityMeasure P := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hlog0 : 0 ≤ log (2 : ℝ) := (log_pos (by norm_num)).le
  have hlog : -log (2 : ℝ) ≤ 0 := neg_nonpos.mpr hlog0
  refine (boundedCount_lower_tail_of_tilt S hf h01 hmean m (-log 2) hlog).trans ?_
  have hexp : exp (-log (2 : ℝ)) = 1 / 2 := by
    rw [exp_neg, exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hexp]
  apply exp_le_exp.mpr
  have hlog_lt : log (2 : ℝ) < 3 / 4 := Real.log_two_lt_d9.trans (by norm_num)
  have hmp_nonneg : 0 ≤ (m : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
  nlinarith

end Causalean.Stat.Concentration
