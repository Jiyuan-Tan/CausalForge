/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Hoeffding's inequality for i.i.d. samples

Causalean-facing corollaries of Mathlib's sub-Gaussian framework
(`Mathlib.Probability.Moments.SubGaussian`) specialized to the `IIDSample`
model.  We package:

* `IIDSample.map_eq` — each sample point has law `P`;
* `IIDSample.integral_comp_eq` — the population-mean identity
  `∫ f (Z i) ∂μ = ∫ f ∂P`;
* `iIndepFun_comp` — independence of `fun i ↦ f ∘ S.Z i`;
* `hoeffding_ge` / `hoeffding_abs_ge` — one-sided and two-sided Hoeffding tail
  bounds for the sample mean of a bounded statistic `f`.

The constants follow the standard scaling: an `[a,b]`-valued summand has
sub-Gaussian proxy `((b-a)/2)²` (Hoeffding's lemma), the `n`-fold sum has
proxy `n·((b-a)/2)²`, and rescaling by `1/n` yields the `2nε²/(b-a)²`
exponent.
-/

import Mathlib.Probability.Moments.SubGaussian
import Causalean.Stat.Sample

/-! # Hoeffding inequalities

This file specializes Mathlib's sub-Gaussian tail machinery to the
`IIDSample` model. It records sample-point law and expectation identities
(`IIDSample.map_eq` from `Causalean.Stat.Sample`, `IIDSample.integral_comp_eq`),
independence of composed sample statistics (`IIDSample.iIndepFun_comp`), the
centered sample-mean/sum event identity `sampleMean_sub_ge_setEq`, and the
one- and two-sided sample-mean bounds `hoeffding_ge` and `hoeffding_abs_ge`.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}


/-- The population mean of a statistic equals its sample-point expectation:
`∫ ω, f (S.Z i ω) ∂μ = ∫ x, f x ∂P`. -/
lemma IIDSample.integral_comp_eq (S : IIDSample Ω X μ P) {f : X → ℝ}
    (hf : Measurable f) (i : ℕ) :
    ∫ ω, f (S.Z i ω) ∂μ = ∫ x, f x ∂P := by
  rw [← integral_map (S.meas i).aemeasurable hf.aestronglyMeasurable, S.map_eq i]

/-- Independence of the composed family `fun i ↦ f ∘ S.Z i`. -/
lemma IIDSample.iIndepFun_comp (S : IIDSample Ω X μ P) {f : X → ℝ} (hf : Measurable f) :
    iIndepFun (fun i ω => f (S.Z i ω)) μ :=
  S.indep.comp (fun _ => f) (fun _ => hf)

namespace Concentration

/-- For `n > 0`, the centered sample-mean tail event coincides with the
centered-sum tail event: `ε ≤ X̄ₙ − m ⟺ n ε ≤ ∑_{i<n} (f (Z i) − m)`.  Reused
by both the Hoeffding and Bernstein tail bounds. -/
lemma sampleMean_sub_ge_setEq (S : IIDSample Ω X μ P) (f : X → ℝ) (m : ℝ)
    {n : ℕ} (hn : 0 < n) (ε : ℝ) :
    {ω | ε ≤ S.sampleMean f n ω - m}
      = {ω | (n : ℝ) * ε ≤ ∑ i ∈ Finset.range n, (f (S.Z i ω) - m)} := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  ext ω
  simp only [Set.mem_setOf_eq, IIDSample.sampleMean, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  constructor
  · intro h
    have := mul_le_mul_of_nonneg_left h (le_of_lt hnR)
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hnR), one_mul] at this
    exact this
  · intro h
    have := mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr hnR))
    rw [mul_sub, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hnR), one_mul,
      one_mul] at this
    exact this

/-- **One-sided Hoeffding inequality** for the sample mean of a bounded
statistic.  If `f` takes values in `[a, b]` (`a < b`) `P`-almost everywhere,
then for `ε ≥ 0`,
`P(X̄ₙ − E[f] ≥ ε) ≤ exp(−2 n ε² / (b − a)²)`. -/
theorem hoeffding_ge (S : IIDSample Ω X μ P) {f : X → ℝ} (hf : Measurable f)
    {a b : ℝ} (hab : a < b) (hbound : ∀ᵐ x ∂P, f x ∈ Set.Icc a b)
    (n : ℕ) (hn : 0 < n) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ S.sampleMean f n ω - ∫ x, f x ∂P}
      ≤ Real.exp (-2 * n * ε ^ 2 / (b - a) ^ 2) := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  set m : ℝ := ∫ x, f x ∂P with hm
  set c : ℝ≥0 := (‖b - a‖₊ / 2) ^ 2 with hc
  -- centered family
  set Y : ℕ → Ω → ℝ := fun i ω => f (S.Z i ω) - m with hY
  -- independence of the centered family
  have hYindep : iIndepFun Y μ :=
    S.indep.comp (fun _ x => f x - m) (fun _ => hf.sub_const m)
  -- per-term boundedness pulled back along `Z i`
  have hbound_i : ∀ i, ∀ᵐ ω ∂μ, f (S.Z i ω) ∈ Set.Icc a b := by
    intro i
    have hb2 := hbound
    rw [← S.map_eq i] at hb2
    exact (ae_map_iff (S.meas i).aemeasurable (hf measurableSet_Icc)).mp hb2
  -- per-term sub-Gaussian
  have hsubg : ∀ i < n, HasSubgaussianMGF (Y i) c μ := by
    intro i _
    have hmean : (∫ ω, f (S.Z i ω) ∂μ) = m := S.integral_comp_eq hf i
    have := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := fun ω => f (S.Z i ω))
      (hf.comp (S.meas i)).aemeasurable (hbound_i i)
    simpa [hY, hmean] using this
  have hnε : (0 : ℝ) ≤ (n : ℝ) * ε := by positivity
  have key := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hYindep hsubg hnε
  -- rewrite the event set
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hset : {ω | ε ≤ S.sampleMean f n ω - m}
      = {ω | (n : ℝ) * ε ≤ ∑ i ∈ Finset.range n, Y i ω} :=
    sampleMean_sub_ge_setEq S f m hn ε
  rw [hset]
  refine key.trans (le_of_eq ?_)
  -- exponent identity
  have hca : (c : ℝ) = ((b - a) / 2) ^ 2 := by
    rw [hc]
    push_cast
    rw [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hab)]
  have hba : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  rw [show ((n : ℝ) * ε) ^ 2 = (n : ℝ) ^ 2 * ε ^ 2 by ring]
  congr 1
  rw [hca]
  field_simp

/-- Generic two-sided assembly: the two-sided deviation event `{ε ≤ |T − m|}` is
covered by the two one-sided events, so its measure is at most the sum of their
one-sided bounds.  Reused by the Hoeffding and Bernstein two-sided tail bounds. -/
lemma measureReal_abs_dev_le_two_sided {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (T : Ω → ℝ) (m B ε : ℝ)
    (hup : μ.real {ω | ε ≤ T ω - m} ≤ B)
    (hlow : μ.real {ω | ε ≤ -T ω + m} ≤ B) :
    μ.real {ω | ε ≤ |T ω - m|} ≤ 2 * B := by
  have hunion : {ω | ε ≤ |T ω - m|}
      ⊆ {ω | ε ≤ T ω - m} ∪ {ω | ε ≤ -T ω + m} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    rcases le_abs.mp hω with h | h
    · exact Or.inl h
    · exact Or.inr (by simp only [Set.mem_setOf_eq]; linarith)
  calc μ.real {ω | ε ≤ |T ω - m|}
      ≤ μ.real ({ω | ε ≤ T ω - m} ∪ {ω | ε ≤ -T ω + m}) := measureReal_mono hunion
    _ ≤ μ.real {ω | ε ≤ T ω - m} + μ.real {ω | ε ≤ -T ω + m} := measureReal_union_le _ _
    _ ≤ B + B := add_le_add hup hlow
    _ = 2 * B := by ring

/-- **Two-sided Hoeffding inequality** for the sample mean of a bounded
statistic.  If `f` takes values in `[a, b]` (`a < b`) `P`-almost everywhere,
then for `ε ≥ 0`,
`P(|X̄ₙ − E[f]| ≥ ε) ≤ 2 exp(−2 n ε² / (b − a)²)`. -/
theorem hoeffding_abs_ge (S : IIDSample Ω X μ P) {f : X → ℝ} (hf : Measurable f)
    {a b : ℝ} (hab : a < b) (hbound : ∀ᵐ x ∂P, f x ∈ Set.Icc a b)
    (n : ℕ) (hn : 0 < n) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |S.sampleMean f n ω - ∫ x, f x ∂P|}
      ≤ 2 * Real.exp (-2 * n * ε ^ 2 / (b - a) ^ 2) := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  set m : ℝ := ∫ x, f x ∂P with hm
  -- upper tail
  have hup := hoeffding_ge S hf hab hbound n hn hε
  -- lower tail via negation: apply the one-sided bound to `-f`
  have hbound' : ∀ᵐ x ∂P, (fun x => -f x) x ∈ Set.Icc (-b) (-a) := by
    filter_upwards [hbound] with x hx
    exact ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩
  have hlow := hoeffding_ge S (f := fun x => -f x) hf.neg (a := -b) (b := -a)
    (by linarith) hbound' n hn hε
  have hint_neg : (∫ x, (fun x => -f x) x ∂P) = -m := by simp [hm, integral_neg]
  have hmean_neg : ∀ ω, S.sampleMean (fun x => -f x) n ω = -S.sampleMean f n ω := by
    intro ω; simp [IIDSample.sampleMean, Finset.sum_neg_distrib, mul_neg]
  have hrange : (-a) - (-b) = b - a := by ring
  rw [hint_neg, hrange] at hlow
  simp only [hmean_neg, sub_neg_eq_add] at hlow
  exact measureReal_abs_dev_le_two_sided (S.sampleMean f n) m _ ε hup hlow

end Concentration

end Stat

end Causalean
