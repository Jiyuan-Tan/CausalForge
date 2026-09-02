/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.Analysis.BernoulliKL
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


/-!
# Bernoulli measures

This file defines the Bernoulli law on the real line, supported on `0` and
`1`, and proves its basic probability, support, integral, absolute-continuity,
and KL-divergence facts. It also provides the corresponding Bool-valued law and
its measurability, probability, integral, bind, and map formulas.
-/

namespace Causalean.Mathlib.Probability

open MeasureTheory
open scoped BigOperators

/-- The Bernoulli law on `ℝ` with success probability `p`.  Concentrates
`ENNReal.ofReal p` on `1` and `ENNReal.ofReal (1 − p)` on `0`. -/
noncomputable def bernoulliLaw (p : ℝ) : Measure ℝ :=
  ENNReal.ofReal p • Measure.dirac (1 : ℝ)
    + ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)

/-- Two-point integral for the custom `bernoulliLaw`: since
`bernoulliLaw p = ENNReal.ofReal p • dirac 1 + ENNReal.ofReal (1-p) • dirac 0`,
its integral splits via `integral_add_measure` / `integral_smul_measure` /
`integral_dirac` into the two-point weighted sum, with `0 ≤ p ≤ 1` collapsing
the `ENNReal → ℝ` coercions to `p` and `1 - p`. -/
lemma bernoulliLaw_integral {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : ℝ → ℝ) :
    ∫ y, f y ∂(bernoulliLaw p) = p * f 1 + (1 - p) * f 0 := by
  unfold bernoulliLaw
  rw [integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure]
    simp [hp0, sub_nonneg.mpr hp1, smul_eq_mul]
  · exact Integrable.smul_measure (μ := Measure.dirac (1 : ℝ))
      (c := ENNReal.ofReal p)
      (integrable_dirac (f := f) (a := (1 : ℝ)) (by simp [enorm])) (by simp)
  · exact Integrable.smul_measure (μ := Measure.dirac (0 : ℝ))
      (c := ENNReal.ofReal (1 - p))
      (integrable_dirac (f := f) (a := (0 : ℝ)) (by simp [enorm])) (by simp)

/-- The custom `bernoulliLaw` is a probability measure for `0 ≤ p ≤ 1`:
its total mass is `p + (1 - p) = 1`. -/
lemma bernoulliLaw_isProbabilityMeasure {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (bernoulliLaw p) := by
  rw [isProbabilityMeasure_iff]
  unfold bernoulliLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [Measure.dirac_apply, Set.indicator_of_mem, Set.mem_univ,
    Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp0 (sub_nonneg.mpr hp1)]
  norm_num

/-- The Bernoulli law on the real line is almost surely nonnegative, since all
of its mass is placed at `0` and `1`. -/
lemma bernoulliLaw_ae_nonneg {p : ℝ} :
    0 ≤ᵐ[bernoulliLaw p] (fun y : ℝ => y) := by
  change (bernoulliLaw p) {y : ℝ | ¬ 0 ≤ y} = 0
  have hset : {y : ℝ | ¬ 0 ≤ y} = {y | y < 0} := by
    ext y
    simp [not_le]
  rw [hset]
  unfold bernoulliLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp

/-- The Bernoulli law on the real line is almost surely at most one, since all
of its mass is placed at `0` and `1`. -/
lemma bernoulliLaw_ae_le_one {p : ℝ} :
    (fun y : ℝ => y) ≤ᵐ[bernoulliLaw p] fun _ => (1 : ℝ) := by
  change (bernoulliLaw p) {y : ℝ | ¬ y ≤ 1} = 0
  have hset : {y : ℝ | ¬ y ≤ 1} = {y | 1 < y} := by
    ext y
    simp [not_le]
  rw [hset]
  unfold bernoulliLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp

/-- A draw from the real-valued Bernoulli law is almost surely either `0` or
`1`. -/
lemma bernoulliLaw_ae_zero_or_one {p : ℝ} :
    ∀ᵐ y ∂bernoulliLaw p, y = 0 ∨ y = 1 := by
  change (bernoulliLaw p) {y : ℝ | ¬ (y = 0 ∨ y = 1)} = 0
  unfold bernoulliLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp

/-- A Bernoulli law is absolutely continuous with respect to any Bernoulli law
whose success probability is strictly between zero and one. -/
lemma bernoulliLaw_ac_of_reference_interior {p q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    bernoulliLaw p ≪ bernoulliLaw q := by
  have hq_ne0 : ENNReal.ofReal q ≠ 0 := by
    intro h
    have hle := ENNReal.ofReal_eq_zero.mp h
    linarith
  have h1q_ne0 : ENNReal.ofReal (1 - q) ≠ 0 := by
    intro h
    have hle := ENNReal.ofReal_eq_zero.mp h
    linarith
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s hs hzero
  unfold bernoulliLaw at hzero ⊢
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply] at hzero ⊢
  by_cases h1 : (1 : ℝ) ∈ s
  · exfalso
    by_cases h0 : (0 : ℝ) ∈ s
    · simp [h1, h0, hq_ne0] at hzero
    · simp [h1, h0, hq_ne0] at hzero
  · by_cases h0 : (0 : ℝ) ∈ s
    · exfalso
      simp [h1, h0, h1q_ne0] at hzero
    · simp [h1, h0]

/-- The log-likelihood ratio between any two real-parameter Bernoulli laws is
integrable under the first law. -/
@[fun_prop]
lemma bernoulliLaw_llr_integrable {p q : ℝ} :
    Integrable (llr (bernoulliLaw p) (bernoulliLaw q)) (bernoulliLaw p) := by
  unfold bernoulliLaw
  rw [integrable_add_measure]
  constructor
  · exact Integrable.smul_measure (μ := Measure.dirac (1 : ℝ))
      (c := ENNReal.ofReal p)
      (integrable_dirac
        (f := llr (ENNReal.ofReal p • Measure.dirac (1 : ℝ)
          + ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)) (bernoulliLaw q))
        (a := (1 : ℝ)) (by simp [enorm])) (by simp)
  · exact Integrable.smul_measure (μ := Measure.dirac (0 : ℝ))
      (c := ENNReal.ofReal (1 - p))
      (integrable_dirac
        (f := llr (ENNReal.ofReal p • Measure.dirac (1 : ℝ)
          + ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)) (bernoulliLaw q))
        (a := (0 : ℝ)) (by simp [enorm])) (by simp)

/-- Let $p$ be a Bernoulli success probability with [$0 \le p \le 1$](hyp:hp0,hp1), and let $q$
be a reference success probability with [$0 < q < 1$](hyp:hq0,hq1). Then [the
Kullback–Leibler divergence from the Bernoulli($p$) law to the Bernoulli($q$) law equals
$p \log(p/q) + (1-p)\log((1-p)/(1-q))$](goal), the usual two-point KL formula: a success
contribution plus a failure contribution. -/
lemma bernoulliLaw_klDiv_toReal {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    (InformationTheory.klDiv (bernoulliLaw p) (bernoulliLaw q)).toReal
      = p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) := by
  classical
  haveI hp_prob : IsProbabilityMeasure (bernoulliLaw p) :=
    bernoulliLaw_isProbabilityMeasure hp0 hp1
  haveI hq_prob : IsProbabilityMeasure (bernoulliLaw q) :=
    bernoulliLaw_isProbabilityMeasure hq0.le hq1.le
  let g : ℝ → ENNReal :=
    fun x =>
      if x = 1 then ENNReal.ofReal (p / q)
      else ENNReal.ofReal ((1 - p) / (1 - q))
  have hg : Measurable g := by
    dsimp [g]
    exact Measurable.ite (measurableSet_singleton (1 : ℝ)) measurable_const measurable_const
  have hq_ne0 : ENNReal.ofReal q ≠ 0 := by
    intro h
    have hle := ENNReal.ofReal_eq_zero.mp h
    linarith
  have h1q_ne0 : ENNReal.ofReal (1 - q) ≠ 0 := by
    intro h
    have hle := ENNReal.ofReal_eq_zero.mp h
    linarith
  have hwd : bernoulliLaw p = (bernoulliLaw q).withDensity g := by
    ext s hs
    rw [withDensity_apply _ hs]
    rw [← lintegral_indicator hs g]
    unfold bernoulliLaw
    dsimp [g]
    rw [lintegral_add_measure]
    rw [lintegral_smul_measure, lintegral_smul_measure]
    simp only [lintegral_dirac]
    by_cases h1 : (1 : ℝ) ∈ s
    · by_cases h0 : (0 : ℝ) ∈ s
      · simp [h1, h0, ENNReal.ofReal_div_of_pos hq0,
          ENNReal.ofReal_div_of_pos (sub_pos.mpr hq1),
          ENNReal.mul_div_cancel hq_ne0 ENNReal.ofReal_ne_top,
          ENNReal.mul_div_cancel h1q_ne0 ENNReal.ofReal_ne_top]
      · simp [h1, h0, ENNReal.ofReal_div_of_pos hq0,
          ENNReal.mul_div_cancel hq_ne0 ENNReal.ofReal_ne_top]
    · by_cases h0 : (0 : ℝ) ∈ s
      · simp [h1, h0, ENNReal.ofReal_div_of_pos (sub_pos.mpr hq1),
          ENNReal.mul_div_cancel h1q_ne0 ENNReal.ofReal_ne_top]
      · simp [h1, h0]
  have hac : bernoulliLaw p ≪ bernoulliLaw q := by
    rw [hwd]
    exact withDensity_absolutelyContinuous (bernoulliLaw q) g
  have hrn : (bernoulliLaw p).rnDeriv (bernoulliLaw q) =ᵐ[bernoulliLaw q] g := by
    rw [hwd]
    exact Measure.rnDeriv_withDensity (bernoulliLaw q) hg
  rw [InformationTheory.toReal_klDiv_eq_integral_klFun hac]
  trans ∫ x, InformationTheory.klFun (g x).toReal ∂(bernoulliLaw q)
  · exact integral_congr_ae <| by
      filter_upwards [hrn] with x hx
      rw [hx]
  rw [bernoulliLaw_integral hq0.le hq1.le]
  dsimp [g]
  have hpq_nonneg : 0 ≤ p / q := div_nonneg hp0 hq0.le
  have hcp_nonneg : 0 ≤ (1 - p) / (1 - q) :=
    div_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hq1.le)
  simp only [↓reduceIte, zero_ne_one]
  rw [ENNReal.toReal_ofReal hpq_nonneg, ENNReal.toReal_ofReal hcp_nonneg]
  have hqne : q ≠ 0 := hq0.ne'
  have h1qne : 1 - q ≠ 0 := sub_ne_zero.mpr hq1.ne'
  have hA :
      q * InformationTheory.klFun (p / q) = p * Real.log (p / q) + q - p := by
    rw [InformationTheory.klFun_apply]
    field_simp [hqne]
  have hB :
      (1 - q) * InformationTheory.klFun ((1 - p) / (1 - q))
        = (1 - p) * Real.log ((1 - p) / (1 - q)) + (1 - q) - (1 - p) := by
    rw [InformationTheory.klFun_apply]
    field_simp [h1qne]
  rw [hA, hB]
  ring

/-- If both success probabilities $p$ and $q$ lie in the middle half of the unit interval,
[$1/4 \le p \le 3/4$](hyp:hp_lo,hp_hi) and [$1/4 \le q \le 3/4$](hyp:hq_lo,hq_hi), then
[the Kullback–Leibler divergence from the Bernoulli($p$) law to the Bernoulli($q$) law is
at most four times the squared difference of the probabilities, $4(p-q)^2$](goal). -/
lemma bernoulliLaw_klDiv_le_four_sq_sub {p q : ℝ}
    (hp_lo : (1 : ℝ) / 4 ≤ p) (hp_hi : p ≤ 3 / 4)
    (hq_lo : (1 : ℝ) / 4 ≤ q) (hq_hi : q ≤ 3 / 4) :
    InformationTheory.klDiv (bernoulliLaw p) (bernoulliLaw q)
      ≤ ENNReal.ofReal (4 * (p - q) ^ 2) := by
  have hp0 : 0 < p := by linarith
  have hp1 : p < 1 := by linarith
  have hq0 : 0 < q := by linarith
  have hq1 : q < 1 := by linarith
  have hac : bernoulliLaw p ≪ bernoulliLaw q :=
    bernoulliLaw_ac_of_reference_interior hq0 hq1
  have hint : Integrable (llr (bernoulliLaw p) (bernoulliLaw q)) (bernoulliLaw p) :=
    bernoulliLaw_llr_integrable
  have hfinite :
      InformationTheory.klDiv (bernoulliLaw p) (bernoulliLaw q) ≠ ⊤ :=
    InformationTheory.klDiv_ne_top hac hint
  rw [← ENNReal.ofReal_toReal hfinite]
  exact ENNReal.ofReal_le_ofReal <| by
    rw [bernoulliLaw_klDiv_toReal hp0.le hp1.le hq0 hq1]
    exact Causalean.Mathlib.Analysis.bernoulli_kl_le_four_sq_sub_of_mem_quarter_band
      hp_lo hp_hi hq_lo hq_hi

/-- `ℝ≥0∞`/`lintegral` analogue of `bernoulliLaw_integral`: a Bernoulli law
integrates an `ℝ≥0∞`-valued function as the two-point weighted sum. -/
lemma bernoulliLaw_lintegral_ofReal {p : ℝ} (f : ℝ → ENNReal) :
    ∫⁻ y, f y ∂(bernoulliLaw p)
      = ENNReal.ofReal p * f 1 + ENNReal.ofReal (1 - p) * f 0 := by
  unfold bernoulliLaw
  rw [lintegral_add_measure]
  · simp [lintegral_smul_measure, mul_comm]

/-- The Boolean Bernoulli distribution assigns success probability to truth and failure
probability to falsehood. It is the same two-point law as the existing real-valued Bernoulli
distribution on zero and one, but its Boolean values make it usable as a Markov kernel into
a Boolean coordinate of a potential-outcome tuple.

This is the Bool-valued sibling of `bernoulliLaw`. -/
noncomputable def bernoulliBool (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac true +
    ENNReal.ofReal (1 - p) • Measure.dirac false

/-- The Bool-valued Bernoulli distribution varies measurably with its success probability,
so a measurable probability parameter can be used to construct a measurable kernel. -/
@[fun_prop]
lemma measurable_bernoulliBool : Measurable bernoulliBool := by
  unfold bernoulliBool
  fun_prop

/-- A Bool-valued Bernoulli distribution is a probability distribution whenever its
success probability lies between zero and one. -/
lemma bernoulliBool_isProbabilityMeasure {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (bernoulliBool p) := by
  rw [isProbabilityMeasure_iff]
  unfold bernoulliBool
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [Measure.dirac_apply, Set.indicator_of_mem, Set.mem_univ,
    Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp0 (sub_nonneg.mpr hp1)]
  convert ENNReal.ofReal_one using 2
  all_goals ring

/-- The expectation of a real-valued function of a Bool-valued Bernoulli draw is its value
at success times the success probability plus its value at failure times the failure
probability. -/
lemma bernoulliBool_integral {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : Bool → ℝ) :
    ∫ z, f z ∂bernoulliBool p =
      p * f true + (1 - p) * f false := by
  unfold bernoulliBool
  rw [integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure]
    simp [hp0, sub_nonneg.mpr hp1, smul_eq_mul]
  · exact Integrable.smul_measure (μ := Measure.dirac true)
      (c := ENNReal.ofReal p)
      (integrable_dirac (f := f) (a := true) (by simp [enorm])) (by simp)
  · exact Integrable.smul_measure (μ := Measure.dirac false)
      (c := ENNReal.ofReal (1 - p))
      (integrable_dirac (f := f) (a := false) (by simp [enorm])) (by simp)

/-- Drawing a Bool-valued Bernoulli variable and then selecting a distribution according to
its value produces the corresponding success-probability mixture of the two distributions. -/
lemma bernoulliBool_bind {β : Type*} [MeasurableSpace β] (p : ℝ)
    (K : Bool → Measure β) :
    (bernoulliBool p).bind K =
      ENNReal.ofReal p • K true + ENNReal.ofReal (1 - p) • K false := by
  ext A hA
  rw [Measure.bind_apply hA (measurable_of_finite _).aemeasurable]
  unfold bernoulliBool
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  simp [Measure.add_apply, Measure.smul_apply, smul_eq_mul]

/-- Transforming a Bool-valued Bernoulli draw produces a two-point distribution concentrated
on the transformed success and failure values with their original probabilities. -/
lemma bernoulliBool_map {β : Type*} [MeasurableSpace β] (p : ℝ)
    (f : Bool → β) :
    (bernoulliBool p).map f =
      ENNReal.ofReal p • Measure.dirac (f true) +
        ENNReal.ofReal (1 - p) • Measure.dirac (f false) := by
  have hf : Measurable f := measurable_of_finite f
  unfold bernoulliBool
  rw [Measure.map_add _ _ hf, Measure.map_smul, Measure.map_smul]
  rw [Measure.map_dirac' hf, Measure.map_dirac' hf]

end Causalean.Mathlib.Probability
namespace Causalean.Mathlib.Probability

open scoped BigOperators

/-- The real binomial weight of count `j` among `m` trials with success
parameter `p`. -/
def binomialWeight (m : Nat) (p : Real) (j : Nat) : Real :=
  (Nat.choose m j : Real) * p ^ j * (1 - p) ^ (m - j)

private def boolFunEquivFinset (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (ι → Bool) ≃ Finset ι where
  toFun b := Finset.univ.filter fun i => b i = true
  invFun s := fun i => decide (i ∈ s)
  left_inv b := by
    funext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases b i <;> simp
  right_inv s := by
    ext i
    simp

private lemma prod_bernoulli_eq_card {ι : Type*} [Fintype ι]
    (p : Real) (b : ι → Bool) :
    (∏ i, if b i then p else 1 - p) =
      p ^ (Finset.univ.filter fun i => b i = true).card *
        (1 - p) ^ (Fintype.card ι - (Finset.univ.filter fun i => b i = true).card) := by
  classical
  let s := Finset.univ.filter fun i => b i = true
  let t := Finset.univ.filter fun i => ¬ b i = true
  have hcard : t.card = Fintype.card ι - s.card := by
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ι)) (fun i => b i = true)
    simp only [Finset.card_univ] at hsum
    dsimp [s, t]
    omega
  calc
    (∏ i, if b i then p else 1 - p) =
        (∏ i ∈ s, (if b i then p else 1 - p)) *
          ∏ i ∈ t, (if b i then p else 1 - p) := by
      rw [Finset.prod_filter_mul_prod_filter_not]
    _ = p ^ s.card * (1 - p) ^ t.card := by
      congr 1
      · apply Finset.prod_eq_pow_card
        intro i hi
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp [hi]
      · apply Finset.prod_eq_pow_card
        intro i hi
        simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        cases h : b i <;> simp_all
    _ = _ := by rw [hcard]

/-- [A Bernoulli-weighted sum of any function of the success count equals the
corresponding sum against the binomial mass function](goal). -/
lemma sum_bernoulli_eq_binomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Real) (F : Nat → Real) :
    (∑ b : ι → Bool, (∏ i, if b i then p else 1 - p) *
      F (Finset.univ.filter fun i => b i = true).card) =
    ∑ j ∈ Finset.range (Fintype.card ι + 1),
      binomialWeight (Fintype.card ι) p j * F j := by
  classical
  rw [Fintype.sum_equiv (boolFunEquivFinset ι) _
    (fun s : Finset ι => p ^ s.card * (1 - p) ^ (Fintype.card ι - s.card) * F s.card)
    (fun b => by
      rw [prod_bernoulli_eq_card]
      rfl)]
  rw [show (Finset.univ : Finset (Finset ι)) = Finset.univ.powerset by
    ext s
    simp]
  rw [Finset.sum_powerset]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_powersetCard j Finset.univ
    (fun j => p ^ j * (1 - p) ^ (Fintype.card ι - j) * F j)]
  simp only [Finset.card_univ, binomialWeight]
  ring

/-- [The reciprocal of a positive integer, totalized to zero at the
origin, is at most twice the reciprocal of its successor](goal). -/
lemma totalized_inverse_count_le (j : Nat) :
    (if 0 < j then (j : Real)⁻¹ else 0) ≤ 2 * ((j : Real) + 1)⁻¹ := by
  by_cases hj : 0 < j
  · rw [if_pos hj, ← div_eq_mul_inv]
    have hjR : (0 : Real) < j := by
      exact_mod_cast hj
    have hj1R : (0 : Real) < (j : Real) + 1 := by positivity
    apply (le_div_iff₀ hj1R).2
    calc
      (j : Real)⁻¹ * ((j : Real) + 1) = 1 + (j : Real)⁻¹ := by
        field_simp
      _ ≤ 2 := by
        have hinv : (j : Real)⁻¹ ≤ 1 :=
          (inv_le_one₀ hjR).2 (by exact_mod_cast hj)
        linarith
  · simp [hj]
    positivity

/-- When [the success probability is positive and at most one](hyp:hp,hp1),
[the binomial expectation of the zero-safe inverse success count is at most
twice the reciprocal of the trial count plus one times that probability](goal). -/
lemma binomial_totalized_inverse_count_le (m : Nat) (p : Real)
    (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
      (if 0 < j then (j : Real)⁻¹ else 0)) ≤
      2 / (((m + 1 : Nat) : Real) * p) := by
  -- Proof route: compare `1/j` with `2/(j+1)`, shift `choose m j`,
  -- and evaluate the resulting binomial row by `add_pow`.
  let d : Real := ((m + 1 : Nat) : Real) * p
  let S : Real := ∑ j ∈ Finset.range (m + 1),
    binomialWeight m p j * ((j : Real) + 1)⁻¹
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hterm (j : Nat) (hj : j ∈ Finset.range (m + 1)) :
      d * (binomialWeight m p j * ((j : Real) + 1)⁻¹) =
        (Nat.choose (m + 1) (j + 1) : Real) * p ^ (j + 1) *
          (1 - p) ^ ((m + 1) - (j + 1)) := by
    have hjlt : j < m + 1 := Finset.mem_range.mp hj
    have hsub : (m + 1) - (j + 1) = m - j := by omega
    have hc : (((m + 1 : Nat) : Real) * (Nat.choose m j : Real)) =
        (Nat.choose (m + 1) (j + 1) : Real) * ((j + 1 : Nat) : Real) := by
      exact_mod_cast Nat.add_one_mul_choose_eq m j
    dsimp [d]
    rw [binomialWeight, hsub, pow_succ]
    field_simp
    calc
      ((m + 1 : Nat) : Real) * (Nat.choose m j : Real) * (1 - p) ^ (m - j) =
          ((((m + 1 : Nat) : Real) * (Nat.choose m j : Real)) *
            (1 - p) ^ (m - j)) := by ring
      _ = (((Nat.choose (m + 1) (j + 1) : Real) * ((j + 1 : Nat) : Real)) *
            (1 - p) ^ (m - j)) := by rw [hc]
      _ = (1 - p) ^ (m - j) * ((j : Real) + 1) *
            (Nat.choose (m + 1) (j + 1) : Real) := by push_cast; ring
  have hid : d * S = 1 - (1 - p) ^ (m + 1) := by
    dsimp [S]
    rw [Finset.mul_sum]
    calc
      (∑ j ∈ Finset.range (m + 1),
          d * (binomialWeight m p j * ((j : Real) + 1)⁻¹)) =
          ∑ j ∈ Finset.range (m + 1),
            p ^ (j + 1) * (1 - p) ^ ((m + 1) - (j + 1)) *
              (Nat.choose (m + 1) (j + 1) : Real) := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [hterm j hj]
                ring
      _ = (p + (1 - p)) ^ (m + 1) - (1 - p) ^ (m + 1) := by
        rw [add_pow]
        rw [Finset.sum_range_succ' (fun k =>
          p ^ k * (1 - p) ^ ((m + 1) - k) *
            (Nat.choose (m + 1) k : Real)) (m + 1)]
        simp
      _ = 1 - (1 - p) ^ (m + 1) := by ring
  have hS : S ≤ 1 / d := by
    apply (le_div_iff₀ hd).2
    rw [mul_comm S d, hid]
    have hpow := pow_nonneg hq (m + 1)
    linarith
  calc
    (∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
        (if 0 < j then (j : Real)⁻¹ else 0)) ≤
        ∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
          (2 * ((j : Real) + 1)⁻¹) := by
            apply Finset.sum_le_sum
            intro j hj
            apply mul_le_mul_of_nonneg_left (totalized_inverse_count_le j)
            dsimp [binomialWeight]
            positivity
    _ = 2 * S := by
      dsimp [S]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ 2 * (1 / d) := by nlinarith
    _ = 2 / (((m + 1 : Nat) : Real) * p) := by
      dsimp [d]
      ring

/-- If [the overlap margin is positive](hyp:hepsilon) and [the success
probability lies between that margin and one minus the margin](hyp:hlo,hhi),
[the binomial expectation of the two inverse arm counts on the interior event
is at most four divided by the trial count plus one times the margin](goal). -/
lemma binomial_inverse_two_arms_interior_le (m : Nat) (p epsilon : Real)
    (hepsilon : 0 < epsilon) (hlo : epsilon ≤ p)
    (hhi : p ≤ 1 - epsilon) :
    (∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
      (if 0 < j ∧ j < m then
        (j : Real)⁻¹ + ((m - j : Nat) : Real)⁻¹
      else 0)) ≤
      4 / (((m + 1 : Nat) : Real) * epsilon) := by
  -- Apply the preceding estimate to successes with parameter `p` and to
  -- failures with parameter `1-p`; deleting the two endpoints only lowers
  -- the nonnegative sums.  Then use both overlap inequalities.
  have hp : 0 < p := lt_of_lt_of_le hepsilon hlo
  have hp1 : p ≤ 1 := by linarith
  have hq : 0 < 1 - p := by linarith
  have hq1 : 1 - p ≤ 1 := by linarith
  have hinter (j : Nat) :
      (if 0 < j ∧ j < m then
          (j : Real)⁻¹ + ((m - j : Nat) : Real)⁻¹
        else 0) ≤
        (if 0 < j then (j : Real)⁻¹ else 0) +
          (if 0 < m - j then ((m - j : Nat) : Real)⁻¹ else 0) := by
    by_cases hj : 0 < j ∧ j < m
    · have hmj : 0 < m - j := Nat.sub_pos_of_lt hj.2
      simp [hj, hmj]
    · rw [if_neg hj]
      positivity
  have hfail :
      (∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
        (if 0 < m - j then ((m - j : Nat) : Real)⁻¹ else 0)) =
      ∑ j ∈ Finset.range (m + 1), binomialWeight m (1 - p) j *
        (if 0 < j then (j : Real)⁻¹ else 0) := by
    rw [← Finset.sum_range_reflect (fun j => binomialWeight m p j *
      (if 0 < m - j then ((m - j : Nat) : Real)⁻¹ else 0)) (m + 1)]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < m + 1 := Finset.mem_range.mp hj
    have hjle : j ≤ m := by omega
    have hreflect : m + 1 - 1 - j = m - j := by omega
    have hcancel : m - (m - j) = j := by omega
    rw [hreflect, binomialWeight, binomialWeight, hcancel, Nat.choose_symm hjle]
    congr 1
    ring
  have hsuccess := binomial_totalized_inverse_count_le m p hp hp1
  have hfailure := binomial_totalized_inverse_count_le m (1 - p) hq hq1
  have hn : (0 : Real) < ((m + 1 : Nat) : Real) := by positivity
  have hnepsilon :
      ((m + 1 : Nat) : Real) * epsilon ≤ ((m + 1 : Nat) : Real) * p :=
    mul_le_mul_of_nonneg_left hlo hn.le
  have hnqepsilon :
      ((m + 1 : Nat) : Real) * epsilon ≤
        ((m + 1 : Nat) : Real) * (1 - p) := by
    apply mul_le_mul_of_nonneg_left _ hn.le
    linarith
  have hinvp :
      1 / (((m + 1 : Nat) : Real) * p) ≤
        1 / (((m + 1 : Nat) : Real) * epsilon) :=
    one_div_le_one_div_of_le (mul_pos hn hepsilon) hnepsilon
  have hinvq :
      1 / (((m + 1 : Nat) : Real) * (1 - p)) ≤
        1 / (((m + 1 : Nat) : Real) * epsilon) :=
    one_div_le_one_div_of_le (mul_pos hn hepsilon) hnqepsilon
  calc
    (∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
      (if 0 < j ∧ j < m then
        (j : Real)⁻¹ + ((m - j : Nat) : Real)⁻¹
      else 0)) ≤
      ∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
        ((if 0 < j then (j : Real)⁻¹ else 0) +
          (if 0 < m - j then ((m - j : Nat) : Real)⁻¹ else 0)) := by
            apply Finset.sum_le_sum
            intro j hj
            apply mul_le_mul_of_nonneg_left (hinter j)
            dsimp [binomialWeight]
            positivity
    _ = (∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
          (if 0 < j then (j : Real)⁻¹ else 0)) +
        ∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
          (if 0 < m - j then ((m - j : Nat) : Real)⁻¹ else 0) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            ring
    _ ≤ 2 / (((m + 1 : Nat) : Real) * p) +
        2 / (((m + 1 : Nat) : Real) * (1 - p)) := by
          rw [hfail]
          linarith
    _ ≤ 4 / (((m + 1 : Nat) : Real) * epsilon) := by
      rw [show 2 / (((m + 1 : Nat) : Real) * p) =
          2 * (1 / (((m + 1 : Nat) : Real) * p)) by ring,
        show 2 / (((m + 1 : Nat) : Real) * (1 - p)) =
          2 * (1 / (((m + 1 : Nat) : Real) * (1 - p))) by ring,
        show 4 / (((m + 1 : Nat) : Real) * epsilon) =
          4 * (1 / (((m + 1 : Nat) : Real) * epsilon)) by ring]
      linarith

end Causalean.Mathlib.Probability
