/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Finite-sample confidence intervals from concentration tails

Inverting the two-sided Hoeffding and (oracle) Bernstein tail bounds of
`Causalean.Stat.Concentration` into *finite-sample* confidence half-widths.  Given a
confidence parameter `δ ∈ (0, 1]`, each result produces an explicit half-width
`w(n, δ)` and proves the **miss-probability guarantee**

    P( w ≤ |X̄ₙ − m| ) ≤ δ,

i.e. with probability at least `1 − δ` the population mean `m = ∫ f ∂P` lies in
the random interval `[X̄ₙ − w, X̄ₙ + w]`.  This is the finite-sample analogue of
the asymptotic Wald interval (`Stat/Inference/`); unlike the latter it holds at
every fixed `n`, not only in the limit.

## Contents

* `hoeffdingCIHalfWidth a b n δ = (b − a) · √(log(2/δ) / (2n))` — the Hoeffding
  half-width, valid for any `[a,b]`-valued statistic.
* `hoeffding_ci_miss` — `P(w ≤ |X̄ₙ − m|) ≤ δ`, by inverting `hoeffding_abs_ge`.
* `hoeffding_ci_cover` — coverage complement: `1 − δ ≤ P(|X̄ₙ − m| < w)`.
* `bernsteinCIHalfWidth c σ n δ = 2σ·√(log(2/δ)/n) + 2c·(log(2/δ)/n)` — the
  variance-adaptive Bernstein half-width.  When the variance proxy `σ²` is small
  this is much tighter than Hoeffding's `O((b−a)/√n)`: its leading term is
  `2σ√(log(2/δ)/n)` with a fast `O(1/n)` correction.
* `bernstein_ci_miss` — `P(w ≤ |X̄ₙ − m|) ≤ δ`, by inverting `bernstein_abs_ge`.
* `bernstein_ci_cover` — coverage complement: `1 − δ ≤ P(|X̄ₙ − m| < w)`.

The Bernstein exponent inversion is exact up to a nonnegative slack: writing
`L = log(2/δ)` and `s = √(L/n)`, the chosen half-width satisfies
`n·w² − 2Lc·w − 4Lσ² = 4nσc·s³ ≥ 0`, which is precisely the quadratic
condition making the tail `≤ δ`.
-/

import Causalean.Stat.Concentration.TailBounds.Bernstein

/-! # Concentration confidence intervals

This file inverts the two-sided Hoeffding and Bernstein sample-mean tail
bounds into explicit finite-sample confidence intervals. It defines
`hoeffdingCIHalfWidth` and `bernsteinCIHalfWidth`, proves miss-probability
forms `hoeffding_ci_miss` and `bernstein_ci_miss`, and proves the corresponding
coverage forms `hoeffding_ci_cover` and `bernstein_ci_cover`.
-/

namespace Causalean.Stat.Concentration

open MeasureTheory ProbabilityTheory Real

variable {Ω X' : Type*} [MeasurableSpace Ω] [MeasurableSpace X']
  {μ : Measure Ω} {P : Measure X'}

/-- The two-sided **Hoeffding confidence half-width** at level `δ` for an
`[a, b]`-valued statistic and sample size `n`:
`(b − a)·√(log(2/δ) / (2n))`. -/
noncomputable def hoeffdingCIHalfWidth (a b : ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  (b - a) * Real.sqrt (Real.log (2 / δ) / (2 * n))

/-- The two-sided **Bernstein confidence half-width** at level `δ` for a
statistic with range bound `c` (`|f − m| ≤ c`) and variance proxy `σ²`:
`2σ·√(log(2/δ)/n) + 2c·(log(2/δ)/n)`.  Variance-adaptive: the leading term
scales with `σ`, not the range `c`. -/
noncomputable def bernsteinCIHalfWidth (c σ : ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  2 * σ * Real.sqrt (Real.log (2 / δ) / n) + 2 * c * (Real.log (2 / δ) / n)

/-- `log (2/δ) ≥ 0` for `0 < δ ≤ 1` (since then `2/δ ≥ 2 ≥ 1`). -/
private lemma log_two_div_nonneg {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    0 ≤ Real.log (2 / δ) := by
  apply Real.log_nonneg
  rw [le_div_iff₀ hδ0]; linarith

/-- `exp (-(log (2/δ))) = δ/2` for `0 < δ`. -/
private lemma exp_neg_log_two_div {δ : ℝ} (hδ0 : 0 < δ) :
    Real.exp (-(Real.log (2 / δ))) = δ / 2 := by
  rw [Real.exp_neg, Real.exp_log (by positivity)]
  field_simp

/-- **Finite-sample Hoeffding confidence interval (miss-probability form).**
For an `[a, b]`-valued statistic `f` (`a < b`) and any confidence level
`δ ∈ (0, 1]`, the population mean `m = ∫ f ∂P` lies outside the random interval
`[X̄ₙ − w, X̄ₙ + w]` with probability at most `δ`, where
`w = hoeffdingCIHalfWidth a b n δ`. -/
theorem hoeffding_ci_miss (S : IIDSample Ω X' μ P) {f : X' → ℝ} (hf : Measurable f)
    {a b : ℝ} (hab : a < b) (hbound : ∀ᵐ x ∂P, f x ∈ Set.Icc a b)
    (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    μ.real {ω | hoeffdingCIHalfWidth a b n δ ≤ |S.sampleMean f n ω - ∫ x, f x ∂P|}
      ≤ δ := by
  set L : ℝ := Real.log (2 / δ) with hLdef
  set w : ℝ := hoeffdingCIHalfWidth a b n δ with hwdef
  have hLnn : 0 ≤ L := log_two_div_nonneg hδ0 hδ1
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hba' : (b - a) ≠ 0 := ne_of_gt hba
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hwnn : 0 ≤ w := by
    rw [hwdef, hoeffdingCIHalfWidth]
    exact mul_nonneg (le_of_lt hba) (Real.sqrt_nonneg _)
  have harg : (0 : ℝ) ≤ L / (2 * n) := by positivity
  have hw2 : w ^ 2 = (b - a) ^ 2 * (L / (2 * n)) := by
    rw [hwdef, hoeffdingCIHalfWidth, ← hLdef, mul_pow, Real.sq_sqrt harg]
  have htail := hoeffding_abs_ge S hf hab hbound n hn hwnn
  refine htail.trans (le_of_eq ?_)
  have hexp : -2 * (n : ℝ) * w ^ 2 / (b - a) ^ 2 = -L := by
    rw [hw2]; field_simp
  rw [hexp, hLdef, exp_neg_log_two_div hδ0]; ring

/-- **Finite-sample Bernstein confidence interval (miss-probability form).**
For a statistic `f` with population mean `m = ∫ f ∂P`, range bound `|f − m| ≤ c`
and variance `∫ (f − m)² ≤ σ²` (with `0 < σ`), and any confidence level
`δ ∈ (0, 1]`, the mean `m` lies outside `[X̄ₙ − w, X̄ₙ + w]` with probability at
most `δ`, where `w = bernsteinCIHalfWidth c σ n δ`.

Variance-adaptive: the half-width's leading term is `2σ√(log(2/δ)/n)`, so for
low-variance statistics it is far tighter than the Hoeffding interval. -/
theorem bernstein_ci_miss (S : IIDSample Ω X' μ P) {f : X' → ℝ} (hf : Measurable f)
    (hfint : Integrable f P) {c σ : ℝ} (hc : 0 ≤ c) (hσ : 0 < σ)
    (hbound : ∀ᵐ x ∂P, |f x - ∫ y, f y ∂P| ≤ c)
    (hvar : ∫ x, (f x - ∫ y, f y ∂P) ^ 2 ∂P ≤ σ ^ 2)
    (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    μ.real {ω | bernsteinCIHalfWidth c σ n δ ≤ |S.sampleMean f n ω - ∫ x, f x ∂P|}
      ≤ δ := by
  set L : ℝ := Real.log (2 / δ) with hLdef
  have hLnn : 0 ≤ L := log_two_div_nonneg hδ0 hδ1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hσnn : 0 ≤ σ := le_of_lt hσ
  have hσ2 : (0 : ℝ) < σ ^ 2 := by positivity
  set s : ℝ := Real.sqrt (L / n) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = L / n := Real.sq_sqrt (by positivity)
  have hLs : L = (n : ℝ) * s ^ 2 := by rw [hs2]; field_simp
  set w : ℝ := bernsteinCIHalfWidth c σ n δ with hwdef
  have hw' : w = 2 * σ * s + 2 * c * s ^ 2 := by
    rw [hwdef, bernsteinCIHalfWidth]
    simp only [← hLdef, ← hsdef]
    rw [← hs2]
  have hwnn : 0 ≤ w := by
    rw [hw']
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hσnn) hs0)
      (mul_nonneg (mul_nonneg (by norm_num) hc) (pow_nonneg hs0 2))
  have htail := bernstein_abs_ge S hf hfint hc hσnn hbound hvar n hn hwnn
  refine htail.trans ?_
  have hcw : 0 ≤ c * w := mul_nonneg hc hwnn
  have hDpos : (0 : ℝ) < 2 * (2 * σ ^ 2 + c * w) := by nlinarith [hσ2, hcw]
  have hquad : (n : ℝ) * w ^ 2 - 2 * L * c * w - 4 * L * σ ^ 2
      = 4 * (n : ℝ) * σ * c * s ^ 3 := by
    rw [hw', hLs]; ring
  have hquad_nn : 0 ≤ (n : ℝ) * w ^ 2 - 2 * L * c * w - 4 * L * σ ^ 2 := by
    rw [hquad]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hσnn) hc) (pow_nonneg hs0 3)
  have hge : L ≤ (n : ℝ) * w ^ 2 / (2 * (2 * σ ^ 2 + c * w)) := by
    rw [le_div_iff₀ hDpos]; nlinarith [hquad_nn]
  have hmono : Real.exp (-(n : ℝ) * w ^ 2 / (2 * (2 * σ ^ 2 + c * w)))
      ≤ Real.exp (-(Real.log (2 / δ))) := by
    apply Real.exp_le_exp.mpr
    rw [neg_mul, neg_div, ← hLdef]
    linarith [hge]
  calc 2 * Real.exp (-(n : ℝ) * w ^ 2 / (2 * (2 * σ ^ 2 + c * w)))
      ≤ 2 * Real.exp (-(Real.log (2 / δ))) := by linarith [hmono]
    _ = 2 * (δ / 2) := by rw [exp_neg_log_two_div hδ0]
    _ = δ := by ring

/-- Measurability of the sample mean `X̄ₙ = n⁻¹ ∑ᵢ f (Zᵢ)`, established inline so
this file need not import the limit layer. -/
private lemma measurable_sampleMean (S : IIDSample Ω X' μ P) {f : X' → ℝ}
    (hf : Measurable f) (n : ℕ) : Measurable (S.sampleMean f n) := by
  change Measurable (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f (S.Z i ω))
  exact (Finset.measurable_sum _ (fun i _ => hf.comp (S.meas i))).const_mul _

/-- **Finite-sample Hoeffding confidence interval (coverage form).**
The complement of `hoeffding_ci_miss`: the population mean `m = ∫ f ∂P` lies
strictly inside the random interval `(X̄ₙ − w, X̄ₙ + w)` with probability at least
`1 − δ`, where `w = hoeffdingCIHalfWidth a b n δ`. -/
theorem hoeffding_ci_cover (S : IIDSample Ω X' μ P) {f : X' → ℝ} (hf : Measurable f)
    {a b : ℝ} (hab : a < b) (hbound : ∀ᵐ x ∂P, f x ∈ Set.Icc a b)
    (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 - δ ≤
      μ.real {ω | |S.sampleMean f n ω - ∫ x, f x ∂P| < hoeffdingCIHalfWidth a b n δ} := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  have hSM : Measurable (S.sampleMean f n) := measurable_sampleMean S hf n
  set m : ℝ := ∫ x, f x ∂P with hmdef
  set w : ℝ := hoeffdingCIHalfWidth a b n δ with hwdef
  have hMmeas : MeasurableSet {ω | w ≤ |S.sampleMean f n ω - m|} :=
    measurableSet_le measurable_const ((hSM.sub measurable_const).abs)
  have hcompl : {ω | |S.sampleMean f n ω - m| < w}
      = {ω | w ≤ |S.sampleMean f n ω - m|}ᶜ := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  have hmiss := hoeffding_ci_miss S hf hab hbound n hn hδ0 hδ1
  rw [hcompl, measureReal_compl hMmeas, probReal_univ]
  linarith [hmiss]

/-- **Finite-sample Bernstein confidence interval (coverage form).**
The complement of `bernstein_ci_miss`: the population mean `m = ∫ f ∂P` lies
strictly inside the random interval `(X̄ₙ − w, X̄ₙ + w)` with probability at least
`1 − δ`, where `w = bernsteinCIHalfWidth c σ n δ`. -/
theorem bernstein_ci_cover (S : IIDSample Ω X' μ P) {f : X' → ℝ} (hf : Measurable f)
    (hfint : Integrable f P) {c σ : ℝ} (hc : 0 ≤ c) (hσ : 0 < σ)
    (hbound : ∀ᵐ x ∂P, |f x - ∫ y, f y ∂P| ≤ c)
    (hvar : ∫ x, (f x - ∫ y, f y ∂P) ^ 2 ∂P ≤ σ ^ 2)
    (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 - δ ≤
      μ.real {ω | |S.sampleMean f n ω - ∫ x, f x ∂P| < bernsteinCIHalfWidth c σ n δ} := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  have hSM : Measurable (S.sampleMean f n) := measurable_sampleMean S hf n
  set m : ℝ := ∫ x, f x ∂P with hmdef
  set w : ℝ := bernsteinCIHalfWidth c σ n δ with hwdef
  have hMmeas : MeasurableSet {ω | w ≤ |S.sampleMean f n ω - m|} :=
    measurableSet_le measurable_const ((hSM.sub measurable_const).abs)
  have hcompl : {ω | |S.sampleMean f n ω - m| < w}
      = {ω | w ≤ |S.sampleMean f n ω - m|}ᶜ := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  have hmiss := bernstein_ci_miss S hf hfint hc hσ hbound hvar n hn hδ0 hδ1
  rw [hcompl, measureReal_compl hMmeas, probReal_univ]
  linarith [hmiss]

end Causalean.Stat.Concentration
