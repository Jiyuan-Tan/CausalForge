/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Empirical (sample-variance) Bernstein infrastructure

This file develops the **sample variance** of an i.i.d. sample, an **elementary,
fully rigorous** population-variance concentration bound, and a *data-driven*
Bernstein confidence interval built on top of it.

The full Maurer–Pontil empirical-Bernstein bound is research-level and out of
scope; we take the *elementary* route instead.  Writing `m := ∫ f ∂P`,
`σ² := ∫ (f − m)² ∂P`, `X̄ₙ := S.sampleMean f n` and `V̂ₙ := S.sampleVariance f n`,
the population–sample variance gap decomposes (using `σ² = μ₂ − m²` with
`μ₂ := ∫ f² ∂P`, and `V̂ₙ = M̂₂ − X̄ₙ²` with `M̂₂ := (1/n) Σ f(Zᵢ)²`) as

    σ² − V̂ₙ = (μ₂ − M̂₂) + (X̄ₙ² − m²).

With `f` valued in `[a, b]` a.e. and `M := max |a| |b|` (so `|f| ≤ M`, hence
`|m|, |X̄ₙ| ≤ M` and `f² ∈ [0, M²]`), each gap term is controlled by a Hoeffding
deviation at level `δ/2`.  Writing `d := √(log(4/δ) / (2n))`:

* `μ₂ − M̂₂` is the centered deviation of `g := f²` on `[0, M²]`, so on a good
  event `|μ₂ − M̂₂| ≤ M²·d`;
* `X̄ₙ² − m² = (X̄ₙ − m)(X̄ₙ + m)` with `|X̄ₙ + m| ≤ 2M`, and on a good event
  `|X̄ₙ − m| ≤ (b − a)·d`, so `|X̄ₙ² − m²| ≤ 2M(b − a)·d`.

A union bound over the two Hoeffding tail events (each at level `δ/2`) gives the
*deterministic* slack

    empiricalVarianceSlack a b n δ := M²·d + 2 M (b − a)·d

and `empirical_variance_concentration`: `P(V̂ₙ + τ < σ²) ≤ δ`.  Feeding the
resulting `σ ≤ √(V̂ₙ + τ)` into the (oracle) Bernstein half-width then yields a
confidence interval whose width is computed from the **observed** sample variance
(`empirical_bernstein_ci_miss`, total miss probability `≤ 2δ`).

The constants here are looser than Maurer–Pontil's because the second-moment
Hoeffding step is wasteful, but the route is elementary and keeps the
data-driven interval explicit.

## Contents

* `IIDSample.sampleVariance` / `sampleVariance_nonneg` / `measurable_sampleVariance`
  / `sampleVariance_eq` — the `1/n`-normalised empirical variance and basics.
* `empiricalVarianceSlack` / `empirical_variance_concentration` — the deterministic
  slack `τ` and the data-driven variance bound `P(V̂ₙ + τ < σ²) ≤ δ`.
* `empirical_bernstein_ci_miss` — a Bernstein-style confidence interval whose
  half-width uses `√(V̂ₙ + τ)` in place of an oracle `σ`.
-/

import Causalean.Stat.Concentration.UniformDeviation.ConfidenceInterval

/-! # Empirical Bernstein confidence intervals

This file develops the sample-variance layer needed for data-driven Bernstein
intervals. It defines `IIDSample.sampleVariance` and proves its nonnegativity,
measurability, and computational identity; defines the deterministic slack
`empiricalVarianceSlack`; proves `empirical_variance_concentration`, a
high-probability upper bound on the population variance by observed sample
variance plus slack; and proves `empirical_bernstein_ci_miss`, an empirical
Bernstein miss-probability theorem whose half-width is
`empiricalBernsteinCIHalfWidth`.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Real

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X} {f : X → ℝ}

/-! ## Sample variance infrastructure

These declarations live in namespace `Causalean.Stat` (alongside
`IIDSample.sampleMean`) so dot-notation `S.sampleVariance` resolves through the
structure's namespace. -/

/-- The **sample variance** of `f` over the first `n` observations, normalised by
`1/n`:
`V̂ₙ(ω) = (1/n) ∑_{i<n} (f (Zᵢ ω) − X̄ₙ(ω))²`,
where `X̄ₙ = S.sampleMean f n` is the sample mean.  (This is the biased estimator;
the unbiased one would divide by `n − 1`.) -/
noncomputable def IIDSample.sampleVariance (S : IIDSample Ω X μ P) (f : X → ℝ)
    (n : ℕ) : Ω → ℝ :=
  fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
    (f (S.Z i ω) - S.sampleMean f n ω) ^ 2

/-- The sample variance is nonnegative: it is `1/n` times a sum of squares. -/
theorem IIDSample.sampleVariance_nonneg (S : IIDSample Ω X μ P) (f : X → ℝ)
    (n : ℕ) (ω : Ω) : 0 ≤ S.sampleVariance f n ω := by
  unfold IIDSample.sampleVariance
  apply mul_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro i _
    positivity

/-- The sample variance is a measurable function of `ω`. -/
theorem IIDSample.measurable_sampleVariance (S : IIDSample Ω X μ P)
    (hf : Measurable f) (n : ℕ) : Measurable (S.sampleVariance f n) := by
  unfold IIDSample.sampleVariance
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  have hmean : Measurable (S.sampleMean f n) := by
    unfold IIDSample.sampleMean
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro j _
    exact hf.comp (S.meas j)
  exact ((hf.comp (S.meas i)).sub hmean).pow_const 2

/-- The classical computational form of the sample variance: empirical second
moment minus the square of the empirical mean,
`V̂ₙ(ω) = (1/n) ∑_{i<n} f(Zᵢ ω)² − X̄ₙ(ω)²`. -/
theorem IIDSample.sampleVariance_eq (S : IIDSample Ω X μ P) (f : X → ℝ)
    (n : ℕ) (ω : Ω) :
    S.sampleVariance f n ω
      = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (f (S.Z i ω)) ^ 2
        - (S.sampleMean f n ω) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [IIDSample.sampleVariance, IIDSample.sampleMean]
  have hn' : (n : ℝ) ≠ 0 := by positivity
  set m := S.sampleMean f n ω with hm
  have hsum_mean : ∑ i ∈ Finset.range n, f (S.Z i ω) = (n : ℝ) * m := by
    rw [hm, IIDSample.sampleMean]
    field_simp
  have hexpand : ∀ i ∈ Finset.range n,
      (f (S.Z i ω) - m) ^ 2
        = (f (S.Z i ω)) ^ 2 - 2 * m * f (S.Z i ω) + m ^ 2 := by
    intro i _; ring
  rw [IIDSample.sampleVariance, ← hm, Finset.sum_congr rfl hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum, hsum_mean]
  field_simp
  ring

end Causalean.Stat

namespace Causalean.Stat.Concentration

open MeasureTheory ProbabilityTheory Real

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X} {f : X → ℝ}

/-! ## Data-driven population-variance bound -/

/-- The deterministic slack added to the observed sample variance to upper-bound
the population variance with probability `≥ 1 − δ`.  With `M := max |a| |b|` and
`d := √(log(4/δ)/(2n))` the (level `δ/2`) Hoeffding deviation factor, it is
`M²·d + 2 M (b − a)·d`.  The first term controls the second-moment deviation
(`f²` on `[0, M²]`), the second the squared-mean deviation
(`|X̄ₙ² − m²| ≤ 2M·|X̄ₙ − m|`). -/
noncomputable def empiricalVarianceSlack (a b : ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  (max |a| |b|) ^ 2 * Real.sqrt (Real.log (4 / δ) / (2 * n))
    + 2 * (max |a| |b|) * (b - a) * Real.sqrt (Real.log (4 / δ) / (2 * n))

/-- The half-width Hoeffding deviation at level `δ/2` for an `[a,b]`-range
statistic is `(b − a) · √(log(4/δ)/(2n))`; we record the identity
`hoeffdingCIHalfWidth a b n (δ/2) = (b−a) · d`. -/
private lemma hoeffdingCIHalfWidth_half (a b : ℝ) (n : ℕ) {δ : ℝ} (_hδ0 : 0 < δ) :
    hoeffdingCIHalfWidth a b n (δ / 2)
      = (b - a) * Real.sqrt (Real.log (4 / δ) / (2 * n)) := by
  rw [hoeffdingCIHalfWidth]
  congr 3
  rw [div_div_eq_mul_div]
  ring_nf

/-- **Data-driven population-variance bound.**  For an `[a, b]`-valued statistic
`f` (`a < b`) and any confidence level `δ ∈ (0, 1]`, with probability `≥ 1 − δ`
the population variance `σ² = ∫ (f − ∫f)² ∂P` is bounded by the *observed* sample
variance plus the deterministic slack `empiricalVarianceSlack a b n δ`.  Stated in
miss form: the event `V̂ₙ + τ < σ²` has probability at most `δ`. -/
theorem empirical_variance_concentration (S : IIDSample Ω X μ P) {f : X → ℝ}
    (hf : Measurable f) {a b : ℝ} (hab : a < b)
    (hbound : ∀ᵐ x ∂P, f x ∈ Set.Icc a b)
    (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    μ.real {ω | S.sampleVariance f n ω + empiricalVarianceSlack a b n δ
        < ∫ x, (f x - ∫ y, f y ∂P) ^ 2 ∂P} ≤ δ := by
  classical
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  haveI hP : IsProbabilityMeasure P := by
    rw [← S.law]; exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  set m : ℝ := ∫ x, f x ∂P with hmdef
  set M : ℝ := max |a| |b| with hMdef
  set d : ℝ := Real.sqrt (Real.log (4 / δ) / (2 * n)) with hddef
  have hδ20 : (0 : ℝ) < δ / 2 := by positivity
  have hδ21 : δ / 2 ≤ 1 := by linarith
  have hMnn : 0 ≤ M := le_trans (abs_nonneg a) (le_max_left _ _)
  have hg := hf.pow_const 2
  -- `|f x| ≤ M` a.e.
  have habs : ∀ᵐ x ∂P, |f x| ≤ M := by
    filter_upwards [hbound] with x hx
    rw [hMdef, abs_le]
    refine ⟨?_, le_trans hx.2 (le_trans (le_abs_self b) (le_max_right _ _))⟩
    have : -|a| ≤ a := neg_abs_le a
    linarith [le_trans (neg_le_neg (le_max_left |a| |b|)) this, hx.1]
  -- integrability of `f` and `f²` (bounded on a probability measure)
  have hfint : Integrable f P :=
    Integrable.mono' (integrable_const M) hf.aestronglyMeasurable
      (by filter_upwards [habs] with x hx; rwa [Real.norm_eq_abs])
  have hf2int : Integrable (fun x => (f x) ^ 2) P :=
    Integrable.mono' (integrable_const (M ^ 2)) hg.aestronglyMeasurable
      (by filter_upwards [habs] with x hx
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          nlinarith [hx, abs_nonneg (f x), sq_abs (f x)])
  -- `|m| ≤ M`
  have hm_abs : |m| ≤ M := by
    rw [hmdef]
    calc |∫ x, f x ∂P| ≤ ∫ x, |f x| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ _, M ∂P := integral_mono_ae hfint.abs (integrable_const M) habs
      _ = M := by rw [integral_const]; simp
  -- population variance identity `σ² = μ₂ − m²`
  set μ₂ : ℝ := ∫ x, (f x) ^ 2 ∂P with hμ₂def
  have hvar_id : (∫ x, (f x - m) ^ 2 ∂P) = μ₂ - m ^ 2 := by
    have hexp : ∀ x, (f x - m) ^ 2 = (f x) ^ 2 - 2 * m * f x + m ^ 2 := fun x => by ring
    simp only [hexp]
    rw [integral_add (by exact (hf2int.sub (hfint.const_mul (2 * m))))
        (integrable_const _), integral_sub hf2int (hfint.const_mul (2 * m)),
        integral_const_mul, integral_const]
    simp only [hμ₂def, hmdef]
    simp
    ring
  -- `g := f²` ranges in `[0, M²]` a.e.
  have hg_bound : ∀ᵐ x ∂P, (fun x => (f x) ^ 2) x ∈ Set.Icc (0 : ℝ) (M ^ 2) := by
    filter_upwards [habs] with x hx
    exact ⟨sq_nonneg _, by nlinarith [hx, abs_nonneg (f x), sq_abs (f x)]⟩
  -- Since `a < b`, the range bound `M = max |a| |b|` is strictly positive.
  have hMpos : 0 < M := by
    rw [hMdef]
    rcases le_total 0 b with hb | hb
    · -- 0 ≤ b
      rcases eq_or_lt_of_le hb with hb0 | hb0
      · -- b = 0, so a < 0, hence |a| > 0
        have : a < 0 := by rw [hb0]; exact hab
        exact lt_of_lt_of_le (by rw [abs_of_neg this]; linarith) (le_max_left _ _)
      · exact lt_of_lt_of_le (by rw [abs_of_pos hb0]; exact hb0) (le_max_right _ _)
    · -- b ≤ 0, so a < 0, hence |a| > 0
      have ha : a < 0 := lt_of_lt_of_le hab hb
      exact lt_of_lt_of_le (by rw [abs_of_neg ha]; linarith) (le_max_left _ _)
  have hMsq : (0 : ℝ) < M ^ 2 := by positivity
  -- Hoeffding tail (level δ/2) for `f` and for `g = f²`.
  -- Event B: deviation of `f` (range `[a,b]`) at level δ/2
  have hmissB : μ.real {ω | (b - a) * d ≤ |S.sampleMean f n ω - m|} ≤ δ / 2 := by
    have := hoeffding_ci_miss S hf hab hbound n hn hδ20 hδ21
    rwa [hoeffdingCIHalfWidth_half a b n hδ0, ← hddef, ← hmdef] at this
  -- Event A: deviation of `g = f²` (range `[0,M²]`) at level δ/2
  have hmissA : μ.real {ω | M ^ 2 * d ≤
      |S.sampleMean (fun x => (f x) ^ 2) n ω - μ₂|} ≤ δ / 2 := by
    have := hoeffding_ci_miss S hg (show (0:ℝ) < M ^ 2 from hMsq) hg_bound n hn hδ20 hδ21
    rwa [hoeffdingCIHalfWidth_half 0 (M ^ 2) n hδ0, sub_zero, ← hddef, ← hμ₂def] at this
  -- a.e. each `f (Zᵢ)` is `≤ M` in absolute value, hence so is the sample mean.
  have hMnR : (0 : ℝ) < n := by exact_mod_cast hn
  have haeXbar : ∀ᵐ ω ∂μ, |S.sampleMean f n ω| ≤ M := by
    have hperterm : ∀ i, ∀ᵐ ω ∂μ, |f (S.Z i ω)| ≤ M := by
      intro i
      have hb2 := habs
      rw [← S.map_eq i] at hb2
      exact (ae_map_iff (S.meas i).aemeasurable
        (measurableSet_le hf.abs measurable_const)).mp hb2
    have hall : ∀ᵐ ω ∂μ, ∀ i ∈ Finset.range n, |f (S.Z i ω)| ≤ M :=
      (ae_ball_iff (Finset.range n).countable_toSet).mpr (fun i _ => hperterm i)
    filter_upwards [hall] with ω hω
    rw [IIDSample.sampleMean, abs_mul, abs_inv, Nat.abs_cast]
    rw [inv_mul_le_iff₀ hMnR]
    calc |∑ i ∈ Finset.range n, f (S.Z i ω)|
        ≤ ∑ i ∈ Finset.range n, |f (S.Z i ω)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range n, M := Finset.sum_le_sum (fun i hi => hω i hi)
      _ = (n : ℝ) * M := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  set N : Set Ω := {ω | M < |S.sampleMean f n ω|} with hNdef
  have hNnull : μ N = 0 := by
    rw [hNdef]
    have hcompl : {ω | M < |S.sampleMean f n ω|} = {ω | |S.sampleMean f n ω| ≤ M}ᶜ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    rw [hcompl]
    exact haeXbar
  -- The bad variance event is contained in the union of B, A, and the null set N.
  have hsub : {ω | S.sampleVariance f n ω + empiricalVarianceSlack a b n δ
        < ∫ x, (f x - m) ^ 2 ∂P}
      ⊆ ({ω | (b - a) * d ≤ |S.sampleMean f n ω - m|}
        ∪ {ω | M ^ 2 * d ≤ |S.sampleMean (fun x => (f x) ^ 2) n ω - μ₂|}) ∪ N := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    by_contra hcon
    rw [Set.mem_union, not_or, Set.mem_union, not_or] at hcon
    obtain ⟨⟨hB', hA'⟩, hN'⟩ := hcon
    simp only [Set.mem_setOf_eq, not_le] at hB' hA'
    have hXbar_abs : |S.sampleMean f n ω| ≤ M := by
      rw [hNdef, Set.mem_setOf_eq, not_lt] at hN'; exact hN'
    have hB := hB'
    have hA := hA'
    -- expand sample variance: V̂ₙ = Mhat2 − X̄ₙ²
    have hVeq := S.sampleVariance_eq f n ω
    set Xbar : ℝ := S.sampleMean f n ω with hXbardef
    set Mhat2 : ℝ := S.sampleMean (fun x => (f x) ^ 2) n ω with hM2def
    have hVeq' : S.sampleVariance f n ω = Mhat2 - Xbar ^ 2 := by
      rw [hVeq, hM2def, IIDSample.sampleMean, hXbardef]
    rw [hvar_id, hVeq'] at hω
    -- σ² − V̂ₙ = (μ₂ − Mhat2) + (Xbar² − m²)
    have hsplit : μ₂ - m ^ 2 - (Mhat2 - Xbar ^ 2)
        = (μ₂ - Mhat2) + (Xbar ^ 2 - m ^ 2) := by ring
    have hsq_diff : |Xbar ^ 2 - m ^ 2| ≤ 2 * M * ((b - a) * d) := by
      have hfac : Xbar ^ 2 - m ^ 2 = (Xbar - m) * (Xbar + m) := by ring
      rw [hfac, abs_mul]
      have h1 : |Xbar - m| ≤ (b - a) * d := le_of_lt hB
      have h2 : |Xbar + m| ≤ 2 * M := by
        calc |Xbar + m| ≤ |Xbar| + |m| := abs_add_le _ _
          _ ≤ M + M := add_le_add hXbar_abs hm_abs
          _ = 2 * M := by ring
      have hbd_nn : 0 ≤ (b - a) * d := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
      calc |Xbar - m| * |Xbar + m| ≤ ((b - a) * d) * (2 * M) :=
            mul_le_mul h1 h2 (abs_nonneg _) hbd_nn
        _ = 2 * M * ((b - a) * d) := by ring
    have hm2_diff : |μ₂ - Mhat2| ≤ M ^ 2 * d := by
      rw [abs_sub_comm]; exact le_of_lt hA
    have hτ : empiricalVarianceSlack a b n δ = M ^ 2 * d + 2 * M * (b - a) * d := by
      rw [empiricalVarianceSlack, ← hMdef, ← hddef]
    have hchain : μ₂ - m ^ 2 - (Mhat2 - Xbar ^ 2)
        ≤ M ^ 2 * d + 2 * M * ((b - a) * d) := by
      rw [hsplit]
      calc (μ₂ - Mhat2) + (Xbar ^ 2 - m ^ 2)
          ≤ |μ₂ - Mhat2| + |Xbar ^ 2 - m ^ 2| := by
            gcongr <;> exact le_abs_self _
        _ ≤ M ^ 2 * d + 2 * M * ((b - a) * d) := add_le_add hm2_diff hsq_diff
    rw [hτ] at hω
    nlinarith [hω, hchain]
  -- conclude via union bound (the null set N contributes 0)
  calc μ.real {ω | S.sampleVariance f n ω + empiricalVarianceSlack a b n δ
          < ∫ x, (f x - ∫ y, f y ∂P) ^ 2 ∂P}
      = μ.real {ω | S.sampleVariance f n ω + empiricalVarianceSlack a b n δ
          < ∫ x, (f x - m) ^ 2 ∂P} := by rw [hmdef]
    _ ≤ μ.real (({ω | (b - a) * d ≤ |S.sampleMean f n ω - m|}
          ∪ {ω | M ^ 2 * d ≤ |S.sampleMean (fun x => (f x) ^ 2) n ω - μ₂|}) ∪ N) :=
        measureReal_mono hsub
    _ ≤ μ.real ({ω | (b - a) * d ≤ |S.sampleMean f n ω - m|}
          ∪ {ω | M ^ 2 * d ≤ |S.sampleMean (fun x => (f x) ^ 2) n ω - μ₂|})
          + μ.real N := measureReal_union_le _ _
    _ ≤ (μ.real {ω | (b - a) * d ≤ |S.sampleMean f n ω - m|}
          + μ.real {ω | M ^ 2 * d ≤
            |S.sampleMean (fun x => (f x) ^ 2) n ω - μ₂|}) + μ.real N := by
        gcongr; exact measureReal_union_le _ _
    _ ≤ (δ / 2 + δ / 2) + 0 := by
        have hN0 : μ.real N = 0 := by rw [measureReal_def, hNnull]; simp
        exact add_le_add (add_le_add hmissB hmissA) (le_of_eq hN0)
    _ = δ := by ring

/-! ## Data-driven Bernstein confidence interval -/

/-- The **data-driven Bernstein half-width**: the Bernstein half-width with the
oracle standard deviation `σ` replaced by the *observed* upper bound
`√(V̂ₙ(ω) + τ)`, where `τ = empiricalVarianceSlack a b n δ`.  This is a function of
`ω` (it depends on the sample through `V̂ₙ`). -/
noncomputable def empiricalBernsteinCIHalfWidth (S : IIDSample Ω X μ P) (f : X → ℝ)
    (a b : ℝ) (c : ℝ) (n : ℕ) (δ : ℝ) : Ω → ℝ :=
  fun ω => bernsteinCIHalfWidth c
    (Real.sqrt (S.sampleVariance f n ω + empiricalVarianceSlack a b n δ)) n δ

/-- `bernsteinCIHalfWidth c · n δ` is monotone in the standard-deviation argument
`σ` (for `0 ≤ log(2/δ)`), since both summands are nonnegative-coefficient affine
in `σ` and `√(·)·`. -/
private lemma bernsteinCIHalfWidth_mono_sigma {c : ℝ} {n : ℕ}
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {σ σ' : ℝ} (hσσ' : σ ≤ σ') :
    bernsteinCIHalfWidth c σ n δ ≤ bernsteinCIHalfWidth c σ' n δ := by
  unfold bernsteinCIHalfWidth
  have hL : 0 ≤ Real.log (2 / δ) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hδ0]; linarith
  gcongr

/-- **Data-driven (empirical) Bernstein confidence interval, miss-probability
form.**  For an `[a,b]`-valued statistic `f` (`a < b`) with population mean
`m = ∫ f ∂P`, range bound `|f − m| ≤ c`, and *positive* population variance
`σ² := ∫ (f − m)² ∂P` (`0 < σ²`), the population mean `m` lies outside the random,
**data-driven** interval `[X̄ₙ − ŵ(ω), X̄ₙ + ŵ(ω)]` — whose half-width
`ŵ(ω) = empiricalBernsteinCIHalfWidth S f a b c n δ ω` is computed from the
*observed* sample variance via `√(V̂ₙ(ω) + τ)` — with probability at most `2δ`.

The proof unions two level-`δ` failure events: the oracle Bernstein miss (with the
true `σ = √σ²`) and the variance-bound failure `σ² > V̂ₙ + τ`.  On the good
variance event `σ ≤ √(V̂ₙ + τ)`, so monotonicity of the Bernstein half-width in `σ`
makes the data-driven width at least the oracle width, hence the data-driven miss
event is contained in the oracle miss event. -/
theorem empirical_bernstein_ci_miss (S : IIDSample Ω X μ P) {f : X → ℝ}
    (hf : Measurable f) {a b : ℝ} (hab : a < b)
    (hbound_ab : ∀ᵐ x ∂P, f x ∈ Set.Icc a b)
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ᵐ x ∂P, |f x - ∫ y, f y ∂P| ≤ c)
    (hposvar : 0 < ∫ x, (f x - ∫ y, f y ∂P) ^ 2 ∂P)
    (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    μ.real {ω | empiricalBernsteinCIHalfWidth S f a b c n δ ω
        ≤ |S.sampleMean f n ω - ∫ x, f x ∂P|} ≤ 2 * δ := by
  classical
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  haveI hP : IsProbabilityMeasure P := by
    rw [← S.law]; exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  set m : ℝ := ∫ x, f x ∂P with hmdef
  set τ : ℝ := empiricalVarianceSlack a b n δ with hτdef
  set V : ℝ := ∫ x, (f x - m) ^ 2 ∂P with hVdef
  -- integrability of `f` and `f²` (bounded on a probability measure)
  set M : ℝ := max |a| |b| with hMdef
  have hMnn : 0 ≤ M := le_trans (abs_nonneg a) (le_max_left _ _)
  have habsM : ∀ᵐ x ∂P, |f x| ≤ M := by
    filter_upwards [hbound_ab] with x hx
    rw [hMdef, abs_le]
    refine ⟨?_, le_trans hx.2 (le_trans (le_abs_self b) (le_max_right _ _))⟩
    have : -|a| ≤ a := neg_abs_le a
    linarith [le_trans (neg_le_neg (le_max_left |a| |b|)) this, hx.1]
  have hfint : Integrable f P :=
    Integrable.mono' (integrable_const M) hf.aestronglyMeasurable
      (by filter_upwards [habsM] with x hx; rwa [Real.norm_eq_abs])
  -- the oracle standard deviation `σ = √V`
  set σ : ℝ := Real.sqrt V with hσdef
  have hσpos : 0 < σ := Real.sqrt_pos.mpr hposvar
  have hσsq : σ ^ 2 = V := Real.sq_sqrt (le_of_lt hposvar)
  -- oracle Bernstein miss event (level δ)
  have hmiss_oracle :
      μ.real {ω | bernsteinCIHalfWidth c σ n δ ≤ |S.sampleMean f n ω - m|} ≤ δ := by
    have := bernstein_ci_miss S hf hfint hc hσpos hbound (le_of_eq hσsq.symm) n hn hδ0 hδ1
    rwa [← hmdef] at this
  -- variance-bound failure event (level δ)
  have hmiss_var :
      μ.real {ω | S.sampleVariance f n ω + τ < V} ≤ δ := by
    have := empirical_variance_concentration S hf hab hbound_ab n hn hδ0 hδ1
    rwa [← hmdef, ← hVdef, ← hτdef] at this
  -- containment: data-driven miss ⊆ oracle miss ∪ variance failure
  have hsub : {ω | empiricalBernsteinCIHalfWidth S f a b c n δ ω
        ≤ |S.sampleMean f n ω - m|}
      ⊆ {ω | bernsteinCIHalfWidth c σ n δ ≤ |S.sampleMean f n ω - m|}
        ∪ {ω | S.sampleVariance f n ω + τ < V} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, empiricalBernsteinCIHalfWidth, ← hτdef] at hω
    by_cases hgood : V ≤ S.sampleVariance f n ω + τ
    · -- good variance event: σ ≤ √(V̂ₙ + τ), so oracle width ≤ data-driven width
      left
      simp only [Set.mem_setOf_eq]
      have hσle : σ ≤ Real.sqrt (S.sampleVariance f n ω + τ) := by
        rw [hσdef]
        exact Real.sqrt_le_sqrt hgood
      have hmono := bernsteinCIHalfWidth_mono_sigma (c := c) (n := n) hδ0 hδ1 hσle
      exact le_trans hmono hω
    · -- bad variance event
      right
      simp only [Set.mem_setOf_eq]
      exact lt_of_not_ge hgood
  -- conclude via union bound
  calc μ.real {ω | empiricalBernsteinCIHalfWidth S f a b c n δ ω
          ≤ |S.sampleMean f n ω - m|}
      ≤ μ.real ({ω | bernsteinCIHalfWidth c σ n δ ≤ |S.sampleMean f n ω - m|}
          ∪ {ω | S.sampleVariance f n ω + τ < V}) := measureReal_mono hsub
    _ ≤ μ.real {ω | bernsteinCIHalfWidth c σ n δ ≤ |S.sampleMean f n ω - m|}
          + μ.real {ω | S.sampleVariance f n ω + τ < V} := measureReal_union_le _ _
    _ ≤ δ + δ := add_le_add hmiss_oracle hmiss_var
    _ = 2 * δ := by ring

end Causalean.Stat.Concentration
