/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Empirical cumulative distribution function

Causal-agnostic statistical primitive: the empirical cdf of an i.i.d. real
sample,

    empiricalCDF S y n ω := (1/n) Σ_{i<n} 1{Z_i ω ≤ y},

the sample analogue of `ProbabilityTheory.cdf P y = P(Iic y)`.  It is the
`IIDSample.sampleMean` of the indicator `1{· ≤ y}`, so all of the i.i.d.
machinery applies verbatim.

The pointwise (fixed-`y`) influence function is

    cdfIF P y z := 1{z ≤ y} − F(y),       F := cdf P,

a bounded, mean-zero, square-integrable function with variance
`∫ cdfIF² dP = F(y)(1 − F(y))` (the Bernoulli variance of the event
`{Z ≤ y}`).  Because `√n (F̂ₙ(y) − F(y))` **is** the normalized sum
`(1/√n) Σ cdfIF(Z_i)`, the empirical cdf is asymptotically linear with an
*identically zero* remainder; the headline corollary

    √n (F̂ₙ(y) − F(y)) ⇒ N(0, F(y)(1 − F(y)))

is therefore a direct instance of `IsAsymLinear.tendsto_normal`.  This is the
base layer for the sample-quantile asymptotics in `Stat/SampleQuantile.lean`
(Bahadur representation) and, downstream, for quantile-treatment-effect
inference.

File is project-agnostic and a candidate for upstream contribution to Mathlib.
-/

import Causalean.Stat.CLT.AsymptoticLinearity
import Causalean.Stat.Limit.WLLN
import Mathlib.Probability.CDF
import Causalean.Tactic.Attr

/-! # Empirical Distribution Functions

This file defines the empirical cumulative distribution function of a real
i.i.d. sample and its pointwise influence function. It proves the boundedness,
mean-zero, variance, weak-law, and asymptotic-linearity facts that support
sample-quantile and quantile-treatment-effect inference. -/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {P : Measure ℝ}

/-- The indicator statistic `1{· ≤ y} : ℝ → ℝ` of the lower-ray event. -/
noncomputable def cdfStat (y : ℝ) : ℝ → ℝ :=
  Set.indicator (Set.Iic y) (fun _ => (1 : ℝ))

/-- The lower-ray indicator statistic at level `y` is the indicator function of the
lower ray `(-∞, y]`, taking the value one on that ray and zero off it. -/
@[causal_defs_simps]
lemma cdfStat_eq (y : ℝ) :
    cdfStat y = Set.indicator (Set.Iic y) (fun _ => (1 : ℝ)) :=
  rfl

/-- The lower-ray indicator is measurable. -/
@[fun_prop]
lemma measurable_cdfStat (y : ℝ) : Measurable (cdfStat y) :=
  measurable_const.indicator measurableSet_Iic

/-- The lower-ray indicator is nonnegative. -/
lemma cdfStat_nonneg (y z : ℝ) : 0 ≤ cdfStat y z := by
  simp only [causal_defs_simps]
  by_cases h : z ∈ Set.Iic y <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]

/-- The lower-ray indicator is bounded above by one. -/
lemma cdfStat_le_one (y z : ℝ) : cdfStat y z ≤ 1 := by
  simp only [causal_defs_simps]
  by_cases h : z ∈ Set.Iic y <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]

/-- The indicator is idempotent: `(1{z ≤ y})² = 1{z ≤ y}`. -/
lemma cdfStat_sq (y z : ℝ) : (cdfStat y z) ^ 2 = cdfStat y z := by
  simp only [causal_defs_simps]
  by_cases h : z ∈ Set.Iic y <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]

/-- `cdfStat y` is integrable (bounded by `1` on a finite measure). -/
@[fun_prop]
lemma integrable_cdfStat [IsProbabilityMeasure P] (y : ℝ) : Integrable (cdfStat y) P := by
  refine (integrable_const (1 : ℝ)).mono' (measurable_cdfStat y).aestronglyMeasurable ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (cdfStat_nonneg y z)]
  exact cdfStat_le_one y z

/-- The integral of the indicator statistic is the cdf value `F(y)`. -/
lemma integral_cdfStat [IsProbabilityMeasure P] (y : ℝ) :
    ∫ z, cdfStat y z ∂P = cdf P y := by
  rw [cdf_eq_real]
  simp only [causal_defs_simps]
  rw [MeasureTheory.integral_indicator measurableSet_Iic, setIntegral_const]
  simp [measureReal_def]

/-- The empirical cumulative distribution function
`F̂ₙ(y) = (1/n) Σ_{i<n} 1{Z_i ≤ y}`, the `sampleMean` of `cdfStat y`. -/
noncomputable def IIDSample.empiricalCDF (S : IIDSample Ω ℝ μ P) (y : ℝ) :
    ℕ → Ω → ℝ :=
  S.sampleMean (cdfStat y)

/-! ## Pointwise influence function of the empirical cdf -/

/-- The fixed-`y` influence function of the empirical cdf:
`cdfIF P y z = 1{z ≤ y} − F(y)`. -/
noncomputable def cdfIF (P : Measure ℝ) (y : ℝ) : ℝ → ℝ :=
  fun z => cdfStat y z - cdf P y

/-- The empirical-cdf influence function is measurable. -/
@[fun_prop]
lemma measurable_cdfIF (y : ℝ) : Measurable (cdfIF P y) :=
  (measurable_cdfStat y).sub measurable_const

/-- `cdfIF` has mean zero under `P`. -/
lemma cdfIF_mean_zero [IsProbabilityMeasure P] (y : ℝ) :
    ∫ z, cdfIF P y z ∂P = 0 := by
  unfold cdfIF
  rw [integral_sub (integrable_cdfStat y) (integrable_const _), integral_cdfStat,
    integral_const, probReal_univ, one_smul, sub_self]

/-- `cdfIF` is bounded by `1` in absolute value. -/
lemma abs_cdfIF_le_one [IsProbabilityMeasure P] (y z : ℝ) : |cdfIF P y z| ≤ 1 := by
  have hF0 : 0 ≤ cdf P y := by rw [cdf_eq_real]; exact measureReal_nonneg
  have hF1 : cdf P y ≤ 1 := by rw [cdf_eq_real]; exact measureReal_le_one
  unfold cdfIF
  by_cases hz : z ≤ y
  · have h1 : cdfStat y z = 1 := by
      simp only [causal_defs_simps]; rw [Set.indicator_of_mem (Set.mem_Iic.mpr hz)]
    rw [h1, abs_le]; constructor <;> linarith
  · have h0 : cdfStat y z = 0 := by
      simp only [causal_defs_simps]
      rw [Set.indicator_of_notMem (by simp only [Set.mem_Iic]; exact hz)]
    rw [h0, zero_sub, abs_neg, abs_of_nonneg hF0]; linarith

/-- `cdfIF` is square-integrable (it is bounded). -/
@[fun_prop]
lemma cdfIF_sq_integrable [IsProbabilityMeasure P] (y : ℝ) :
    Integrable (fun z => (cdfIF P y z) ^ 2) P := by
  refine (integrable_const (1 : ℝ)).mono'
    ((measurable_cdfIF y).pow_const 2).aestronglyMeasurable ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_le_one_iff_abs_le_one]
  exact abs_cdfIF_le_one y z

/-- **Variance of the empirical-cdf influence function.** [At a fixed threshold `y`](hyp:y), [the
population second moment of the cdf influence function equals `F(y)(1 − F(y))`](goal), the
Bernoulli variance of the indicator event `{Z ≤ y}`. -/
lemma cdfIF_variance [IsProbabilityMeasure P] (y : ℝ) :
    ∫ z, (cdfIF P y z) ^ 2 ∂P = cdf P y * (1 - cdf P y) := by
  have hstat_int : Integrable (cdfStat y) P := integrable_cdfStat y
  -- `(1{·} − F)² = 1{·} − 2F·1{·} + F²` via idempotence of the indicator.
  have hexpand : (fun z => (cdfIF P y z) ^ 2)
      = (fun z => cdfStat y z - 2 * cdf P y * cdfStat y z + (cdf P y) ^ 2) := by
    funext z
    simp only [cdfIF]
    rw [show (cdfStat y z - cdf P y) ^ 2
          = (cdfStat y z) ^ 2 - 2 * cdf P y * cdfStat y z + (cdf P y) ^ 2 from by ring,
      cdfStat_sq y z]
  have h1 : Integrable (fun z => cdfStat y z - 2 * cdf P y * cdfStat y z) P := by
    fun_prop
  rw [hexpand, integral_add h1 (integrable_const _),
    integral_sub hstat_int (hstat_int.const_mul (2 * cdf P y)), integral_const_mul]
  simp only [integral_cdfStat, integral_const, probReal_univ, one_smul]
  ring

/-! ## Asymptotic linearity and the empirical-cdf CLT

`√n (F̂ₙ(y) − F(y))` **is** the normalized sum `(1/√n) Σ cdfIF(Z_i)`, so the
empirical cdf is asymptotically linear with an identically-zero remainder. -/

/-- `o_p`-triviality of the zero sequence at the constant rate `rₙ = 1`. -/
lemma isLittleOp_zero : IsLittleOp (fun _ (_ : Ω) => (0 : ℝ)) (fun _ => (1 : ℝ)) μ := by
  intro ε hε
  have hset : {ω : Ω | ε * (1 : ℝ) < |(0 : ℝ)|} = (∅ : Set Ω) := by
    ext ω
    simp only [mul_one, abs_zero, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact hε.le
  simp only [hset, measure_empty]
  exact tendsto_const_nhds

/-- **Key identity.**  The rescaled empirical-cdf deviation equals the
normalized influence-function sum: `√n (F̂ₙ(y) − F(y)) = (1/√n) Σ cdfIF(Z_i)`. -/
lemma rescaledEmpiricalCDF_eq_normalizedSum (S : IIDSample Ω ℝ μ P) (y : ℝ) (n : ℕ) (ω : Ω) :
    Real.sqrt ((Finset.range n).card : ℝ) * (S.empiricalCDF y n ω - cdf P y)
      = (Real.sqrt ((Finset.range n).card : ℝ))⁻¹
        * ∑ i ∈ Finset.range n, cdfIF P y (S.Z i ω) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [IIDSample.empiricalCDF, IIDSample.sampleMean]
  · have hcard : ((Finset.range n).card : ℝ) = (n : ℝ) := by rw [Finset.card_range]
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsum : ∑ i ∈ Finset.range n, cdfIF P y (S.Z i ω)
        = (∑ i ∈ Finset.range n, cdfStat y (S.Z i ω)) - (n : ℝ) * cdf P y := by
      simp only [cdfIF, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hcard, hsum]
    simp only [IIDSample.empiricalCDF, IIDSample.sampleMean]
    set t := ∑ i ∈ Finset.range n, cdfStat y (S.Z i ω) with ht
    set r := Real.sqrt (n : ℝ) with hrdef
    have hr2 : r * r = (n : ℝ) := by rw [hrdef]; exact Real.mul_self_sqrt hnpos.le
    have hrne : r ≠ 0 := by rw [hrdef]; exact (Real.sqrt_pos.mpr hnpos).ne'
    have hrr : r * r ≠ 0 := mul_ne_zero hrne hrne
    rw [← hr2]
    field_simp [hrne, hrr]

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

omit [IsProbabilityMeasure μ] in
/-- **Asymptotic linearity of the empirical cdf.** For [an i.i.d. real sample `S`](hyp:S) [at a
fixed point `y`](hyp:y), [the empirical cdf `F̂ₙ(y)` is asymptotically linear at `F(y)` with
influence function `cdfIF P y` and an identically-zero remainder](goal). -/
lemma empiricalCDF_isAsymLinear (S : IIDSample Ω ℝ μ P) (y : ℝ) :
    IsAsymLinear (S.empiricalCDF y) (cdf P y) (cdfIF P y) S (fun m => Finset.range m) where
  mean_zero := cdfIF_mean_zero y
  finite_var := cdfIF_sq_integrable y
  remainder := by
    have hzero : (fun n (ω : Ω) =>
        Real.sqrt ((Finset.range n).card : ℝ) * (S.empiricalCDF y n ω - cdf P y)
          - (Real.sqrt ((Finset.range n).card : ℝ))⁻¹
            * ∑ i ∈ Finset.range n, cdfIF P y (S.Z i ω))
        = (fun _ _ => (0 : ℝ)) := by
      funext n ω; rw [rescaledEmpiricalCDF_eq_normalizedSum S y n ω, sub_self]
    simpa only [hzero] using
      (isLittleOp_zero : IsLittleOp (fun _ (_ : Ω) => (0 : ℝ)) (fun _ => (1 : ℝ)) μ)

/-- **Empirical-cdf central limit theorem.** For an i.i.d. real sample and a threshold `y`, provided
[the rescaled empirical-cdf estimator $\sqrt n\,(\hat F_n(y)-F(y))$ is almost-everywhere measurable
at every sample size](hyp:hθn_meas), [the rescaled deviation converges in distribution, as $n\to
\infty$, to the centered Gaussian law with variance $F(y)(1-F(y))$](goal), where $F$ is the
population cdf and $\hat F_n$ the empirical cdf.

The measurability obligation on the rescaled estimator is imposed at the call
site (matching `IsAsymLinear.tendsto_normal`). -/
theorem empiricalCDF_tendsto_normal (S : IIDSample Ω ℝ μ P) (y : ℝ)
    (hθn_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.rescaledEstimator (S.empiricalCDF y) (cdf P y)
        (fun m => Finset.range m) n) μ) :
    Tendsto_dist
      (IsAsymLinear.rescaledEstimator (S.empiricalCDF y) (cdf P y) (fun m => Finset.range m))
      (gaussianMeasure 0 (cdf P y * (1 - cdf P y)))
      μ
      hθn_meas := by
  have h := (empiricalCDF_isAsymLinear S y).tendsto_normal (measurable_cdfIF y) hθn_meas
  rwa [cdfIF_variance] at h

omit [IsProbabilityMeasure μ] in
/-- **Empirical-cdf consistency (WLLN).** For [an i.i.d. real sample `S`](hyp:S) [at a fixed point
`y`](hyp:y), [the empirical cdf `F̂ₙ(y)` converges to `F(y)` in probability](goal). -/
theorem empiricalCDF_tendsto_inProb (S : IIDSample Ω ℝ μ P) (y : ℝ) :
    Tendsto_inProb (S.empiricalCDF y) (fun _ => cdf P y) μ := by
  have h := S.sampleMean_tendsto_inProb (measurable_cdfStat y) (integrable_cdfStat y)
  rw [integral_cdfStat] at h
  exact h

end Causalean.Stat
