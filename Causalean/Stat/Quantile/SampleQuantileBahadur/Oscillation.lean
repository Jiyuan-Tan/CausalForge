/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bahadur representation of the sample quantile

For the sample quantile `q̂ₙ(τ)` (generalized inverse of the empirical cdf,
`Stat/Quantile/EmpiricalQuantile.lean`) the Bahadur representation

    √n (q̂ₙ − q₀)  =  −Gₙ(q₀)/f₀ + o_p(1),     Gₙ(y) := √n (F̂ₙ(y) − F(y)),

equivalently the asymptotic linearity with influence function
`ψ_τ(z) = (τ − 1{z ≤ q₀})/f₀`, is **derived here from elementary tools** — no
Donsker / empirical-process layer is assumed.  Only `Stat/SampleQuantile.lean`'s
generic bundle exposed `bahadur` as a hypothesis; for the *sample* quantile it
becomes a theorem.

## Derivation (each step elementary)

Let `Gₙ(y) = √n (F̂ₙ(y) − F(y))` (`empProcess`).

* **Chebyshev increment.**  For `yₙ = q₀ + u/√n`, `Gₙ(yₙ) − Gₙ(q₀) →ₚ 0`:
  a centered Bernoulli sum of variance `pₙ(1−pₙ)`, `pₙ = F(yₙ) − F(q₀) → 0`.
* **Monotone-grid oscillation.**  At a random endpoint
  `Uₙ = O_p(1)`, `Gₙ(q₀ + Uₙ/√n) − Gₙ(q₀) →ₚ 0`.  Proof: mesh-`ε` grid on
  `[−M,M]`; monotonicity of `F̂ₙ` and `F` sandwiches the oscillation per cell by
  a grid-node value plus `f₀ε`; finite union ⇒ node max `→ₚ 0`; `ε → 0`.
* **Root-n rate.**  `√n (q̂ₙ − q₀) = O_p(1)`, from the fixed-`q₀` cdf CLT + a
  Slutsky tail bound on `P(q̂ₙ > q₀ + M/√n)`.
* **Inversion and Taylor expansion.**  `Gₙ(q̂ₙ) = −f₀·√n(q̂ₙ − q₀) + o_p(1)`, from the
  switching relation (atom bound `|F̂ₙ(q̂ₙ) − τ| ≤ 1/n`) and `HasDerivAt F f₀ q₀`.
* **Assembly.**  The monotone-grid oscillation, applied at
  `Uₙ = √n(q̂ₙ − q₀)`, combines with inversion and Taylor expansion to give the
  Bahadur remainder `o_p(1)`, hence `IsAsymLinear` for `q̂ₙ`.

References: Bahadur (1966); van der Vaart (1998) §21; Serfling (1980) §2.3.
-/

import Causalean.Stat.Quantile.EmpiricalQuantile
import Causalean.Stat.Quantile.SampleQuantile
import Causalean.Stat.Limit.ContinuousMapping
import Causalean.Mathlib.IIDCenteredSum

/-! # Empirical-Process Oscillation for Sample Quantiles

This file supplies the regularity bundle and empirical-process estimates used
to derive the sample-quantile Bahadur representation without assuming a Donsker
theorem. `SampleQuantileReg` records the interior probability level, positive
density, cdf identification, differentiability, and atomless-population
conditions; `IIDSample.empProcess` is the centered scaled cdf process
`G_n(y) = sqrt n (Fhat_n(y) - F(y))`.

The key public lemmas prove that fixed local-shift increments vanish in
probability, grid-node maxima vanish over finite meshes, the deterministic
Taylor increment converges to `f₀ * a`, and the local oscillation
`IIDSample.empProcess_oscillation` holds for any `O_p(1)` random endpoint. These
facts are the empirical-process input for the root-`n` rate and final
linearization modules.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {P : Measure ℝ}

/-! ## Regularity bundle for the sample quantile -/

/-- Regularity for sample-quantile asymptotics.  Same content as the
`hasDeriv`/identification fields of `QuantileRegularity`, **plus** the atomless
hypothesis `cont` (`P` has no atoms), which lets the Bahadur remainder be
*derived* rather than assumed. -/
structure SampleQuantileReg (P : Measure ℝ) (τ q₀ f₀ : ℝ) : Prop where
  /-- Interior level. -/
  tau_pos : 0 < τ
  /-- Interior level. -/
  tau_lt_one : τ < 1
  /-- Positive density at the quantile. -/
  density_pos : 0 < f₀
  /-- `q₀` is the population `τ`-quantile. -/
  cdf_eq : cdf P q₀ = τ
  /-- `f₀` is the density at `q₀`. -/
  hasDeriv : HasDerivAt (fun y => cdf P y) f₀ q₀
  /-- Atomless population: the cdf is continuous (no ties a.s.). -/
  cont : Continuous (fun y => cdf P y)

/-! ## The centered, scaled empirical process -/

/-- The centered, scaled empirical process `Gₙ(y) = √n (F̂ₙ(y) − F(y))`. -/
noncomputable def IIDSample.empProcess (S : IIDSample Ω ℝ μ P) (n : ℕ) (ω : Ω) (y : ℝ) :
    ℝ :=
  Real.sqrt (n : ℝ) * (S.empiricalCDF y n ω - cdf P y)

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

/-! ## Chebyshev increment -/

/-- **Fixed local-shift increment.** For a fixed local shift `u`, the empirical
process increment between `q₀` and `q₀ + u/√n` vanishes in probability:
`Gₙ(q₀ + u/√n) − Gₙ(q₀) →ₚ 0`.  Elementary second-moment / Chebyshev bound,
since the increment is a centered Bernoulli sum of variance `pₙ(1−pₙ) → 0`. -/
lemma IIDSample.empProcess_increment_tendsto_zero (S : IIDSample Ω ℝ μ P)
    {τ q₀ f₀ : ℝ} (hreg : SampleQuantileReg P τ q₀ f₀) (u : ℝ) :
    Tendsto_inProb
      (fun n ω => S.empProcess n ω (q₀ + u / Real.sqrt (n : ℝ)) - S.empProcess n ω q₀)
      (fun _ => 0) μ := by
  classical
  -- Abbreviations.
  set yn : ℕ → ℝ := fun n => q₀ + u / Real.sqrt (n : ℝ) with hyn
  -- `g_n z = 1{z ≤ yn} − 1{z ≤ q₀}`, a fixed (in `ω`) increment of indicators.
  set g : ℕ → ℝ → ℝ := fun n z => cdfStat (yn n) z - cdfStat q₀ z with hg
  -- The centered tail probability: `pₙ = |F(yn) − F(q₀)| → 0`.
  set p : ℕ → ℝ := fun n => |cdf P (yn n) - cdf P q₀| with hp
  have hp_nonneg : ∀ n, 0 ≤ p n := fun n => abs_nonneg _
  -- Each `g n` is bounded, hence in `L²(P)`.
  have hg_bdd : ∀ n z, |g n z| ≤ 1 := by
    intro n z
    have ha := cdfStat_nonneg (yn n) z; have hb := cdfStat_le_one (yn n) z
    have hc := cdfStat_nonneg q₀ z; have hd := cdfStat_le_one q₀ z
    rw [hg]; rw [abs_le]; constructor <;> simp only [] <;> linarith
  have hg_meas : ∀ n, Measurable (g n) := by
    intro n; exact (measurable_cdfStat (yn n)).sub (measurable_cdfStat q₀)
  have hg_memLp : ∀ n, MemLp (g n) 2 P := by
    intro n
    exact (memLp_top_of_bound (hg_meas n).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact hg_bdd n z)).mono_exponent (by norm_num)
  -- `∫ g n dP = F(yn) − F(q₀)`.
  have hg_int : ∀ n, ∫ z, g n z ∂P = cdf P (yn n) - cdf P q₀ := by
    intro n
    rw [hg, integral_sub (integrable_cdfStat _) (integrable_cdfStat _),
      integral_cdfStat, integral_cdfStat]
  -- `(g n z)² = |g n z|`, hence `∫ (g n)² dP = |F(yn) − F(q₀)| = p n`.
  have hg_sq_int : ∀ n, ∫ z, (g n z) ^ 2 ∂P = p n := by
    intro n
    rcases le_total q₀ (yn n) with hle | hle
    · -- `g n z ∈ {0, 1}`, so `(g n z)² = g n z`.
      have hsq : ∀ z, (g n z) ^ 2 = g n z := by
        intro z
        have h01 : g n z = 0 ∨ g n z = 1 := by
          simp only [hg, cdfStat, hyn]
          by_cases h1 : z ≤ yn n <;> by_cases h2 : z ≤ q₀ <;>
            simp_all [Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_Iic] <;>
            linarith
        rcases h01 with h | h <;> simp [h]
      have hcong : ∫ z, (g n z) ^ 2 ∂P = ∫ z, g n z ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall hsq)
      rw [hcong, hg_int, hp]
      simp only []
      rw [abs_of_nonneg (by linarith [monotone_cdf P hle])]
    · -- `g n z ∈ {0, -1}`, so `(g n z)² = - g n z`.
      have hsq : ∀ z, (g n z) ^ 2 = - g n z := by
        intro z
        have h01 : g n z = 0 ∨ g n z = -1 := by
          simp only [hg, cdfStat, hyn]
          by_cases h1 : z ≤ yn n <;> by_cases h2 : z ≤ q₀ <;>
            simp_all [Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_Iic] <;>
            linarith
        rcases h01 with h | h <;> simp [h]
      have hcong : ∫ z, (g n z) ^ 2 ∂P = ∫ z, - g n z ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall hsq)
      rw [hcong, integral_neg, hg_int, hp]
      simp only []
      rw [abs_of_nonpos (by linarith [monotone_cdf P hle]), neg_sub]
  -- `p n → 0` by continuity of the cdf and `yn n → q₀`.
  have hp_tendsto : Tendsto p atTop (𝓝 0) := by
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have h0 : Tendsto (fun n : ℕ => u / Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
      hsqrt.const_div_atTop u
    have hyn_tendsto : Tendsto yn atTop (𝓝 q₀) := by
      have := (tendsto_const_nhds (x := q₀)).add h0
      simpa [hyn] using this
    have hcont : Tendsto (fun n => cdf P (yn n)) atTop (𝓝 (cdf P q₀)) :=
      (hreg.cont.tendsto q₀).comp hyn_tendsto
    have hdiff : Tendsto (fun n => cdf P (yn n) - cdf P q₀) atTop (𝓝 0) := by
      have := hcont.sub (tendsto_const_nhds (x := cdf P q₀))
      simpa using this
    have := (continuous_abs.tendsto (0 : ℝ)).comp hdiff
    simpa [hp, Function.comp_def] using this
  -- The increment equals the normalized centered i.i.d. sum.
  have hincr_eq : ∀ (n : ℕ) (ω : Ω),
      S.empProcess n ω (yn n) - S.empProcess n ω q₀
        = (Real.sqrt (n : ℝ))⁻¹ *
            ∑ i ∈ Finset.range n, (g n (S.Z i ω) - ∫ z, g n z ∂P) := by
    intro n ω
    have h1 := rescaledEmpiricalCDF_eq_normalizedSum S (yn n) n ω
    have h2 := rescaledEmpiricalCDF_eq_normalizedSum S q₀ n ω
    rw [Finset.card_range] at h1 h2
    simp only [IIDSample.empProcess]
    rw [h1, h2, ← mul_sub, ← Finset.sum_sub_distrib]
    rw [hg_int]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [cdfIF, hg]
    ring
  -- AE-measurability of the normalized centered sum (for Markov).
  have hZsum_meas : ∀ (n : ℕ), AEMeasurable
      (fun ω => (Real.sqrt (n : ℝ))⁻¹ *
        ∑ i ∈ Finset.range n, (g n (S.Z i ω) - ∫ z, g n z ∂P)) μ := by
    intro n
    refine (Measurable.const_mul ?_ _).aemeasurable
    refine Finset.measurable_sum _ ?_
    intro i _
    exact ((hg_meas n).comp (S.meas i)).sub measurable_const
  -- i.i.d. product law for the first `n` coordinates.
  have hiid_pi : ∀ (n : ℕ),
      μ.map (fun ω (i : Finset.range n) => S.Z i ω) =
        Measure.pi (fun _ : Finset.range n => P) := by
    intro n
    have hiid : iIndepFun (fun i : Finset.range n => S.Z i) μ :=
      S.indep.precomp (Subtype.val_injective (p := fun i => i ∈ Finset.range n))
    have hmap := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun i : Finset.range n => (S.meas i).aemeasurable)).mp hiid
    calc μ.map (fun ω (i : Finset.range n) => S.Z i ω)
        = Measure.pi (fun i : Finset.range n => μ.map (S.Z i)) := hmap
      _ = Measure.pi (fun _ : Finset.range n => P) := by
          congr with i; rw [← (S.identDist i).map_eq, S.law]
  -- Second-moment bound: `∫⁻ incr² ≤ ofReal (p n)`.
  have hsecond : ∀ (n : ℕ),
      ∫⁻ ω, ENNReal.ofReal
        (((Real.sqrt (n : ℝ))⁻¹ *
          ∑ i ∈ Finset.range n, (g n (S.Z i ω) - ∫ z, g n z ∂P)) ^ 2) ∂μ
        ≤ ENNReal.ofReal (p n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [Nat.cast_zero, Real.sqrt_zero, inv_zero, zero_mul, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ENNReal.ofReal_zero,
        lintegral_const, measure_univ, mul_one]
      exact zero_le _
    · have hbound := Causalean.Mathlib.iid_centered_sum_sq_lintegral_le
        (μ := μ) (P := P) (s := Finset.range n)
        (by simpa [Finset.card_range] using hn) (W := S.Z) (fun i _ => S.meas i)
        (m_A := ⊥) (hm_A_le := bot_le)
        (hW_indep_A := ProbabilityTheory.indep_bot_left _)
        (hW_iid_pi := hiid_pi n)
        (g := fun _ z => g n z)
        (hg_uncurry_meas := (hg_meas n).comp measurable_snd)
        (hg_memLp := fun _ => hg_memLp n)
      simp only [Finset.card_range] at hbound
      refine hbound.trans ?_
      -- `(eLpNorm (g n) 2 P).toReal² = ∫ (g n)² dP = p n`.
      have heLp : (eLpNorm (g n) 2 P).toReal ^ 2 = p n := by
        have hpow := (hg_memLp n).eLpNorm_eq_integral_rpow_norm
          (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)
        rw [hpow]
        simp only [ENNReal.toReal_ofNat]
        have hroot_nonneg : 0 ≤ (∫ a, ‖g n a‖ ^ (2 : ℝ) ∂P) ^ (2 : ℝ)⁻¹ :=
          Real.rpow_nonneg (integral_nonneg fun x => by positivity) _
        rw [ENNReal.toReal_ofReal hroot_nonneg]
        have hint_eq : (∫ a, ‖g n a‖ ^ (2 : ℝ) ∂P) = ∫ z, (g n z) ^ 2 ∂P := by
          congr with x; rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
        rw [hint_eq]
        rw [← Real.rpow_natCast ((∫ z, (g n z) ^ 2 ∂P) ^ (2 : ℝ)⁻¹) 2,
          ← Real.rpow_mul (integral_nonneg fun z => sq_nonneg _)]
        rw [show ((2 : ℝ)⁻¹ * (2 : ℕ)) = 1 by norm_num, Real.rpow_one, hg_sq_int n]
      rw [heLp]
      rw [lintegral_const]
      simp [measure_univ]
  -- Now fix `ε` and run Markov / squeeze.
  unfold Tendsto_inProb
  rw [MeasureTheory.tendstoInMeasure_iff_norm]
  intro ε hε
  -- Markov on `{ε ≤ ‖incr‖}`.
  have hmarkov : ∀ (n : ℕ),
      μ {ω | ε ≤ ‖(S.empProcess n ω (yn n) - S.empProcess n ω q₀) - 0‖}
        ≤ ENNReal.ofReal (p n) / ENNReal.ofReal (ε ^ 2) := by
    intro n
    have hεsq_ne : ENNReal.ofReal (ε ^ 2) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]; positivity
    have hεsq_top : ENNReal.ofReal (ε ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hsub : {ω | ε ≤ ‖(S.empProcess n ω (yn n) - S.empProcess n ω q₀) - 0‖}
        ⊆ {ω | ENNReal.ofReal (ε ^ 2) ≤ ENNReal.ofReal
            (((Real.sqrt (n : ℝ))⁻¹ *
              ∑ i ∈ Finset.range n, (g n (S.Z i ω) - ∫ z, g n z ∂P)) ^ 2)} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, sub_zero, Real.norm_eq_abs] at hω
      rw [hincr_eq n ω] at hω
      apply ENNReal.ofReal_le_ofReal
      rw [← sq_abs ((Real.sqrt (n : ℝ))⁻¹ *
        ∑ i ∈ Finset.range n, (g n (S.Z i ω) - ∫ z, g n z ∂P))]
      exact pow_le_pow_left₀ hε.le hω 2
    calc μ {ω | ε ≤ ‖(S.empProcess n ω (yn n) - S.empProcess n ω q₀) - 0‖}
        ≤ μ {ω | ENNReal.ofReal (ε ^ 2) ≤ ENNReal.ofReal
            (((Real.sqrt (n : ℝ))⁻¹ *
              ∑ i ∈ Finset.range n, (g n (S.Z i ω) - ∫ z, g n z ∂P)) ^ 2)} :=
          measure_mono hsub
      _ ≤ (∫⁻ ω, ENNReal.ofReal
            (((Real.sqrt (n : ℝ))⁻¹ *
              ∑ i ∈ Finset.range n, (g n (S.Z i ω) - ∫ z, g n z ∂P)) ^ 2) ∂μ)
            / ENNReal.ofReal (ε ^ 2) :=
          MeasureTheory.meas_ge_le_lintegral_div
            ((hZsum_meas n).pow_const 2).ennreal_ofReal hεsq_ne hεsq_top
      _ ≤ ENNReal.ofReal (p n) / ENNReal.ofReal (ε ^ 2) := by
          gcongr; exact hsecond n
  -- Squeeze the Markov bound to `0`.
  have hrhs_tendsto : Tendsto (fun n => ENNReal.ofReal (p n) / ENNReal.ofReal (ε ^ 2))
      atTop (𝓝 0) := by
    have hp_en : Tendsto (fun n => ENNReal.ofReal (p n)) atTop (𝓝 0) := by
      rw [show (0 : ENNReal) = ENNReal.ofReal 0 by simp]
      exact (ENNReal.continuous_ofReal.tendsto 0).comp hp_tendsto
    have hεsq_ne : ENNReal.ofReal (ε ^ 2) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]; positivity
    have hc_ne_top : (ENNReal.ofReal (ε ^ 2))⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.mpr hεsq_ne
    have := ENNReal.Tendsto.mul_const hp_en (Or.inr hc_ne_top)
    simp only [zero_mul] at this
    simpa [ENNReal.div_eq_inv_mul, mul_comm] using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hrhs_tendsto (fun n => zero_le _) (fun n => hmarkov n)


/-! ## Monotone-grid oscillation -/

/-- **Pointwise monotone sandwich for the empirical process.**  Fix `n, ω` and a
bracketing cell `a ≤ u ≤ b` of local shifts.  Writing `Gₙ(y) := empProcess n ω y`
and `ya = q₀+a/√n`, `yb = q₀+b/√n`, monotonicity of *both* `F̂ₙ` and `F`
sandwiches the oscillation at the interior point `q₀+u/√n` between the two
grid-node increments plus the deterministic mesh term:

    |Gₙ(q₀+u/√n) − Gₙ(q₀)|
      ≤ max |Gₙ(ya) − Gₙ(q₀)| |Gₙ(yb) − Gₙ(q₀)|
        + √n·(F(yb) − F(ya)).

Pure (probability-free) inequality; the only inputs are the two monotonicities
and `√n ≥ 0`. -/
lemma IIDSample.empProcess_cell_sandwich (S : IIDSample Ω ℝ μ P)
    (n : ℕ) (ω : Ω) {q₀ a b u : ℝ} (hau : a ≤ u) (hub : u ≤ b) :
    |S.empProcess n ω (q₀ + u / Real.sqrt (n : ℝ)) - S.empProcess n ω q₀|
      ≤ max |S.empProcess n ω (q₀ + a / Real.sqrt (n : ℝ)) - S.empProcess n ω q₀|
            |S.empProcess n ω (q₀ + b / Real.sqrt (n : ℝ)) - S.empProcess n ω q₀|
        + Real.sqrt (n : ℝ) *
            (cdf P (q₀ + b / Real.sqrt (n : ℝ)) - cdf P (q₀ + a / Real.sqrt (n : ℝ))) := by
  set s : ℝ := Real.sqrt (n : ℝ) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set ya : ℝ := q₀ + a / s with hya
  set yb : ℝ := q₀ + b / s with hyb
  set yu : ℝ := q₀ + u / s with hyu
  -- Order of the evaluation points.
  have hsa : a / s ≤ u / s := by
    rcases eq_or_lt_of_le hs0 with h | h
    · simp [← h]
    · exact div_le_div_of_nonneg_right hau h.le
  have hsu : u / s ≤ b / s := by
    rcases eq_or_lt_of_le hs0 with h | h
    · simp [← h]
    · exact div_le_div_of_nonneg_right hub h.le
  have hau' : ya ≤ yu := by rw [hya, hyu]; linarith
  have hub' : yu ≤ yb := by rw [hyu, hyb]; linarith
  -- Monotonicities.
  have hFhat_mono := S.empiricalCDF_monotone n ω
  have hF_mono := monotone_cdf P
  -- `empProcess` unfolded: `Gₙ(y) = s·(F̂ₙ(y) − F(y))`.
  have hGdef : ∀ y, S.empProcess n ω y = s * (S.empiricalCDF y n ω - cdf P y) := by
    intro y; simp only [IIDSample.empProcess, hs]
  -- Differenced empirical-cdf monotonicities scaled by `s ≥ 0`.
  have hFhat_au : s * S.empiricalCDF ya n ω ≤ s * S.empiricalCDF yu n ω :=
    mul_le_mul_of_nonneg_left (hFhat_mono hau') hs0
  have hFhat_ub : s * S.empiricalCDF yu n ω ≤ s * S.empiricalCDF yb n ω :=
    mul_le_mul_of_nonneg_left (hFhat_mono hub') hs0
  have hF_au : s * cdf P ya ≤ s * cdf P yu :=
    mul_le_mul_of_nonneg_left (hF_mono hau') hs0
  have hF_ub : s * cdf P yu ≤ s * cdf P yb :=
    mul_le_mul_of_nonneg_left (hF_mono hub') hs0
  -- The deterministic mesh term `D := s·(F(yb) − F(ya)) ≥ 0`.
  set D : ℝ := s * (cdf P yb - cdf P ya) with hD
  have hD0 : 0 ≤ D := by rw [hD, mul_sub]; linarith [hF_au, hF_ub]
  -- Increment abbreviations.
  set Iu : ℝ := S.empProcess n ω yu - S.empProcess n ω q₀ with hIu
  set Ia : ℝ := S.empProcess n ω ya - S.empProcess n ω q₀ with hIa
  set Ib : ℝ := S.empProcess n ω yb - S.empProcess n ω q₀ with hIb
  -- Upper bound: `Iu ≤ Ib + D`.
  have hupper : Iu ≤ Ib + D := by
    rw [hIu, hIb, hD, mul_sub]
    rw [hGdef yu, hGdef yb, hGdef q₀]
    have e1 : s * S.empiricalCDF yu n ω ≤ s * S.empiricalCDF yb n ω := hFhat_ub
    have e2 : s * cdf P ya ≤ s * cdf P yu := hF_au
    nlinarith [e1, e2]
  -- Lower bound: `Ia − D ≤ Iu`.
  have hlower : Ia - D ≤ Iu := by
    rw [hIu, hIa, hD, mul_sub]
    rw [hGdef yu, hGdef ya, hGdef q₀]
    have e1 : s * S.empiricalCDF ya n ω ≤ s * S.empiricalCDF yu n ω := hFhat_au
    have e2 : s * cdf P yu ≤ s * cdf P yb := hF_ub
    nlinarith [e1, e2]
  -- Combine: `|Iu| ≤ max |Ia| |Ib| + D`.
  have hmaxa : Ia ≤ max |Ia| |Ib| := le_trans (le_abs_self _) (le_max_left _ _)
  have hmaxb : Ib ≤ max |Ia| |Ib| := le_trans (le_abs_self _) (le_max_right _ _)
  have hmaxa' : -(max |Ia| |Ib|) ≤ Ia :=
    neg_le.mp (le_trans (neg_le_abs _) (le_max_left _ _))
  have hmaxb' : -(max |Ia| |Ib|) ≤ Ib :=
    neg_le.mp (le_trans (neg_le_abs _) (le_max_right _ _))
  rw [abs_le]
  constructor
  · -- `-(max + D) ≤ Iu`.
    have : -(max |Ia| |Ib|) - D ≤ Iu := le_trans (by linarith [hmaxa']) hlower
    linarith
  · -- `Iu ≤ max + D`.
    have : Iu ≤ max |Ia| |Ib| + D := le_trans hupper (by linarith [hmaxb])
    linarith

/-- **Finite grid-node maximum tends to zero.**  The maximum, over a *finite*
nonempty index set `s` of local shifts `v i`, of the grid-node increments
`|Gₙ(q₀+v i/√n) − Gₙ(q₀)|` vanishes in probability.  A finite union of the L2
limits `empProcess_increment_tendsto_zero`: `μ{ε ≤ maxᵢ |Δᵢ|} ≤ Σᵢ μ{ε ≤ |Δᵢ|}`,
each summand `→ 0`. -/
lemma IIDSample.empProcess_node_max_tendsto_zero (S : IIDSample Ω ℝ μ P)
    {τ q₀ f₀ : ℝ} (hreg : SampleQuantileReg P τ q₀ f₀)
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (v : ι → ℝ) :
    Tendsto_inProb
      (fun n ω => s.sup' hs (fun i =>
        |S.empProcess n ω (q₀ + v i / Real.sqrt (n : ℝ)) - S.empProcess n ω q₀|))
      (fun _ => 0) μ := by
  classical
  -- abbreviation for the per-node increment.
  set Δ : ι → ℕ → Ω → ℝ := fun i n ω =>
    S.empProcess n ω (q₀ + v i / Real.sqrt (n : ℝ)) - S.empProcess n ω q₀ with hΔ
  -- Each node increment vanishes in probability (L2).
  have heach : ∀ i ∈ s, Tendsto_inProb (Δ i) (fun _ => 0) μ := fun i _ =>
    S.empProcess_increment_tendsto_zero hreg (v i)
  unfold Tendsto_inProb
  rw [MeasureTheory.tendstoInMeasure_iff_norm]
  intro ε hε
  -- Each summand tends to 0.
  have heach' : ∀ i ∈ s, Tendsto
      (fun n => μ {ω | ε ≤ |Δ i n ω - 0|}) atTop (𝓝 0) := by
    intro i hi
    have := (MeasureTheory.tendstoInMeasure_iff_norm.mp (heach i hi)) ε hε
    simpa [Real.norm_eq_abs] using this
  -- Finite sum of the per-node tails tends to 0.
  have hsum : Tendsto
      (fun n => ∑ i ∈ s, μ {ω | ε ≤ |Δ i n ω - 0|}) atTop (𝓝 0) := by
    have := tendsto_finset_sum s (fun i hi => heach' i hi)
    simpa using this
  -- Set inclusion: `{ε ≤ sup' s |Δ·|} ⊆ ⋃ i∈s {ε ≤ |Δ i|}`, hence ≤ the sum.
  have hbound : ∀ n,
      μ {ω | ε ≤ ‖s.sup' hs (fun i => |Δ i n ω|) - 0‖}
        ≤ ∑ i ∈ s, μ {ω | ε ≤ |Δ i n ω - 0|} := by
    intro n
    refine le_trans (measure_mono ?_)
      (MeasureTheory.measure_biUnion_finset_le s _)
    intro ω hω
    simp only [Set.mem_setOf_eq, sub_zero, Real.norm_eq_abs] at hω
    -- `sup'` of abs values is nonneg, so `|sup'| = sup'`.
    have hsup_nonneg : 0 ≤ s.sup' hs (fun i => |Δ i n ω|) := by
      obtain ⟨j, hj⟩ := hs
      exact le_trans (abs_nonneg _) (Finset.le_sup' (fun i => |Δ i n ω|) hj)
    rw [abs_of_nonneg hsup_nonneg] at hω
    -- `sup'` is attained, so some node exceeds `ε`.
    obtain ⟨i, hi, hival⟩ := Finset.exists_mem_eq_sup' hs (fun i => |Δ i n ω|)
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, sub_zero, exists_prop]
    exact ⟨i, hi, by rw [← hival]; exact hω⟩
  -- Squeeze.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun n => zero_le _) (fun n => hbound n)

/-- **Uniform grid bracketing.**  For the uniform mesh `u_k = −M + 2M·k/K`
on `[−M, M]` (`K ≥ 1`, `M > 0`), any `x ∈ [−M, M]` lies in some cell
`[u_j, u_{j+1}]` with `j < K`.  Pure real-arithmetic fact (floor of the scaled
coordinate, clamped to the last cell). -/
lemma exists_grid_bracket {M : ℝ} (hM : 0 < M) {K : ℕ} (hK : 1 ≤ K)
    {x : ℝ} (hx : -M ≤ x) (hx' : x ≤ M) :
    ∃ j, j < K ∧ -M + 2 * M * (j : ℝ) / K ≤ x ∧ x ≤ -M + 2 * M * ((j : ℝ) + 1) / K := by
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  set h : ℝ := 2 * M / K with hh
  have hhpos : 0 < h := by rw [hh]; positivity
  set t : ℝ := (x + M) / h with ht
  have hxeq : x = -M + h * t := by
    rw [ht, mul_div_cancel₀ _ hhpos.ne']; ring
  have ht0 : 0 ≤ t := by rw [ht]; apply div_nonneg (by linarith) hhpos.le
  have htK : t ≤ K := by rw [ht, div_le_iff₀ hhpos, hh]; field_simp; nlinarith
  have hnode : ∀ r : ℝ, -M + 2 * M * r / K = -M + h * r := by intro r; rw [hh]; ring
  refine ⟨min (Nat.floor t) (K - 1), ?_, ?_, ?_⟩
  · omega
  · have hjle : ((min (Nat.floor t) (K - 1) : ℕ) : ℝ) ≤ t := by
      have h1 : (Nat.floor t : ℝ) ≤ t := Nat.floor_le ht0
      have h2 : ((min (Nat.floor t) (K - 1) : ℕ) : ℝ) ≤ (Nat.floor t : ℝ) := by
        exact_mod_cast Nat.min_le_left _ _
      linarith
    rw [hnode, hxeq]; nlinarith [hhpos, hjle]
  · have htlt : t ≤ ((min (Nat.floor t) (K - 1) : ℕ) : ℝ) + 1 := by
      have h1 : t < (Nat.floor t : ℝ) + 1 := Nat.lt_floor_add_one t
      by_cases hc : Nat.floor t ≤ K - 1
      · have he : min (Nat.floor t) (K - 1) = Nat.floor t := by omega
        rw [he]; linarith
      · have he : min (Nat.floor t) (K - 1) = K - 1 := by omega
        rw [he]
        have hKe : ((K - 1 : ℕ) : ℝ) + 1 = (K : ℝ) := by
          have h1 : 1 ≤ K := hK; push_cast [Nat.cast_sub h1]; ring
        rw [hKe]; exact htK
    rw [hnode, hxeq]; nlinarith [hhpos, htlt]

/-- **Taylor increment.**  `√n (F(q₀+a/√n) − F(q₀)) → f₀·a` from `HasDerivAt F f₀ q₀`.
Used by both the L3 oscillation mesh term and the L4 root-`n` rate (in `Rate.lean`). -/
lemma cdf_increment_sqrt_tendsto {P : Measure ℝ} {τ q₀ f₀ : ℝ}
    (hreg : SampleQuantileReg P τ q₀ f₀) (a : ℝ) :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) *
        (cdf P (q₀ + a / Real.sqrt (n : ℝ)) - cdf P q₀)) atTop (𝓝 (f₀ * a)) := by
  set F : ℝ → ℝ := fun y => cdf P y with hFdef
  have hxn : Tendsto (fun n : ℕ => q₀ + a / Real.sqrt (n : ℝ)) atTop (𝓝 q₀) := by
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have h0 : Tendsto (fun n : ℕ => a / Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
      hsqrt.const_div_atTop a
    simpa using (tendsto_const_nhds (x := q₀)).add h0
  rcases eq_or_ne a 0 with ha0 | ha0
  · subst ha0; simp
  · have hxn_ne : ∀ᶠ n : ℕ in atTop, q₀ + a / Real.sqrt (n : ℝ) ≠ q₀ := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hsq : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
      have : a / Real.sqrt (n : ℝ) ≠ 0 := div_ne_zero ha0 hsq.ne'
      intro h; exact this (by linarith [h])
    have hslope : Tendsto (fun n : ℕ => slope F q₀ (q₀ + a / Real.sqrt (n : ℝ)))
        atTop (𝓝 f₀) := by
      have htend := (hasDerivAt_iff_tendsto_slope.mp hreg.hasDeriv)
      exact htend.comp (tendsto_nhdsWithin_iff.mpr ⟨hxn, hxn_ne⟩)
    have hlim : Tendsto (fun n : ℕ => a * slope F q₀ (q₀ + a / Real.sqrt (n : ℝ)))
        atTop (𝓝 (a * f₀)) := hslope.const_mul a
    rw [mul_comm f₀ a]
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hsq : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hden : (q₀ + a / Real.sqrt (n : ℝ)) - q₀ = a / Real.sqrt (n : ℝ) := by ring
    rw [slope_def_field, hden, hFdef]
    rw [div_div_eq_mul_div]
    field_simp

/-- **Local oscillation of the sample-quantile empirical process.** The empirical
process over a window shrinking at rate `n^{-1/2}`, evaluated at a *random*
endpoint `Uₙ = O_p(1)`:

    Gₙ(q₀ + Uₙ/√n) − Gₙ(q₀)  →ₚ  0.

Proof sketch: fix `M` with `Uₙ ∈ [−M, M]` w.h.p.; partition `[−M, M]` into a
mesh-`ε` grid; monotonicity of both `F̂ₙ` and `F` sandwiches the oscillation on
each cell by a grid-node increment (controlled by L2) plus the deterministic
mesh `f₀ε`; the node maximum vanishes (finite union of L2 limits); let `ε → 0`. -/
lemma IIDSample.empProcess_oscillation (S : IIDSample Ω ℝ μ P)
    {τ q₀ f₀ : ℝ} (hreg : SampleQuantileReg P τ q₀ f₀)
    {Un : ℕ → Ω → ℝ} (hUn : IsBigOp Un (fun _ => (1 : ℝ)) μ) :
    Tendsto_inProb
      (fun n ω => S.empProcess n ω (q₀ + Un n ω / Real.sqrt (n : ℝ)) - S.empProcess n ω q₀)
      (fun _ => 0) μ := by
  classical
  have hf0 : 0 < f₀ := hreg.density_pos
  -- The random increment.
  set incr : ℕ → Ω → ℝ := fun n ω =>
    S.empProcess n ω (q₀ + Un n ω / Real.sqrt (n : ℝ)) - S.empProcess n ω q₀ with hincr
  unfold Tendsto_inProb
  rw [MeasureTheory.tendstoInMeasure_iff_norm]
  intro ε hε
  -- Reduce `Tendsto … 0` to `∀ δ>0, limsup ≤ ofReal δ` (ENNReal limsup squeeze).
  have hredu : (∀ δ : ℝ, 0 < δ →
      Filter.limsup (fun n => μ {ω | ε ≤ ‖incr n ω - 0‖}) atTop ≤ ENNReal.ofReal δ) →
      Tendsto (fun n => μ {ω | ε ≤ ‖incr n ω - 0‖}) atTop (𝓝 0) := by
    intro hall
    have hle : Filter.limsup (fun n => μ {ω | ε ≤ ‖incr n ω - 0‖}) atTop ≤ 0 := by
      refine ENNReal.le_of_forall_pos_le_add ?_
      intro r hr _
      have hh := hall r (by exact_mod_cast hr)
      rw [zero_add]
      refine le_trans hh ?_
      rw [ENNReal.ofReal_coe_nnreal]
    refine tendsto_of_le_liminf_of_limsup_le bot_le (le_antisymm hle bot_le).le
      ⟨⊤, by filter_upwards with n using le_top⟩
      ⟨0, by filter_upwards with n using bot_le⟩
  apply hredu
  intro δ hδ
  -- Step 1: from O_p(1), choose the window `M`.
  obtain ⟨M₀, hM₀⟩ := hUn δ hδ
  set M : ℝ := max M₀ 1 with hMdef
  have hMpos : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hM₀le : M₀ ≤ M := le_max_left _ _
  -- `limsup μ{M<|Un|} ≤ ofReal δ` (sub-event of the `M₀`-tail).
  have hUntail : Filter.limsup (fun n => μ {ω | M < |Un n ω|}) atTop ≤ ENNReal.ofReal δ := by
    refine le_trans (Filter.limsup_le_limsup (Eventually.of_forall fun n => ?_)) hM₀
    refine measure_mono fun ω hω => ?_
    simp only [Set.mem_setOf_eq, mul_one] at hω ⊢
    linarith
  -- Step 2: choose the grid resolution `K` so the deterministic mesh `< ε/2`.
  obtain ⟨K, hKpos, hKmesh⟩ : ∃ K : ℕ, 1 ≤ K ∧ f₀ * (2 * M / K) < ε / 2 := by
    obtain ⟨K, hK⟩ := exists_nat_gt (2 * f₀ * (2 * M) / ε)
    refine ⟨max K 1, le_max_right _ _, ?_⟩
    have hKR : (0:ℝ) < (max K 1 : ℕ) := by positivity
    have hKle : (K : ℝ) ≤ (max K 1 : ℕ) := by exact_mod_cast le_max_left _ _
    have hKbig : 2 * f₀ * (2 * M) / ε < (max K 1 : ℕ) := lt_of_lt_of_le hK hKle
    rw [div_lt_iff₀ hε] at hKbig
    rw [show f₀ * (2 * M / (max K 1 : ℕ)) = f₀ * (2 * M) / (max K 1 : ℕ) by ring,
      div_lt_iff₀ hKR]
    nlinarith [hKbig, hKR, hMpos, hf0]
  -- Node function `u_k = −M + 2M·k/K` on the grid `{0,…,K}`.
  set node : ℕ → ℝ := fun k => -M + 2 * M * (k : ℝ) / K with hnode
  have hne : (Finset.range (K + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  -- The node-maximum process and its L2 vanishing (step 5 helper).
  set NodeMax : ℕ → Ω → ℝ := fun n ω => (Finset.range (K + 1)).sup' hne
    (fun k => |S.empProcess n ω (q₀ + node k / Real.sqrt (n : ℝ)) - S.empProcess n ω q₀|)
    with hNodeMax
  have hNodeMax_p : Tendsto_inProb NodeMax (fun _ => 0) μ :=
    S.empProcess_node_max_tendsto_zero hreg (Finset.range (K + 1)) hne node
  -- `μ{ε/2 ≤ NodeMax} → 0`.
  have hNodeTail : Tendsto (fun n => μ {ω | ε / 2 ≤ |NodeMax n ω|}) atTop (𝓝 0) := by
    have h := (MeasureTheory.tendstoInMeasure_iff_norm.mp hNodeMax_p) (ε / 2) (by linarith)
    simpa [Real.norm_eq_abs] using h
  -- Step 4+6: the deterministic mesh-max is eventually `< ε/2`.
  -- For each cell `j`, `√n(F(node(j+1)/√n)−F(node j/√n)) → f₀·(2M/K) < ε/2`.
  have hMeshEv : ∀ᶠ n : ℕ in atTop, ∀ j ∈ Finset.range K,
      Real.sqrt (n : ℝ) * (cdf P (q₀ + node (j + 1) / Real.sqrt (n : ℝ))
        - cdf P (q₀ + node j / Real.sqrt (n : ℝ))) < ε / 2 := by
    rw [eventually_all_finset]
    intro j _
    -- limit of the cell mesh term is `f₀·(node(j+1)−node j) = f₀·(2M/K) < ε/2`.
    have hlim : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) *
        (cdf P (q₀ + node (j + 1) / Real.sqrt (n : ℝ))
          - cdf P (q₀ + node j / Real.sqrt (n : ℝ)))) atTop (𝓝 (f₀ * (2 * M / K))) := by
      have ha := cdf_increment_sqrt_tendsto hreg (node (j + 1))
      have hb := cdf_increment_sqrt_tendsto hreg (node j)
      have hdiff := ha.sub hb
      have hgoal : f₀ * node (j + 1) - f₀ * node j = f₀ * (2 * M / K) := by
        simp only [hnode]; push_cast; ring
      rw [← hgoal]
      refine hdiff.congr fun n => ?_
      ring
    exact hlim.eventually (eventually_lt_nhds hKmesh)
  -- Step 3+7: CORE inclusion.  Eventually,
  -- `μ{ε ≤ |incr|} ≤ μ{M<|Un|} + μ{ε/2 ≤ NodeMax}`.
  have hcore : ∀ᶠ n : ℕ in atTop,
      μ {ω | ε ≤ ‖incr n ω - 0‖}
        ≤ μ {ω | M < |Un n ω|} + μ {ω | ε / 2 ≤ |NodeMax n ω|} := by
    filter_upwards [hMeshEv] with n hmesh
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro ω hω
    simp only [Set.mem_setOf_eq, sub_zero, Real.norm_eq_abs] at hω
    by_cases hUnM : M < |Un n ω|
    · exact Or.inl hUnM
    · -- `|Un| ≤ M`: bracket, sandwich, conclude `ε/2 ≤ NodeMax`.
      right
      push_neg at hUnM
      have hUnbd := abs_le.mp hUnM
      -- Bracketing cell.
      obtain ⟨j, hjK, hja, hjb⟩ :=
        exists_grid_bracket hMpos hKpos hUnbd.1 hUnbd.2
      -- Sandwich at the bracketing cell.
      have hsand := S.empProcess_cell_sandwich n ω (q₀ := q₀)
        (a := node j) (b := node (j + 1)) (u := Un n ω)
        (by simpa [hnode] using hja) (by simpa [hnode] using hjb)
      -- The two cell-node increments are bounded by NodeMax.
      have hjmem : j ∈ Finset.range (K + 1) := Finset.mem_range.mpr (by omega)
      have hj1mem : j + 1 ∈ Finset.range (K + 1) := Finset.mem_range.mpr (by omega)
      have hbnda : |S.empProcess n ω (q₀ + node j / Real.sqrt (n : ℝ))
          - S.empProcess n ω q₀| ≤ NodeMax n ω :=
        Finset.le_sup' (fun k => |S.empProcess n ω (q₀ + node k / Real.sqrt (n : ℝ))
          - S.empProcess n ω q₀|) hjmem
      have hbndb : |S.empProcess n ω (q₀ + node (j + 1) / Real.sqrt (n : ℝ))
          - S.empProcess n ω q₀| ≤ NodeMax n ω :=
        Finset.le_sup' (fun k => |S.empProcess n ω (q₀ + node k / Real.sqrt (n : ℝ))
          - S.empProcess n ω q₀|) hj1mem
      have hmaxle : max
          |S.empProcess n ω (q₀ + node j / Real.sqrt (n : ℝ)) - S.empProcess n ω q₀|
          |S.empProcess n ω (q₀ + node (j + 1) / Real.sqrt (n : ℝ)) - S.empProcess n ω q₀|
          ≤ NodeMax n ω := max_le hbnda hbndb
      -- Mesh term `< ε/2` at this cell.
      have hmeshj := hmesh j (Finset.mem_range.mpr hjK)
      -- Combine: `ε ≤ |incr| ≤ NodeMax + (mesh < ε/2)`, so `ε/2 ≤ NodeMax`.
      simp only [Set.mem_setOf_eq]
      have hNMnn : 0 ≤ NodeMax n ω := le_trans (abs_nonneg _) hbnda
      rw [abs_of_nonneg hNMnn]
      have hincr_eq : incr n ω = S.empProcess n ω (q₀ + Un n ω / Real.sqrt (n : ℝ))
          - S.empProcess n ω q₀ := by rw [hincr]
      have hchain : ε ≤ NodeMax n ω + ε / 2 :=
        calc ε ≤ |incr n ω| := hω
          _ = |S.empProcess n ω (q₀ + Un n ω / Real.sqrt (n : ℝ))
                - S.empProcess n ω q₀| := by rw [hincr_eq]
          _ ≤ max
                |S.empProcess n ω (q₀ + node j / Real.sqrt (n : ℝ)) - S.empProcess n ω q₀|
                |S.empProcess n ω (q₀ + node (j + 1) / Real.sqrt (n : ℝ))
                  - S.empProcess n ω q₀|
              + Real.sqrt (n : ℝ) * (cdf P (q₀ + node (j + 1) / Real.sqrt (n : ℝ))
                  - cdf P (q₀ + node j / Real.sqrt (n : ℝ))) := hsand
          _ ≤ NodeMax n ω + ε / 2 := add_le_add hmaxle (le_of_lt hmeshj)
      linarith
  -- ASSEMBLE: limsup of the eventual bound; the NodeMax-tail vanishes.
  calc Filter.limsup (fun n => μ {ω | ε ≤ ‖incr n ω - 0‖}) atTop
      ≤ Filter.limsup (fun n => μ {ω | M < |Un n ω|}
            + μ {ω | ε / 2 ≤ |NodeMax n ω|}) atTop :=
        Filter.limsup_le_limsup hcore
    _ = Filter.limsup (fun n => μ {ω | M < |Un n ω|}) atTop :=
        ENNReal.limsup_add_of_right_tendsto_zero hNodeTail _
    _ ≤ ENNReal.ofReal δ := hUntail

end Causalean.Stat
