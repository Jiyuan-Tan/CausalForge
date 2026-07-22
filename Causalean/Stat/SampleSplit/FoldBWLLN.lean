/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Fold-B weak law of large numbers

Generic weak law of large numbers restricted to the estimation fold `B(n)` of a
`OneShotSplit`.  For a fixed, square-integrable statistic `g`, the fold-B sample
mean `|B(n)|⁻¹ Σ_{i ∈ B(n)} g (Z i)` converges in probability to the population
integral `∫ g dP`.

Unlike the full-sample WLLN (`IIDSample.sampleMean_tendsto_inProb`, which is
SLLN-based and ranges over the prefix `{0, …, N−1}`), this lemma works directly
on the growing fold-B index set.  It complements the fold-B `oₚ(1)`
nuisance-vanishing lemmas, which only handle statistics whose mean is zero.

The proof is a textbook Chebyshev argument: fold-B independence (and identical
distribution) gives mean `∫ g dP` and variance `Var[g] / |B(n)|` for the fold-B
average; Chebyshev's inequality then bounds the deviation probability by
`Var[g] / (ε² |B(n)|)`, which vanishes because `|B(n)| → ∞`.
-/

import Causalean.Stat.SampleSplit.OneShot
import Causalean.Stat.Limit.Convergence
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.IdentDistrib

/-! # Fold-B Weak Law of Large Numbers

This file provides a weak law of large numbers for the estimation fold of a
one-shot sample split: the fold-B average of a fixed square-integrable statistic
converges in probability to its population mean. It is the substrate that lets a
fold-B average of a fixed function converge to its mean, as opposed to the
existing fold-B lemmas which only treat the nuisance-vanishing regime. -/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-- **Chebyshev squeeze for convergence in probability.**  If a sequence `Yn`
has constant mean `c` and a Chebyshev tail bound `Var / (ε² b n)` that vanishes
because `b n → ∞`, then `Yn` converges in probability to the constant `c`.

This is a convenience packaging of the standard `0 ≤ … ≤ (vanishing bound)`
squeeze used to turn a Chebyshev inequality into convergence in measure. -/
private lemma tendsto_inProb_of_chebyshev
    {Yn : ℕ → Ω → ℝ} {c V : ℝ} {b : ℕ → ℝ}
    (hb : Tendsto b atTop atTop)
    (hcheb : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        μ {ω | ε ≤ |Yn n ω - c|} ≤ ENNReal.ofReal (V / (ε ^ 2 * b n))) :
    Tendsto_inProb Yn (fun _ => c) μ := by
  unfold Tendsto_inProb
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  -- The Chebyshev bound, written with the real distance `|· - ·|`.
  have hcheb' : ∀ᶠ n in atTop,
      μ {ω | ε ≤ dist (Yn n ω) c} ≤ ENNReal.ofReal (V / (ε ^ 2 * b n)) := by
    filter_upwards [hcheb ε hε] with n hn
    simpa [Real.dist_eq] using hn
  -- The bound vanishes: `V / (ε² b n) → 0` since `b n → ∞`.
  have hbound : Tendsto (fun n => ENNReal.ofReal (V / (ε ^ 2 * b n))) atTop (𝓝 0) := by
    have hden : Tendsto (fun n => ε ^ 2 * b n) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity) hb
    have hreal : Tendsto (fun n => V / (ε ^ 2 * b n)) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds hden
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hreal
    simpa [ENNReal.ofReal_zero, Function.comp] using this
  -- Squeeze between the zero sequence and the vanishing Chebyshev bound.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Eventually.of_forall (fun n => zero_le _)) ?_
  filter_upwards [hcheb'] with n hn using hn

namespace OneShotSplit

variable {S : IIDSample Ω X μ P} (split : OneShotSplit S)

/-- The law of the `i`-th sample point matches the population law `P`. -/
private lemma map_Z_eq (S : IIDSample Ω X μ P) (i : ℕ) : μ.map (S.Z i) = P := by
  rw [← (S.identDist i).map_eq, S.law]

/-- **Fold-B weak law of large numbers.**  For an i.i.d. sample, a one-shot split
into a nuisance fold and an estimation fold, and a fixed square-integrable
statistic `g`, the estimation-fold sample average converges in probability to the
population integral `∫ g dP` as the sample size grows.

This restricts the weak law of large numbers to the estimation fold of the split:
the fold-B index set grows without bound, so the standard Chebyshev argument
(mean `∫ g dP`, variance `Var[g] / |B(n)|`) gives convergence in probability. -/
theorem foldB_sampleMean_tendsto_inProb
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (S : IIDSample Ω X μ P) (split : OneShotSplit S) {g : X → ℝ}
    (hg_meas : Measurable g) (hg_memLp : MemLp g 2 P) :
    Tendsto_inProb
      (fun n ω => ((split.foldB n).card : ℝ)⁻¹ * ∑ i ∈ split.foldB n, g (S.Z i ω))
      (fun _ => ∫ x, g x ∂P) μ := by
  set V : ℝ := variance g P with hV_def
  -- Per-index facts transported through `μ.map (Z i) = P`.
  have hmemLp_i : ∀ i, MemLp (fun ω => g (S.Z i ω)) 2 μ := by
    intro i
    have h : MemLp g 2 (μ.map (S.Z i)) := by rw [map_Z_eq S i]; exact hg_memLp
    exact h.comp_of_map (S.meas i).aemeasurable
  have hint_i : ∀ i, ∫ ω, g (S.Z i ω) ∂μ = ∫ x, g x ∂P := by
    intro i
    rw [← integral_map (S.meas i).aemeasurable hg_meas.aestronglyMeasurable, map_Z_eq S i]
  have hvar_i : ∀ i, variance (fun ω => g (S.Z i ω)) μ = V := by
    intro i
    have hident : IdentDistrib (fun ω => g (S.Z i ω)) g μ P := by
      refine ⟨(hg_meas.comp (S.meas i)).aemeasurable, hg_meas.aemeasurable, ?_⟩
      change Measure.map (g ∘ S.Z i) μ = Measure.map g P
      rw [← Measure.map_map hg_meas (S.meas i), map_Z_eq S i]
    rw [hident.variance_eq, hV_def]
  have hintegrable_i : ∀ i, Integrable (fun ω => g (S.Z i ω)) μ :=
    fun i => (hmemLp_i i).integrable (by norm_num)
  -- Independence of `g ∘ Z i` across distinct indices.
  have hindep_comp : iIndepFun (fun i => g ∘ S.Z i) μ :=
    S.indep.comp (fun _ => g) (fun _ => hg_meas)
  -- Abbreviations for the fold-B average as a function of `n`.
  set Yn : ℕ → Ω → ℝ :=
    fun n ω => ((split.foldB n).card : ℝ)⁻¹ * ∑ i ∈ split.foldB n, g (S.Z i ω) with hYn_def
  -- Mean of the fold-B average is `∫ g dP` whenever the fold is nonempty.
  have hmean : ∀ n, 0 < (split.foldB n).card → ∫ ω, Yn n ω ∂μ = ∫ x, g x ∂P := by
    intro n hcard
    have hsum : ∫ ω, ∑ i ∈ split.foldB n, g (S.Z i ω) ∂μ
        = ((split.foldB n).card : ℝ) * ∫ x, g x ∂P := by
      rw [integral_finset_sum _ (fun i _ => hintegrable_i i)]
      simp only [hint_i]
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hYn_def]
    simp only []
    rw [integral_const_mul, hsum, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  -- Variance of the fold-B average is `V / |B(n)|`.
  have hvar : ∀ n, 0 < (split.foldB n).card →
      variance (Yn n) μ = V / ((split.foldB n).card : ℝ) := by
    intro n hcard
    have hsum_var : variance (fun ω => ∑ i ∈ split.foldB n, g (S.Z i ω)) μ
        = ((split.foldB n).card : ℝ) * V := by
      have hpair : (↑(split.foldB n) : Set ℕ).Pairwise
          (fun i j => IndepFun (fun ω => g (S.Z i ω)) (fun ω => g (S.Z j ω)) μ) := by
        intro i _ j _ hij
        exact hindep_comp.indepFun hij
      have hfun_eq : (fun ω => ∑ i ∈ split.foldB n, g (S.Z i ω))
          = ∑ i ∈ split.foldB n, fun ω => g (S.Z i ω) := by
        funext ω; rw [Finset.sum_apply]
      rw [hfun_eq, ProbabilityTheory.IndepFun.variance_sum
        (fun i _ => hmemLp_i i) hpair]
      simp only [hvar_i]
      rw [Finset.sum_const, nsmul_eq_mul]
    have hcong : Yn n = fun ω => ((split.foldB n).card : ℝ)⁻¹
        * (fun ω => ∑ i ∈ split.foldB n, g (S.Z i ω)) ω := rfl
    rw [hcong, variance_const_mul, hsum_var]
    have hcard_ne : ((split.foldB n).card : ℝ) ≠ 0 := by positivity
    field_simp
  -- Chebyshev bound on the fold-B average, eventually (once `|B(n)| > 0`).
  have hcard_pos : ∀ᶠ n in atTop, 0 < (split.foldB n).card := by
    have := split.foldB_card_tendsto
    filter_upwards [(tendsto_atTop.mp this) 1] with n hn
    exact hn
  have hcheb : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      μ {ω | ε ≤ |Yn n ω - ∫ x, g x ∂P|}
        ≤ ENNReal.ofReal (V / (ε ^ 2 * (split.foldB n).card)) := by
    intro ε hε
    filter_upwards [hcard_pos] with n hcard
    have hmemLp_Yn : MemLp (Yn n) 2 μ := by
      rw [hYn_def]
      exact ((memLp_finset_sum _ (fun i _ => hmemLp_i i)).const_mul _)
    have hcheb_raw := ProbabilityTheory.meas_ge_le_variance_div_sq hmemLp_Yn hε
    rw [hmean n hcard] at hcheb_raw
    rw [hvar n hcard] at hcheb_raw
    -- Rewrite `(V / |B|) / ε² = V / (ε² · |B|)`.
    have hrw : V / ((split.foldB n).card : ℝ) / ε ^ 2
        = V / (ε ^ 2 * (split.foldB n).card) := by
      rw [div_div]; ring_nf
    rwa [hrw] at hcheb_raw
  -- `|B(n)| → ∞` as a real sequence.
  have hb : Tendsto (fun n => ((split.foldB n).card : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp split.foldB_card_tendsto
  exact tendsto_inProb_of_chebyshev hb hcheb

end OneShotSplit

end Causalean.Stat
