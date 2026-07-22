/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# One orientation of the asymptotic Imbens-Manski pointwise confidence argument

The finite-sample honest interval of `Inference/IntervalCI.lean` protects *both*
endpoints two-sidedly, paying a Bonferroni price (`1 − δ_L − δ_U`).  Imbens and
Manski (2004) observed that when the identified set `[L, U]` has *positive width*
`Δ = U − L > 0`, covering the single true value `θ₀ ∈ [L, U]` (rather than the
whole set) needs protection on only **one** side: as `n → ∞` the sampling error
`O(n^{-1/2})` is negligible relative to the fixed width `Δ`, so the non-coverage
risk is one-sided.  Hence a *one-sided* critical value `c = z_{1−α}` already
delivers `1 − α` coverage of `θ₀`, where the set-coverage interval would need the
two-sided `z_{1−α/2}` (cf. Stoye 2009, and Molinari 2020 §"Pointwise vs. Uniform
Coverage"; Imbens–Manski 2004, Lemma 1).

This file formalizes the lower-protected, upper-far endpoint orientation of that
argument. The proved coverage theorem uses the lower endpoint's normal limit at
the fixed one-sided cutoff and assumes the upper endpoint's far-tail failure
probability vanishes; the symmetric upper-protected orientation is not supplied
here.

## Normalization

Write the (studentized) endpoint statistics

    Sₗ,ₙ = √n (θ̂ₗ,ₙ − L) / σₗ,    Sᵤ,ₙ = √n (θ̂ᵤ,ₙ − U) / σᵤ,

each converging in distribution to `N(0,1)`.  For a fixed `θ₀ ∈ [L, U]` put the
nonnegative normalized offsets

    aₙ = √n (θ₀ − L) / σₗ ≥ 0,    bₙ = √n (U − θ₀) / σᵤ ≥ 0.

A direct computation shows the Imbens–Manski interval
`[θ̂ₗ,ₙ − c σₗ/√n, θ̂ᵤ,ₙ + c σᵤ/√n]` covers `θ₀` exactly when

    Sₗ,ₙ ≤ c + aₙ    and    −(c + bₙ) ≤ Sᵤ,ₙ.

The theorem below treats the case where the upper offset `bₙ` is the far endpoint:
its vanishing-failure hypothesis says the event `Sᵤ,ₙ < −(c + bₙ)` has probability
tending to zero. The helper `farEnd_vanishes_of_tendsto_atBot` discharges this
when the moving upper threshold tends to `−∞`, as happens when `bₙ → ∞`.

## Main results

* `gaussianMeasure_zero_one_frontier_Iic` — the standard normal gives zero mass to
  the boundary `{c}` of a closed half-line `(-∞, c]`.
* `imbensManski_pointwise_coverage` — **the lower-protected asymptotic
  guarantee.** If `Sₗ ⇒ N(0,1)`, the offsets `aₙ ≥ 0`, and the far upper endpoint
  fails with vanishing probability, then for every `ε > 0` the Imbens–Manski coverage
  probability of `θ₀` eventually exceeds `Φ(c) − ε`, where `Φ(c) = N(0,1)((-∞,c])`.
  Taking `c = z_{1−α}` (so `Φ(c) = 1 − α`) gives asymptotic coverage `≥ 1 − α`.
* `farEnd_vanishes_of_tendsto_atBot` — discharges the far-endpoint hypothesis: if
  `Sᵤ ⇒ N(0,1)` and the threshold `−(c + bₙ) → −∞` (i.e. `bₙ → ∞`, the `Δ > 0`
  regime), then `P(Sᵤ,ₙ < −(c + bₙ)) → 0`.  This is where positivity of the width
  enters, via the Gaussian tail bound `gaussian_tail_small`.

For this endpoint orientation, the two-sided-vs-one-sided gain is made precise:
the limiting lower bound is `Φ(c)` for a *one-sided* `c`, not `Φ(c) − Φ(−c)`.
Uniformity over `P` (Stoye's refinement, requiring superefficient estimation of
the nuisance width) and the symmetric upper-protected theorem are not addressed
here.
-/

import Causalean.PO.ID.Partial.Inference.Basic
import Causalean.Stat.Inference.Studentize
import Causalean.Stat.CLT.GaussianTail

/-! # Imbens-Manski Asymptotic Confidence Intervals

This file formalizes the lower-protected, upper-far orientation of the asymptotic
one-sided critical-value argument for confidence intervals covering a true scalar
parameter inside an identified interval. It relates lower-endpoint convergence
and vanishing upper far-tail failure to the Imbens-Manski parameter-coverage
refinement.

The helper `gaussianMeasure_zero_one_frontier_Iic` supplies the continuity-point
fact needed for portmanteau at a closed half-line. The theorem
`farEnd_vanishes_of_tendsto_atBot` proves that a normalized endpoint statistic
with a standard-normal limit has vanishing probability below a threshold tending
to `-infinity`. The main theorem `imbensManski_pointwise_coverage` combines the
lower endpoint's normal limit, a nonnegative lower offset, and the far-endpoint
tail condition to show eventual coverage at least `Phi(c) - epsilon` for the
one-sided critical value `c`.

Only this endpoint orientation is formalized here; the symmetric
upper-protected statement and uniform-in-distribution refinements are outside
this file. -/

namespace Causalean.PartialID.Inference

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The standard normal gives zero mass to the boundary `{c}` of the closed
half-line `(-∞, c]`; the continuity-point fact needed to apply portmanteau to a
one-sided threshold. -/
theorem gaussianMeasure_zero_one_frontier_Iic (c : ℝ) :
    gaussianMeasure 0 1 (frontier (Set.Iic c)) = 0 := by
  rw [frontier_Iic]
  exact gaussianMeasure_zero_one_singleton c

/-- **Far-endpoint failure vanishes (the `Δ > 0` regime).**
If the normalized upper-endpoint statistic `Sᵤ ⇒ N(0,1)` and the (signed)
threshold drifts to `−∞`, then the probability that `Sᵤ,ₙ` falls below it tends to
`0`.  Concretely `tₙ = −(c + bₙ)` with `bₙ → ∞` (the positive-width regime);
the proof bounds the moving tail by a fixed Gaussian tail `N(0,1)((-∞,-R])` made
arbitrarily small via `gaussian_tail_small`, then transported by portmanteau. -/
theorem farEnd_vanishes_of_tendsto_atBot
    {Su : ℕ → Ω → ℝ} (hSu : ∀ n, Measurable (Su n))
    (hSud : Tendsto_dist Su (gaussianMeasure 0 1) μ (fun n => (hSu n).aemeasurable))
    {t : ℕ → ℝ} (ht : Tendsto t atTop atBot) :
    Tendsto (fun n => (μ {ω | Su n ω < t n}).toReal) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- A fixed Gaussian lower tail below level `ε/2`.
  obtain ⟨R, hRpos, hRiic, _⟩ := gaussian_tail_small (v := 1) (ε := ε / 2) (by linarith)
  -- Portmanteau at the fixed continuity point `-R`: `P(Su,ₙ ≤ -R) → N(0,1)((-∞,-R])`.
  have hport : Tendsto (fun n => ((μ.map (Su n)) (Set.Iic (-R))).toReal) atTop
      (𝓝 ((gaussianMeasure 0 1) (Set.Iic (-R))).toReal) :=
    Tendsto_dist.tendsto_measure_of_null_frontier (fun n => (hSu n).aemeasurable) hSud
      (gaussianMeasure_zero_one_frontier_Iic (-R))
  -- Rewrite the pushforward as a probability of `Su,ₙ ≤ -R`.
  have hmapeq : ∀ n, ((μ.map (Su n)) (Set.Iic (-R))).toReal
      = (μ {ω | Su n ω ≤ -R}).toReal := by
    intro n
    rw [Measure.map_apply_of_aemeasurable (hSu n).aemeasurable measurableSet_Iic]; rfl
  rw [tendsto_congr hmapeq] at hport
  -- The Gaussian fixed tail is `≤ ε/2`.
  have hGle : ((gaussianMeasure 0 1) (Set.Iic (-R))).toReal ≤ ε / 2 := by
    have hfin : (gaussianMeasure 0 1) (Set.Iic (-R)) ≤ ENNReal.ofReal (ε / 2) := hRiic
    calc ((gaussianMeasure 0 1) (Set.Iic (-R))).toReal
        ≤ (ENNReal.ofReal (ε / 2)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfin
      _ = ε / 2 := ENNReal.toReal_ofReal (by linarith)
  -- Eventually the fixed-tail probability is within `ε/2` of its Gaussian limit, hence `< ε`.
  have hport_ev : ∀ᶠ n in atTop, (μ {ω | Su n ω ≤ -R}).toReal < ε := by
    have := (Metric.tendsto_atTop.mp hport) (ε / 2) (by linarith)
    obtain ⟨N, hN⟩ := this
    filter_upwards [eventually_ge_atTop N] with n hn
    have hd := hN n hn
    rw [Real.dist_eq] at hd
    have : (μ {ω | Su n ω ≤ -R}).toReal
        < ((gaussianMeasure 0 1) (Set.Iic (-R))).toReal + ε / 2 := by
      have := abs_lt.mp hd
      linarith [this.2]
    linarith [hGle]
  -- Eventually the moving threshold is below `-R`.
  have ht_ev : ∀ᶠ n in atTop, t n ≤ -R := by
    have := ht.eventually (eventually_le_atBot (-R))
    exact this
  -- Combine: `{Su,ₙ < tₙ} ⊆ {Su,ₙ ≤ -R}` once `tₙ ≤ -R`.
  rw [eventually_atTop] at hport_ev ht_ev
  obtain ⟨N1, hN1⟩ := hport_ev
  obtain ⟨N2, hN2⟩ := ht_ev
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hprob := hN1 n (le_trans (le_max_left N1 N2) hn)
  have htn := hN2 n (le_trans (le_max_right N1 N2) hn)
  have hsub : {ω | Su n ω < t n} ⊆ {ω | Su n ω ≤ -R} := by
    intro ω hω
    exact le_of_lt (lt_of_lt_of_le hω htn)
  have hmono : (μ {ω | Su n ω < t n}).toReal ≤ (μ {ω | Su n ω ≤ -R}).toReal :=
    ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)
  rw [Real.dist_eq, sub_zero]
  have hnn : 0 ≤ (μ {ω | Su n ω < t n}).toReal := ENNReal.toReal_nonneg
  rw [abs_of_nonneg hnn]
  linarith [hmono, hprob]

/-- **Lower-protected Imbens-Manski pointwise coverage.** If the normalized lower
endpoint has a standard-normal limit, the lower offset is nonnegative, and the
upper endpoint is the far endpoint whose lower-tail miss probability vanishes,
then the eventual coverage of that point is at least the normal one-sided
probability, up to any positive tolerance.

Here `Sl` is the normalized lower-endpoint statistic, `Su` is the normalized
upper-endpoint statistic, `c` is the one-sided critical value, `aL` is the
nonnegative lower offset of the point inside the interval, and `bU` is the upper
offset. The conclusion says that the event

    Sl n ≤ c + aL n  and  -(c + bU n) ≤ Su n

has probability at least `Φ(c) - ε` for all sufficiently large `n`, where `Φ` is
the standard-normal distribution function. This theorem is one endpoint
orientation only; it does not claim simultaneous coverage over the whole
identified set or supply the symmetric upper-protected orientation. -/
theorem imbensManski_pointwise_coverage
    {Sl Su : ℕ → Ω → ℝ} (hSl : ∀ n, Measurable (Sl n)) (hSu : ∀ n, Measurable (Su n))
    (hSld : Tendsto_dist Sl (gaussianMeasure 0 1) μ (fun n => (hSl n).aemeasurable))
    (c : ℝ) {aL bU : ℕ → ℝ} (haL : ∀ n, 0 ≤ aL n)
    (hfar : Tendsto (fun n => (μ {ω | Su n ω < -(c + bU n)}).toReal) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, (gaussianMeasure 0 1 (Set.Iic c)).toReal - ε ≤
      (μ {ω | Sl n ω ≤ c + aL n ∧ -(c + bU n) ≤ Su n ω}).toReal := by
  set g : ℝ := (gaussianMeasure 0 1 (Set.Iic c)).toReal with hg
  -- F1: portmanteau at the fixed lower threshold `c`.
  have hF1 : Tendsto (fun n => (μ {ω | Sl n ω ≤ c}).toReal) atTop (𝓝 g) := by
    have hport : Tendsto (fun n => ((μ.map (Sl n)) (Set.Iic c)).toReal) atTop (𝓝 g) :=
      Tendsto_dist.tendsto_measure_of_null_frontier (fun n => (hSl n).aemeasurable) hSld
        (gaussianMeasure_zero_one_frontier_Iic c)
    refine hport.congr ?_
    intro n
    rw [Measure.map_apply_of_aemeasurable (hSl n).aemeasurable measurableSet_Iic]; rfl
  -- Eventually `P(Sₗ,ₙ ≤ c) > g - ε/2`.
  have hlo_ev : ∀ᶠ n in atTop, g - ε / 2 < (μ {ω | Sl n ω ≤ c}).toReal := by
    have := (Metric.tendsto_atTop.mp hF1) (ε / 2) (by linarith)
    obtain ⟨N, hN⟩ := this
    filter_upwards [eventually_ge_atTop N] with n hn
    have hd := hN n hn
    rw [Real.dist_eq] at hd
    linarith [(abs_lt.mp hd).1]
  -- Eventually the far-endpoint failure probability is `< ε/2`.
  have hfar_ev : ∀ᶠ n in atTop, (μ {ω | Su n ω < -(c + bU n)}).toReal < ε / 2 := by
    have := (Metric.tendsto_atTop.mp hfar) (ε / 2) (by linarith)
    obtain ⟨N, hN⟩ := this
    filter_upwards [eventually_ge_atTop N] with n hn
    have hd := hN n hn
    rw [Real.dist_eq, sub_zero] at hd
    have hnn : 0 ≤ (μ {ω | Su n ω < -(c + bU n)}).toReal := ENNReal.toReal_nonneg
    rw [abs_of_nonneg hnn] at hd
    exact hd
  filter_upwards [hlo_ev, hfar_ev] with n hlo hfarn
  -- Names for the two endpoint events.
  set A : Set Ω := {ω | Sl n ω ≤ c + aL n} with hA
  set B : Set Ω := {ω | -(c + bU n) ≤ Su n ω} with hB
  have hBmeas : MeasurableSet B := measurableSet_le measurable_const (hSu n)
  -- The coverage event is `A ∩ B`.
  have hcov_eq : {ω | Sl n ω ≤ c + aL n ∧ -(c + bU n) ≤ Su n ω} = A ∩ B := rfl
  -- `Bᶜ` is exactly the far-endpoint failure set.
  have hBc_eq : Bᶜ = {ω | Su n ω < -(c + bU n)} := by
    ext ω; simp only [hB, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  -- Inclusion–exclusion lower bound: `P(A∩B) ≥ P(A) - P(Bᶜ)`.
  have hsplit : μ A ≤ μ (A ∩ B) + μ Bᶜ := by
    calc μ A = μ (A ∩ B) + μ (A \ B) := (measure_inter_add_diff A hBmeas).symm
      _ ≤ μ (A ∩ B) + μ Bᶜ := by
          gcongr
          exact fun ω h => h.2
  have hsplitR : (μ A).toReal ≤ (μ (A ∩ B)).toReal + (μ Bᶜ).toReal := by
    have h := ENNReal.toReal_mono (by
      exact ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _, measure_ne_top μ _⟩) hsplit
    rwa [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at h
  -- `P(A) ≥ P(Sₗ,ₙ ≤ c)` since `aₙ ≥ 0` enlarges the event.
  have hAmono : (μ {ω | Sl n ω ≤ c}).toReal ≤ (μ A).toReal := by
    refine ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono ?_)
    intro ω hω
    have hω' : Sl n ω ≤ c := hω
    exact le_trans hω' (by linarith [haL n])
  rw [hcov_eq]
  rw [hBc_eq] at hsplitR
  linarith [hsplitR, hAmono, hlo, hfarn]

end Causalean.PartialID.Inference
