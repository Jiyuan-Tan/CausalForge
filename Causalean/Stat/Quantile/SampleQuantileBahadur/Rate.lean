/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bahadur representation — root-n rate

Root-`n` consistency of the sample quantile, `√n (q̂ₙ − q₀) = O_p(1)`, assembled
from the fixed-`q₀` empirical-cdf CLT, the Taylor increment of `F`, and a Slutsky
tail bound. Builds on the empirical-process oscillation layer in `.Oscillation`.
-/

import Causalean.Stat.Quantile.SampleQuantileBahadur.Oscillation
import Causalean.Stat.CLT.GaussianTail

/-! # Root-n Rate for the Sample Quantile

This file proves `IIDSample.sampleQuantile_rate`, the `O_p(1)` bound for
`sqrt n * (qhat_n - q₀)`. The proof combines the fixed-quantile empirical-cdf
CLT, tightness of the centered empirical process at `q₀`, Taylor control of the
two local endpoints `q₀ + M / sqrt n` and `q₀ - M / sqrt n`, and a Slutsky-style
tail argument based on the sample quantile switching relation.

The supporting declarations include measurability of `IIDSample.empProcess`,
the fixed-`q₀` CLT `IIDSample.empProcess_q0_tendsto_normal`, tightness
`IIDSample.empProcess_q0_bigO`, and the closed-set portmanteau helper
`Tendsto_dist.limsup_measure_closed_le`.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {P : Measure ℝ}
variable [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

/-! ## Root-n rate -/

/-! ### Helper facts for root-n consistency.

The root-n consistency proof is assembled from four ingredients, isolated here
as lemmas:

* `empProcess_q0_tendsto_normal` — the fixed-`q₀` empirical-cdf CLT, restated
  for `empProcess(·,q₀)` with limit `N(0, τ(1−τ))`.
* `empProcess_q0_bigO` — tightness of `empProcess(·,q₀)` (`O_p(1)`), a direct
  corollary of the CLT.
* `cdf_increment_sqrt_tendsto` (imported from `.Oscillation`) — the Taylor limit
  `√n (F(q₀+M/√n) − F(q₀)) → f₀·M` from `HasDerivAt F f₀ q₀`.
* `gaussian_tail_small` — for a nondegenerate variance the symmetric Gaussian
  half-line tails can be made `< ε`. -/

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Measurability of `empProcess(·,y)` (a constant times a measurable sample
mean minus a constant). -/
lemma IIDSample.measurable_empProcess (S : IIDSample Ω ℝ μ P) (n : ℕ) (y : ℝ) :
    Measurable (fun ω => S.empProcess n ω y) := by
  unfold IIDSample.empProcess IIDSample.empiricalCDF IIDSample.sampleMean
  refine Measurable.mul measurable_const ?_
  refine Measurable.sub (Measurable.const_mul ?_ _) measurable_const
  exact Finset.measurable_sum _ fun i _ => (measurable_cdfStat y).comp (S.meas i)

/-- **Fixed-quantile empirical-process CLT.**
`empProcess(·,q₀) = √n(F̂ₙ(q₀) − F(q₀)) ⇒ N(0, τ(1−τ))`.
Restates `empiricalCDF_tendsto_normal` at `y = q₀`, using `cdf P q₀ = τ`. -/
lemma IIDSample.empProcess_q0_tendsto_normal (S : IIDSample Ω ℝ μ P)
    {τ q₀ f₀ : ℝ} (hreg : SampleQuantileReg P τ q₀ f₀)
    (hmeas : ∀ n : ℕ, AEMeasurable (fun ω => S.empProcess n ω q₀) μ) :
    Tendsto_dist (fun n ω => S.empProcess n ω q₀)
      (gaussianMeasure 0 (τ * (1 - τ))) μ hmeas := by
  -- `rescaledEstimator (F̂ q₀) (F q₀) range n = empProcess(·,q₀)` (card_range).
  have hθeq : (IsAsymLinear.rescaledEstimator (S.empiricalCDF q₀) (cdf P q₀)
        (fun m => Finset.range m)) = fun n ω => S.empProcess n ω q₀ := by
    funext n ω
    simp only [IsAsymLinear.rescaledEstimator, IIDSample.empProcess, Finset.card_range]
  -- Measurability obligations for the underlying CLT.
  have hθn_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.rescaledEstimator (S.empiricalCDF q₀) (cdf P q₀)
        (fun m => Finset.range m) n) μ := by
    intro n; rw [hθeq]; exact (S.measurable_empProcess n q₀).aemeasurable
  have hSum_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.normalizedSum S (cdfIF P q₀) (fun m => Finset.range m) n) μ := by
    intro n
    refine (Measurable.const_mul ?_ _).aemeasurable
    exact Finset.measurable_sum _ fun i _ => (measurable_cdfIF q₀).comp (S.meas i)
  have h := empiricalCDF_tendsto_normal S q₀ hθn_meas hSum_meas
  -- Rewrite the *goal's* variance `τ → cdf P q₀` (the goal's `hmeas` does not
  -- mention `cdf`, so this is motive-safe), matching `h`'s limit measure.
  rw [← hreg.cdf_eq]
  -- `h : Tendsto_dist (rescaledEstimator …) (gaussianMeasure 0 (F q₀*(1-F q₀))) μ hθn_meas`.
  unfold Tendsto_dist at h ⊢
  -- The two probability-measure sequences agree pointwise (same function).
  refine h.congr' ?_
  filter_upwards with n
  apply Subtype.ext
  change μ.map (IsAsymLinear.rescaledEstimator (S.empiricalCDF q₀) (cdf P q₀)
      (fun m => Finset.range m) n) = μ.map (fun ω => S.empProcess n ω q₀)
  rw [hθeq]

/-- **Fixed-quantile empirical-process tightness.**  `empProcess(·,q₀)` is `O_p(1)`. -/
lemma IIDSample.empProcess_q0_bigO (S : IIDSample Ω ℝ μ P)
    {τ q₀ f₀ : ℝ} (hreg : SampleQuantileReg P τ q₀ f₀) :
    IsBigOp (fun n ω => S.empProcess n ω q₀) (fun _ => (1 : ℝ)) μ :=
  Tendsto_dist.tightness (fun n => (S.measurable_empProcess n q₀).aemeasurable)
    (S.empProcess_q0_tendsto_normal hreg _)

/-- **Portmanteau (closed-set limsup).**  If `Xn ⇒ Q` in distribution, then for
every closed `F`, `limsup μ{ω | Xn n ω ∈ F} ≤ Q F`.  Mirrors the closed-set
half of `Tendsto_dist.tightness`. -/
theorem Tendsto_dist.limsup_measure_closed_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Xn : ℕ → Ω → ℝ} {Q : Measure ℝ} [IsProbabilityMeasure Q]
    (hXn : ∀ n, AEMeasurable (Xn n) μ)
    (hX : Tendsto_dist Xn Q μ hXn)
    {F : Set ℝ} (hF : IsClosed F) :
    Filter.limsup (fun n => μ {ω | Xn n ω ∈ F}) atTop ≤ Q F := by
  unfold Tendsto_dist at hX
  let μs : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨μ.map (Xn n), Measure.isProbabilityMeasure_map (hXn n)⟩
  let ν : ProbabilityMeasure ℝ := ⟨Q, inferInstance⟩
  have hpm : Filter.limsup (fun n => ((μs n : ProbabilityMeasure ℝ) : Measure ℝ) F) atTop
      ≤ (ν : Measure ℝ) F :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto (μs := μs) (μ := ν) hX hF
  refine le_trans (Filter.limsup_le_limsup (Eventually.of_forall ?_)) hpm
  intro n
  change μ {ω | Xn n ω ∈ F} ≤ (μ.map (Xn n)) F
  rw [Measure.map_apply_of_aemeasurable (hXn n) hF.measurableSet]
  exact le_refl _

-- `gaussian_tail_small` (Gaussian half-line tail control) lives in
-- `Causalean/Stat/CLT/GaussianTail.lean`, imported above.

/-- **Root-`n` consistency of the sample quantile.**
`√n (q̂ₙ − q₀) = O_p(1)`.  From L2 + the fixed-`q₀` empirical-cdf CLT and a
Slutsky tail bound on `P(q̂ₙ > q₀ + M/√n) = P(τ > F̂ₙ(q₀ + M/√n))`. -/
lemma IIDSample.sampleQuantile_rate (S : IIDSample Ω ℝ μ P)
    {τ q₀ f₀ : ℝ} (hreg : SampleQuantileReg P τ q₀ f₀) :
    IsBigOp (fun n ω => Real.sqrt (n : ℝ) * (S.sampleQuantile τ n ω - q₀))
      (fun _ => (1 : ℝ)) μ := by
  classical
  set σ2 : ℝ := τ * (1 - τ) with hσ2
  have hσ2pos : 0 < σ2 := by
    rw [hσ2]; exact mul_pos hreg.tau_pos (by linarith [hreg.tau_lt_one])
  have hf0 : 0 < f₀ := hreg.density_pos
  intro ε hε
  -- Choose the Gaussian half-line cutoff `R` at level `ε/2` (both tails).
  obtain ⟨R, hRpos, hRiic, hRici⟩ := gaussian_tail_small (v := σ2) (ε := ε / 2) (by linarith)
  -- The window constant `M := 4R/f₀`, so that `f₀·M/4 = R`.
  refine ⟨4 * R / f₀, ?_⟩
  set M : ℝ := 4 * R / f₀ with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  have hfM4 : f₀ * M / 4 = R := by rw [hM]; field_simp
  -- Abbreviations: the empirical process at `q₀`, and the two L2 increments.
  set Gq : ℕ → Ω → ℝ := fun n ω => S.empProcess n ω q₀ with hGq
  -- The two endpoints `y± = q₀ ± M/√n`.
  set Δp : ℕ → Ω → ℝ := fun n ω =>
    S.empProcess n ω (q₀ + M / Real.sqrt (n : ℝ)) - S.empProcess n ω q₀ with hΔp
  set Δm : ℕ → Ω → ℝ := fun n ω =>
    S.empProcess n ω (q₀ + (-M) / Real.sqrt (n : ℝ)) - S.empProcess n ω q₀ with hΔm
  -- L2: both increments vanish in probability.
  have hL2p : Tendsto_inProb Δp (fun _ => 0) μ :=
    S.empProcess_increment_tendsto_zero hreg M
  have hL2m : Tendsto_inProb Δm (fun _ => 0) μ :=
    S.empProcess_increment_tendsto_zero hreg (-M)
  -- Δ-tail events vanish: `μ{|Δ| > R} → 0` (squeeze below the `≤`-tail from L2).
  have hΔp_tail : Tendsto (fun n => μ {ω | R < |Δp n ω|}) atTop (𝓝 0) := by
    have h := (tendstoInMeasure_iff_norm.mp hL2p) R hRpos
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
      (fun n => zero_le _) (fun n => measure_mono fun ω hω => ?_)
    simp only [Set.mem_setOf_eq, sub_zero, Real.norm_eq_abs] at hω ⊢
    exact le_of_lt hω
  have hΔm_tail : Tendsto (fun n => μ {ω | R < |Δm n ω|}) atTop (𝓝 0) := by
    have h := (tendstoInMeasure_iff_norm.mp hL2m) R hRpos
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
      (fun n => zero_le _) (fun n => measure_mono fun ω hω => ?_)
    simp only [Set.mem_setOf_eq, sub_zero, Real.norm_eq_abs] at hω ⊢
    exact le_of_lt hω
  -- Taylor: `√n(F(q₀)−F(y₊)) → −f₀M` and `√n(F(q₀)−F(y₋)) → f₀M`.
  have hTayp : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) *
      (τ - cdf P (q₀ + M / Real.sqrt (n : ℝ)))) atTop (𝓝 (- (f₀ * M))) := by
    have h := cdf_increment_sqrt_tendsto hreg M
    have h' := h.neg
    rw [hreg.cdf_eq] at h'
    refine h'.congr fun n => ?_
    ring
  have hTaym : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) *
      (τ - cdf P (q₀ + (-M) / Real.sqrt (n : ℝ)))) atTop (𝓝 (f₀ * M)) := by
    have h := cdf_increment_sqrt_tendsto hreg (-M)
    have h' := h.neg
    rw [hreg.cdf_eq, mul_neg] at h'
    simp only [neg_neg] at h'
    refine h'.congr fun n => ?_
    ring
  -- Eventually `√n(τ−F(y₊)) < −f₀M/2`.
  have hTaypEv : ∀ᶠ n : ℕ in atTop, Real.sqrt (n : ℝ) *
      (τ - cdf P (q₀ + M / Real.sqrt (n : ℝ))) < - (f₀ * M / 2) := by
    have hlt : - (f₀ * M) < - (f₀ * M / 2) := by nlinarith [hMpos, hf0]
    exact hTayp.eventually (eventually_lt_nhds hlt)
  -- Eventually `√n(τ−F(y₋)) > f₀M/2`.
  have hTaymEv : ∀ᶠ n : ℕ in atTop, f₀ * M / 2 < Real.sqrt (n : ℝ) *
      (τ - cdf P (q₀ + (-M) / Real.sqrt (n : ℝ))) := by
    have hlt : f₀ * M / 2 < f₀ * M := by nlinarith [hMpos, hf0]
    exact hTaym.eventually (eventually_gt_nhds hlt)
  -- The single closed exceptional set `F = Iic(−R) ∪ Ici R`.
  set F : Set ℝ := Set.Iic (-R) ∪ Set.Ici R with hF
  have hFclosed : IsClosed F := isClosed_Iic.union isClosed_Ici
  -- Portmanteau on `F`, and `Q(F) ≤ ε` (disjoint half-lines, `R > 0`).
  have hcl : Filter.limsup (fun n => μ {ω | Gq n ω ∈ F}) atTop
      ≤ gaussianMeasure 0 σ2 F := by
    refine Tendsto_dist.limsup_measure_closed_le
      (fun n => (S.measurable_empProcess n q₀).aemeasurable) ?_ hFclosed
    exact S.empProcess_q0_tendsto_normal hreg _
  have hQF : gaussianMeasure 0 σ2 F ≤ ENNReal.ofReal ε := by
    refine le_trans (measure_union_le _ _) ?_
    refine le_trans (add_le_add hRiic hRici) ?_
    rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
    apply le_of_eq; congr 1; ring
  -- The combined increment-tail sequence vanishes.
  have hΔboth_tail : Tendsto
      (fun n => μ {ω | R < |Δp n ω|} + μ {ω | R < |Δm n ω|}) atTop (𝓝 0) := by
    have := hΔp_tail.add hΔm_tail; simpa using this
  -- CORE event inclusion (eventually in `n`):
  -- `{M < |Xn|} ⊆ {Gq ∈ F} ∪ {R<|Δp|} ∪ {R<|Δm|}`.
  have hcore : ∀ᶠ n : ℕ in atTop,
      μ {ω | M * (fun _ => (1 : ℝ)) n <
          |Real.sqrt (n : ℝ) * (S.sampleQuantile τ n ω - q₀)|}
        ≤ μ {ω | Gq n ω ∈ F}
          + (μ {ω | R < |Δp n ω|} + μ {ω | R < |Δm n ω|}) := by
    filter_upwards [hTaypEv, hTaymEv, eventually_ge_atTop 1] with n hyp hym hn1
    -- Positive `√n`.
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hn1)
    have hsq : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
    have hnpos' : 0 < n := lt_of_lt_of_le zero_lt_one hn1
    refine le_trans (measure_mono ?_) (le_trans (measure_union_le _ _)
      (add_le_add (le_refl _) (measure_union_le _ _)))
    intro ω hω
    simp only [Set.mem_setOf_eq, mul_one] at hω
    -- Switching relation specialised at `ω, n`.
    have hsw := fun x => S.sampleQuantile_le_iff hnpos' ω hreg.tau_pos hreg.tau_lt_one x
    -- Unfold the empirical-process / cdf relation at an endpoint `y`.
    -- `empProcess n ω y = √n F̂ₙ(y) − √n F(y)`.
    set X : ℝ := Real.sqrt (n : ℝ) * (S.sampleQuantile τ n ω - q₀) with hX
    -- `M < |X|` ⇒ `M < X` (upper) or `X < -M` (lower).
    rcases lt_abs.mp hω with hup | hlow
    · -- UPPER tail: into `{Gq ∈ F}` (via `Iic(−R)`) or `{R<|Δp|}`.
      set y : ℝ := q₀ + M / Real.sqrt (n : ℝ) with hy
      -- `M < X` ⇒ `q₀ + M/√n < q̂ₙ` ⇒ `¬ q̂ₙ ≤ y` ⇒ `F̂ₙ(y) < τ`.
      have hqgt : y < S.sampleQuantile τ n ω := by
        rw [hy]
        have : M / Real.sqrt (n : ℝ) < S.sampleQuantile τ n ω - q₀ := by
          rw [div_lt_iff₀ hsq]; rw [hX] at hup; linarith [hup]
        linarith
      have hFlt : S.empiricalCDF y n ω < τ := by
        by_contra hcon; push_neg at hcon
        exact absurd ((hsw y).mpr hcon) (not_le.mpr hqgt)
      -- Translate to `empProcess y < √n(τ − F(y))`.
      have hempY : S.empProcess n ω y < Real.sqrt (n : ℝ) * (τ - cdf P y) := by
        have : Real.sqrt (n : ℝ) * S.empiricalCDF y n ω
            < Real.sqrt (n : ℝ) * τ := by exact mul_lt_mul_of_pos_left hFlt hsq
        simp only [IIDSample.empProcess]; nlinarith [this]
      -- Combine with Taylor: `empProcess y < −f₀M/2`.
      have hempY2 : S.empProcess n ω y < - (f₀ * M / 2) := lt_trans hempY (by rw [hy]; exact hyp)
      -- Case on the increment.
      by_cases hΔ : R < |Δp n ω|
      · right; left; exact hΔ
      · left
        -- `|Δp| ≤ R` ⇒ `Gq ≤ −R` ⇒ `Gq ∈ F`.
        push_neg at hΔ
        simp only [Set.mem_setOf_eq, hF, Set.mem_union, Set.mem_Iic, Set.mem_Ici, hGq]
        left
        have hΔeq : S.empProcess n ω y = S.empProcess n ω q₀ + Δp n ω := by
          rw [hΔp]; simp only [hy]; ring
        have hbound : -(Δp n ω) ≤ R := by
          have := neg_le_of_abs_le hΔ; linarith [this]
        have : S.empProcess n ω q₀ < - (f₀ * M / 2) - Δp n ω := by
          rw [hΔeq] at hempY2; linarith
        rw [← hfM4]; rw [← hfM4] at hbound
        linarith [this, hbound]
    · -- LOWER tail: into `{Gq ∈ F}` (via `Ici R`) or `{R<|Δm|}`.
      set y : ℝ := q₀ + (-M) / Real.sqrt (n : ℝ) with hy
      -- `M < -X` ⇒ `q̂ₙ − q₀ < -M/√n` ⇒ `q̂ₙ ≤ y` ⇒ `τ ≤ F̂ₙ(y)`.
      have hX' : S.sampleQuantile τ n ω - q₀ < -M / Real.sqrt (n : ℝ) := by
        rw [lt_div_iff₀ hsq]; rw [hX] at hlow; nlinarith [hlow]
      have hqle : S.sampleQuantile τ n ω ≤ y := by rw [hy]; linarith [hX']
      have hFge : τ ≤ S.empiricalCDF y n ω := (hsw y).mp hqle
      -- Translate to `empProcess y ≥ √n(τ − F(y))`.
      have hempY : Real.sqrt (n : ℝ) * (τ - cdf P y) ≤ S.empProcess n ω y := by
        have : Real.sqrt (n : ℝ) * τ ≤ Real.sqrt (n : ℝ) * S.empiricalCDF y n ω :=
          mul_le_mul_of_nonneg_left hFge hsq.le
        simp only [IIDSample.empProcess]; nlinarith [this]
      have hempY2 : f₀ * M / 2 < S.empProcess n ω y :=
        lt_of_lt_of_le (by rw [hy]; exact hym) hempY
      by_cases hΔ : R < |Δm n ω|
      · right; right; exact hΔ
      · left
        push_neg at hΔ
        simp only [Set.mem_setOf_eq, hF, Set.mem_union, Set.mem_Iic, Set.mem_Ici, hGq]
        right
        have hΔeq : S.empProcess n ω y = S.empProcess n ω q₀ + Δm n ω := by
          rw [hΔm]; simp only [hy]; ring
        have hbound : Δm n ω ≤ R := le_trans (le_abs_self _) hΔ
        have : f₀ * M / 2 - Δm n ω < S.empProcess n ω q₀ := by
          rw [hΔeq] at hempY2; linarith
        rw [← hfM4]; rw [← hfM4] at hbound
        linarith [this, hbound]
  -- ASSEMBLE: `limsup` of the eventual bound `μ{Gq∈F} + (vanishing increment tails)`.
  calc Filter.limsup (fun n : ℕ => μ {ω | M * (fun _ => (1 : ℝ)) n <
            |Real.sqrt (n : ℝ) * (S.sampleQuantile τ n ω - q₀)|}) atTop
      ≤ Filter.limsup (fun n => μ {ω | Gq n ω ∈ F}
            + (μ {ω | R < |Δp n ω|} + μ {ω | R < |Δm n ω|})) atTop :=
        Filter.limsup_le_limsup hcore
    _ = Filter.limsup (fun n => μ {ω | Gq n ω ∈ F}) atTop := by
        -- the increment tails vanish, so they drop out of the `limsup`.
        exact ENNReal.limsup_add_of_right_tendsto_zero hΔboth_tail
          (fun n => μ {ω | Gq n ω ∈ F})
    _ ≤ gaussianMeasure 0 σ2 F := hcl
    _ ≤ ENNReal.ofReal ε := hQF

end Causalean.Stat
