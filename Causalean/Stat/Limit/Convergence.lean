/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Convergence modes and stochastic order for ℝ-valued random variables

Causal-agnostic primitives for the estimation layer.  Wraps Mathlib's
`TendstoInMeasure` and `eLpNorm`; introduces `Tendsto_dist`, `IsBigOp`, and
`IsLittleOp` matching the natural-language definitions in
`doc/basic_concepts/po/estimation.tex` (`def:est-conv-prob`,
`def:est-conv-l2`, `def:est-conv-dist`, `def:est-stoch-order`).

All declarations are proved.  The arithmetic lemmas
`IsLittleOp.mul_isBigOp`, `IsBigOp.add`, and
`IsBigOp.mul_isLittleOp_one_isLittleOp`, plus the Δ-method helpers
`Tendsto_dist.tightness` and `IsBigOp.const_mul_tendsto_zero`, are
candidates for upstream contribution to Mathlib.
-/

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Basic
import Causalean.Mathlib.ConvergenceInDistribution

/-!
Defines scalar convergence in probability, L² convergence, convergence in distribution, and
stochastic-order notation used by the estimation layer.

The core predicates are `Tendsto_inProb`, `Tendsto_L2`, `Tendsto_dist`,
`IsBigOp`, and `IsLittleOp`.  The main theorem set includes deterministic-scalar
Slutsky for distributional convergence (`Tendsto_dist.const_mul_tendsto`),
tightness from convergence in distribution (`Tendsto_dist.tightness`),
degenerate Slutsky (`IsBigOp.const_mul_tendsto_zero`), and stochastic-order
arithmetic such as `IsLittleOp.add_eventually_nonneg_rate`,
`IsLittleOp.mul_isBigOp`, `IsBigOp.add`, and
`IsBigOp.mul_isLittleOp_one_isLittleOp`.
-/

namespace Causalean.Stat

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Convergence in probability -/

/-- A sequence of real random variables converges in probability to a limit
when, for every positive tolerance, the probability that the absolute error
exceeds that tolerance tends to zero.

This is the project-level wrapper around Mathlib's convergence-in-measure
predicate along the natural-number limit. -/
def Tendsto_inProb (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (μ : Measure Ω) : Prop :=
  TendstoInMeasure μ Xn atTop X

/-! ## L² convergence -/

/-- `Tendsto_L2 Xn X μ` is convergence in `L²(μ)` of `Xn` to `X`. -/
def Tendsto_L2 (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (μ : Measure Ω) : Prop :=
  Tendsto (fun n => eLpNorm (fun ω => Xn n ω - X ω) 2 μ) atTop (𝓝 0)

/-! ## Convergence in distribution

Defined as weak convergence of the pushforward measures of `Xn` to a target
probability measure `Q` on ℝ.  Phrased at the measure level (rather than as
convergence to a limiting random variable) so the target laws — e.g. a
Gaussian — can be supplied directly.  A thin re-statement wrapper may be
needed once the upstream `CLT` repo is wired in. -/
/-- Convergence in distribution means that the laws of the random variables
converge weakly to a specified probability law on the real line.

This is the project-level scalar convergence-in-distribution wrapper, phrased directly
in terms of pushforward probability measures. -/
def Tendsto_dist (Xn : ℕ → Ω → ℝ) (Q : Measure ℝ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
    (hXn : ∀ n, AEMeasurable (Xn n) μ) : Prop :=
  Tendsto (β := ProbabilityMeasure ℝ)
    (fun n =>
      ⟨μ.map (Xn n), Measure.isProbabilityMeasure_map (hXn n)⟩) atTop
    (𝓝 ⟨Q, ‹IsProbabilityMeasure Q›⟩)

/-- Deterministic-scalar Slutsky for the project's measure-level
`Tendsto_dist` wrapper.

If `Xn ⇒ Q` and `a n → a₀`, then `a n * Xn ⇒ Q.map (fun x => a₀ * x)`.
The nontrivial weak-convergence fact is isolated in
`MeasureTheory.ProbabilityMeasure.tendsto_map_mul_of_tendsto`. -/
theorem Tendsto_dist.const_mul_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Xn : ℕ → Ω → ℝ} {Q : Measure ℝ} [IsProbabilityMeasure Q]
    {a : ℕ → ℝ} {a₀ : ℝ}
    (hXn : ∀ n, AEMeasurable (Xn n) μ)
    (hScaled : ∀ n, AEMeasurable (fun ω => a n * Xn n ω) μ)
    [IsProbabilityMeasure (Q.map (fun x : ℝ => a₀ * x))]
    (hX : Tendsto_dist Xn Q μ hXn)
    (ha : Tendsto a atTop (𝓝 a₀)) :
    Tendsto_dist (fun n ω => a n * Xn n ω)
      (Q.map (fun x : ℝ => a₀ * x)) μ hScaled := by
  unfold Tendsto_dist at hX ⊢
  have hpm := MeasureTheory.ProbabilityMeasure.tendsto_map_mul_of_tendsto hX ha
  refine hpm.congr' ?_
  filter_upwards with n
  apply Subtype.ext
  change Measure.map (fun x : ℝ => a n * x) (μ.map (Xn n))
    = μ.map (fun ω => a n * Xn n ω)
  rw [AEMeasurable.map_map_of_aemeasurable]
  · rfl
  · exact (measurable_const.mul measurable_id).aemeasurable
  · exact hXn n

/-! ## Stochastic order -/

/-- `IsBigOp Xn rn μ`: the sequence `Xn` is bounded in probability at rate
`rn` under `μ`.  Matches `def:est-stoch-order`(1):

  ∀ ε > 0, ∃ M, limsup_n μ {ω : |Xn n ω| > M · rn n} ≤ ε. -/
def IsBigOp (Xn : ℕ → Ω → ℝ) (rn : ℕ → ℝ) (μ : Measure Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℝ,
    Filter.limsup (fun n => μ {ω | M * rn n < |Xn n ω|}) atTop
      ≤ ENNReal.ofReal ε

/-- `IsLittleOp Xn rn μ`: the sequence `Xn` is `o_p(rn)` under `μ`.  Matches
`def:est-stoch-order`(2):

  ∀ ε > 0, μ {ω : |Xn n ω| > ε · rn n} → 0. -/
def IsLittleOp (Xn : ℕ → Ω → ℝ) (rn : ℕ → ℝ) (μ : Measure Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => μ {ω | ε * rn n < |Xn n ω|}) atTop (𝓝 0)

/-! ## Tightness and degenerate Slutsky (helpers for the Δ-method)

`Tendsto_dist.tightness` says that any sequence converging in distribution
is bounded in probability (Prokhorov tightness for a single tight limit).
`IsBigOp.const_mul_tendsto_zero` is the degenerate-Slutsky helper used in
the Δ-method linearization step: `a n · X n` is `o_p(1)` whenever
`a n → 0` and `X n` is `O_p(1)`. -/

/-- **Tightness from convergence in distribution.**  If `Xn ⇒ Q` in
distribution under `μ` (with `Q` a probability measure on ℝ), then `Xn`
is `O_p(1)`.  Standard fact: any single tight limit gives a tight
sequence (Prokhorov). -/
theorem Tendsto_dist.tightness
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Xn : ℕ → Ω → ℝ} {Q : Measure ℝ} [IsProbabilityMeasure Q]
    (hXn : ∀ n, AEMeasurable (Xn n) μ)
    (hX : Tendsto_dist Xn Q μ hXn) :
    IsBigOp Xn (fun _ => (1 : ℝ)) μ := by
  intro ε hε
  let s : ℕ → Set ℝ := fun n => {x | (n : ℝ) ≤ |x|}
  have hQtail : Tendsto (fun n => Q (s n)) atTop (𝓝 0) := by
    have hs : ∀ n, NullMeasurableSet (s n) Q := by
      intro n
      exact (isClosed_le continuous_const continuous_abs).measurableSet.nullMeasurableSet
    have hm : Antitone s := by
      intro i j hij x hx
      dsimp [s] at hx ⊢
      exact le_trans (Nat.cast_le.mpr hij) hx
    have hf : ∃ n, Q (s n) ≠ ⊤ := ⟨0, measure_ne_top Q _⟩
    have hinter : (⋂ n, s n) = ∅ := by
      ext x
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_gt |x|
        exact (not_lt_of_ge (Set.mem_iInter.mp hx n)) hn
      · intro hx
        cases hx
    have ht := tendsto_measure_iInter_atTop hs hm hf
    simpa [Function.comp_def, hinter] using ht
  have hεtail_pos : 0 < ENNReal.ofReal (ε / 2) := by
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have hQevent := (ENNReal.tendsto_nhds_zero.mp hQtail) (ENNReal.ofReal (ε / 2)) hεtail_pos
  obtain ⟨N, hN⟩ := hQevent.exists
  refine ⟨(N : ℝ), ?_⟩
  let F : Set ℝ := s N
  have hFclosed : IsClosed F := by
    exact isClosed_le continuous_const continuous_abs
  unfold Tendsto_dist at hX
  let νs : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨μ.map (Xn n), Measure.isProbabilityMeasure_map (hXn n)⟩
  let ν : ProbabilityMeasure ℝ := ⟨Q, inferInstance⟩
  have hpm : Filter.limsup (fun n => ((νs n : ProbabilityMeasure ℝ) : Measure ℝ) F) atTop
      ≤ (ν : Measure ℝ) F := by
    exact ProbabilityMeasure.limsup_measure_closed_le_of_tendsto (μs := νs) (μ := ν) hX hFclosed
  have hhalf_le : ENNReal.ofReal (ε / 2) ≤ ENNReal.ofReal ε := by
    gcongr
    linarith
  have hpoint : ∀ n, μ {ω | (N : ℝ) * (fun _ => (1 : ℝ)) n < |Xn n ω|}
      ≤ ((νs n : ProbabilityMeasure ℝ) : Measure ℝ) F := by
    intro n
    change μ {ω | (N : ℝ) * (fun _ => (1 : ℝ)) n < |Xn n ω|} ≤ (μ.map (Xn n)) F
    rw [Measure.map_apply_of_aemeasurable (hXn n) hFclosed.measurableSet]
    apply measure_mono
    intro ω hω
    dsimp [F, s]
    have hω' : (N : ℝ) < |Xn n ω| := by
      simpa using hω
    exact le_of_lt hω'
  calc
    Filter.limsup (fun n => μ {ω | (N : ℝ) * (fun _ => (1 : ℝ)) n < |Xn n ω|}) atTop
        ≤ Filter.limsup (fun n => ((νs n : ProbabilityMeasure ℝ) : Measure ℝ) F) atTop := by
          exact Filter.limsup_le_limsup (Eventually.of_forall hpoint)
    _ ≤ (ν : Measure ℝ) F := hpm
    _ = Q F := rfl
    _ ≤ ENNReal.ofReal (ε / 2) := by
      simpa [F] using hN
    _ ≤ ENNReal.ofReal ε := hhalf_le

/-- **Degenerate Slutsky.**  If `a n → 0` deterministically and `Xn` is
`O_p(1)` under `μ`, then `a n · Xn` is `o_p(1)`.  Concretely: the product
of a sequence converging to `0` with a tight sequence is `o_p(1)`.

In particular, when `Xn ⇒ Q` for some probability measure `Q` and
`a n = 1/√n`, we get `a n · Xn →_p 0`.  Used in the Δ-method linearization
step to conclude `T_n − t₀ →_p 0` from `√n (T_n − t₀) ⇒ Q`. -/
theorem IsBigOp.const_mul_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Xn : ℕ → Ω → ℝ} {a : ℕ → ℝ}
    (hX : IsBigOp Xn (fun _ => (1 : ℝ)) μ)
    (ha : Tendsto a atTop (𝓝 0)) :
    IsLittleOp (fun n ω => a n * Xn n ω) (fun _ => (1 : ℝ)) μ := by
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  by_cases hδtop : δ = ⊤
  · filter_upwards with n
    simp [hδtop]
  have hδpos : 0 < δ.toReal := ENNReal.toReal_pos (ne_of_gt hδ) hδtop
  let α : ℝ := δ.toReal / 2
  have hαpos : 0 < α := by
    dsimp [α]
    linarith
  rcases hX α hαpos with ⟨M0, hM0⟩
  let M : ℝ := max M0 1
  have hMpos : 0 < M := by
    dsimp [M]
    exact lt_of_lt_of_le zero_lt_one (le_max_right M0 1)
  have hM0le : M0 ≤ M := by
    dsimp [M]
    exact le_max_left M0 1
  let A : ℕ → Set Ω := fun n => {ω | M < |Xn n ω|}
  let C : ℕ → Set Ω := fun n => {ω | ε < |a n * Xn n ω|}
  have hlimA : Filter.limsup (fun n => μ (A n)) atTop ≤ ENNReal.ofReal α := by
    refine le_trans (Filter.limsup_le_limsup (Eventually.of_forall ?_)) hM0
    intro n
    apply measure_mono
    intro ω hω
    dsimp [A] at hω ⊢
    linarith
  have hα_lt_delta : ENNReal.ofReal α < δ := by
    rw [ENNReal.ofReal_lt_iff_lt_toReal]
    · dsimp [α]
      linarith
    · dsimp [α]
      linarith [le_of_lt hδpos]
    · exact hδtop
  have hAevent := Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hlimA hα_lt_delta)
  have haevent : ∀ᶠ n in atTop, |a n| < ε / M := by
    have ht := (Metric.tendsto_nhds.mp ha) (ε / M) (div_pos hε hMpos)
    simpa [Real.dist_eq] using ht
  filter_upwards [hAevent, haevent] with n hAn han
  have hsubset : C n ⊆ A n := by
    intro ω hω
    by_contra hnot
    have hXle : |Xn n ω| ≤ M := le_of_not_gt hnot
    have hprod_lt : |a n * Xn n ω| < ε := by
      calc
        |a n * Xn n ω| = |a n| * |Xn n ω| := abs_mul (a n) (Xn n ω)
        _ ≤ |a n| * M := mul_le_mul_of_nonneg_left hXle (abs_nonneg (a n))
        _ < (ε / M) * M := mul_lt_mul_of_pos_right han hMpos
        _ = ε := by
          field_simp [hMpos.ne']
    exact (not_lt_of_ge (le_of_lt hprod_lt)) hω
  have heq : {ω | ε * (fun _ => (1 : ℝ)) n < |a n * Xn n ω|} = C n := by
    ext ω; simp [C]
  rw [heq]
  exact le_of_lt (lt_of_le_of_lt (measure_mono hsubset) hAn)

/-! ## Arithmetic of stochastic orders

Standard facts for stochastic-order bookkeeping.  These proved statements are
candidates for upstream contribution to Mathlib. -/

variable {Xn Yn : ℕ → Ω → ℝ} {rn sn : ℕ → ℝ} {μ : Measure Ω}

/-- The sum of two stochastic little-o terms is stochastic little-o for an
eventually nonnegative rate. -/
theorem IsLittleOp.add_eventually_nonneg_rate
    (hrn_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ rn n)
    (hX : IsLittleOp Xn rn μ) (hY : IsLittleOp Yn rn μ) :
    IsLittleOp (fun n ω => Xn n ω + Yn n ω) rn μ := by
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  by_cases hδtop : δ = ⊤
  · filter_upwards with n
    simp [hδtop]
  have hδpos : 0 < δ.toReal := ENNReal.toReal_pos (ne_of_gt hδ) hδtop
  let α : ℝ := δ.toReal / 4
  have hαpos : 0 < α := by
    dsimp [α]
    linarith
  let A : ℕ → Set Ω := fun n => {ω | (ε / 2) * rn n < |Xn n ω|}
  let B : ℕ → Set Ω := fun n => {ω | (ε / 2) * rn n < |Yn n ω|}
  let C : ℕ → Set Ω := fun n => {ω | ε * rn n < |Xn n ω + Yn n ω|}
  have hXevent_le := (ENNReal.tendsto_nhds_zero.mp (hX (ε / 2) (by linarith)))
    (ENNReal.ofReal α) (ENNReal.ofReal_pos.mpr hαpos)
  have hYevent_le := (ENNReal.tendsto_nhds_zero.mp (hY (ε / 2) (by linarith)))
    (ENNReal.ofReal α) (ENNReal.ofReal_pos.mpr hαpos)
  have htwo_alpha_lt_delta : ENNReal.ofReal (2 * α) < δ := by
    rw [ENNReal.ofReal_lt_iff_lt_toReal]
    · dsimp [α]
      linarith
    · dsimp [α]
      linarith [le_of_lt hδpos]
    · exact hδtop
  filter_upwards [hrn_nonneg, hXevent_le, hYevent_le] with n hrn hXA hYB
  have hsubset : C n ⊆ A n ∪ B n := by
    intro ω hω
    by_contra hnot
    have hnotA : ¬ (ε / 2) * rn n < |Xn n ω| := by
      intro hx
      exact hnot (Or.inl hx)
    have hnotB : ¬ (ε / 2) * rn n < |Yn n ω| := by
      intro hy
      exact hnot (Or.inr hy)
    have hXle : |Xn n ω| ≤ (ε / 2) * rn n := le_of_not_gt hnotA
    have hYle : |Yn n ω| ≤ (ε / 2) * rn n := le_of_not_gt hnotB
    have hsum : |Xn n ω + Yn n ω| ≤ ε * rn n := by
      calc
        |Xn n ω + Yn n ω| ≤ |Xn n ω| + |Yn n ω| :=
          abs_add_le (Xn n ω) (Yn n ω)
        _ ≤ (ε / 2) * rn n + (ε / 2) * rn n := add_le_add hXle hYle
        _ = ε * rn n := by ring
    exact not_lt_of_ge hsum hω
  exact le_of_lt <| calc
    μ {ω | ε * rn n < |Xn n ω + Yn n ω|} = μ (C n) := by
      simp [C]
    _ ≤ μ (A n ∪ B n) := measure_mono hsubset
    _ ≤ μ (A n) + μ (B n) := MeasureTheory.measure_union_le (A n) (B n)
    _ ≤ ENNReal.ofReal α + ENNReal.ofReal α := add_le_add hXA hYB
    _ = ENNReal.ofReal (2 * α) := by
      rw [← ENNReal.ofReal_add]
      · congr 1
        ring
      · linarith
      · linarith
    _ < δ := htwo_alpha_lt_delta

/-- Domination by a positive constant times a stochastic little-o term preserves
the stochastic little-o rate. -/
theorem IsLittleOp.of_abs_le_const_mul
    {C : ℝ} (hC : 0 < C) (hY : IsLittleOp Yn rn μ)
    (hbound : ∀ n ω, |Xn n ω| ≤ C * |Yn n ω|) :
    IsLittleOp Xn rn μ := by
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hYevent := (ENNReal.tendsto_nhds_zero.mp
    (hY (ε / C) (div_pos hε hC))) δ hδ
  filter_upwards [hYevent] with n hn
  refine (measure_mono ?_).trans hn
  intro ω hω
  by_contra hnot
  have hYle : |Yn n ω| ≤ (ε / C) * rn n := le_of_not_gt hnot
  have hprod : C * |Yn n ω| ≤ ε * rn n := by
    calc
      C * |Yn n ω| ≤ C * ((ε / C) * rn n) :=
        mul_le_mul_of_nonneg_left hYle hC.le
      _ = ε * rn n := by
        field_simp [hC.ne']
  exact not_lt_of_ge ((hbound n ω).trans hprod) hω

/-- The sum of two `o_p(1)` sequences is `o_p(1)`. -/
theorem IsLittleOp.add_one
    (hX : IsLittleOp Xn (fun _ => (1 : ℝ)) μ)
    (hY : IsLittleOp Yn (fun _ => (1 : ℝ)) μ) :
    IsLittleOp (fun n ω => Xn n ω + Yn n ω) (fun _ => (1 : ℝ)) μ :=
  IsLittleOp.add_eventually_nonneg_rate
    (Eventually.of_forall (fun _ => zero_le_one)) hX hY

/-- Domination by a positive constant times an `o_p(1)` sequence preserves
`o_p(1)`. -/
theorem IsLittleOp.of_abs_le_const_mul_one
    {C : ℝ} (hC : 0 < C) (hY : IsLittleOp Yn (fun _ => (1 : ℝ)) μ)
    (hbound : ∀ n ω, |Xn n ω| ≤ C * |Yn n ω|) :
    IsLittleOp Xn (fun _ => (1 : ℝ)) μ :=
  IsLittleOp.of_abs_le_const_mul (rn := fun _ => (1 : ℝ)) hC hY hbound

/-- `o_p(rn) · O_p(sn) = o_p(rn · sn)`, assuming positive rates. -/
theorem IsLittleOp.mul_isBigOp
    (hrn : ∀ n, 0 < rn n) (hsn : ∀ n, 0 < sn n)
    (hX : IsLittleOp Xn rn μ) (hY : IsBigOp Yn sn μ) :
    IsLittleOp (fun n ω => Xn n ω * Yn n ω) (fun n => rn n * sn n) μ := by
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  by_cases hδtop : δ = ⊤
  · filter_upwards with n
    simp [hδtop]
  have hδpos : 0 < δ.toReal := ENNReal.toReal_pos (ne_of_gt hδ) hδtop
  let α : ℝ := δ.toReal / 8
  have hαpos : 0 < α := by
    dsimp [α]
    linarith
  rcases hY α hαpos with ⟨M0, hM0⟩
  let M : ℝ := max M0 1
  have hMpos : 0 < M := by
    dsimp [M]
    exact lt_of_lt_of_le zero_lt_one (le_max_right M0 1)
  have hM0le : M0 ≤ M := by
    dsimp [M]
    exact le_max_left M0 1
  let A : ℕ → Set Ω := fun n => {ω | (ε / M) * rn n < |Xn n ω|}
  let B : ℕ → Set Ω := fun n => {ω | M * sn n < |Yn n ω|}
  let C : ℕ → Set Ω :=
    fun n => {ω | ε * (rn n * sn n) < |Xn n ω * Yn n ω|}
  have hlimB : Filter.limsup (fun n => μ (B n)) atTop ≤ ENNReal.ofReal α := by
    refine le_trans (Filter.limsup_le_limsup (Eventually.of_forall ?_)) hM0
    intro n
    apply measure_mono
    intro ω hω
    dsimp [B] at hω ⊢
    nlinarith [mul_le_mul_of_nonneg_right hM0le (le_of_lt (hsn n))]
  have hpoint : ∀ n, μ (C n) ≤ μ (A n) + μ (B n) := by
    intro n
    have hsubset : C n ⊆ A n ∪ B n := by
      intro ω hω
      by_contra hnot
      have hnotA : ¬ (ε / M) * rn n < |Xn n ω| := by
        intro hx
        exact hnot (Or.inl hx)
      have hnotB : ¬ M * sn n < |Yn n ω| := by
        intro hy
        exact hnot (Or.inr hy)
      have hXle : |Xn n ω| ≤ (ε / M) * rn n := le_of_not_gt hnotA
      have hYle : |Yn n ω| ≤ M * sn n := le_of_not_gt hnotB
      have hXbound_nonneg : 0 ≤ (ε / M) * rn n :=
        le_of_lt (mul_pos (div_pos hε hMpos) (hrn n))
      have hprod : |Xn n ω * Yn n ω| ≤ ε * (rn n * sn n) := by
        calc
          |Xn n ω * Yn n ω| = |Xn n ω| * |Yn n ω| :=
            abs_mul (Xn n ω) (Yn n ω)
          _ ≤ ((ε / M) * rn n) * (M * sn n) :=
            mul_le_mul hXle hYle (abs_nonneg _) hXbound_nonneg
          _ = ε * (rn n * sn n) := by
            field_simp [hMpos.ne']
      exact not_lt_of_ge hprod hω
    calc
      μ (C n) ≤ μ (A n ∪ B n) := measure_mono hsubset
      _ ≤ μ (A n) + μ (B n) := MeasureTheory.measure_union_le (A n) (B n)
  have halpha_two : ENNReal.ofReal α < ENNReal.ofReal (2 * α) := by
    rw [ENNReal.ofReal_lt_ofReal_iff]
    · linarith
    · linarith
  have hBevent := Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hlimB halpha_two)
  have hXt : Tendsto (fun n => μ (A n)) atTop (𝓝 0) := by
    simpa [A] using hX (ε / M) (div_pos hε hMpos)
  have hAevent_le := (ENNReal.tendsto_nhds_zero.mp hXt) (ENNReal.ofReal α) (by
    exact ENNReal.ofReal_pos.mpr hαpos)
  have hAevent : ∀ᶠ n in atTop, μ (A n) < ENNReal.ofReal (2 * α) := by
    filter_upwards [hAevent_le] with n hn
    exact lt_of_le_of_lt hn halpha_two
  have hfour_lt_delta : ENNReal.ofReal (4 * α) < δ := by
    rw [ENNReal.ofReal_lt_iff_lt_toReal]
    · dsimp [α]
      linarith
    · dsimp [α]
      linarith [le_of_lt hδpos]
    · exact hδtop
  filter_upwards [hAevent, hBevent] with n hAn hBn
  exact le_of_lt <| calc
    μ {ω | ε * (fun n => rn n * sn n) n < |Xn n ω * Yn n ω|} = μ (C n) := by
      simp [C]
    _ ≤ μ (A n) + μ (B n) := hpoint n
    _ < ENNReal.ofReal (2 * α) + ENNReal.ofReal (2 * α) := ENNReal.add_lt_add hAn hBn
    _ = ENNReal.ofReal (4 * α) := by
      rw [← ENNReal.ofReal_add]
      · congr 1; ring
      · linarith
      · linarith
    _ < δ := hfour_lt_delta

/-- `O_p(rn) + O_p(rn) = O_p(rn)`. -/
theorem IsBigOp.add
    (hX : IsBigOp Xn rn μ) (hY : IsBigOp Yn rn μ) :
    IsBigOp (fun n ω => Xn n ω + Yn n ω) rn μ := by
  intro ε hε
  rcases hX (ε / 4) (by linarith) with ⟨MX, hMX⟩
  rcases hY (ε / 4) (by linarith) with ⟨MY, hMY⟩
  refine ⟨MX + MY, ?_⟩
  let A : ℕ → Set Ω := fun n => {ω | MX * rn n < |Xn n ω|}
  let B : ℕ → Set Ω := fun n => {ω | MY * rn n < |Yn n ω|}
  let C : ℕ → Set Ω := fun n => {ω | (MX + MY) * rn n < |Xn n ω + Yn n ω|}
  have hpoint : ∀ n, μ (C n) ≤ μ (A n) + μ (B n) := by
    intro n
    have hsubset : C n ⊆ A n ∪ B n := by
      intro ω hω
      by_contra hnot
      have hnotA : ¬ MX * rn n < |Xn n ω| := by
        intro hx
        exact hnot (Or.inl hx)
      have hnotB : ¬ MY * rn n < |Yn n ω| := by
        intro hy
        exact hnot (Or.inr hy)
      have hXle : |Xn n ω| ≤ MX * rn n := le_of_not_gt hnotA
      have hYle : |Yn n ω| ≤ MY * rn n := le_of_not_gt hnotB
      have hsum : |Xn n ω + Yn n ω| ≤ (MX + MY) * rn n := by
        calc
          |Xn n ω + Yn n ω| ≤ |Xn n ω| + |Yn n ω| :=
            abs_add_le (Xn n ω) (Yn n ω)
          _ ≤ MX * rn n + MY * rn n := add_le_add hXle hYle
          _ = (MX + MY) * rn n := by ring
      exact not_lt_of_ge hsum hω
    calc
      μ (C n) ≤ μ (A n ∪ B n) := measure_mono hsubset
      _ ≤ μ (A n) + μ (B n) := MeasureTheory.measure_union_le (A n) (B n)
  rw [Filter.limsup_le_iff]
  intro y hy
  have hquarter_half : ENNReal.ofReal (ε / 4) < ENNReal.ofReal (ε / 2) := by
    rw [ENNReal.ofReal_lt_ofReal_iff]
    · linarith
    · linarith
  have hAevent := Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hMX hquarter_half)
  have hBevent := Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hMY hquarter_half)
  filter_upwards [hAevent, hBevent] with n hAn hBn
  calc
    μ (C n) ≤ μ (A n) + μ (B n) := hpoint n
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hAn hBn
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add]
      · congr 1; ring
      · linarith
      · linarith
    _ < y := hy

/-- Slutsky-style product: `Xn = O_p(1)` and `Yn = o_p(1)` imply
`Xn · Yn = o_p(1)`. -/
theorem IsBigOp.mul_isLittleOp_one_isLittleOp
    (hX : IsBigOp Xn (fun _ => (1 : ℝ)) μ)
    (hY : IsLittleOp Yn (fun _ => (1 : ℝ)) μ) :
    IsLittleOp (fun n ω => Xn n ω * Yn n ω) (fun _ => (1 : ℝ)) μ := by
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  by_cases hδtop : δ = ⊤
  · filter_upwards with n
    simp [hδtop]
  have hδpos : 0 < δ.toReal := ENNReal.toReal_pos (ne_of_gt hδ) hδtop
  let α : ℝ := δ.toReal / 8
  have hαpos : 0 < α := by
    dsimp [α]
    linarith
  rcases hX α hαpos with ⟨M0, hM0⟩
  let M : ℝ := max M0 1
  have hMpos : 0 < M := by
    dsimp [M]
    exact lt_of_lt_of_le zero_lt_one (le_max_right M0 1)
  have hM0le : M0 ≤ M := by
    dsimp [M]
    exact le_max_left M0 1
  let A : ℕ → Set Ω := fun n => {ω | M < |Xn n ω|}
  let B : ℕ → Set Ω := fun n => {ω | ε / M < |Yn n ω|}
  let C : ℕ → Set Ω := fun n => {ω | ε < |Xn n ω * Yn n ω|}
  have hlimA : Filter.limsup (fun n => μ (A n)) atTop ≤ ENNReal.ofReal α := by
    refine le_trans (Filter.limsup_le_limsup (Eventually.of_forall ?_)) hM0
    intro n
    apply measure_mono
    intro ω hω
    dsimp [A] at hω ⊢
    nlinarith
  have hpoint : ∀ n, μ (C n) ≤ μ (A n) + μ (B n) := by
    intro n
    have hsubset : C n ⊆ A n ∪ B n := by
      intro ω hω
      by_contra hnot
      have hnotA : ¬ M < |Xn n ω| := by
        intro hx
        exact hnot (Or.inl hx)
      have hnotB : ¬ ε / M < |Yn n ω| := by
        intro hy
        exact hnot (Or.inr hy)
      have hXle : |Xn n ω| ≤ M := le_of_not_gt hnotA
      have hYle : |Yn n ω| ≤ ε / M := le_of_not_gt hnotB
      have hprod : |Xn n ω * Yn n ω| ≤ ε := by
        calc
          |Xn n ω * Yn n ω| = |Xn n ω| * |Yn n ω| :=
            abs_mul (Xn n ω) (Yn n ω)
          _ ≤ M * (ε / M) := mul_le_mul hXle hYle (abs_nonneg _) (le_of_lt hMpos)
          _ = ε := by
            field_simp [hMpos.ne']
      exact not_lt_of_ge hprod hω
    calc
      μ (C n) ≤ μ (A n ∪ B n) := measure_mono hsubset
      _ ≤ μ (A n) + μ (B n) := MeasureTheory.measure_union_le (A n) (B n)
  have halpha_two : ENNReal.ofReal α < ENNReal.ofReal (2 * α) := by
    rw [ENNReal.ofReal_lt_ofReal_iff]
    · linarith
    · linarith
  have hAevent := Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hlimA halpha_two)
  have hYt : Tendsto (fun n => μ (B n)) atTop (𝓝 0) := by
    simpa [B, mul_comm] using hY (ε / M) (div_pos hε hMpos)
  have hBevent_le := (ENNReal.tendsto_nhds_zero.mp hYt) (ENNReal.ofReal α) (by
    exact ENNReal.ofReal_pos.mpr hαpos)
  have hBevent : ∀ᶠ n in atTop, μ (B n) < ENNReal.ofReal (2 * α) := by
    filter_upwards [hBevent_le] with n hn
    exact lt_of_le_of_lt hn halpha_two
  have hfour_lt_delta : ENNReal.ofReal (4 * α) < δ := by
    rw [ENNReal.ofReal_lt_iff_lt_toReal]
    · dsimp [α]
      linarith
    · dsimp [α]
      linarith [le_of_lt hδpos]
    · exact hδtop
  filter_upwards [hAevent, hBevent] with n hAn hBn
  exact le_of_lt <| calc
    μ {ω | ε * (fun _ => (1 : ℝ)) n < |Xn n ω * Yn n ω|} = μ (C n) := by
      simp [C]
    _ ≤ μ (A n) + μ (B n) := hpoint n
    _ < ENNReal.ofReal (2 * α) + ENNReal.ofReal (2 * α) := ENNReal.add_lt_add hAn hBn
    _ = ENNReal.ofReal (4 * α) := by
      rw [← ENNReal.ofReal_add]
      · congr 1; ring
      · linarith
      · linarith
    _ < δ := hfour_lt_delta

end Causalean.Stat
