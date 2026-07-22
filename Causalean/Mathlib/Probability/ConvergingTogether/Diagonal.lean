/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Probability.ConvergingTogether.CharFunBound
import Mathlib.Probability.Distributions.Gaussian.Real
import Clt.Inversion

/-!
# The converging-together theorem (Billingsley Thm 3.2 / Slutsky for `⇒`)

This file proves the general **converging-together** theorem: a sequence of real random variables
that is approximated in `L²` by a triangular family, each row of which converges in distribution to
a common limit law `G`, itself converges in distribution to `G`.  This is the load-bearing diagonal
step of every approximation-based CLT (m-dependent approximation of a mixing field, blocking
arguments, …).

The proof is the standard characteristic-function ε/3 argument:
* for each frequency `t`, split
  `‖charFun (law S n) t − charFun G t‖ ≤ ‖charFun (law S n) t − charFun (law T m n) t‖
        + ‖charFun (law T m n) t − charFun G t‖`;
* bound the first summand by the approximation bound `charFun_sub_enorm_le_L2` plus the iterated
  `L²` control `(H2)`;
* the second summand tends to `0` by the per-row weak convergence `(H1)` (the easy direction of
  Lévy continuity, `tendsto_iff_tendsto_charFun.mp`);
* pick `m` large then `n` large to conclude pointwise `charFun (law S n) t → charFun G t`;
* upgrade pointwise characteristic-function convergence to weak convergence with the `clt`
  package's Lévy continuity theorem
  `MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`.

The `L²` discrepancies are controlled in `ℝ≥0∞` via `Filter.limsup`, which sidesteps the
boundedness side-conditions of the real-valued `limsup`; the squared `L²` integral
`∫ ω, (S n ω − T m n ω)² ∂(μ n)` is wrapped with `ENNReal.ofReal`, a faithful rendering of
Billingsley's hypothesis `limsupₙ ∫ |S − T|² ≤ ε`.

Everything is stated for a general limit law `G : ProbabilityMeasure ℝ`; `clt_of_l2_approx`
specializes to the standard normal `gaussianReal 0 1`, the shape an m-dependent-approximation CLT
consumes.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology ENNReal

namespace Causalean.Mathlib.Probability.ConvergingTogether

/-- Bundle a probability measure on `ℝ` (with an explicit `IsProbabilityMeasure` proof) as a
`ProbabilityMeasure ℝ`.  A thin wrapper around the subtype constructor whose declared return type
keeps the bundled `ProbabilityMeasure` topology in scope (avoiding the raw-subtype unfolding that
breaks `𝓝`). -/
def lawPM (m : Measure ℝ) (h : IsProbabilityMeasure m) : ProbabilityMeasure ℝ := ⟨m, h⟩

@[simp] lemma lawPM_coe (m : Measure ℝ) (h : IsProbabilityMeasure m) :
    (lawPM m h : Measure ℝ) = m := rfl

/-- **The converging-together theorem (Billingsley Thm 3.2).**
Let `G` be a limit probability law on `ℝ`, let `S n : Ω n → ℝ` be a sequence of real random
variables (on probability spaces `(Ω n, μ n)`), and for each `m` let `T m n : Ω n → ℝ` be the
`m`-th approximating row, all square-integrable.  Assume:

* `(H1)` for every `m`, the laws `(μ n).map (T m n)` converge weakly to `G` as `n → ∞`;
* `(H2)` for every `ε > 0` there is `M` such that for all `m ≥ M`,
  `limsupₙ ENNReal.ofReal (∫ ω, (S n ω − T m n ω)² ∂(μ n)) ≤ ENNReal.ofReal ε`
  (the rows approximate `S` in `L²`, uniformly in `n` in the iterated-`limsup` sense).

Then the laws `(μ n).map (S n)` converge weakly to `G` as `n → ∞`.

This is the diagonal step of any approximation-based CLT; it is *not* assumed (it is the goal), and
it is proved through characteristic functions, reusing the `clt` package's Lévy continuity theorem.
-/
theorem tendsto_inDistribution_of_l2_approx
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (G : ProbabilityMeasure ℝ)
    (S : (n : ℕ) → Ω n → ℝ) (T : ℕ → (n : ℕ) → Ω n → ℝ)
    (hS_meas : ∀ n, Measurable (S n)) (hT_meas : ∀ m n, Measurable (T m n))
    (hS_sq : ∀ n, MemLp (S n) 2 (μ n)) (hT_sq : ∀ m n, MemLp (T m n) 2 (μ n))
    (H1 : ∀ m, Tendsto
      (fun n => lawPM ((μ n).map (T m n))
        (Measure.isProbabilityMeasure_map (hT_meas m n).aemeasurable)) atTop (𝓝 G))
    (H2 : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m ≥ M,
      Filter.limsup (fun n => ENNReal.ofReal (∫ ω, (S n ω - T m n ω) ^ 2 ∂(μ n))) atTop
        ≤ ENNReal.ofReal ε) :
    Tendsto
      (fun n => lawPM ((μ n).map (S n))
        (Measure.isProbabilityMeasure_map (hS_meas n).aemeasurable)) atTop (𝓝 G) := by
  refine MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr ?_
  intro t
  let c := charFun (G : Measure ℝ) t
  have hrow : ∀ m, Tendsto (fun n => charFun ((μ n).map (T m n)) t) atTop (𝓝 c) := by
    intro m
    have h := (MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp (H1 m)) t
    simpa [lawPM_coe, c] using h
  rw [Metric.tendsto_atTop]
  intro δ hδ
  let ε : ℝ := (δ / (2 * (|t| + 1))) ^ 2 / 2
  have hε : 0 < ε := by
    have htpos : 0 < |t| + 1 := by positivity
    have hbase : 0 < δ / (2 * (|t| + 1)) := by positivity
    dsimp [ε]
    positivity
  have hεbound : |t| * Real.sqrt (2 * ε) < δ / 2 := by
    have htpos : 0 < |t| + 1 := by positivity
    have hbase_nonneg : 0 ≤ δ / (2 * (|t| + 1)) := by positivity
    have hsqrt : Real.sqrt (2 * ε) = δ / (2 * (|t| + 1)) := by
      dsimp [ε]
      rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
      exact Real.sqrt_sq hbase_nonneg
    rw [hsqrt]
    have hlt : |t| / (|t| + 1) < 1 := by
      rw [div_lt_one htpos]
      linarith [abs_nonneg t]
    calc
      |t| * (δ / (2 * (|t| + 1)))
          = (δ / 2) * (|t| / (|t| + 1)) := by
            field_simp [ne_of_gt htpos, (by norm_num : (2 : ℝ) ≠ 0)]
      _ < (δ / 2) * 1 := mul_lt_mul_of_pos_left hlt (by linarith)
      _ = δ / 2 := by ring
  obtain ⟨M, hM⟩ := H2 ε hε
  have hlim :
      Filter.limsup
          (fun n => ENNReal.ofReal (∫ ω, (S n ω - T M n ω) ^ 2 ∂(μ n))) atTop
        ≤ ENNReal.ofReal ε := hM M le_rfl
  have hεlt : ENNReal.ofReal ε < ENNReal.ofReal (2 * ε) := by
    rw [ENNReal.ofReal_lt_ofReal_iff]
    · linarith
    · linarith
  have hev :
      ∀ᶠ n in atTop,
        ENNReal.ofReal (∫ ω, (S n ω - T M n ω) ^ 2 ∂(μ n))
          < ENNReal.ofReal (2 * ε) :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt hlim hεlt)
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp (hrow M) (δ / 2) (by linarith))
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn₁ : n ≥ N₁ := le_trans (le_max_left _ _) hn
  have hn₂ : n ≥ N₂ := le_trans (le_max_right _ _) hn
  have hsecond : dist (charFun ((μ n).map (T M n)) t) c < δ / 2 := hN₁ n hn₁
  have hsq_nonneg : 0 ≤ ∫ ω, (S n ω - T M n ω) ^ 2 ∂(μ n) := by
    exact integral_nonneg fun ω => sq_nonneg _
  have hsq_lt : ∫ ω, (S n ω - T M n ω) ^ 2 ∂(μ n) < 2 * ε := by
    have := hN₂ n hn₂
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hsq_nonneg).mp this
  have hsqrt_le :
      Real.sqrt (∫ ω, (S n ω - T M n ω) ^ 2 ∂(μ n))
        ≤ Real.sqrt (2 * ε) :=
    Real.sqrt_le_sqrt hsq_lt.le
  have hfirst_le :
      dist (charFun ((μ n).map (S n)) t) (charFun ((μ n).map (T M n)) t)
        ≤ |t| * Real.sqrt (2 * ε) := by
    calc
      dist (charFun ((μ n).map (S n)) t) (charFun ((μ n).map (T M n)) t)
          = ‖charFun ((μ n).map (S n)) t - charFun ((μ n).map (T M n)) t‖ := by
            rw [dist_eq_norm]
      _ ≤ |t| * Real.sqrt (∫ ω, (S n ω - T M n ω) ^ 2 ∂(μ n)) :=
            tendsto_charFun_sub_le_L2 (μ n) (hS_sq n) (hT_sq M n) t
      _ ≤ |t| * Real.sqrt (2 * ε) := by
            exact mul_le_mul_of_nonneg_left hsqrt_le (abs_nonneg t)
  have hfirst : dist (charFun ((μ n).map (S n)) t) (charFun ((μ n).map (T M n)) t) < δ / 2 :=
    lt_of_le_of_lt hfirst_le hεbound
  calc
    dist (charFun ((μ n).map (S n)) t) c
        ≤ dist (charFun ((μ n).map (S n)) t) (charFun ((μ n).map (T M n)) t)
            + dist (charFun ((μ n).map (T M n)) t) c := dist_triangle _ _ _
    _ < δ := by linarith

/-- **Converging-together corollary for the standard normal (the CLT diagonal step).**
The specialization of `tendsto_inDistribution_of_l2_approx` to the limit law `gaussianReal 0 1`:
if each `L²`-approximating row `T m` satisfies a standard-normal CLT `(H1)` and the rows approximate
`S` in `L²` in the iterated-`limsup` sense `(H2)`, then the laws of `S n` converge weakly to the
standard normal.  This is exactly the shape an m-dependent-approximation CLT consumes to pass from
the per-`m` m-dependent CLT to the limit. -/
theorem clt_of_l2_approx
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (S : (n : ℕ) → Ω n → ℝ) (T : ℕ → (n : ℕ) → Ω n → ℝ)
    (hS_meas : ∀ n, Measurable (S n)) (hT_meas : ∀ m n, Measurable (T m n))
    (hS_sq : ∀ n, MemLp (S n) 2 (μ n)) (hT_sq : ∀ m n, MemLp (T m n) 2 (μ n))
    (H1 : ∀ m, Tendsto
      (fun n => lawPM ((μ n).map (T m n))
        (Measure.isProbabilityMeasure_map (hT_meas m n).aemeasurable)) atTop
        (𝓝 (lawPM (gaussianReal 0 1) inferInstance)))
    (H2 : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m ≥ M,
      Filter.limsup (fun n => ENNReal.ofReal (∫ ω, (S n ω - T m n ω) ^ 2 ∂(μ n))) atTop
        ≤ ENNReal.ofReal ε) :
    Tendsto
      (fun n => lawPM ((μ n).map (S n))
        (Measure.isProbabilityMeasure_map (hS_meas n).aemeasurable)) atTop
      (𝓝 (lawPM (gaussianReal 0 1) inferInstance)) :=
  tendsto_inDistribution_of_l2_approx μ _ S T hS_meas hT_meas hS_sq hT_sq H1 H2

end Causalean.Mathlib.Probability.ConvergingTogether
