/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Ville's inequality and test supermartingales

The probabilistic engine of **anytime-valid inference**.  A *test supermartingale* is a nonnegative
supermartingale `M` adapted to the data-collection filtration with `E[M₀] ≤ 1`; it is the wealth
process of a bet against the null hypothesis, and the supermartingale property is what survives
*adaptive* (sequential, data-dependent) sampling.  **Ville's inequality** is the time-uniform
maximal inequality: the probability that a nonnegative supermartingale `M` ever exceeds a level `λ`
is at most `E[M₀] / λ`.  Because the bound holds simultaneously for all times `n`, it licenses
inference at a data-dependent stopping time — the defining feature of valid sequential inference.

The time-uniform statement is obtained from the finite-horizon supermartingale maximal inequality
(`supermartingale_maximal_ineq`) by monotone convergence over the horizon; the finite-horizon
inequality is the one genuinely measure-theoretic step (it is the supermartingale analogue of
Mathlib's `MeasureTheory.maximal_ineq` for nonnegative submartingales, proved by optional stopping
at the hitting time of `[λ,∞)`).
-/

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-! # Ville inequality

Ville's inequality gives time-uniform control for nonnegative test supermartingales.

The predicate `IsTestSupermartingale` packages a nonnegative supermartingale with initial expected
wealth at most one.  The theorem `supermartingale_maximal_ineq` proves the finite-horizon maximal
bound, `ville_inequality` passes to the event of ever crossing a positive level, and `ville_test`
specializes the result to the `1/α` threshold used by anytime-valid tests.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal MeasureTheory ProbabilityTheory BigOperators

namespace Causalean
namespace Experimentation
namespace Sequential

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}

/-- A **test supermartingale** for a null hypothesis: a nonnegative supermartingale adapted to the
data filtration whose initial expected value is at most one.  It is the wealth process of a bet
against the null that cannot grow in expectation under it. -/
def IsTestSupermartingale (M : ℕ → Ω → ℝ) (ℱ : Filtration ℕ m0) (μ : Measure Ω) : Prop :=
  Supermartingale M ℱ μ ∧ (∀ n, 0 ≤ M n) ∧ μ[M 0] ≤ 1

/-- **Finite-horizon supermartingale maximal inequality.** For a nonnegative supermartingale `M` and
level `λ > 0`, the probability that `M` reaches `λ` by time `n` is at most `E[M₀] / λ`.

This is the supermartingale analogue of `MeasureTheory.maximal_ineq` (which is stated for nonnegative
submartingales); it is proved by optional stopping of the supermartingale at the hitting time of
`[λ,∞)`. -/
theorem supermartingale_maximal_ineq [IsFiniteMeasure μ] {M : ℕ → Ω → ℝ}
    (hM : Supermartingale M ℱ μ) (hnonneg : ∀ n, 0 ≤ M n) {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    μ {ω | lam ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_succ (fun k => M k ω)}
      ≤ ENNReal.ofReal (μ[M 0] / lam) := by
  classical
  let τ : Ω → ℕ∞ := fun ω => (hittingBtwn M {y : ℝ | lam ≤ y} (0 : ℕ) n ω : ℕ)
  let A : Set Ω :=
    {ω | lam ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_succ (fun k => M k ω)}
  have hAmeas : MeasurableSet A := by
    exact measurableSet_le measurable_const
      (Finset.measurable_range_sup'' fun k _ => (hM.1.stronglyMeasurable (i := k)).measurable)
  have hτstop : IsStoppingTime ℱ τ := by
    exact hM.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hτbdd : ∀ ω, τ ω ≤ n := by
    intro ω
    simpa [τ] using
      (show (((hittingBtwn M {y : ℝ | lam ≤ y} (0 : ℕ) n ω : ℕ) : ℕ∞) ≤ (n : ℕ∞)) from by
        exact WithTop.coe_le_coe.2
          (hittingBtwn_le (u := M) (s := {y : ℝ | lam ≤ y}) (n := (0 : ℕ))
            (m := n) (ω := ω)))
  have hτint : Integrable (stoppedValue M τ) μ :=
    integrable_stoppedValue ℕ hτstop hM.2.2 hτbdd
  have hhit : ∀ ω ∈ A, lam ≤ stoppedValue M τ ω := by
    intro ω hω
    simp_rw [A, Set.mem_setOf_eq, Finset.le_sup'_iff, Finset.mem_range, Nat.lt_succ_iff] at hω
    refine stoppedValue_hittingBtwn_mem ?_
    simpa only [Set.mem_setOf_eq, Set.mem_Icc, zero_le, true_and] using hω
  have hsetLower :
      lam * (μ A).toReal ≤ ∫ ω in A, stoppedValue M τ ω ∂μ :=
    setIntegral_ge_of_const_le_real hAmeas (measure_ne_top _ _) hhit hτint.integrableOn
  have hstopped_nonneg : 0 ≤ stoppedValue M τ := by
    intro ω
    exact hnonneg _ ω
  have hset_le_total : ∫ ω in A, stoppedValue M τ ω ∂μ ≤ μ[stoppedValue M τ] := by
    have hcompl_nonneg : 0 ≤ ∫ ω in Aᶜ, stoppedValue M τ ω ∂μ :=
      setIntegral_nonneg hAmeas.compl fun ω _ => hstopped_nonneg ω
    have hadd := integral_add_compl hAmeas hτint
    linarith
  have hτ_le_M0 : μ[stoppedValue M τ] ≤ μ[M 0] := by
    have hneg : Submartingale (fun k ω => -M k ω) ℱ μ := hM.neg
    have hopt :
        μ[stoppedValue (fun k ω => -M k ω) (fun _ : Ω => ((0 : ℕ) : ℕ∞))]
          ≤ μ[stoppedValue (fun k ω => -M k ω) τ] := by
      refine hneg.expected_stoppedValue_mono (isStoppingTime_const ℱ 0) hτstop ?_ hτbdd
      intro ω
      simp [τ]
    have hleft :
        μ[stoppedValue (fun k ω => -M k ω) (fun _ : Ω => ((0 : ℕ) : ℕ∞))] =
          - μ[M 0] := by
      rw [show stoppedValue (fun k ω => -M k ω) (fun _ : Ω => ((0 : ℕ) : ℕ∞)) =
          fun ω => -M 0 ω by
        simpa only using stoppedValue_const (fun k ω => -M k ω) 0]
      exact integral_neg (M 0)
    have hright :
        μ[stoppedValue (fun k ω => -M k ω) τ] = - μ[stoppedValue M τ] := by
      rw [show stoppedValue (fun k ω => -M k ω) τ = fun ω => - stoppedValue M τ ω by
        funext ω
        simp [stoppedValue]]
      exact integral_neg (stoppedValue M τ)
    rw [hleft, hright] at hopt
    linarith
  have hmul : lam * (μ A).toReal ≤ μ[M 0] :=
    hsetLower.trans (hset_le_total.trans hτ_le_M0)
  have hM0_nonneg : 0 ≤ μ[M 0] := integral_nonneg (hnonneg 0)
  have hdiv_nonneg : 0 ≤ μ[M 0] / lam := div_nonneg hM0_nonneg hlam.le
  change μ A ≤ ENNReal.ofReal (μ[M 0] / lam)
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hdiv_nonneg]
  exact (le_div_iff₀ hlam).2 (by simpa [mul_comm] using hmul)

/-- **Ville's inequality (time-uniform maximal inequality).** For a nonnegative supermartingale `M`
and level `λ > 0`, the probability that `M` *ever* reaches `λ` is at most `E[M₀] / λ`.  The bound is
over the event of reaching the boundary at some finite time. -/
theorem ville_inequality [IsFiniteMeasure μ] {M : ℕ → Ω → ℝ}
    (hM : Supermartingale M ℱ μ) (hnonneg : ∀ n, 0 ≤ M n) {lam : ℝ} (hlam : 0 < lam) :
    μ {ω | ∃ n, lam ≤ M n ω} ≤ ENNReal.ofReal (μ[M 0] / lam) := by
  -- The "ever reaches lam" event is the increasing union of the finite-horizon events; apply the
  -- finite-horizon maximal inequality termwise.
  set A : ℕ → Set Ω :=
    fun N => {ω | lam ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_succ (fun k => M k ω)}
    with hA
  have hUnion : {ω | ∃ n, lam ≤ M n ω} = ⋃ N, A N := by
    ext ω
    simp only [hA, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, Finset.le_sup'_of_le (f := fun k => M k ω) (Finset.self_mem_range_succ n) hn⟩
    · rintro ⟨N, hN⟩
      obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_succ (fun k => M k ω)
      exact ⟨k, hN.trans hk.le⟩
  have hmono : Monotone A := by
    intro a b hab ω hω
    simp only [hA, Set.mem_setOf_eq] at hω ⊢
    have hsub : Finset.range (a + 1) ⊆ Finset.range (b + 1) :=
      Finset.range_mono (Nat.succ_le_succ hab)
    exact le_trans hω (Finset.sup'_mono (fun k => M k ω) hsub Finset.nonempty_range_succ)
  rw [hUnion, hmono.measure_iUnion]
  exact iSup_le (fun N => supermartingale_maximal_ineq hM hnonneg hlam N)

/-- Ville's inequality for a test supermartingale: the chance of ever reaching `1/α` is at most
`α`. -/
theorem ville_test [IsFiniteMeasure μ] {M : ℕ → Ω → ℝ} (hM : IsTestSupermartingale M ℱ μ)
    {α : ℝ} (hα : 0 < α) :
    μ {ω | ∃ n, 1 / α ≤ M n ω} ≤ ENNReal.ofReal α := by
  obtain ⟨hsuper, hnn, hM0⟩ := hM
  have hlam : (0 : ℝ) < 1 / α := by positivity
  refine le_trans (ville_inequality hsuper hnn hlam) ?_
  apply ENNReal.ofReal_le_ofReal
  rw [div_div_eq_mul_div, div_one]
  calc μ[M 0] * α ≤ 1 * α := mul_le_mul_of_nonneg_right hM0 hα.le
    _ = α := one_mul α

end Sequential
end Experimentation
end Causalean
