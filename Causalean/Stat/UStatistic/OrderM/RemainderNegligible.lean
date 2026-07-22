/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Negligibility of the higher-order remainder for fixed-order U-statistics

This file discharges the `OrderDegenerateNegligible` hypothesis carried by the
order-`m` U-statistic CLT `uStatisticOrder_clt`
(`Causalean.Stat.UStatistic.OrderM.CLT`): it proves that the rescaled higher-order
Hájek remainder `√n · Gₙ` is `o_p(1)`.  The end-to-end CLT that composes this
discharge with the CLT — the order-`m` analogue of `uStatistic_clt_of_symmetric` —
lives in `OrderM.CLT`.

The two supporting layers:

* `OrderM.FirstDegenKernel` — the `OrderFirstDegenKernel` hypothesis (first-order
  degeneracy, the correct notion for the remainder — *not* the complete
  degeneracy of `OrderDegenKernel`) and its `L²` transport lemmas.
* `OrderM.RemainderSecondMoment` — the keystone `L²` bound
  `E[(√n·Uₙ)²] ≤ C/n` for first-order degenerate kernels.

Given the keystone bound, negligibility is `L²`-boundedness with variance `→ 0`
via Chebyshev (mirroring the order-2 `degenerateNegligible_of_degenKernel`).
-/

import Causalean.Stat.UStatistic.OrderM.RemainderSecondMoment

/-!
Discharges the fixed-order Hájek remainder negligibility hypothesis.

The theorem `orderDegenerateNegligible_of_firstDegen` proves that a first-order
degenerate kernel has `√n`-rescaled U-statistic `o_p(1)`, using the
second-moment estimate from `OrderM.RemainderSecondMoment` and Chebyshev's
inequality.  The public wrapper `orderDegenerateNegligible_of_residual` applies
this result to the residual kernel `uDegenOrder h P`, producing the
`OrderDegenerateNegligible S h` hypothesis required by the fixed-order
asymptotic-linearity and CLT statements.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

namespace IIDSample

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
  {m : ℕ} [NeZero m] {g : (Fin m → X) → ℝ} (S : IIDSample Ω X μ P)

/-- The rescaled higher-order remainder has mean zero. -/
theorem integral_rescaled_order_eq_zero (hg : OrderFirstDegenKernel P g)
    {n : ℕ} (hmn : m ≤ n) :
    ∫ ω, Real.sqrt (n : ℝ) * uStatisticOrder S g n ω ∂μ = 0 :=
  S.integral_rescaled_uStatisticOrder_eq_zero_of_uMean_zero hg.meas hg.integrable hmn
    hg.integral_eq_zero

/-- **Negligibility of the higher-order remainder.**  Under first-order
degeneracy, `√n · Uₙ → 0` in probability, i.e. it is `o_p(1)`.  Proof: `L²`
boundedness (`memLp_rescaled_sqKernel`) with mean zero and variance `≤ C/n → 0`
(`integral_rescaled_order_sq_le`), via Chebyshev — mirror the order-2
`degenerateNegligible_of_degenKernel`. -/
theorem orderDegenerateNegligible_of_firstDegen (hg : OrderFirstDegenKernel P g) :
    IsLittleOp (fun n ω => Real.sqrt (n : ℝ) * uStatisticOrder S g n ω)
      (fun _ => (1 : ℝ)) μ := by
  intro ε hε
  rcases S.integral_rescaled_order_sq_le hg with ⟨C, hCnn, hCbound⟩
  have hb_tendsto :
      Tendsto (fun n : ℕ => ENNReal.ofReal ((C / ε ^ 2) / (n : ℝ))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    apply ENNReal.tendsto_ofReal
    have : Tendsto (fun n : ℕ => (C / ε ^ 2) * ((n : ℝ))⁻¹)
        atTop (𝓝 ((C / ε ^ 2) * 0)) := by
      apply Filter.Tendsto.const_mul
      exact tendsto_natCast_atTop_atTop.inv_tendsto_atTop
    simpa [div_eq_mul_inv, mul_zero] using this
  have hbound : ∀ᶠ n : ℕ in atTop,
      μ {ω | ε * (fun _ => (1 : ℝ)) n
          < |Real.sqrt (n : ℝ) * uStatisticOrder S g n ω|}
        ≤ ENNReal.ofReal ((C / ε ^ 2) / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop m] with n hmn
    set X : Ω → ℝ := fun ω => Real.sqrt (n : ℝ) * uStatisticOrder S g n ω with hXdef
    have hmem : MemLp X 2 μ := by
      simpa [X, hXdef] using S.memLp_rescaled_sqKernel hg.meas hg.sq n
    have hmean : ∫ ω, X ω ∂μ = 0 := by
      simpa [X, hXdef] using S.integral_rescaled_order_eq_zero hg hmn
    have hvar_le : variance X μ ≤ C / (n : ℝ) := by
      rw [ProbabilityTheory.variance_eq_sub hmem, hmean]
      simp only [Pi.pow_apply]
      simpa [X, hXdef] using hCbound hmn
    have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq hmem (c := ε) hε
    simp only [hmean, sub_zero] at hcheb
    have hsub :
        {ω | ε * (fun _ => (1 : ℝ)) n
            < |Real.sqrt (n : ℝ) * uStatisticOrder S g n ω|}
          ⊆ {ω | ε ≤ |X ω|} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, mul_one, X] at hω ⊢
      exact le_of_lt hω
    refine le_trans (measure_mono hsub) ?_
    calc
      μ {ω | ε ≤ |X ω|}
          ≤ ENNReal.ofReal (variance X μ / ε ^ 2) := hcheb
      _ ≤ ENNReal.ofReal ((C / (n : ℝ)) / ε ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          gcongr
      _ = ENNReal.ofReal ((C / ε ^ 2) / (n : ℝ)) := by
          exact congrArg ENNReal.ofReal (by ring)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb_tendsto
    (Eventually.of_forall (fun n => zero_le _)) hbound

end IIDSample

/-! ## Discharging `OrderDegenerateNegligible` for the Hájek remainder -/

/-- **The higher-order remainder of a fixed-order U-statistic is negligible.**
For an order-`m` kernel `h` whose residual `uDegenOrder h P` is measurable and
square-integrable and whose slice/Fubini integrability side conditions hold, the
rescaled remainder `√n · Gₙ` is `o_p(1)`.  This discharges the
`OrderDegenerateNegligible` hypothesis consumed by the order-`m` CLT
`uStatisticOrder_clt` (`Causalean.Stat.UStatistic.OrderM.CLT`).

Proof: assemble `OrderFirstDegenKernel P (uDegenOrder h P)` — `firstDeg` is
`uDegenOrder_integral_tail_eq_zero` — and apply
`orderDegenerateNegligible_of_firstDegen`; the goal `OrderDegenerateNegligible S h`
unfolds to negligibility of `uStatisticOrder S (uDegenOrder h P)`. -/
theorem orderDegenerateNegligible_of_residual
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {P : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (S : IIDSample Ω X μ P) {m : ℕ} [NeZero m] (h : (Fin m → X) → ℝ)
    (hmeas : Measurable (uDegenOrder h P))
    (hL2 : Integrable (fun z => (uDegenOrder h P z) ^ 2)
      (Measure.pi fun _ : Fin m => P))
    (hslice_int : ∀ j : Fin m, Integrable
      (fun x => ∫ tail : ({k : Fin m // k ≠ j}) → X,
        h (insertCoord j x tail) ∂(Measure.pi fun _ : {k : Fin m // k ≠ j} => P)) P)
    (hmean : ∀ j : Fin m,
      ∫ x, (∫ tail : ({k : Fin m // k ≠ j}) → X,
        h (insertCoord j x tail) ∂(Measure.pi fun _ : {k : Fin m // k ≠ j} => P)) ∂P
        = uMeanOrder h P)
    (hrow : ∀ (j : Fin m) (x : X),
      Integrable (fun tail : ({k : Fin m // k ≠ j}) → X =>
        h (insertCoord j x tail))
        (Measure.pi fun _ : {k : Fin m // k ≠ j} => P)) :
    OrderDegenerateNegligible S h := by
  have hg : OrderFirstDegenKernel P (uDegenOrder h P) := {
    meas := hmeas
    firstDeg := fun j x => uDegenOrder_integral_tail_eq_zero hslice_int hmean hrow j x
    sq := hL2
  }
  unfold OrderDegenerateNegligible uRemainderOrder
  exact S.orderDegenerateNegligible_of_firstDegen hg

end Causalean.Stat
