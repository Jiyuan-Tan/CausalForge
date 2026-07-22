/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# The characteristic-function approximation bound

The "converging-together" theorem is proved through characteristic functions, and its load-bearing
analytic input is the **Lipschitz-in-`L¹` bound** on the difference of two pushforward
characteristic functions:

> for real, integrable `S T : Ω → ℝ` on a probability measure `μ` and a frequency `t : ℝ`,
> `‖charFun (μ.map S) t − charFun (μ.map T) t‖ ≤ |t| · ∫ ω, |S ω − T ω| ∂μ`.

The elementary ingredient is the pointwise estimate `‖cexp (a·I) − cexp (b·I)‖ ≤ |a − b|`
(`norm_cexp_mul_I_sub_cexp_mul_I_le`).  Applying Cauchy–Schwarz to the `L¹` bound upgrades it to
the **`L²` form** `≤ |t| · √(∫ (S − T)²)` (`tendsto_charFun_sub_le_L2`), the shape consumed by the
diagonal ε/3 argument of the converging-together theorem.

These are fully general real-random-variable statements; nothing here is specific to a network /
m-dependent setting.
-/

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Real Topology ENNReal

namespace Causalean.Mathlib.Probability.ConvergingTogether

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Pointwise Lipschitz bound for the unit-circle exponential.**
For real arguments `a b`, the chord between the points `e^{ia}` and `e^{ib}` on the unit circle is
no longer than the arc, i.e. `‖exp (a·I) − exp (b·I)‖ ≤ |a − b|`.  This is the elementary input to
the characteristic-function approximation bound. -/
theorem norm_cexp_mul_I_sub_cexp_mul_I_le (a b : ℝ) :
    ‖Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I)‖ ≤ |a - b| := by
  have harg :
      (a : ℂ) * Complex.I = (b : ℂ) * Complex.I + ((a - b : ℝ) : ℂ) * Complex.I := by
    norm_num [sub_eq_add_neg]
    ring
  calc
    ‖Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I)‖
        = ‖Complex.exp (b * Complex.I) *
            (Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1)‖ := by
          rw [harg, Complex.exp_add]
          ring_nf
    _ = ‖Complex.exp (b * Complex.I)‖ *
          ‖Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1‖ := by
          rw [norm_mul]
    _ = ‖Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1‖ := by
          rw [Complex.norm_exp_ofReal_mul_I]
          norm_num
    _ = ‖Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1‖ := by
          rw [mul_comm]
    _ ≤ ‖a - b‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = |a - b| := Real.norm_eq_abs _

private theorem tendsto_charFun_sub_le_ae (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S T : Ω → ℝ} (hS : AEMeasurable S μ) (hT : AEMeasurable T μ)
    (hint : Integrable (fun ω => S ω - T ω) μ) (t : ℝ) :
    ‖charFun (μ.map S) t - charFun (μ.map T) t‖
      ≤ |t| * ∫ ω, |S ω - T ω| ∂μ := by
  let gS : Ω → ℂ := fun ω => Complex.exp ((t : ℂ) * (S ω : ℂ) * Complex.I)
  let gT : Ω → ℂ := fun ω => Complex.exp ((t : ℂ) * (T ω : ℂ) * Complex.I)
  have hgS_int : Integrable gS μ := by
    refine Integrable.of_bound ?_ 1 (ae_of_all μ fun ω => ?_)
    · dsimp [gS]
      fun_prop
    · dsimp [gS]
      calc
        ‖Complex.exp ((t : ℂ) * (S ω : ℂ) * Complex.I)‖
            = ‖Complex.exp (((t * S ω : ℝ) : ℂ) * Complex.I)‖ := by
              congr 2
              norm_num
        _ = 1 := Complex.norm_exp_ofReal_mul_I _
        _ ≤ 1 := le_rfl
  have hgT_int : Integrable gT μ := by
    refine Integrable.of_bound ?_ 1 (ae_of_all μ fun ω => ?_)
    · dsimp [gT]
      fun_prop
    · dsimp [gT]
      calc
        ‖Complex.exp ((t : ℂ) * (T ω : ℂ) * Complex.I)‖
            = ‖Complex.exp (((t * T ω : ℝ) : ℂ) * Complex.I)‖ := by
              congr 2
              norm_num
        _ = 1 := Complex.norm_exp_ofReal_mul_I _
        _ ≤ 1 := le_rfl
  have hcharS : charFun (μ.map S) t = ∫ ω, gS ω ∂μ := by
    rw [MeasureTheory.charFun_apply_real]
    exact MeasureTheory.integral_map hS (by fun_prop)
  have hcharT : charFun (μ.map T) t = ∫ ω, gT ω ∂μ := by
    rw [MeasureTheory.charFun_apply_real]
    exact MeasureTheory.integral_map hT (by fun_prop)
  have hdiff_int : Integrable (fun ω => gS ω - gT ω) μ := hgS_int.sub hgT_int
  have hnorm_int : Integrable (fun ω => ‖gS ω - gT ω‖) μ := hdiff_int.norm
  have hright_int : Integrable (fun ω => |t| * |S ω - T ω|) μ := hint.abs.const_mul |t|
  have hpoint : ∀ ω, ‖gS ω - gT ω‖ ≤ |t| * |S ω - T ω| := by
    intro ω
    calc
      ‖gS ω - gT ω‖
          = ‖Complex.exp (((t * S ω : ℝ) : ℂ) * Complex.I) -
              Complex.exp (((t * T ω : ℝ) : ℂ) * Complex.I)‖ := by
            dsimp [gS, gT]
            congr 1
            norm_num
      _ ≤ |t * S ω - t * T ω| :=
            norm_cexp_mul_I_sub_cexp_mul_I_le (t * S ω) (t * T ω)
      _ = |t| * |S ω - T ω| := by
            rw [← mul_sub, abs_mul]
  rw [hcharS, hcharT]
  calc
    ‖(∫ ω, gS ω ∂μ) - ∫ ω, gT ω ∂μ‖
        = ‖∫ ω, gS ω - gT ω ∂μ‖ := by
          rw [integral_sub hgS_int hgT_int]
    _ ≤ ∫ ω, ‖gS ω - gT ω‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, |t| * |S ω - T ω| ∂μ := integral_mono hnorm_int hright_int hpoint
    _ = |t| * ∫ ω, |S ω - T ω| ∂μ := by
          rw [integral_const_mul]

private theorem integral_abs_le_sqrt_integral_sq (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : MemLp f 2 μ) :
    ∫ ω, |f ω| ∂μ ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂μ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hf2 : MemLp f (ENNReal.ofReal 2) μ := by
    rwa [show ENNReal.ofReal 2 = 2 by norm_num]
  have h1 : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    exact memLp_const (1 : ℝ)
  have hkey := integral_mul_norm_le_Lp_mul_Lq (μ := μ) hpq hf2 h1
  have hleft : (∫ ω, ‖f ω‖ * ‖(1 : ℝ)‖ ∂μ) = ∫ ω, |f ω| ∂μ := by
    simp [Real.norm_eq_abs]
  have hsqrt : ∀ c : ℝ, c ^ (1 / (2:ℝ)) = Real.sqrt c := by
    intro c
    rw [Real.sqrt_eq_rpow]
  have hnormsq : ∀ ω, ‖f ω‖ ^ (2:ℝ) = f ω ^ 2 := by
    intro ω
    rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  have honesq : (∫ _ω : Ω, ‖(1 : ℝ)‖ ^ (2:ℝ) ∂μ) = 1 := by
    simp
  calc
    ∫ ω, |f ω| ∂μ
        = ∫ ω, ‖f ω‖ * ‖(1 : ℝ)‖ ∂μ := hleft.symm
    _ ≤ (∫ ω, ‖f ω‖ ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ)) *
          (∫ _ω : Ω, ‖(1 : ℝ)‖ ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ)) := hkey
    _ = Real.sqrt (∫ ω, f ω ^ 2 ∂μ) * Real.sqrt 1 := by
          rw [hsqrt, hsqrt, honesq]
          simp_rw [hnormsq]
    _ = Real.sqrt (∫ ω, f ω ^ 2 ∂μ) := by
          simp

/-- **Characteristic-function approximation bound (`L¹` form).**
For real random variables `S T : Ω → ℝ` that are measurable and whose difference is integrable
on a probability measure `μ`, the two pushforward characteristic functions differ, at frequency
`t`, by at most `|t|` times the `L¹` distance of `S` and `T`:
`‖charFun (μ.map S) t − charFun (μ.map T) t‖ ≤ |t| · ∫ ω, |S ω − T ω| ∂μ`.

Proof: write each characteristic function as `∫ ω, exp (t · S ω · I) ∂μ` via `integral_map`; the
integrand difference is bounded in norm by `|t| · |S ω − T ω|` thanks to
`norm_cexp_mul_I_sub_cexp_mul_I_le`; conclude with `norm_integral_le_integral_norm` and
`integral_mono`. -/
theorem tendsto_charFun_sub_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S T : Ω → ℝ} (hS : Measurable S) (hT : Measurable T)
    (hint : Integrable (fun ω => S ω - T ω) μ) (t : ℝ) :
    ‖charFun (μ.map S) t - charFun (μ.map T) t‖ ≤ |t| * ∫ ω, |S ω - T ω| ∂μ := by
  exact tendsto_charFun_sub_le_ae μ hS.aemeasurable hT.aemeasurable hint t

/-- **Characteristic-function approximation bound (`L²` form).**
The Cauchy–Schwarz upgrade of `tendsto_charFun_sub_le`: for square-integrable `S T`, the
characteristic functions differ at frequency `t` by at most `|t| · √(∫ (S − T)²)`:
`‖charFun (μ.map S) t − charFun (μ.map T) t‖ ≤ |t| · √(∫ ω, (S ω − T ω)² ∂μ)`.

Proof: `∫ |S − T| ≤ √(∫ (S − T)²)` on a probability measure (Cauchy–Schwarz against the constant
`1`, `integral_mul_norm_le_Lp_mul_Lq`), then chain with the `L¹` form. -/
theorem tendsto_charFun_sub_le_L2 (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S T : Ω → ℝ} (hS : MemLp S 2 μ) (hT : MemLp T 2 μ) (t : ℝ) :
    ‖charFun (μ.map S) t - charFun (μ.map T) t‖
      ≤ |t| * Real.sqrt (∫ ω, (S ω - T ω) ^ 2 ∂μ) := by
  have hdiff : MemLp (fun ω => S ω - T ω) 2 μ := hS.sub hT
  have hint : Integrable (fun ω => S ω - T ω) μ :=
    hdiff.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hL1 := tendsto_charFun_sub_le_ae μ hS.aestronglyMeasurable.aemeasurable
    hT.aestronglyMeasurable.aemeasurable hint t
  have hcs := integral_abs_le_sqrt_integral_sq μ (fun ω => S ω - T ω) hdiff
  exact hL1.trans (mul_le_mul_of_nonneg_left hcs (abs_nonneg t))

end Causalean.Mathlib.Probability.ConvergingTogether
