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

> for almost-everywhere measurable, real, integrable `S T : Ω → ℝ` on a finite measure `μ`
> and a frequency `t : ℝ`,
> `‖charFun (μ.map S) t − charFun (μ.map T) t‖ ≤ |t| · ∫ ω, |S ω − T ω| ∂μ`.

The elementary ingredient is the pointwise estimate `‖cexp (a·I) − cexp (b·I)‖ ≤ |a − b|`
(`norm_cexp_mul_I_sub_cexp_mul_I_le`).  Applying Cauchy–Schwarz to the `L¹` bound upgrades it to
the **`L²` form** `≤ |t| · √(∫ (S − T)²)` (`norm_charFun_sub_le_L2`), the shape consumed by the
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

/-- Almost-everywhere measurable real variables with an integrable difference
have characteristic functions whose distance is at most the frequency magnitude
times their expected absolute difference. -/
theorem norm_charFun_sub_le (μ : Measure Ω) [IsFiniteMeasure μ]
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
  have hdiff_int : Integrable (fun ω => gS ω - gT ω) μ := by fun_prop
  have hnorm_int : Integrable (fun ω => ‖gS ω - gT ω‖) μ := by fun_prop
  have hright_int : Integrable (fun ω => |t| * |S ω - T ω|) μ := by fun_prop
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

/-- On a probability space, the expected norm of a square-integrable variable
is at most the square root of its expected squared norm. -/
theorem integral_abs_le_sqrt_integral_sq (μ : Measure Ω) [IsProbabilityMeasure μ]
    {E : Type*} [NormedAddCommGroup E] (f : Ω → E) (hf : MemLp f 2 μ) :
    ∫ ω, ‖f ω‖ ∂μ ≤ Real.sqrt (∫ ω, ‖f ω‖ ^ 2 ∂μ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hf2 : MemLp (fun ω => ‖f ω‖) (ENNReal.ofReal 2) μ := by
    simpa only [show ENNReal.ofReal 2 = 2 by norm_num] using hf.norm
  have h1 : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    exact memLp_const (1 : ℝ)
  have hkey := integral_mul_norm_le_Lp_mul_Lq (μ := μ) hpq hf2 h1
  have hleft : (∫ ω, ‖f ω‖ * ‖(1 : ℝ)‖ ∂μ) = ∫ ω, ‖f ω‖ ∂μ := by
    simp
  have hsqrt : ∀ c : ℝ, c ^ (1 / (2:ℝ)) = Real.sqrt c := by
    intro c
    rw [Real.sqrt_eq_rpow]
  have hnormsq : (∫ ω, ‖f ω‖ ^ (2 : ℝ) ∂μ) = ∫ ω, ‖f ω‖ ^ 2 ∂μ := by
    congr with ω
    exact Real.rpow_two _
  have honesq : (∫ _ω : Ω, ‖(1 : ℝ)‖ ^ (2:ℝ) ∂μ) = 1 := by
    simp
  calc
    ∫ ω, ‖f ω‖ ∂μ
        = ∫ ω, ‖f ω‖ * ‖(1 : ℝ)‖ ∂μ := hleft.symm
    _ ≤ (∫ ω, ‖f ω‖ ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ)) *
          (∫ _ω : Ω, ‖(1 : ℝ)‖ ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ)) := by
            simpa using hkey
    _ = Real.sqrt (∫ ω, ‖f ω‖ ^ 2 ∂μ) * Real.sqrt 1 := by
          rw [hnormsq, hsqrt, hsqrt, honesq]
    _ = Real.sqrt (∫ ω, ‖f ω‖ ^ 2 ∂μ) := by
          simp

/-- **Characteristic-function approximation bound (`L²` form).** Let $\mu$ be a probability
measure and let $S, T$ be real random variables on the same space, with [$S$
almost-everywhere measurable](hyp:hS) and [$T$ almost-everywhere measurable](hyp:hT); assume
further that [their difference $S - T$ is square-integrable under $\mu$](hyp:hdiff). Then for
every real frequency $t$, [the characteristic functions of the laws of $S$ and $T$ differ at
$t$ by at most $|t|$ times the $L^2$ norm of $S - T$: $\|{\rm charFun}(\mu \circ S^{-1})(t) -
{\rm charFun}(\mu \circ T^{-1})(t)\| \le |t| \cdot \sqrt{\int (S - T)^2 \, d\mu}$](goal).

Proof: `∫ |S − T| ≤ √(∫ (S − T)²)` on a probability measure (Cauchy–Schwarz against the constant
`1`, `integral_mul_norm_le_Lp_mul_Lq`), then chain with the `L¹` form (`norm_charFun_sub_le`). -/
theorem norm_charFun_sub_le_L2 (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S T : Ω → ℝ} (hS : AEMeasurable S μ) (hT : AEMeasurable T μ)
    (hdiff : MemLp (fun ω => S ω - T ω) 2 μ) (t : ℝ) :
    ‖charFun (μ.map S) t - charFun (μ.map T) t‖
      ≤ |t| * Real.sqrt (∫ ω, (S ω - T ω) ^ 2 ∂μ) := by
  have hint : Integrable (fun ω => S ω - T ω) μ :=
    hdiff.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hL1 := norm_charFun_sub_le μ hS hT hint t
  have hcs : ∫ ω, |S ω - T ω| ∂μ ≤
      Real.sqrt (∫ ω, (S ω - T ω) ^ 2 ∂μ) := by
    simpa [Real.norm_eq_abs, sq_abs] using
      integral_abs_le_sqrt_integral_sq μ (fun ω => S ω - T ω) hdiff
  exact hL1.trans (mul_le_mul_of_nonneg_left hcs (abs_nonneg t))

end Causalean.Mathlib.Probability.ConvergingTogether
