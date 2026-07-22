/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The Stein equation and its solution (standard normal)

Stein's method for normal approximation rests on the *Stein equation*
`f'(w) − w·f(w) = h(w) − E[h(Z)]`, `Z ∼ 𝒩(0,1)`. For a bounded measurable `h` the bounded
solution is

    f_h(w) = e^{w²/2} ∫_{-∞}^{w} (h(x) − E[h(Z)]) e^{−x²/2} dx.

This file defines `steinSol`, proves it solves the Stein equation (`steinSol_hasDerivAt`), and
records the subtractive form `steinSol_stein_eq`. Uniform bounds for the solution and its
derivatives are proved in `Causalean.Mathlib.Probability.SteinMethod.Bounds`. See
`doc/stein_clt_plan.md`.
-/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Stein equation for the standard normal distribution

This file defines `gExpect`, the bounded solution `steinSol` of the
standard-normal Stein equation, and the two public identities
`steinSol_hasDerivAt` and `steinSol_stein_eq`. The supporting lemmas establish
the Gaussian expectation and integrability facts needed by the Stein-method
bounds.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Real

namespace Causalean
namespace SteinMethod

/-- Expectation of `h` under the standard normal law, `E[h(Z)]`. -/
noncomputable def gExpect (h : ℝ → ℝ) : ℝ := ∫ x, h x ∂(gaussianReal 0 1)

/-- The bounded solution of the Stein equation `f' − w·f = h − E[h(Z)]`. -/
noncomputable def steinSol (h : ℝ → ℝ) (w : ℝ) : ℝ :=
  Real.exp (w ^ 2 / 2) * ∫ x in Set.Iic w, (h x - gExpect h) * Real.exp (-x ^ 2 / 2)

/-- The integrand `(h x − E[h(Z)])·e^{−x²/2}` appearing inside `steinSol`. -/
private noncomputable def steinIntegrand (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  (h x - gExpect h) * Real.exp (-x ^ 2 / 2)

private theorem steinIntegrand_continuous (h : ℝ → ℝ) (hh : Continuous h) :
    Continuous (steinIntegrand h) := by
  unfold steinIntegrand
  fun_prop

/-- The Gaussian expectation of a bounded function is bounded by the same constant. -/
private theorem abs_gExpect_le {h : ℝ → ℝ} {C : ℝ} (hb : ∀ x, |h x| ≤ C) :
    |gExpect h| ≤ C := by
  unfold gExpect
  calc |∫ x, h x ∂(gaussianReal 0 1)| ≤ ∫ x, |h x| ∂(gaussianReal 0 1) :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ _x, C ∂(gaussianReal 0 1) := by
        apply MeasureTheory.integral_mono_of_nonneg
        · filter_upwards with x using abs_nonneg _
        · exact MeasureTheory.integrable_const C
        · filter_upwards with x using hb x
    _ = C := by
        rw [MeasureTheory.integral_const]; simp

/-- The integrand is globally integrable: it is dominated by a Gaussian. -/
private theorem steinIntegrand_integrable {h : ℝ → ℝ} (hh : Continuous h) {C : ℝ}
    (hb : ∀ x, |h x| ≤ C) : Integrable (steinIntegrand h) := by
  have hdom : Integrable (fun x : ℝ => (C + |gExpect h|) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _
  refine hdom.mono' (steinIntegrand_continuous h hh).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, steinIntegrand, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  have hexp : Real.exp (-x ^ 2 / 2) = Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
    rw [neg_div]; ring_nf
  rw [hexp]
  gcongr
  calc |h x - gExpect h| ≤ |h x| + |gExpect h| := abs_sub _ _
    _ ≤ C + |gExpect h| := by gcongr; exact hb x

/-- **The Stein equation.** For bounded continuous `h`, `steinSol h` is differentiable with
`f'(w) = w·f(w) + (h(w) − E[h(Z)])`, i.e. it solves `f'(w) − w·f(w) = h(w) − E[h(Z)]`. -/
theorem steinSol_hasDerivAt (h : ℝ → ℝ) (hh : Continuous h) {C : ℝ} (hb : ∀ x, |h x| ≤ C)
    (w : ℝ) :
    HasDerivAt (steinSol h) (w * steinSol h w + (h w - gExpect h)) w := by
  set g := steinIntegrand h with hg_def
  have hg_cont : Continuous g := steinIntegrand_continuous h hh
  have hg_int : Integrable g := steinIntegrand_integrable hh hb
  -- The cumulative integral `G w = ∫ x in Iic w, g x` has derivative `g w`.
  set G : ℝ → ℝ := fun u => ∫ x in Set.Iic u, g x with hG_def
  have hG_deriv : HasDerivAt G (g w) w := by
    -- Base point `a := w - 1`.
    set a : ℝ := w - 1 with ha_def
    have hIIc_int : ∀ u : ℝ, IntegrableOn g (Set.Iic u) :=
      fun u => hg_int.integrableOn
    -- `G u = (∫ x in Iic a, g) + ∫ x in a..u, g`.
    have hGeq : ∀ u : ℝ, G u = (∫ x in Set.Iic a, g x) + ∫ x in a..u, g x := by
      intro u
      have := intervalIntegral.integral_Iic_sub_Iic (hIIc_int a) (hIIc_int u)
      rw [hG_def]; linarith [this]
    have hivint : IntervalIntegrable g MeasureTheory.volume a w :=
      hg_int.intervalIntegrable
    have hd : HasDerivAt (fun u => ∫ x in a..u, g x) (g w) w :=
      intervalIntegral.integral_hasDerivAt_right hivint
        hg_cont.aestronglyMeasurable.stronglyMeasurableAtFilter hg_cont.continuousAt
    have hd' : HasDerivAt (fun u => (∫ x in Set.Iic a, g x) + ∫ x in a..u, g x) (g w) w := by
      simpa using hd.const_add (∫ x in Set.Iic a, g x)
    exact hd'.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun u => hGeq u))
  -- Derivative of `e^{w²/2}`.
  have hexp_deriv :
      HasDerivAt (fun u : ℝ => Real.exp (u ^ 2 / 2)) (w * Real.exp (w ^ 2 / 2)) w := by
    have hpow : HasDerivAt (fun u : ℝ => u ^ 2 / 2) w w := by
      have := (hasDerivAt_pow 2 w).div_const 2
      simpa using this
    have := (Real.hasDerivAt_exp (w ^ 2 / 2)).comp w hpow
    simpa [mul_comm] using this
  -- Product rule.
  have hprod := hexp_deriv.mul hG_deriv
  -- Rewrite `steinSol h = fun u => e^{u²/2} * G u`.
  have hsol_eq : steinSol h = fun u => Real.exp (u ^ 2 / 2) * G u := by
    funext u; rfl
  -- Match derivatives: `w * steinSol h w + (h w - gExpect h)`.
  have hgcancel : Real.exp (w ^ 2 / 2) * g w = h w - gExpect h := by
    rw [hg_def, steinIntegrand, ← mul_assoc, mul_comm (Real.exp _) (h w - gExpect h),
      mul_assoc, ← Real.exp_add]
    rw [show w ^ 2 / 2 + -w ^ 2 / 2 = 0 by ring, Real.exp_zero, mul_one]
  rw [hsol_eq]
  convert hprod using 1
  change w * (Real.exp (w ^ 2 / 2) * G w) + (h w - gExpect h)
    = w * Real.exp (w ^ 2 / 2) * G w + Real.exp (w ^ 2 / 2) * g w
  rw [hgcancel]; ring

/-- The Stein equation in subtractive form. -/
theorem steinSol_stein_eq (h : ℝ → ℝ) (hh : Continuous h) {C : ℝ} (hb : ∀ x, |h x| ≤ C) (w : ℝ) :
    deriv (steinSol h) w - w * steinSol h w = h w - gExpect h := by
  have := (steinSol_hasDerivAt h hh hb w).deriv
  rw [this]; ring

end SteinMethod
end Causalean
