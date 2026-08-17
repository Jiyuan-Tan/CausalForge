/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.JensenFormula

/-!
# Circle argument-principle definitions and local residue

This module provides the normalized logarithmic-derivative integral around a
positively oriented complex circle, the associated multiplicity-weighted zero
count in its open disk, and the local factorization behind their relationship.
-/

@[expose] public section

noncomputable section

open Filter Function Metric Set
open scoped Topology

namespace Causalean.Mathlib.Analysis.ArgumentPrincipleCircle

/-- This quantity is the winding count obtained by integrating the logarithmic derivative of a
complex-valued function around a positively oriented circle and scaling so that one enclosed
simple zero contributes one. -/
def normalizedLogDerivCircleIntegral (f : ℂ → ℂ) (c : ℂ) (R : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * circleIntegral (logDeriv f) c R

open Classical in
/-- This count adds the analytic multiplicity of every zero strictly inside a given open disk;
outside finite-support settings it uses the standard totalized finite sum. -/
def zeroMultiplicityCount (f : ℂ → ℂ) (c : ℂ) (R : ℝ) : ℕ :=
  ∑ᶠ z : ℂ, if z ∈ ball c R then analyticOrderNatAt f z else 0

open Classical in
/-- This set comprises exactly the zeros of a complex-valued function that lie strictly inside a
given open disk. -/
def interiorZeros (f : ℂ → ℂ) (c : ℂ) (R : ℝ) : Set ℂ :=
  {z | z ∈ ball c R ∧ f z = 0}

/-- Near a finite-order zero of an analytic complex function, its logarithmic derivative is the
zero multiplicity divided by displacement from the zero plus the logarithmic derivative of an
analytic factor that does not vanish there. -/
theorem eventuallyEq_logDeriv_add_order_div_sub {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hfinite : analyticOrderAt f a ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧ g a ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] a,
        logDeriv f z = (analyticOrderNatAt f a : ℂ) / (z - a) + logDeriv g z := by
  obtain ⟨g, hg, hga, hfg⟩ := hf.analyticOrderAt_ne_top.mp hfinite
  refine ⟨g, hg, hga, ?_⟩
  have hg_ne : ∀ᶠ z in 𝓝 a, g z ≠ 0 := hg.continuousAt.eventually_ne hga
  filter_upwards [hfg.eventuallyEq_nhds.filter_mono inf_le_left,
    hg.eventually_analyticAt.filter_mono inf_le_left, hg_ne.filter_mono inf_le_left,
    self_mem_nhdsWithin] with z hz hgz hg_ne_z hza
  have hlogDeriv :
      logDeriv f z =
        logDeriv (fun w : ℂ ↦ (w - a) ^ analyticOrderNatAt f a * g w) z := by
    have hz' : f =ᶠ[𝓝 z]
        fun w : ℂ ↦ (w - a) ^ analyticOrderNatAt f a * g w := by
      simpa only [smul_eq_mul] using hz
    simp only [logDeriv_apply]
    rw [hz'.deriv_eq, hz'.self_of_nhds]
  rw [hlogDeriv,
    logDeriv_mul (f := fun w : ℂ ↦ (w - a) ^ analyticOrderNatAt f a) (g := g) z
      (pow_ne_zero (analyticOrderNatAt f a) (sub_ne_zero.mpr hza)) hg_ne_z
      (by fun_prop) hgz.differentiableAt,
    logDeriv_fun_pow (by fun_prop)]
  simp [logDeriv_apply, div_eq_mul_inv]

/-- A centered complex monomial has normalized logarithmic-derivative integral equal to its
exponent whenever the circle encloses its root. -/
theorem normalizedLogDerivCircleIntegral_centeredMonomial {c a : ℂ} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (ha : a ∈ ball c R) :
    normalizedLogDerivCircleIntegral (fun z ↦ (z - a) ^ n) c R = (n : ℂ) := by
  have hlogDeriv : logDeriv (fun z : ℂ ↦ (z - a) ^ n) =
      fun z ↦ (n : ℂ) * (z - a)⁻¹ := by
    funext z
    rw [logDeriv_fun_pow (by fun_prop)]
    simp [logDeriv_apply, div_eq_mul_inv]
  rw [normalizedLogDerivCircleIntegral, hlogDeriv,
    circleIntegral.integral_const_mul, circleIntegral.integral_sub_inv_of_mem_ball ha]
  field_simp

end Causalean.Mathlib.Analysis.ArgumentPrincipleCircle
