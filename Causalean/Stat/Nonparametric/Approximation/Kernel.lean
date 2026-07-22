/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.Approximation.HolderTaylor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Kernel smoothing bias for Hölder regression

Kernel smoothing bias bounds for Hölder regression functions using finite-order kernels with
vanishing moments.

This file defines a finite-order kernel (`KernelOrder`) and the population
kernel-smoothing bias `kernelSmoothingBias`, and proves the classical interior
bias estimate (Fan–Gijbels 1996 §3; Tsybakov 2009 Ch. 1): a kernel of order
`p = holderDerivOrder β` applied to a `β`-Hölder regression function has smoothing bias `O(h^β)`.

The mechanism: substitute `u = t + h v`; the kernel's vanishing moments
`∫ vʲ K = 0` (`1 ≤ j ≤ p`) annihilate the degree-`p` Taylor polynomial of `f`
at `t`, leaving only the Hölder–Taylor remainder `|f(t+hv) − T_p(t+hv)| ≤
(M/p!)·(h|v|)^β` (`holder_taylor_remainder`), which integrates against `|K|`
(supported in `[-1,1]`) to `O(h^β)`.
-/

namespace Causalean.Stat.Nonparametric

open MeasureTheory
open scoped BigOperators

/-- A kernel `K` of order `≥ p`: supported in `[-1,1]`, integrable, with unit mass
`∫ K = 1` and vanishing moments `∫ uʲ K(u) du = 0` for `1 ≤ j ≤ p`. These are the
inputs of the classical interior local-polynomial / kernel bias theorem. -/
structure KernelOrder (K : ℝ → ℝ) (p : ℕ) : Prop where
  /-- `K` is supported in `[-1,1]`. -/
  supp : ∀ u : ℝ, 1 < |u| → K u = 0
  /-- `K` is (Lebesgue) integrable. -/
  integrable : Integrable K
  /-- `K` has unit mass. -/
  mass : ∫ u, K u = 1
  /-- The moments `1,…,p` of `K` vanish. -/
  moments : ∀ j : ℕ, 1 ≤ j → j ≤ p → ∫ u, u ^ j * K u = 0

/-- Population kernel smoothing bias of estimating the value `f t` of a regression
function `f` at point `t` with bandwidth `h` and kernel `K`:
`∫ h⁻¹ K((u−t)/h) (f u − f t) du`. -/
noncomputable def kernelSmoothingBias (f K : ℝ → ℝ) (t h : ℝ) : ℝ :=
  ∫ u, h⁻¹ * K ((u - t) / h) * (f u - f t)

/-- If a function `F` is dominated in absolute value by a constant multiple `C·|K|`
of an integrable kernel `K`, then `F` is itself integrable. This is the integrability
workhorse for kernel-smoothing arguments: every factor multiplying `K` (a monomial, a
Taylor remainder) is bounded by `|K|` on the kernel's support and vanishes off it. -/
theorem integrable_of_abs_le_const_mul_kernel {K F : ℝ → ℝ} {C : ℝ}
    (hKi : Integrable K) (hF : AEStronglyMeasurable F)
    (hbd : ∀ v, |F v| ≤ C * |K v|) : Integrable F := by
  refine Integrable.mono' (hKi.abs.const_mul C) hF ?_
  filter_upwards with v
  simpa only [Real.norm_eq_abs] using hbd v

/-- **Change of variables for the kernel smoothing bias.** Substituting `u = t + h v`
(`h > 0`) turns the bias integral into `∫ K(v) (f(t+hv) − f t) dv`: the `h⁻¹` prefactor
cancels the Jacobian `h`, and `(u−t)/h = v`. -/
theorem kernelSmoothingBias_changeOfVar (f K : ℝ → ℝ) (t h : ℝ) (hh : 0 < h) :
    kernelSmoothingBias f K t h = ∫ v, K v * (f (t + h * v) - f t) := by
  unfold kernelSmoothingBias
  set ψ : ℝ → ℝ := fun u => K ((u - t) / h) * (f u - f t) with hψ
  have hL : (∫ u, h⁻¹ * K ((u - t) / h) * (f u - f t)) = h⁻¹ * ∫ u, ψ u := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp only [hψ]; ring
  have hR : (∫ v, K v * (f (t + h * v) - f t)) = ∫ v, ψ (t + h * v) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    have harg : (t + h * v - t) / h = v := by
      rw [add_sub_cancel_left]; field_simp
    simp only [hψ, harg]
  rw [hL, hR]; symm
  calc (∫ v, ψ (t + h * v))
      = ∫ v, (fun w => ψ (t + w)) (h * v) := rfl
    _ = |h⁻¹| • ∫ w, (fun w => ψ (t + w)) w := by
        simpa using Measure.integral_comp_mul_left (fun w : ℝ => ψ (t + w)) h
    _ = |h⁻¹| • ∫ w, ψ (t + w) := rfl
    _ = |h⁻¹| • ∫ u, ψ u := by rw [integral_add_left_eq_self ψ t]
    _ = h⁻¹ * ∫ u, ψ u := by rw [smul_eq_mul, abs_of_pos (inv_pos.mpr hh)]

/-- **Interior kernel smoothing bias is `O(h^β)`.** With a kernel `K` of order
`p = holderDerivOrder β`, a `p`-times continuously differentiable regression
`f` whose `p`-th derivative is `(β−p)`-Hölder with constant `M` on the window
`[t−h, t+h]`, the kernel smoothing bias at bandwidth `h` is bounded by
`(M/p! · ∫|K|)·h^β`. For positive integer `β = m`, `p = m - 1` and the
Hölder exponent is `1`. (Fan–Gijbels 1996 §3.1–3.3; Tsybakov 2009 Ch. 1.) -/
theorem kernelSmoothingBias_bound {f K : ℝ → ℝ} {β M t h : ℝ}
    (hβ : 0 < β) (hM : 0 ≤ M) (hh : 0 < h)
    (hK : KernelOrder K (holderDerivOrder β))
    (hf : ContDiff ℝ ((holderDerivOrder β)) f)
    (hb : ∀ x ∈ Set.Icc (t - h) (t + h), ∀ y ∈ Set.Icc (t - h) (t + h),
            |iteratedDeriv (holderDerivOrder β) f x - iteratedDeriv (holderDerivOrder β) f y|
              ≤ M * |x - y| ^ (β - ((holderDerivOrder β) : ℝ))) :
    |kernelSmoothingBias f K t h|
      ≤ (M / ((holderDerivOrder β)).factorial * ∫ u, |K u|) * h ^ β := by
  have hKi : Integrable K := hK.integrable
  have hsupp : ∀ u : ℝ, 1 < |u| → K u = 0 := hK.supp
  set C : ℝ := M / (((holderDerivOrder β)).factorial : ℝ) * h ^ β with hCdef
  have hcoef : (0 : ℝ) ≤ M / (((holderDerivOrder β)).factorial : ℝ) := div_nonneg hM (by positivity)
  have hhb : (0 : ℝ) ≤ h ^ β := Real.rpow_nonneg hh.le β
  have hCnn : 0 ≤ C := by rw [hCdef]; exact mul_nonneg hcoef hhb
  -- Monomials `v^k K v` are integrable (bounded by `|K|` on `[-1,1]`, zero off it).
  have hmono_int : ∀ k : ℕ, Integrable (fun v => v ^ k * K v) := by
    intro k
    refine integrable_of_abs_le_const_mul_kernel hKi
      ((continuous_pow k).aestronglyMeasurable.mul hKi.aestronglyMeasurable) (C := 1) ?_
    intro v
    by_cases hv : |v| ≤ 1
    · rw [abs_mul, one_mul]
      refine mul_le_of_le_one_left (abs_nonneg _) ?_
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hv
    · exact le_of_eq (by simp [hsupp v (lt_of_not_ge hv)])
  -- Pointwise: `K v · Taylor` is a finite sum of scaled monomials in `v K v`.
  have htay : ∀ v : ℝ, K v * taylorPoly (holderDerivOrder β) f t (t + h * v)
      = ∑ k ∈ Finset.range ((holderDerivOrder β) + 1),
          (iteratedDeriv k f t / (k.factorial : ℝ) * h ^ k) * (v ^ k * K v) := by
    intro v
    unfold taylorPoly
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    have hsub : t + h * v - t = h * v := by ring
    rw [hsub, mul_pow]; ring
  have hKtaylor_int :
      Integrable (fun v => K v * taylorPoly (holderDerivOrder β) f t (t + h * v)) := by
    have e : (fun v => K v * taylorPoly (holderDerivOrder β) f t (t + h * v))
        = (fun v => ∑ k ∈ Finset.range ((holderDerivOrder β) + 1),
            (iteratedDeriv k f t / (k.factorial : ℝ) * h ^ k) * (v ^ k * K v)) := funext htay
    rw [e]
    exact integrable_finset_sum _ (fun k _ => (hmono_int k).const_mul _)
  have hKtay_int :
      Integrable (fun v => K v * (taylorPoly (holderDerivOrder β) f t (t + h * v) - f t)) := by
    have e : (fun v => K v * (taylorPoly (holderDerivOrder β) f t (t + h * v) - f t))
        = (fun v => K v * taylorPoly (holderDerivOrder β) f t (t + h * v) - K v * f t) := by
      funext v; rw [mul_sub]
    rw [e]; exact hKtaylor_int.sub (hKi.mul_const (f t))
  -- Moment annihilation: `∫ K · Taylor = f t` (only the constant term survives).
  have hKtaylor_eq : (∫ v, K v * taylorPoly (holderDerivOrder β) f t (t + h * v)) = f t := by
    have e : (fun v => K v * taylorPoly (holderDerivOrder β) f t (t + h * v))
        = (fun v => ∑ k ∈ Finset.range ((holderDerivOrder β) + 1),
            (iteratedDeriv k f t / (k.factorial : ℝ) * h ^ k) * (v ^ k * K v)) := funext htay
    rw [e, integral_finset_sum _ (fun k _ => (hmono_int k).const_mul _)]
    simp_rw [integral_const_mul]
    rw [Finset.sum_eq_single 0]
    · have h0 : (∫ v, v ^ (0 : ℕ) * K v) = 1 := by
        simp only [pow_zero, one_mul]; exact hK.mass
      rw [h0]; simp [iteratedDeriv_zero]
    · intro k hk hk0
      have hkp : k ≤ (holderDerivOrder β) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      rw [hK.moments k hk1 hkp, mul_zero]
    · intro h0
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h0
  have hmom : (∫ v, K v * (taylorPoly (holderDerivOrder β) f t (t + h * v) - f t)) = 0 := by
    have e : (fun v => K v * (taylorPoly (holderDerivOrder β) f t (t + h * v) - f t))
        = (fun v => K v * taylorPoly (holderDerivOrder β) f t (t + h * v) - K v * f t) := by
      funext v; rw [mul_sub]
    rw [e, integral_sub hKtaylor_int (hKi.mul_const (f t)), hKtaylor_eq,
      integral_mul_const, hK.mass, one_mul, sub_self]
  -- Remainder: `|K v · (f(t+hv) − Taylor)| ≤ C |K v|` with `C = (M/p!) h^β`.
  have hRbd : ∀ v : ℝ,
      |K v * (f (t + h * v) - taylorPoly (holderDerivOrder β) f t (t + h * v))| ≤ C * |K v| := by
    intro v
    by_cases hv : |v| ≤ 1
    · have hvb := abs_le.mp hv
      have hav : t + h * v ∈ Set.Icc (t - h) (t + h) := by
        refine ⟨?_, ?_⟩
        · nlinarith [hvb.1, hh.le]
        · nlinarith [hvb.2, hh.le]
      have htm : t ∈ Set.Icc (t - h) (t + h) := by
        constructor <;> linarith [hh.le]
      have hrem := holder_taylor_remainder (lo := t - h) (hi := t + h)
        (t := t) (a := t + h * v) hβ hM htm hav hf hb
      have hRvC :
          |f (t + h * v) - taylorPoly (holderDerivOrder β) f t (t + h * v)| ≤ C := by
        refine le_trans hrem ?_
        have h1 : (t + h * v) - t = h * v := by ring
        rw [h1, abs_mul, abs_of_pos hh, Real.mul_rpow hh.le (abs_nonneg v), hCdef,
          ← mul_assoc]
        have h3 : |v| ^ β ≤ 1 := Real.rpow_le_one (abs_nonneg _) hv hβ.le
        nth_rewrite 2 [← mul_one (M / (((holderDerivOrder β)).factorial : ℝ) * h ^ β)]
        exact mul_le_mul_of_nonneg_left h3 (mul_nonneg hcoef hhb)
      calc
        |K v * (f (t + h * v) - taylorPoly (holderDerivOrder β) f t (t + h * v))|
          = |K v| *
              |f (t + h * v) - taylorPoly (holderDerivOrder β) f t (t + h * v)| := by
              rw [abs_mul]
        _ ≤ |K v| * C := mul_le_mul_of_nonneg_left hRvC (abs_nonneg _)
        _ = C * |K v| := mul_comm _ _
    · exact le_of_eq (by simp [hsupp v (lt_of_not_ge hv)])
  have hKR_int :
      Integrable
        (fun v => K v *
          (f (t + h * v) - taylorPoly (holderDerivOrder β) f t (t + h * v))) := by
    refine integrable_of_abs_le_const_mul_kernel hKi ?_ hRbd
    refine hKi.aestronglyMeasurable.mul (Continuous.sub ?_ ?_).aestronglyMeasurable
    · exact hf.continuous.comp (by fun_prop)
    · have hcont : Continuous (fun v : ℝ => taylorPoly (holderDerivOrder β) f t (t + h * v)) := by
        unfold taylorPoly
        exact continuous_finset_sum _ (fun k _ => by fun_prop)
      exact hcont
  -- Assemble: change of variables, split off the annihilated polynomial, bound the rest.
  rw [kernelSmoothingBias_changeOfVar f K t h hh]
  have hsplit : (∫ v, K v * (f (t + h * v) - f t))
      = (∫ v, K v * (f (t + h * v) - taylorPoly (holderDerivOrder β) f t (t + h * v)))
        + (∫ v, K v * (taylorPoly (holderDerivOrder β) f t (t + h * v) - f t)) := by
    rw [← integral_add hKR_int hKtay_int]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    ring
  rw [hsplit, hmom, add_zero]
  calc |∫ v, K v * (f (t + h * v) - taylorPoly (holderDerivOrder β) f t (t + h * v))|
      ≤ ∫ v, |K v * (f (t + h * v) - taylorPoly (holderDerivOrder β) f t (t + h * v))| := by
        have := MeasureTheory.norm_integral_le_integral_norm
          (μ := volume)
          (fun v : ℝ => K v * (f (t + h * v) - taylorPoly (holderDerivOrder β) f t (t + h * v)))
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∫ v, C * |K v| := integral_mono hKR_int.abs (hKi.abs.const_mul C) hRbd
    _ = C * ∫ v, |K v| := by rw [integral_const_mul]
    _ = (M / ((holderDerivOrder β)).factorial * ∫ u, |K u|) * h ^ β := by rw [hCdef]; ring

end Causalean.Stat.Nonparametric
