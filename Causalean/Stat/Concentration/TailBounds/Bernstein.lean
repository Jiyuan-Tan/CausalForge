/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bernstein's inequality for bounded i.i.d. samples

Bernstein-type concentration built on the sub-exponential framework of
`Causalean.Stat.Concentration.SubExponential`.  Following the design decision to
route the bound through the constant-`v` sub-exponential structure (rather than
the sharper denominator-form MGF estimate), the variance enters with a factor
`2`, giving the tail `exp(−n ε² / (2 (2σ² + c ε)))`.

## Proof route

The file proves the Bernstein tail bounds without power-series machinery.  The
key observation is that the sub-exponential packaging only needs the MGF bound
`mgf X μ t ≤ exp(σ² t²)` on the validity interval `c|t| < 1`, *not* the sharp
denominator-form Bernstein MGF estimate.  On that interval `|t X| ≤ 1` a.e., so
the elementary pointwise bound `exp u ≤ 1 + u + u²` (for `|u| ≤ 1`, itself a
corollary of `Real.norm_exp_sub_one_sub_id_le`) integrates directly to
`mgf X μ t ≤ 1 + σ² t² ≤ exp(σ² t²)`.

* `exp_le_one_add_add_sq` — pointwise `exp u ≤ 1 + u + u²` for `|u| ≤ 1`.
* `bounded_mgf_le_exp_sq` — `mgf X μ t ≤ exp(σ² t²)` for a bounded mean-zero
  variable on `c|t| ≤ 1`, by integrating the pointwise bound.
* `bounded_hasSubexponentialMGF` — packages a bounded mean-zero variable as
  sub-exponential with parameters `(2σ², c)`.
* `bernstein_ge` / `bernstein_abs_ge` — the one- and two-sided Bernstein tail
  bounds for the sample mean of a bounded statistic, from the independent-sum
  lemma + the sub-exponential Chernoff bound.

The constant is deliberately loosened: the sharp textbook tail
`exp(−n ε² / (2 (σ² + cε/3)))` is *not* reachable through the constant-`v`
sub-exponential structure (it needs a bespoke Chernoff optimisation on the
denominator-form MGF), so the variance proxy is `2σ²` and the scale is `c`.
-/

import Causalean.Stat.Concentration.TailBounds.SubExponential
import Causalean.Stat.Concentration.TailBounds.Hoeffding

/-! # Bernstein inequalities

This file proves Bernstein-style concentration bounds for bounded i.i.d.
sample means by packaging bounded centered variables as sub-exponential
random variables. The main bridge is `bounded_hasSubexponentialMGF`, derived
from the elementary MGF estimate `bounded_mgf_le_exp_sq`; the exported tail
theorems are `bernstein_ge` and `bernstein_abs_ge`.

The constants intentionally come from the constant-`v` sub-exponential route:
the variance proxy is `2 * σ ^ 2` and the final exponent is
`-n * ε ^ 2 / (2 * (2 * σ ^ 2 + c * ε))`.
-/

namespace Causalean.Stat.Concentration

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ}
  {X' : Type*} [MeasurableSpace X'] {P : Measure X'}

/-- Pointwise elementary bound `exp u ≤ 1 + u + u²` valid for `|u| ≤ 1`.

A real corollary of `Real.norm_exp_sub_one_sub_id_le` (`‖exp u − 1 − u‖ ≤ ‖u‖²`
for `‖u‖ ≤ 1`): drop the absolute value on the left and use `‖u‖² = u²`. -/
lemma exp_le_one_add_add_sq {u : ℝ} (hu : |u| ≤ 1) :
    Real.exp u ≤ 1 + u + u ^ 2 := by
  have h := Real.norm_exp_sub_one_sub_id_le (x := u) (by rwa [Real.norm_eq_abs])
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs] at h
  have := (le_abs_self (Real.exp u - 1 - u)).trans h
  linarith

/-- **MGF bound** for a bounded mean-zero random variable on the validity
interval.  For a mean-zero `X` with `|X| ≤ c` `μ`-a.e. and second moment
`E[X²] ≤ σ²`, the moment-generating function obeys `mgf X μ t ≤ exp(σ² t²)`
whenever `c |t| ≤ 1`.

Proof: on this interval `|t X| ≤ 1` a.e., so `exp(t X) ≤ 1 + t X + t² X²`
pointwise (`exp_le_one_add_add_sq`).  Integrating and using `E[X] = 0`,
`E[X²] ≤ σ²` gives `mgf X μ t ≤ 1 + σ² t² ≤ exp(σ² t²)`. -/
lemma bounded_mgf_le_exp_sq [IsProbabilityMeasure μ] {c σ : ℝ} (hc : 0 ≤ c)
    (hmeas : AEMeasurable X μ) (hmean : μ[X] = 0)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ c) (hvar : μ[fun ω => X ω ^ 2] ≤ σ ^ 2)
    {t : ℝ} (ht : c * |t| ≤ 1) :
    mgf X μ t ≤ Real.exp (σ ^ 2 * t ^ 2) := by
  -- integrability of the summands
  have hint_exp : Integrable (fun ω => Real.exp (t * X ω)) μ := by
    refine Integrable.mono' (integrable_const (Real.exp (|t| * c)))
      ((Real.measurable_exp.comp_aemeasurable (hmeas.const_mul t)).aestronglyMeasurable) ?_
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr <| (le_abs_self _).trans <| by
      rw [abs_mul]; gcongr
  have hint_X : Integrable X μ :=
    Integrable.mono' (integrable_const c) hmeas.aestronglyMeasurable
      (by filter_upwards [hbound] with ω hω; rwa [Real.norm_eq_abs])
  have hint_Xsq : Integrable (fun ω => X ω ^ 2) μ :=
    Integrable.mono' (integrable_const (c ^ 2)) (hmeas.pow_const 2).aestronglyMeasurable
      (by filter_upwards [hbound] with ω hω
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          nlinarith [hω, abs_nonneg (X ω), sq_abs (X ω)])
  -- pointwise bound `exp (t X) ≤ 1 + t X + t² X²`
  have hpt : ∀ᵐ ω ∂μ, Real.exp (t * X ω) ≤ 1 + t * X ω + t ^ 2 * X ω ^ 2 := by
    filter_upwards [hbound] with ω hω
    have hu : |t * X ω| ≤ 1 := by
      rw [abs_mul]
      calc |t| * |X ω| ≤ |t| * c := by gcongr
        _ = c * |t| := by ring
        _ ≤ 1 := ht
    calc Real.exp (t * X ω) ≤ 1 + t * X ω + (t * X ω) ^ 2 := exp_le_one_add_add_sq hu
      _ = 1 + t * X ω + t ^ 2 * X ω ^ 2 := by ring
  -- integrate
  have hrhs_int : Integrable (fun ω => 1 + t * X ω + t ^ 2 * X ω ^ 2) μ :=
    ((integrable_const (1 : ℝ)).add (hint_X.const_mul t)).add (hint_Xsq.const_mul (t ^ 2))
  have hval : (∫ ω, (1 + t * X ω + t ^ 2 * X ω ^ 2) ∂μ)
      = 1 + t ^ 2 * (μ[fun ω => X ω ^ 2]) := by
    have h1a : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
    have h1b : Integrable (fun ω => t * X ω) μ := hint_X.const_mul t
    have h1 : Integrable (fun ω => (1 : ℝ) + t * X ω) μ := h1a.add h1b
    have hg : Integrable (fun ω => t ^ 2 * X ω ^ 2) μ := hint_Xsq.const_mul (t ^ 2)
    rw [integral_add h1 hg, integral_add h1a h1b, integral_const_mul, integral_const_mul,
      integral_const, hmean]
    simp
  calc mgf X μ t = ∫ ω, Real.exp (t * X ω) ∂μ := by rw [ProbabilityTheory.mgf]
    _ ≤ ∫ ω, (1 + t * X ω + t ^ 2 * X ω ^ 2) ∂μ := integral_mono_ae hint_exp hrhs_int hpt
    _ = 1 + t ^ 2 * (μ[fun ω => X ω ^ 2]) := hval
    _ ≤ 1 + t ^ 2 * σ ^ 2 := by nlinarith [hvar, sq_nonneg t]
    _ ≤ Real.exp (σ ^ 2 * t ^ 2) := by
        have := Real.add_one_le_exp (σ ^ 2 * t ^ 2); nlinarith [this]

/-- A bounded mean-zero random variable is sub-exponential with parameters
`(2σ², c)`.  The MGF branch is `bounded_mgf_le_exp_sq` (note `2σ² · t²/2 = σ²t²`),
valid on `c|t| < 1`. -/
lemma bounded_hasSubexponentialMGF [IsProbabilityMeasure μ] {c σ : ℝ}
    (hc : 0 ≤ c) (hσ : 0 ≤ σ) (hmeas : AEMeasurable X μ) (hmean : μ[X] = 0)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ c) (hvar : μ[fun ω => X ω ^ 2] ≤ σ ^ 2) :
    HasSubexponentialMGF X ⟨2 * σ ^ 2, by positivity⟩ ⟨c, hc⟩ μ := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · -- integrability of `exp (t X)`: bounded above by the constant `exp (|t| c)`
    refine Integrable.mono' (integrable_const (Real.exp (|t| * c)))
      ((Real.measurable_exp.comp_aemeasurable (hmeas.const_mul t)).aestronglyMeasurable) ?_
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr <| (le_abs_self _).trans <| by
      rw [abs_mul]; gcongr
  · -- mgf bound: `2σ² · t²/2 = σ²t²`
    simp only [NNReal.coe_mk] at ht ⊢
    calc mgf X μ t ≤ Real.exp (σ ^ 2 * t ^ 2) :=
          bounded_mgf_le_exp_sq hc hmeas hmean hbound hvar (le_of_lt ht)
      _ = Real.exp (2 * σ ^ 2 * t ^ 2 / 2) := by
          rw [show 2 * σ ^ 2 * t ^ 2 / 2 = σ ^ 2 * t ^ 2 from by ring]

/-- **One-sided Bernstein inequality** for the sample mean of a bounded
statistic.  If `f` has population mean `m = E[f]`, satisfies `|f − m| ≤ c`
`P`-a.e., and has variance `∫ (f − m)² ≤ σ²`, then for `ε ≥ 0`,
`P(X̄ₙ − m ≥ ε) ≤ exp(−n ε² / (2 (2σ² + c ε)))`. -/
theorem bernstein_ge (S : IIDSample Ω X' μ P) {f : X' → ℝ} (hf : Measurable f)
    (hfint : Integrable f P) {c σ : ℝ} (hc : 0 ≤ c) (hσ : 0 ≤ σ)
    (hbound : ∀ᵐ x ∂P, |f x - ∫ y, f y ∂P| ≤ c)
    (hvar : ∫ x, (f x - ∫ y, f y ∂P) ^ 2 ∂P ≤ σ ^ 2)
    (n : ℕ) (hn : 0 < n) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ S.sampleMean f n ω - ∫ x, f x ∂P}
      ≤ Real.exp (-n * ε ^ 2 / (2 * (2 * σ ^ 2 + c * ε))) := by
  classical
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  haveI : IsProbabilityMeasure P := by
    rw [← S.law]; exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  set m : ℝ := ∫ x, f x ∂P with hm
  set g : X' → ℝ := fun x => f x - m with hg
  have hg_meas : Measurable g := hf.sub_const m
  -- each centered sample point is sub-exponential with parameters `(2σ², c)`
  have hYsubexp : ∀ i, HasSubexponentialMGF (fun ω => g (S.Z i ω))
      ⟨2 * σ ^ 2, by positivity⟩ ⟨c, hc⟩ μ := by
    intro i
    refine bounded_hasSubexponentialMGF hc hσ (hg_meas.comp (S.meas i)).aemeasurable ?_ ?_ ?_
    · -- mean zero
      have heq : (∫ ω, g (S.Z i ω) ∂μ) = ∫ x, g x ∂P := S.integral_comp_eq hg_meas i
      have hz : (∫ x, g x ∂P) = 0 := by
        rw [hg, integral_sub hfint (integrable_const m), integral_const]
        simp only [probReal_univ, one_smul, hm, sub_self]
      rw [show (μ[fun ω => g (S.Z i ω)]) = ∫ ω, g (S.Z i ω) ∂μ from rfl, heq, hz]
    · -- boundedness pulled back along `Z i`
      have hb2 := hbound
      rw [← S.map_eq i] at hb2
      exact (ae_map_iff (S.meas i).aemeasurable
        (measurableSet_le hg_meas.abs measurable_const)).mp hb2
    · -- variance
      have hsq : (μ[fun ω => g (S.Z i ω) ^ 2]) = ∫ x, g x ^ 2 ∂P :=
        S.integral_comp_eq (hg_meas.pow_const 2) i
      rw [hsq, hg]
      exact hvar
  -- the centered family is independent
  have hindep : iIndepFun (fun i ω => g (S.Z i ω)) μ :=
    S.indep.comp (fun _ => g) (fun _ => hg_meas)
  have hmeasZ : ∀ i, AEMeasurable (fun ω => g (S.Z i ω)) μ :=
    fun i => (hg_meas.comp (S.meas i)).aemeasurable
  -- the sum of `n` of them is sub-exponential with parameters `(n•(2σ²), c)`
  have hsum := HasSubexponentialMGF.sum_range_of_iIndepFun hindep hmeasZ
    (v := ⟨2 * σ ^ 2, by positivity⟩) (b := ⟨c, hc⟩) (n := n)
    (fun i _ => hYsubexp i)
  have hcher := hsum.measure_ge_le (ε := (n : ℝ) * ε) (by positivity)
  rw [sampleMean_sub_ge_setEq S f m hn ε]
  -- the two centered-sum events coincide definitionally (`g (Z i) = f (Z i) − m`)
  refine hcher.trans (le_of_eq ?_)
  -- simplify the exponent: cancel the common factor `n > 0`
  have hn' : (n : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hn)
  congr 1
  simp only [nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_mk]
  rw [show -((n : ℝ) * ε) ^ 2 = (n : ℝ) * (-(n : ℝ) * ε ^ 2) from by ring,
    show 2 * ((n : ℝ) * (2 * σ ^ 2) + c * ((n : ℝ) * ε))
      = (n : ℝ) * (2 * (2 * σ ^ 2 + c * ε)) from by ring,
    mul_div_mul_left _ _ hn']

/-- **Two-sided Bernstein inequality** for the sample mean of a bounded
statistic: `P(|X̄ₙ − m| ≥ ε) ≤ 2 exp(−n ε² / (2 (2σ² + c ε)))`. -/
theorem bernstein_abs_ge (S : IIDSample Ω X' μ P) {f : X' → ℝ} (hf : Measurable f)
    (hfint : Integrable f P) {c σ : ℝ} (hc : 0 ≤ c) (hσ : 0 ≤ σ)
    (hbound : ∀ᵐ x ∂P, |f x - ∫ y, f y ∂P| ≤ c)
    (hvar : ∫ x, (f x - ∫ y, f y ∂P) ^ 2 ∂P ≤ σ ^ 2)
    (n : ℕ) (hn : 0 < n) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |S.sampleMean f n ω - ∫ x, f x ∂P|}
      ≤ 2 * Real.exp (-n * ε ^ 2 / (2 * (2 * σ ^ 2 + c * ε))) := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  set m : ℝ := ∫ x, f x ∂P with hm
  have hup := bernstein_ge S hf hfint hc hσ hbound hvar n hn hε
  -- lower tail via negation: apply the one-sided bound to `-f`
  have hbound' : ∀ᵐ x ∂P, |(-f x) - ∫ y, -f y ∂P| ≤ c := by
    rw [integral_neg, ← hm]
    filter_upwards [hbound] with x hx
    rw [show -f x - -m = -(f x - m) from by ring, abs_neg]
    exact hx
  have hvar' : ∫ x, ((-f x) - ∫ y, -f y ∂P) ^ 2 ∂P ≤ σ ^ 2 := by
    rw [integral_neg, ← hm]
    simp only [show ∀ x, (-f x - -m) ^ 2 = (f x - m) ^ 2 from fun x => by ring]
    exact hvar
  have hlow := bernstein_ge S (f := fun x => -f x) hf.neg hfint.neg hc hσ hbound' hvar' n hn hε
  have hint_neg : (∫ x, (fun x => -f x) x ∂P) = -m := by simp [hm, integral_neg]
  have hmean_neg : ∀ ω, S.sampleMean (fun x => -f x) n ω = -S.sampleMean f n ω := by
    intro ω; simp [IIDSample.sampleMean, Finset.sum_neg_distrib, mul_neg]
  rw [hint_neg] at hlow
  simp only [hmean_neg, sub_neg_eq_add] at hlow
  exact measureReal_abs_dev_le_two_sided (S.sampleMean f n) m _ ε hup hlow

end Causalean.Stat.Concentration
