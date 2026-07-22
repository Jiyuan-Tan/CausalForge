/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sub-exponential moment-generating functions

A sub-exponential framework mirroring Mathlib's sub-Gaussian design
(`Mathlib.Probability.Moments.SubGaussian`), in the standard `(v, b)`
parameterization of Wainwright/Boucheron–Lugosi–Massart.

`HasSubexponentialMGF X v b μ` means that the moment-generating function of `X`
is bounded by `exp (v t² / 2)` on the interval `b · |t| < 1` (i.e. `|t| < 1/b`,
with the convention that `b = 0` recovers the sub-Gaussian case, valid for all
`t`).  As in the sub-Gaussian development this implies `E[X] = 0`.

## Main results

* closure under negation (`neg`), a.e.-congruence (`congr`), scaling
  (`const_mul`);
* `measure_ge_le` — the sub-exponential Chernoff tail bound
  `P(X ≥ ε) ≤ exp(−ε² / (2 (v + b ε)))`, proved by evaluating the Chernoff
  bound at the explicit point `t = ε / (v + 2 b ε)` (a single choice valid for
  all `v, b ≥ 0`).
-/

import Mathlib.Probability.Moments.SubGaussian

/-! # Sub-exponential moment bounds

This file defines `HasSubexponentialMGF`, a `(v, b)` moment-generating-function
condition for real random variables, and proves the basic calculus needed by
Bernstein-style concentration: finiteness of the underlying measure, closure
under negation, a.e. congruence, scaling, independent addition, the zero
variable, sums over independent families, and the Chernoff tail theorem
`HasSubexponentialMGF.measure_ge_le`.
-/

namespace Causalean.Stat.Concentration

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {v b : ℝ≥0}

/-- A random variable `X` has a sub-exponential moment-generating function with
parameters `(v, b)` with respect to `μ` if, for every `t` with `b · |t| < 1`,
`exp (t * X)` is `μ`-integrable and `mgf X μ t ≤ exp (v t² / 2)`.

The condition `b · |t| < 1` encodes the validity interval `|t| < 1/b`, with
`b = 0` (no scale restriction, i.e. sub-Gaussian) imposing the bound for all
`t`. -/
structure HasSubexponentialMGF (X : Ω → ℝ) (v b : ℝ≥0)
    (μ : Measure Ω := by volume_tac) : Prop where
  integrable_exp_mul : ∀ t : ℝ, (b : ℝ) * |t| < 1 →
    Integrable (fun ω => Real.exp (t * X ω)) μ
  mgf_le : ∀ t : ℝ, (b : ℝ) * |t| < 1 → mgf X μ t ≤ Real.exp (v * t ^ 2 / 2)

namespace HasSubexponentialMGF

/-- A sub-exponential random variable lives on a finite measure (integrability of
`exp (0 · X) = 1`). -/
lemma isFiniteMeasure (hX : HasSubexponentialMGF X v b μ) : IsFiniteMeasure μ := by
  have h := hX.integrable_exp_mul 0 (by simp)
  simp only [zero_mul, Real.exp_zero] at h
  exact (integrable_const_iff.mp h).resolve_left one_ne_zero

/-- Sub-exponentiality is preserved under negation (same parameters). -/
lemma neg (hX : HasSubexponentialMGF X v b μ) :
    HasSubexponentialMGF (fun ω => -X ω) v b μ where
  integrable_exp_mul t ht := by
    have := hX.integrable_exp_mul (-t) (by rwa [abs_neg])
    simpa [mul_comm, mul_neg, neg_mul] using this
  mgf_le t ht := by
    have hmt : (b : ℝ) * |(-t)| < 1 := by rwa [abs_neg]
    have h := hX.mgf_le (-t) hmt
    have hmgf : mgf (fun ω => -X ω) μ t = mgf X μ (-t) := by
      simp only [mgf, neg_mul, mul_neg]
    rw [hmgf]
    refine h.trans_eq ?_
    congr 1; ring

/-- Sub-exponentiality transfers along an a.e.-equality. -/
lemma congr (hX : HasSubexponentialMGF X v b μ) {Y : Ω → ℝ} (hXY : X =ᵐ[μ] Y) :
    HasSubexponentialMGF Y v b μ where
  integrable_exp_mul t ht := by
    refine (integrable_congr ?_).mp (hX.integrable_exp_mul t ht)
    filter_upwards [hXY] with ω hω using by rw [hω]
  mgf_le t ht := by
    rw [mgf_congr (hXY.symm)]
    exact hX.mgf_le t ht

/-- Sub-exponentiality is preserved under scaling: `r • X` has parameters
`(r² v, |r| b)`. -/
lemma const_mul (hX : HasSubexponentialMGF X v b μ) (r : ℝ) :
    HasSubexponentialMGF (fun ω => r * X ω) (⟨r ^ 2, sq_nonneg r⟩ * v)
      (⟨|r|, abs_nonneg r⟩ * b) μ := by
  have hbcoe : ((⟨|r|, abs_nonneg r⟩ * b : ℝ≥0) : ℝ) = |r| * b := by push_cast; ring
  have hvcoe : ((⟨r ^ 2, sq_nonneg r⟩ * v : ℝ≥0) : ℝ) = r ^ 2 * v := by push_cast; ring
  have hbnd : ∀ t : ℝ, ((⟨|r|, abs_nonneg r⟩ * b : ℝ≥0) : ℝ) * |t| < 1 →
      (b : ℝ) * |r * t| < 1 := by
    intro t ht; rw [hbcoe] at ht; rw [abs_mul]; nlinarith [abs_nonneg t, abs_nonneg r, b.coe_nonneg]
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have := hX.integrable_exp_mul (r * t) (hbnd t ht)
    refine (integrable_congr ?_).mpr this
    filter_upwards with ω using by ring_nf
  · rw [mgf_const_mul]
    refine (hX.mgf_le (r * t) (hbnd t ht)).trans_eq ?_
    rw [hvcoe]; congr 1; ring

/-- Independent sub-exponential variables add: `X + Y` has parameters
`(vX + vY, max bX bY)`. -/
lemma add_of_indepFun {Y : Ω → ℝ} {vX bX vY bY : ℝ≥0}
    (hX : HasSubexponentialMGF X vX bX μ) (hY : HasSubexponentialMGF Y vY bY μ)
    (hindep : IndepFun X Y μ) :
    HasSubexponentialMGF (fun ω => X ω + Y ω) (vX + vY) (max bX bY) μ := by
  have hbX : ∀ t : ℝ, ((max bX bY : ℝ≥0) : ℝ) * |t| < 1 → (bX : ℝ) * |t| < 1 := by
    intro t ht
    refine lt_of_le_of_lt (by gcongr; exact_mod_cast le_max_left bX bY) ht
  have hbY : ∀ t : ℝ, ((max bX bY : ℝ≥0) : ℝ) * |t| < 1 → (bY : ℝ) * |t| < 1 := by
    intro t ht
    refine lt_of_le_of_lt (by gcongr; exact_mod_cast le_max_right bX bY) ht
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have hiX := hX.integrable_exp_mul t (hbX t ht)
    have hiY := hY.integrable_exp_mul t (hbY t ht)
    have hind : IndepFun (fun ω => Real.exp (t * X ω)) (fun ω => Real.exp (t * Y ω)) μ :=
      hindep.comp (φ := fun x => Real.exp (t * x)) (ψ := fun x => Real.exp (t * x))
        (by fun_prop) (by fun_prop)
    simp_rw [mul_add, Real.exp_add]
    exact hind.integrable_mul hiX hiY
  · have hiX := hX.integrable_exp_mul t (hbX t ht)
    have hiY := hY.integrable_exp_mul t (hbY t ht)
    have hmgf : mgf (fun ω => X ω + Y ω) μ t = mgf X μ t * mgf Y μ t :=
      hindep.mgf_add hiX.aestronglyMeasurable hiY.aestronglyMeasurable
    rw [hmgf]
    calc mgf X μ t * mgf Y μ t
        ≤ Real.exp (vX * t ^ 2 / 2) * Real.exp (vY * t ^ 2 / 2) := by
          gcongr <;> first
            | exact mgf_nonneg
            | exact hX.mgf_le t (hbX t ht)
            | exact hY.mgf_le t (hbY t ht)
      _ = Real.exp (((vX + vY : ℝ≥0) : ℝ) * t ^ 2 / 2) := by
          rw [← Real.exp_add]; congr 1; push_cast; ring

/-- The constant `0` is sub-exponential with parameters `(0, b)` (any `b`). -/
lemma zero [IsProbabilityMeasure μ] : HasSubexponentialMGF (fun _ : Ω => (0 : ℝ)) 0 b μ := by
  refine ⟨fun t _ => ?_, fun t _ => ?_⟩
  · simp
  · simp [mgf, mul_zero, Real.exp_zero]

/-- **Chernoff bound** for the right tail of a sub-exponential random variable:
`P(X ≥ ε) ≤ exp(−ε² / (2 (v + b ε)))`. -/
theorem measure_ge_le (hX : HasSubexponentialMGF X v b μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ X ω} ≤ Real.exp (-ε ^ 2 / (2 * ((v : ℝ) + b * ε))) := by
  haveI := hX.isFiniteMeasure
  by_cases hvb : (v : ℝ) + b * ε = 0
  · -- degenerate case: the bound reads `≤ exp 0 = 1`
    rw [hvb]
    have h0 := hX.mgf_le 0 (by simp)
    simp only [mul_zero, div_zero, Real.exp_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_div] at h0 ⊢
    -- `mgf X μ 0 = μ.real univ ≤ 1`, so `μ.real {…} ≤ 1`.
    have huniv : μ.real Set.univ ≤ 1 := by
      have : mgf X μ 0 = μ.real Set.univ := by simp [mgf, Measure.real]
      rwa [this] at h0
    calc μ.real {ω | ε ≤ X ω}
        ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ ≤ 1 := huniv
  · have hbε : (0 : ℝ) ≤ b * ε := by positivity
    have hpos : 0 < (v : ℝ) + b * ε := lt_of_le_of_ne (by positivity) (Ne.symm hvb)
    have hD : 0 < (v : ℝ) + 2 * b * ε := by nlinarith
    set t : ℝ := ε / ((v : ℝ) + 2 * b * ε) with ht
    have ht0 : 0 ≤ t := by positivity
    have htabs : |t| = t := abs_of_nonneg ht0
    have htb : (b : ℝ) * |t| < 1 := by
      rw [htabs, ht, ← mul_div_assoc, div_lt_one hD]
      nlinarith
    have hcheb := measure_ge_le_exp_mul_mgf ε ht0 (hX.integrable_exp_mul t htb)
    calc μ.real {ω | ε ≤ X ω}
        ≤ Real.exp (-t * ε) * mgf X μ t := hcheb
      _ ≤ Real.exp (-t * ε) * Real.exp (v * t ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (hX.mgf_le t htb) (Real.exp_pos _).le
      _ = Real.exp (-t * ε + v * t ^ 2 / 2) := by rw [← Real.exp_add]
      _ ≤ Real.exp (-ε ^ 2 / (2 * ((v : ℝ) + b * ε))) := by
          rw [Real.exp_le_exp]
          -- `t` satisfies `t · (v + 2bε) = ε`; clear the remaining denominator.
          have htD : t * ((v : ℝ) + 2 * b * ε) = ε := by
            rw [ht]; exact div_mul_cancel₀ ε (ne_of_gt hD)
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ((v : ℝ) + b * ε))]
          -- the cleared inequality is an exact identity: LHS·2(v+bε) + ε² = −t²·v·b·ε ≤ 0
          have hfin : (-t * ε + (v : ℝ) * t ^ 2 / 2) * (2 * ((v : ℝ) + b * ε)) + ε ^ 2
              = -t ^ 2 * v * b * ε := by
            linear_combination ((v : ℝ) * t - ε) * htD
          nlinarith [hfin, mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg t)
            v.coe_nonneg) b.coe_nonneg) hε]

/-- A sum of `n` independent sub-exponential variables sharing common parameters
`(v, b)` is sub-exponential with parameters `(n • v, b)` (the `b`-parameters
coincide, so they do not grow). -/
lemma sum_range_of_iIndepFun {Z : ℕ → Ω → ℝ} (h_indep : iIndepFun Z μ)
    (h_meas : ∀ i, AEMeasurable (Z i) μ) {v b : ℝ≥0} {n : ℕ}
    (h : ∀ i < n, HasSubexponentialMGF (Z i) v b μ) :
    HasSubexponentialMGF (fun ω => ∑ i ∈ Finset.range n, Z i ω) (n • v) b μ := by
  haveI : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  induction n with
  | zero => simpa using (zero : HasSubexponentialMGF (fun _ : Ω => (0 : ℝ)) 0 b μ)
  | succ n ih =>
    have ihn := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hZn : HasSubexponentialMGF (Z n) v b μ := h n (Nat.lt_succ_self n)
    have hindZ : IndepFun (fun ω => ∑ i ∈ Finset.range n, Z i ω) (Z n) μ := by
      have h' := h_indep.indepFun_finset_sum_of_notMem₀ h_meas
        (Finset.notMem_range_self (n := n))
      have heq : (fun ω => ∑ i ∈ Finset.range n, Z i ω) = ∑ j ∈ Finset.range n, Z j := by
        funext ω; rw [Finset.sum_apply]
      rwa [heq]
    have hsum := ihn.add_of_indepFun hZn hindZ
    have hfun : (fun ω => ∑ i ∈ Finset.range (n + 1), Z i ω)
        = fun ω => (∑ i ∈ Finset.range n, Z i ω) + Z n ω := by
      funext ω; rw [Finset.sum_range_succ]
    rw [hfun, show ((n + 1) • v) = n • v + v from succ_nsmul v n]
    convert hsum using 2
    exact (max_self b).symm

end HasSubexponentialMGF

end Causalean.Stat.Concentration
