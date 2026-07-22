/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Minimax.Pinsker
import Causalean.Stat.Minimax.LeCam
import Causalean.Stat.Minimax.BretagnolleHuber
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Le Cam two-point lower bound for finite L¹ risk

This file packages two reusable finite-sample Le Cam risk lower bounds for
estimating a real-valued functional from independent product observations.

The L¹ theorem `leCam_two_point_L1_lower` converts a two-point separation
`δ ≤ |θP - θQ|`, an `n`-sample KL budget, a supplied product-KL comparison, and a
supplied product Pinsker bridge into a positive lower bound on the worst-case
Bochner L¹ risk of any measurable estimator.  The MSE theorem
`le_cam_two_point_mse` uses the Bretagnolle-Huber testing floor instead of
Pinsker, so every finite KL budget `K` yields a positive constant
`exp(-K) / 32` for the corresponding worst-case squared-error risk.

The private helper `event_mul_measureReal_le_integral` is the Markov-type
event-to-integral step used by the L¹ theorem; the MSE theorem uses the
project-wide squared-loss event bound.
-/

namespace Causalean.Stat.Minimax

open MeasureTheory

/-- If a nonnegative measurable integrand is at least `s` on an event, then
`s` times the event probability is bounded by its integral. -/
private lemma event_mul_measureReal_le_integral
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf_int : Integrable f μ) (hf_meas : Measurable f)
    {s : ℝ} (hf_nonneg : ∀ᵐ x ∂μ, 0 ≤ f x) :
    s * μ.real {x | s ≤ f x} ≤ ∫ x, f x ∂μ := by
  have hset : MeasurableSet {x | s ≤ f x} :=
    measurableSet_le measurable_const hf_meas
  have hconst_int :
      Integrable ({x | s ≤ f x}.indicator (fun _ : Ω => s)) μ :=
    (integrable_const s).indicator hset
  have hmono_ae :
      ∀ᵐ x ∂μ, {x | s ≤ f x}.indicator (fun _ : Ω => s) x ≤ f x := by
    filter_upwards [hf_nonneg] with x hx_nonneg
    by_cases hx : x ∈ {x | s ≤ f x}
    · rw [Set.indicator_of_mem hx]
      exact hx
    · have hsx : ({x | s ≤ f x}.indicator (fun _ : Ω => s) x) = 0 := by
        simp [Set.indicator_of_notMem hx]
      rw [hsx]
      exact hx_nonneg
  have hle := integral_mono_ae hconst_int hf_int hmono_ae
  have hleft :
      ∫ x, {x | s ≤ f x}.indicator (fun _ : Ω => s) x ∂μ =
        s * μ.real {x | s ≤ f x} := by
    rw [integral_indicator hset, setIntegral_const, smul_eq_mul]
    ring
  simpa [hleft] using hle

/-- Le Cam two-point lower bound on finite Bochner `L¹` risk for estimating a
real-valued functional from `n` i.i.d. observations.

The product-law Pinsker and product-KL facts are explicit hypotheses. -/
theorem leCam_two_point_L1_lower
    {Ω : Type*} [MeasurableSpace Ω]
    (C : ℝ) (_hC_pos : 0 < C) (hC_small : C ≤ 1 / 2) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (n : ℕ), 1 ≤ n →
        ∀ (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
          (θP θQ δ : ℝ),
          (n : ℝ) * (_root_.InformationTheory.klDiv P Q).toReal ≤ C →
          (_root_.InformationTheory.klDiv
              (Measure.pi (fun _ : Fin n => P))
              (Measure.pi (fun _ : Fin n => Q))).toReal
            ≤ (n : ℝ) * (_root_.InformationTheory.klDiv P Q).toReal →
          Causalean.Stat.PinskerBound
            (Measure.pi (fun _ : Fin n => P))
            (Measure.pi (fun _ : Fin n => Q)) →
          0 ≤ δ → δ ≤ |θP - θQ| →
          ∀ (T : (Fin n → Ω) → ℝ), Measurable T →
            Integrable (fun ω : Fin n → Ω => |T ω - θP|)
              (Measure.pi (fun _ : Fin n => P)) →
            Integrable (fun ω : Fin n → Ω => |T ω - θQ|)
              (Measure.pi (fun _ : Fin n => Q)) →
            c₀ * δ ≤ max
              (∫ ω, |T ω - θP| ∂Measure.pi (fun _ : Fin n => P))
              (∫ ω, |T ω - θQ| ∂Measure.pi (fun _ : Fin n => Q)) := by
  refine ⟨(1 / 8 : ℝ), by norm_num, ?_⟩
  intro n _hn P Q _ _ θP θQ δ hKLbound hKLprod hPinsker hδnonneg hδsep
    T hT hIntp hIntq
  have hsep : 2 * (δ / 2) ≤ dist θP θQ := by
    rw [Real.dist_eq]
    linarith
  have hprob := Causalean.Stat.klForm_two_point_lower_bound_of_pinsker
    (P₀ := Measure.pi (fun _ : Fin n => P))
    (P₁ := Measure.pi (fun _ : Fin n => Q))
    (Θ := ℝ) hPinsker hT hsep
  have hklprodC :
      (_root_.InformationTheory.klDiv
        (Measure.pi (fun _ : Fin n => P))
        (Measure.pi (fun _ : Fin n => Q))).toReal ≤ C :=
    hKLprod.trans hKLbound
  have hprobLower :
      (1 / 4 : ℝ) ≤
        max ((Measure.pi (fun _ : Fin n => P)).real
          {ω | δ / 2 ≤ dist (T ω) θP})
        ((Measure.pi (fun _ : Fin n => Q)).real
          {ω | δ / 2 ≤ dist (T ω) θQ}) := by
    have hkl_nonneg :
        0 ≤ (_root_.InformationTheory.klDiv
          (Measure.pi (fun _ : Fin n => P))
          (Measure.pi (fun _ : Fin n => Q))).toReal := ENNReal.toReal_nonneg
    have hpre :
        (1 / 4 : ℝ) ≤
          (1 - Real.sqrt
            (((_root_.InformationTheory.klDiv
              (Measure.pi (fun _ : Fin n => P))
              (Measure.pi (fun _ : Fin n => Q))).toReal) / 2)) / 2 := by
      have hdiv_le :
          ((_root_.InformationTheory.klDiv
            (Measure.pi (fun _ : Fin n => P))
            (Measure.pi (fun _ : Fin n => Q))).toReal) / 2 ≤
            (1 / 4 : ℝ) := by
        nlinarith
      have hsqrt_le :
          Real.sqrt
            (((_root_.InformationTheory.klDiv
              (Measure.pi (fun _ : Fin n => P))
              (Measure.pi (fun _ : Fin n => Q))).toReal) / 2) ≤
              (1 / 2 : ℝ) := by
        have h := Real.sqrt_le_sqrt hdiv_le
        convert h using 1
        rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num]
        rw [Real.sqrt_sq (by norm_num : 0 ≤ (1 / 2 : ℝ))]
      nlinarith
    exact hpre.trans hprob
  have hmeas_p : Measurable (fun ω : Fin n → Ω => |T ω - θP|) := by
    fun_prop
  have hmeas_q : Measurable (fun ω : Fin n → Ω => |T ω - θQ|) := by
    fun_prop
  have hp_event := event_mul_measureReal_le_integral
    (μ := Measure.pi (fun _ : Fin n => P))
    (f := fun ω : Fin n → Ω => |T ω - θP|)
    hIntp hmeas_p (s := δ / 2)
    (Filter.Eventually.of_forall fun _ => abs_nonneg _)
  have hq_event := event_mul_measureReal_le_integral
    (μ := Measure.pi (fun _ : Fin n => Q))
    (f := fun ω : Fin n → Ω => |T ω - θQ|)
    hIntq hmeas_q (s := δ / 2)
    (Filter.Eventually.of_forall fun _ => abs_nonneg _)
  have hp_event' :
      (δ / 2) *
        (Measure.pi (fun _ : Fin n => P)).real
          {ω | δ / 2 ≤ dist (T ω) θP} ≤
      ∫ ω, |T ω - θP| ∂Measure.pi (fun _ : Fin n => P) := by
    simpa [Real.dist_eq] using hp_event
  have hq_event' :
      (δ / 2) *
        (Measure.pi (fun _ : Fin n => Q)).real
          {ω | δ / 2 ≤ dist (T ω) θQ} ≤
      ∫ ω, |T ω - θQ| ∂Measure.pi (fun _ : Fin n => Q) := by
    simpa [Real.dist_eq] using hq_event
  have hmax_event :
      (δ / 2) *
        max ((Measure.pi (fun _ : Fin n => P)).real
          {ω | δ / 2 ≤ dist (T ω) θP})
        ((Measure.pi (fun _ : Fin n => Q)).real
          {ω | δ / 2 ≤ dist (T ω) θQ}) ≤
      max (∫ ω, |T ω - θP| ∂Measure.pi (fun _ : Fin n => P))
        (∫ ω, |T ω - θQ| ∂Measure.pi (fun _ : Fin n => Q)) := by
    by_cases hpq :
        (Measure.pi (fun _ : Fin n => P)).real
          {ω | δ / 2 ≤ dist (T ω) θP} ≤
        (Measure.pi (fun _ : Fin n => Q)).real
          {ω | δ / 2 ≤ dist (T ω) θQ}
    · rw [max_eq_right hpq]
      exact hq_event'.trans (le_max_right _ _)
    · have hqp :
          (Measure.pi (fun _ : Fin n => Q)).real
            {ω | δ / 2 ≤ dist (T ω) θQ} ≤
          (Measure.pi (fun _ : Fin n => P)).real
            {ω | δ / 2 ≤ dist (T ω) θP} :=
        le_of_not_ge hpq
      rw [max_eq_left hqp]
      exact hp_event'.trans (le_max_left _ _)
  have hleft : (1 / 8 : ℝ) * δ ≤ (δ / 2) * (1 / 4 : ℝ) := by
    ring_nf
    rfl
  have hmid :
      (δ / 2) * (1 / 4 : ℝ) ≤
        (δ / 2) *
          max ((Measure.pi (fun _ : Fin n => P)).real
            {ω | δ / 2 ≤ dist (T ω) θP})
          ((Measure.pi (fun _ : Fin n => Q)).real
            {ω | δ / 2 ≤ dist (T ω) θQ}) :=
    mul_le_mul_of_nonneg_left hprobLower (by linarith)
  exact hleft.trans (hmid.trans hmax_event)

/-- **Le Cam two-point reduction in mean-squared-error form, uniform over a finite KL budget.**
For every Kullback–Leibler budget `K` there is a single positive constant `c_K` (here
`exp(−K)/32`), chosen before the laws, such that the following holds for EVERY pair of probability
laws `Q₀, Q₁` on any measurable space whose divergence obeys `KL(Q₀, Q₁) ≤ K`: any measurable
estimator `T` with integrable squared loss under both laws has worst-case mean-squared error at
least `c_K · (θ₁ − θ₀)²`, where `θ₀, θ₁` are the two candidate parameter values.  The finite-budget
hypothesis is encoded as the `ℝ≥0∞` inequality `klDiv Q₀ Q₁ ≤ ENNReal.ofReal K`, which forces a
finite divergence (so it cannot be met vacuously by an infinite divergence collapsing under
`.toReal`) and pins `c_K` to `K` alone.

Unlike Pinsker's inequality — whose testing floor is positive only for `K < 2` — the constant here
is positive for every finite KL budget, because the testing floor is supplied by the
Bretagnolle–Huber inequality (`Causalean.Stat.bretagnolle_huber_affinity`).  The estimation→testing
step uses the `(θ₁ − θ₀)/2` separation via `Causalean.Stat.half_one_sub_tvDist_le_max_error` and a
Markov/Chebyshev bound on the squared loss. -/
lemma le_cam_two_point_mse (K : ℝ) :
    ∃ cK : ℝ, 0 < cK ∧
      ∀ {S : Type*} [MeasurableSpace S]
        (Q0 Q1 : Measure S) [IsProbabilityMeasure Q0] [IsProbabilityMeasure Q1]
        (theta0 theta1 : ℝ),
        InformationTheory.klDiv Q0 Q1 ≤ ENNReal.ofReal K →
        ∀ T : S → ℝ, Measurable T →
          Integrable (fun s => (T s - theta0) ^ 2) Q0 →
          Integrable (fun s => (T s - theta1) ^ 2) Q1 →
          cK * (theta1 - theta0) ^ 2
            ≤ max (∫ s, (T s - theta0) ^ 2 ∂Q0) (∫ s, (T s - theta1) ^ 2 ∂Q1) := by
  refine ⟨Real.exp (-(ENNReal.ofReal K).toReal) / 32, ?_, ?_⟩
  · positivity
  intro S _ Q0 Q1 _ _ theta0 theta1 hKL T hT hInt0 hInt1
  let r : ℝ := |theta1 - theta0| / 2
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  have hsep : 2 * r ≤ |theta0 - theta1| := by
    dsimp [r]
    rw [abs_sub_comm]
    linarith [abs_nonneg (theta1 - theta0)]
  have hsep_dist : 2 * r ≤ dist theta0 theta1 := by
    rwa [Real.dist_eq]
  have hprob_dist := Causalean.Stat.half_one_sub_tvDist_le_max_error
    (P₀ := Q0) (P₁ := Q1) (Θ := ℝ) hT hsep_dist
  have hprob :
      (1 - Causalean.Stat.tvDist Q0 Q1) / 2
        ≤ max (Q0.real {s | r ≤ |T s - theta0|})
            (Q1.real {s | r ≤ |T s - theta1|}) := by
    simpa only [Real.dist_eq] using hprob_dist
  have hkl_toReal_le :
      (InformationTheory.klDiv Q0 Q1).toReal ≤ (ENNReal.ofReal K).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hKL
  have hexp_budget :
      Real.exp (-(ENNReal.ofReal K).toReal)
        ≤ Real.exp (-(InformationTheory.klDiv Q0 Q1).toReal) := by
    exact Real.exp_le_exp.mpr (by linarith)
  -- The finite-budget hypothesis pins down both BH side-conditions.
  have hfin : InformationTheory.klDiv Q0 Q1 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKL
  have hac : Q0 ≪ Q1 := (InformationTheory.klDiv_ne_top_iff.mp hfin).1
  have hBH :=
    Causalean.Stat.bretagnolle_huber_affinity Q0 Q1 hac hfin
  have hprob_floor :
      Real.exp (-(ENNReal.ofReal K).toReal) / 4
        ≤ max (Q0.real {s | r ≤ |T s - theta0|})
            (Q1.real {s | r ≤ |T s - theta1|}) := by
    calc
      Real.exp (-(ENNReal.ofReal K).toReal) / 4
          ≤ ((1 / 2 : ℝ) * Real.exp (-(InformationTheory.klDiv Q0 Q1).toReal)) / 2 := by
            nlinarith [hexp_budget, Real.exp_pos (-(ENNReal.ofReal K).toReal),
              Real.exp_pos (-(InformationTheory.klDiv Q0 Q1).toReal)]
      _ ≤ (1 - Causalean.Stat.tvDist Q0 Q1) / 2 := by
            nlinarith [hBH]
      _ ≤ max (Q0.real {s | r ≤ |T s - theta0|})
            (Q1.real {s | r ≤ |T s - theta1|}) := hprob
  have hset0 :
      {s : S | r ≤ |T s - theta0|} =
        {s : S | r ^ 2 ≤ (T s - theta0) ^ 2} := by
    ext s
    simp only [Set.mem_setOf_eq]
    constructor <;> intro hs <;>
      nlinarith [hr_nonneg, abs_nonneg (T s - theta0), sq_abs (T s - theta0),
        sq_nonneg (T s - theta0)]
  have hset1 :
      {s : S | r ≤ |T s - theta1|} =
        {s : S | r ^ 2 ≤ (T s - theta1) ^ 2} := by
    ext s
    simp only [Set.mem_setOf_eq]
    constructor <;> intro hs <;>
      nlinarith [hr_nonneg, abs_nonneg (T s - theta1), sq_abs (T s - theta1),
        sq_nonneg (T s - theta1)]
  have hmse0 :
      r ^ 2 * Q0.real {s | r ≤ |T s - theta0|}
        ≤ ∫ s, (T s - theta0) ^ 2 ∂Q0 := by
    rw [hset0]
    exact mul_meas_ge_le_integral_of_nonneg
      (μ := Q0) (f := fun s => (T s - theta0) ^ 2)
      (Filter.Eventually.of_forall fun s => sq_nonneg (T s - theta0)) hInt0 (r ^ 2)
  have hmse1 :
      r ^ 2 * Q1.real {s | r ≤ |T s - theta1|}
        ≤ ∫ s, (T s - theta1) ^ 2 ∂Q1 := by
    rw [hset1]
    exact mul_meas_ge_le_integral_of_nonneg
      (μ := Q1) (f := fun s => (T s - theta1) ^ 2)
      (Filter.Eventually.of_forall fun s => sq_nonneg (T s - theta1)) hInt1 (r ^ 2)
  have hmse_max :
      r ^ 2 * max (Q0.real {s | r ≤ |T s - theta0|})
          (Q1.real {s | r ≤ |T s - theta1|})
        ≤ max (∫ s, (T s - theta0) ^ 2 ∂Q0) (∫ s, (T s - theta1) ^ 2 ∂Q1) := by
    by_cases h01 :
        Q0.real {s | r ≤ |T s - theta0|} ≤ Q1.real {s | r ≤ |T s - theta1|}
    · rw [max_eq_right h01]
      exact hmse1.trans (le_max_right _ _)
    · have h10 :
          Q1.real {s | r ≤ |T s - theta1|} ≤ Q0.real {s | r ≤ |T s - theta0|} :=
        le_of_not_ge h01
      rw [max_eq_left h10]
      exact hmse0.trans (le_max_left _ _)
  have hrate :
      r ^ 2 * (Real.exp (-(ENNReal.ofReal K).toReal) / 4)
        ≤ max (∫ s, (T s - theta0) ^ 2 ∂Q0) (∫ s, (T s - theta1) ^ 2 ∂Q1) := by
    calc
      r ^ 2 * (Real.exp (-(ENNReal.ofReal K).toReal) / 4)
          ≤ r ^ 2 * max (Q0.real {s | r ≤ |T s - theta0|})
              (Q1.real {s | r ≤ |T s - theta1|}) :=
            mul_le_mul_of_nonneg_left hprob_floor (sq_nonneg r)
      _ ≤ max (∫ s, (T s - theta0) ^ 2 ∂Q0)
            (∫ s, (T s - theta1) ^ 2 ∂Q1) := hmse_max
  have hcoef :
      (Real.exp (-(ENNReal.ofReal K).toReal) / 32) * (theta1 - theta0) ^ 2
        ≤ r ^ 2 * (Real.exp (-(ENNReal.ofReal K).toReal) / 4) := by
    dsimp [r]
    nlinarith [Real.exp_pos (-(ENNReal.ofReal K).toReal), sq_abs (theta1 - theta0),
      sq_nonneg (theta1 - theta0)]
  exact hcoef.trans hrate

end Causalean.Stat.Minimax
