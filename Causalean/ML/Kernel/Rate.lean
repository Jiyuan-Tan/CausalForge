/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Concentration.UniformDeviation.ERMOracle

/-! # Kernel / L²-ball linear predictors — Rademacher rate

The statistical rate for empirical risk minimization over an `L²`-norm-bounded class of
linear predictors `a ↦ ⟪w, a⟫` (the dual/feature-space view of kernel ridge: the
representer theorem puts the estimator in an RKHS ball).  The theorem
`rademacherComplexity_l2_ball_le` bounds the expected Rademacher complexity of the
`W`-ball class over `Xb`-bounded features by `Xb·W/√n`; `kernel_erm_excess_rate`
combines that bound with the generic ERM oracle inequality
(`erm_oracle_inequality`) to give the `O(1/√n)` excess-risk rate.

Built on FoML's `linear_predictor_l2_bound'` (empirical Rademacher bound for the L²-ball,
lifted here to the expected `rademacherComplexity`).
-/

namespace Causalean.ML

open MeasureTheory ProbabilityTheory Real Causalean.Stat.Concentration

/-- **Rademacher complexity of the L²-ball linear class.**  Over features bounded by `Xb`
in `L²` norm, the expected Rademacher complexity of the class of linear predictors with
weight norm `≤ W` is at most `Xb·W/√n`. -/
theorem rademacherComplexity_l2_ball_le {d n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Xb W : ℝ} (hXb : 0 ≤ Xb) (hW : 0 ≤ W)
    (X : Ω → EuclideanSpace ℝ (Fin d))
    (hXbound : ∀ ω, ‖X ω‖ ≤ Xb) :
    rademacherComplexity n
      (fun w : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W =>
        fun a : EuclideanSpace ℝ (Fin d) => inner ℝ (w : EuclideanSpace ℝ (Fin d)) a)
      μ X ≤ Xb * W / Real.sqrt (n : ℝ) := by
  classical
  haveI : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W) :=
    ⟨⟨0, by simpa [Metric.mem_closedBall, dist_self] using hW⟩⟩
  have hpoint : ∀ ω : Fin n → Ω,
      empiricalRademacherComplexity n
        (fun w : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W =>
          fun a : EuclideanSpace ℝ (Fin d) => inner ℝ (w : EuclideanSpace ℝ (Fin d)) a)
        (X ∘ ω) ≤ Xb * W / Real.sqrt (n : ℝ) := by
    intro ω
    let Y' : Fin n → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) Xb :=
      fun k => ⟨X (ω k), mem_closedBall_zero_iff.mpr (hXbound (ω k))⟩
    simpa [Y', Function.comp_def] using
      (linear_predictor_l2_bound' (d := d) (n := n) (W := W) (X := Xb)
        hXb hW Y' id)
  have hnonneg : ∀ ω : Fin n → Ω,
      0 ≤ empiricalRademacherComplexity n
        (fun w : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W =>
          fun a : EuclideanSpace ℝ (Fin d) => inner ℝ (w : EuclideanSpace ℝ (Fin d)) a)
        (X ∘ ω) := by
    intro ω
    unfold empiricalRademacherComplexity
    refine mul_nonneg ?_ ?_
    · positivity
    · refine Finset.sum_nonneg ?_
      intro σ _
      refine Real.iSup_nonneg ?_
      intro w
      exact abs_nonneg _
  unfold rademacherComplexity
  calc
    ∫ ω : Fin n → Ω,
        empiricalRademacherComplexity n
          (fun w : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W =>
            fun a : EuclideanSpace ℝ (Fin d) => inner ℝ (w : EuclideanSpace ℝ (Fin d)) a)
          (X ∘ ω) ∂(Measure.pi fun _ : Fin n => μ)
        ≤ ∫ _ω : Fin n → Ω, Xb * W / Real.sqrt (n : ℝ) ∂(Measure.pi fun _ : Fin n => μ) := by
      apply MeasureTheory.integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall hnonneg
      · exact integrable_const _
      · exact Filter.Eventually.of_forall hpoint
    _ = Xb * W / Real.sqrt (n : ℝ) := by
      simp

/-- **Kernel ERM excess-risk rate over the L² ball.**  For feature vectors in the closed
`Xb`-ball and linear predictors indexed by the closed `W`-ball, any empirical-risk
minimizer against a comparator `wstar` has excess population risk larger than
`4·Xb·W/√n + 2ε` with probability at most `exp(-ε²tn)`. -/
theorem kernel_erm_excess_rate {d n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Xb W : ℝ} (hXb : 0 ≤ Xb) (hW : 0 ≤ W)
    (X : Ω → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) Xb) (hX : Measurable X)
    {t : ℝ} (ht' : t * (Xb * W) ^ 2 ≤ 1 / 2) {ε : ℝ} (hε : 0 ≤ ε)
    (ŵ : (Fin n → Ω) → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W)
    (wstar : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W)
    (hERM : ∀ ω : Fin n → Ω,
      (n : ℝ)⁻¹ * ∑ k,
          inner ℝ ((ŵ ω) : EuclideanSpace ℝ (Fin d))
            ((X (ω k)) : EuclideanSpace ℝ (Fin d))
        ≤ (n : ℝ)⁻¹ * ∑ k,
          inner ℝ (wstar : EuclideanSpace ℝ (Fin d))
            ((X (ω k)) : EuclideanSpace ℝ (Fin d))) :
    (Measure.pi (fun _ : Fin n => μ)
      (fun ω => 4 * (Xb * W / Real.sqrt (n : ℝ)) + 2 * ε
        < μ[fun ω' => inner ℝ ((ŵ ω) : EuclideanSpace ℝ (Fin d))
          ((X ω') : EuclideanSpace ℝ (Fin d))]
          - μ[fun ω' => inner ℝ (wstar : EuclideanSpace ℝ (Fin d))
            ((X ω') : EuclideanSpace ℝ (Fin d))])).toReal
      ≤ (- ε ^ 2 * t * n).exp := by
  classical
  let 𝒳 := Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) Xb
  let ι := Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W
  let f : ι → 𝒳 → ℝ := fun w a =>
    inner ℝ (w : EuclideanSpace ℝ (Fin d)) (a : EuclideanSpace ℝ (Fin d))
  haveI : Nonempty 𝒳 := ⟨⟨0, by simpa [Metric.mem_closedBall, dist_self, 𝒳] using hXb⟩⟩
  haveI : Nonempty ι := ⟨⟨0, by simpa [Metric.mem_closedBall, dist_self, ι] using hW⟩⟩
  have hb : 0 ≤ Xb * W := mul_nonneg hXb hW
  have hf : ∀ w : ι, Measurable (f w) := by
    intro w
    dsimp [f]
    fun_prop
  have hf' : ∀ w : ι, ∀ a : 𝒳, |f w a| ≤ Xb * W := by
    intro w a
    have hw : ‖(w : EuclideanSpace ℝ (Fin d))‖ ≤ W := by
      simpa [ι] using (mem_closedBall_zero_iff.mp w.2)
    have ha : ‖(a : EuclideanSpace ℝ (Fin d))‖ ≤ Xb := by
      simpa [𝒳] using (mem_closedBall_zero_iff.mp a.2)
    calc
      |f w a| ≤ ‖(w : EuclideanSpace ℝ (Fin d))‖ *
          ‖(a : EuclideanSpace ℝ (Fin d))‖ := by
        dsimp [f]
        exact abs_real_inner_le_norm _ _
      _ ≤ W * Xb := mul_le_mul hw ha (norm_nonneg _) hW
      _ = Xb * W := by ring
  have hf'' : ∀ a : 𝒳, Continuous fun w : ι => f w a := by
    intro a
    dsimp [f]
    fun_prop
  have hRC : rademacherComplexity n f μ X ≤ Xb * W / Real.sqrt (n : ℝ) := by
    have hpoint : ∀ ω : Fin n → Ω,
        empiricalRademacherComplexity n f (X ∘ ω) ≤ Xb * W / Real.sqrt (n : ℝ) := by
      intro ω
      let Y' : Fin n → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) Xb := X ∘ ω
      simpa [f, Y', 𝒳, ι, Function.comp_def] using
        (linear_predictor_l2_bound' (d := d) (n := n) (W := W) (X := Xb)
          hXb hW Y' id)
    have hnonneg : ∀ ω : Fin n → Ω, 0 ≤ empiricalRademacherComplexity n f (X ∘ ω) := by
      intro ω
      unfold empiricalRademacherComplexity
      refine mul_nonneg ?_ ?_
      · positivity
      · refine Finset.sum_nonneg ?_
        intro σ _
        refine Real.iSup_nonneg ?_
        intro w
        exact abs_nonneg _
    unfold rademacherComplexity
    calc
      ∫ ω : Fin n → Ω, empiricalRademacherComplexity n f (X ∘ ω)
          ∂(Measure.pi fun _ : Fin n => μ)
          ≤ ∫ _ω : Fin n → Ω, Xb * W / Real.sqrt (n : ℝ)
              ∂(Measure.pi fun _ : Fin n => μ) := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall hnonneg
        · exact integrable_const _
        · exact Filter.Eventually.of_forall hpoint
      _ = Xb * W / Real.sqrt (n : ℝ) := by
        simp
  have key := erm_oracle_inequality_separable (μ := μ) (n := n) (f := f)
    hf X hX (b := Xb * W) hb hf' hf'' ht' hε ŵ wstar hERM
  refine le_trans ?_ key
  rw [ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
  apply measure_mono
  intro ω hω
  have hthreshold :
      4 • rademacherComplexity n f μ X + 2 * ε
        ≤ 4 * (Xb * W / Real.sqrt (n : ℝ)) + 2 * ε := by
    simp [nsmul_eq_mul]
    nlinarith [hRC]
  exact lt_of_le_of_lt hthreshold hω

end Causalean.ML
