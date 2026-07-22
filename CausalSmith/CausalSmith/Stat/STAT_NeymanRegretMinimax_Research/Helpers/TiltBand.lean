/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Band continuity for bounded linear tilts
-/

import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.Tilt

namespace CausalSmith.Stat.NeymanRegretMinimax

open MeasureTheory Asymptotics
open scoped BigOperators Topology ENNReal

private lemma armMarginal_isProbabilityMeasure_of_isProbabilityMeasure
    (nu : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu] (a : Fin 2) :
    IsProbabilityMeasure (armMarginal nu a) := by
  by_cases ha : a = 0
  · rw [armMarginal, if_pos ha]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  · rw [armMarginal, if_neg ha]
    exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable

private lemma armMarginal_support_Icc_of_bounded
    (nu : Measure (ℝ × ℝ)) (hnu : BoundedOutcomes nu) (a : Fin 2) :
    ∀ᵐ y ∂(armMarginal nu a), y ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases ha : a = 0
  · have hs : ∀ᵐ y ∂(Measure.map Prod.fst nu), y ∈ Set.Icc (0 : ℝ) 1 := by
      refine (MeasureTheory.ae_map_iff measurable_fst.aemeasurable measurableSet_Icc).2 ?_
      filter_upwards [hnu] with p hp
      exact hp.1
    simpa [armMarginal, ha] using hs
  · have ha1 : a = 1 := by
      fin_cases a <;> simp at ha ⊢
    have hs : ∀ᵐ y ∂(Measure.map Prod.snd nu), y ∈ Set.Icc (0 : ℝ) 1 := by
      refine (MeasureTheory.ae_map_iff measurable_snd.aemeasurable measurableSet_Icc).2 ?_
      filter_upwards [hnu] with p hp
      exact hp.2
    simpa [armMarginal, ha1] using hs

private lemma armMarginal_integrable_pow_of_bounded
    (nu : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu] (hnu : BoundedOutcomes nu)
    (a : Fin 2) (k : ℕ) :
    Integrable (fun y : ℝ => y ^ k) (armMarginal nu a) := by
  haveI : IsProbabilityMeasure (armMarginal nu a) :=
    armMarginal_isProbabilityMeasure_of_isProbabilityMeasure nu a
  refine Integrable.of_bound ((continuous_pow k).aestronglyMeasurable) 1 ?_
  filter_upwards [armMarginal_support_Icc_of_bounded nu hnu a] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hy.1 k)]
  exact pow_le_one₀ hy.1 hy.2

private lemma armMarginal_finiteMoment4_of_bounded
    (nu : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu] (hnu : BoundedOutcomes nu)
    (a : Fin 2) :
    Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.FiniteMoment4 (armMarginal nu a) := by
  refine ⟨?_, armMarginal_integrable_pow_of_bounded nu hnu a 2,
    armMarginal_integrable_pow_of_bounded nu hnu a 3,
    armMarginal_integrable_pow_of_bounded nu hnu a 4⟩
  simpa using armMarginal_integrable_pow_of_bounded nu hnu a 1

private lemma armTangentStrength_eq_l2ResidualQuadratic_of_variance_pos
    (nu : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu] (hbounded : BoundedOutcomes nu)
    (a : Fin 2)
    (hnd : Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.moment (armMarginal nu a) 1 ^ 2
      < Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.moment (armMarginal nu a) 2) :
    armTangentStrength nu a =
      Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.l2ResidualQuadratic (armMarginal nu a) := by
  let μ := armMarginal nu a
  haveI : IsProbabilityMeasure μ := armMarginal_isProbabilityMeasure_of_isProbabilityMeasure nu a
  have hfin : Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.FiniteMoment4 μ :=
    armMarginal_finiteMoment4_of_bounded nu hbounded a
  rw [armTangentStrength]
  apply le_antisymm
  · have hbdd :
        BddBelow
          (Set.range fun b : ℝ × ℝ => ∫ y, (y ^ 2 - b.1 - b.2 * y) ^ 2 ∂μ) := by
      exact ⟨Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.l2ResidualQuadratic μ, by
        rintro z ⟨b, rfl⟩
        exact Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.l2ResidualQuadratic_le
          μ hfin hnd b.1 b.2⟩
    calc
      (⨅ b : ℝ × ℝ,
          ∫ y, (y ^ 2 - b.1 - b.2 * y) ^ 2 ∂armMarginal nu a)
          = (⨅ b : ℝ × ℝ, ∫ y, (y ^ 2 - b.1 - b.2 * y) ^ 2 ∂μ) := by
            rfl
      _ ≤ ∫ y,
            (y ^ 2 - Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.optIntercept μ
              - Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.optSlope μ * y) ^ 2 ∂μ :=
            ciInf_le hbdd
              (Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.optIntercept μ,
                Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.optSlope μ)
      _ = Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.l2ResidualQuadratic μ := by
            exact Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.residualQuad_opt_eq μ hfin hnd
  · refine le_ciInf ?_
    intro b
    change Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.l2ResidualQuadratic μ ≤
      ∫ y, (y ^ 2 - b.1 - b.2 * y) ^ 2 ∂armMarginal nu a
    simpa [μ] using Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.l2ResidualQuadratic_le
      μ hfin hnd b.1 b.2

private lemma linearTiltPath_score_mul_integrable_pow
    (nu : Measure (ℝ × ℝ)) (hnu : MTan nu) {s : Fin 2 → ℝ → ℝ}
    (hs : ∀ a : Fin 2,
        Measurable (s a)
        ∧ (∃ C : ℝ, ∀ y ∈ Set.Icc (0 : ℝ) 1, |s a y| ≤ C))
    (a : Fin 2) (k : ℕ) :
    Integrable (fun y : ℝ => y ^ k * s a y) (armMarginal nu a) := by
  rcases (hs a).2 with ⟨C, hC⟩
  let B : ℝ := |C|
  have hpow : Integrable (fun y : ℝ => y ^ k) (armMarginal nu a) :=
    armMarginal_integrable_pow nu hnu.toMInt a k
  have hs_meas : AEStronglyMeasurable (s a) (armMarginal nu a) :=
    (hs a).1.aestronglyMeasurable
  have hs_bound : ∀ᵐ y ∂(armMarginal nu a), ‖s a y‖ ≤ B := by
    filter_upwards [armMarginal_support_Icc nu hnu.toMInt a] with y hy
    simpa [Real.norm_eq_abs, B] using le_trans (hC y hy) (le_abs_self C)
  simpa [mul_comm] using hpow.bdd_mul hs_meas hs_bound

private lemma linearTiltPath_arm_moment_eventually_eq_affine
    (nu : Measure (ℝ × ℝ)) (hnu : MTan nu) (u : ℝ × ℝ)
    (p : ℝ → Measure (ℝ × ℝ)) {s : Fin 2 → ℝ → ℝ} {η : ℝ}
    (hηpos : 0 < η)
    (hs : ∀ a : Fin 2,
        Measurable (s a)
        ∧ (∫ y, s a y ∂(armMarginal nu a) = 0)
        ∧ (∫ y, y * s a y ∂(armMarginal nu a) = 0)
        ∧ (∫ y, y ^ 2 * s a y ∂(armMarginal nu a) = (if a = 0 then u.1 else u.2))
        ∧ (∃ C : ℝ, ∀ y ∈ Set.Icc (0 : ℝ) 1, |s a y| ≤ C))
    (hmargin : ∀ h : ℝ, |h| ≤ η → ∀ a : Fin 2,
        armMarginal (p h) a =
          (armMarginal nu a).withDensity (fun y => ENNReal.ofReal (1 + h * s a y)))
    (a : Fin 2) (k : ℕ) :
    (fun h : ℝ =>
        ∫ y, y ^ k ∂(armMarginal (p h) a))
      =ᶠ[𝓝 (0 : ℝ)]
        (fun h : ℝ =>
          ∫ y, y ^ k ∂(armMarginal nu a)
            + h * ∫ y, y ^ k * s a y ∂(armMarginal nu a)) := by
  rcases (hs a).2.2.2.2 with ⟨C, hC⟩
  let B : ℝ := |C|
  have hC' : ∀ y ∈ Set.Icc (0 : ℝ) 1, |s a y| ≤ B := fun y hy =>
    le_trans (hC y hy) (le_abs_self C)
  have hBnonneg : 0 ≤ B := abs_nonneg C
  have hsmall_ev : ∀ᶠ h in 𝓝 (0 : ℝ), |h| ≤ η ∧ |h| * B ≤ 1 := by
    have hη_ev : ∀ᶠ h in 𝓝 (0 : ℝ), |h| ≤ η := by
      refine Metric.eventually_nhds_iff.2 ⟨η, hηpos, ?_⟩
      intro h hh
      exact le_of_lt (by simpa [Real.dist_eq, sub_zero] using hh)
    have hdenpos : 0 < B + 1 := by linarith
    have hδpos : 0 < 1 / (B + 1) := by positivity
    have hB_ev : ∀ᶠ h in 𝓝 (0 : ℝ), |h| * B ≤ 1 := by
      refine Metric.eventually_nhds_iff.2 ⟨1 / (B + 1), hδpos, ?_⟩
      intro h hh
      have habs : |h| ≤ 1 / (B + 1) := le_of_lt (by
        simpa [Real.dist_eq, sub_zero] using hh)
      have hBle : B ≤ B + 1 := by linarith
      have hmul := mul_le_mul habs hBle hBnonneg (by positivity : 0 ≤ 1 / (B + 1))
      have hδmul : (1 / (B + 1)) * (B + 1) = 1 := by
        field_simp [ne_of_gt hdenpos]
      linarith
    exact hη_ev.and hB_ev
  filter_upwards [hsmall_ev] with h hh
  haveI : IsProbabilityMeasure (armMarginal nu a) :=
    armMarginal_isProbabilityMeasure nu hnu.toMInt a
  have hf_meas :
      Measurable (fun y : ℝ => ENNReal.ofReal (1 + h * s a y)) := by
    have hreal : Measurable (fun y : ℝ => 1 + h * s a y) := by
      exact measurable_const.add ((hs a).1.const_mul h)
    exact ENNReal.measurable_ofReal.comp hreal
  have hf_lt_top :
      ∀ᵐ y ∂(armMarginal nu a), ENNReal.ofReal (1 + h * s a y) < ∞ := by
    simp
  have hg_int : Integrable (fun y : ℝ => y ^ k) (armMarginal nu a) :=
    armMarginal_integrable_pow nu hnu.toMInt a k
  have hgs_int : Integrable (fun y : ℝ => y ^ k * s a y) (armMarginal nu a) :=
    linearTiltPath_score_mul_integrable_pow nu hnu (by
      intro a
      exact ⟨(hs a).1, (hs a).2.2.2.2⟩) a k
  have hnonneg_ae : ∀ᵐ y ∂(armMarginal nu a), 0 ≤ 1 + h * s a y := by
    filter_upwards [armMarginal_support_Icc nu hnu.toMInt a] with y hy
    have h_abs : |h * s a y| ≤ |h| * B := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hC' y hy) (abs_nonneg h)
    have h_lower : -1 ≤ h * s a y := by
      have h_bound : -(|h| * B) ≤ h * s a y := by
        have h_neg : -(|h| * B) ≤ -|h * s a y| := by
          rw [neg_le_neg_iff]
          exact h_abs
        exact le_trans h_neg (neg_abs_le _)
      linarith
    linarith
  calc
    ∫ y, y ^ k ∂(armMarginal (p h) a)
        = ∫ y, y ^ k ∂((armMarginal nu a).withDensity
            (fun y => ENNReal.ofReal (1 + h * s a y))) := by
          rw [hmargin h hh.1 a]
    _ = ∫ y, (ENNReal.ofReal (1 + h * s a y)).toReal • (y ^ k) ∂(armMarginal nu a) := by
          simpa using
            (integral_withDensity_eq_integral_toReal_smul hf_meas hf_lt_top
              (fun y : ℝ => y ^ k))
    _ = ∫ y, (1 + h * s a y) * y ^ k ∂(armMarginal nu a) := by
          apply integral_congr_ae
          filter_upwards [hnonneg_ae] with y hy
          simp [ENNReal.toReal_ofReal hy, smul_eq_mul]
    _ = ∫ y, y ^ k + h * (y ^ k * s a y) ∂(armMarginal nu a) := by
          apply integral_congr_ae
          filter_upwards with y
          ring
    _ = ∫ y, y ^ k ∂(armMarginal nu a)
          + ∫ y, h * (y ^ k * s a y) ∂(armMarginal nu a) := by
          rw [integral_add hg_int (hgs_int.const_mul h)]
    _ = ∫ y, y ^ k ∂(armMarginal nu a)
          + h * ∫ y, y ^ k * s a y ∂(armMarginal nu a) := by
          rw [integral_const_mul]

private lemma linearTiltPath_arm_moment_continuousAt
    (nu : Measure (ℝ × ℝ)) (hnu : MTan nu) (u : ℝ × ℝ)
    (p : ℝ → Measure (ℝ × ℝ)) (hlin : IsLinearTiltPath nu u p)
    (a : Fin 2) (k : ℕ) :
    ContinuousAt (fun h : ℝ =>
      Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.moment (armMarginal (p h) a) k) 0 := by
  rcases hlin with ⟨s, η, hηpos, hs, hmargin⟩
  have hev :
      (fun h : ℝ =>
          Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.moment (armMarginal (p h) a) k)
        =ᶠ[𝓝 (0 : ℝ)]
          (fun h : ℝ =>
            ∫ y, y ^ k ∂(armMarginal nu a)
              + h * ∫ y, y ^ k * s a y ∂(armMarginal nu a)) := by
    simpa [Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.moment] using
      (linearTiltPath_arm_moment_eventually_eq_affine nu hnu u p
        hηpos hs hmargin a k)
  have haff :
      ContinuousAt
        (fun h : ℝ =>
          ∫ y, y ^ k ∂(armMarginal nu a)
            + h * ∫ y, y ^ k * s a y ∂(armMarginal nu a)) 0 := by
    exact (continuousAt_const :
        ContinuousAt (fun _ : ℝ => ∫ y, y ^ k ∂(armMarginal nu a)) 0).add
      (continuousAt_id.mul
        (continuousAt_const :
          ContinuousAt
            (fun _ : ℝ => ∫ y, y ^ k * s a y ∂(armMarginal nu a)) 0))
  refine haff.congr ?_
  exact hev.symm

private lemma linearTiltPath_l2ResidualQuadratic_continuousAt
    (nu : Measure (ℝ × ℝ)) (hnu : MTan nu) (u : ℝ × ℝ)
    (p : ℝ → Measure (ℝ × ℝ)) (hlin : IsLinearTiltPath nu u p)
    (hp : IsLocalPath nu u p)
    (a : Fin 2) :
    ContinuousAt
      (fun h : ℝ =>
        Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.l2ResidualQuadratic
          (armMarginal (p h) a)) 0 := by
  let m1 : ℝ → ℝ := fun h =>
    Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.moment (armMarginal (p h) a) 1
  let m2 : ℝ → ℝ := fun h =>
    Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.moment (armMarginal (p h) a) 2
  let m3 : ℝ → ℝ := fun h =>
    Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.moment (armMarginal (p h) a) 3
  let m4 : ℝ → ℝ := fun h =>
    Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.moment (armMarginal (p h) a) 4
  have hm1 : ContinuousAt m1 0 :=
    linearTiltPath_arm_moment_continuousAt nu hnu u p hlin a 1
  have hm2 : ContinuousAt m2 0 :=
    linearTiltPath_arm_moment_continuousAt nu hnu u p hlin a 2
  have hm3 : ContinuousAt m3 0 :=
    linearTiltPath_arm_moment_continuousAt nu hnu u p hlin a 3
  have hm4 : ContinuousAt m4 0 :=
    linearTiltPath_arm_moment_continuousAt nu hnu u p hlin a 4
  have hden_ne : m1 0 ^ 2 - m2 0 ≠ 0 := by
    have hvar : m1 0 ^ 2 < m2 0 := by
      simpa [m1, m2, hp.1] using arm_variance_pos_of_tangent nu hnu a
    nlinarith
  unfold Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.l2ResidualQuadratic
  unfold Causalean.Stat.MomentProblems.ResidualQuadratic.MomentAlgebra.momentResidual
  change ContinuousAt
    (fun h : ℝ =>
      (m1 h ^ 2 * m4 h - 2 * m1 h * m2 h * m3 h + m2 h ^ 3
          - m2 h * m4 h + m3 h ^ 2) / (m1 h ^ 2 - m2 h)) 0
  have hnum :
      ContinuousAt
        (fun h : ℝ =>
          m1 h ^ 2 * m4 h - 2 * m1 h * m2 h * m3 h + m2 h ^ 3
            - m2 h * m4 h + m3 h ^ 2) 0 := by
    fun_prop
  have hden : ContinuousAt (fun h : ℝ => m1 h ^ 2 - m2 h) 0 := by
    fun_prop
  exact hnum.div hden hden_ne

private lemma linearTiltPath_rootSecondMoment_continuousAt
    (nu : Measure (ℝ × ℝ)) (hnu : MTan nu) (u : ℝ × ℝ)
    (p : ℝ → Measure (ℝ × ℝ)) (hlin : IsLinearTiltPath nu u p)
    (a : Fin 2) :
    ContinuousAt (fun h : ℝ => rootSecondMoment (p h) a) 0 := by
  have hm2 :
      ContinuousAt
        (fun h : ℝ =>
          Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.moment (armMarginal (p h) a) 2) 0 :=
    linearTiltPath_arm_moment_continuousAt nu hnu u p hlin a 2
  simpa [rootSecondMoment, Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.moment] using
    Real.continuous_sqrt.continuousAt.comp hm2

private lemma linearTiltPath_armTangentStrength_continuousAt
    (nu : Measure (ℝ × ℝ)) (hnu : MTan nu) (u : ℝ × ℝ)
    (p : ℝ → Measure (ℝ × ℝ)) (hlin : IsLinearTiltPath nu u p)
    (hp : IsLocalPath nu u p) (a : Fin 2) :
    ContinuousAt (fun h : ℝ => armTangentStrength (p h) a) 0 := by
  let μh : ℝ → Measure ℝ := fun h => armMarginal (p h) a
  let m1 : ℝ → ℝ := fun h =>
    Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.moment (μh h) 1
  let m2 : ℝ → ℝ := fun h =>
    Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.moment (μh h) 2
  have hm1 : ContinuousAt m1 0 :=
    linearTiltPath_arm_moment_continuousAt nu hnu u p hlin a 1
  have hm2 : ContinuousAt m2 0 :=
    linearTiltPath_arm_moment_continuousAt nu hnu u p hlin a 2
  have hvar_cont : ContinuousAt (fun h : ℝ => m2 h - m1 h ^ 2) 0 :=
    hm2.sub (hm1.pow 2)
  have hvar0 : 0 < m2 0 - m1 0 ^ 2 := by
    have hvar : m1 0 ^ 2 < m2 0 := by
      simpa [μh, m1, m2, hp.1] using arm_variance_pos_of_tangent nu hnu a
    linarith
  have hvar_ev :
      ∀ᶠ h in 𝓝 (0 : ℝ), 0 < m2 h - m1 h ^ 2 :=
    hvar_cont.eventually (isOpen_Ioi.mem_nhds hvar0)
  have heq_ev :
      (fun h : ℝ => armTangentStrength (p h) a)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun h : ℝ =>
        Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.l2ResidualQuadratic (μh h)) := by
    filter_upwards [hvar_ev] with h hvarh
    haveI : IsProbabilityMeasure (p h) := hp.2.1 h
    have hnd : m1 h ^ 2 < m2 h := by linarith
    simpa [μh, m1, m2] using
      armTangentStrength_eq_l2ResidualQuadratic_of_variance_pos
        (p h) (hp.2.2.1 h) a hnd
  have hl2 :
      ContinuousAt
        (fun h : ℝ =>
          Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.l2ResidualQuadratic (μh h)) 0 := by
    simpa [μh] using linearTiltPath_l2ResidualQuadratic_continuousAt nu hnu u p hlin hp a
  refine hl2.congr ?_
  exact heq_ev.symm

-- @node: LinearTiltBandFunctionalContinuity
/-- Continuity, at the base point of a linear tilt, of the two scalar functionals
that define membership in a regular band.  The paper derives this from bounded
linear tilts by continuity of bounded moments and of the finite-dimensional
projection residual. -/
def LinearTiltBandFunctionalContinuity (p : ℝ → Measure (ℝ × ℝ)) : Prop :=
  ∀ a : Fin 2,
    ContinuousAt (fun h : ℝ => rootSecondMoment (p h) a) 0
      ∧ ContinuousAt (fun h : ℝ => armTangentStrength (p h) a) 0

-- @node: lem:band-continuity-for-linear-tilts
/-- For `nu` in the strict interior of the regular band, a fixed
finite-information linear tilt `nu^(u,h)` stays inside the closed band
`M(underline_m, overline_m, underline_r)` for all `|h| ≤ η`.  (The strict-interior
premise is the `M^circ` hypothesis carried by the global converse, threaded down.)
The band-radius domain hypotheses `0 < um`, `um < om`, `om ≤ 1` (the note's
`0 < underline_m < overline_m ≤ 1`) are required to conclude `MBand` (whose
`umPos`/`umLeOm`/`omLeOne` well-formedness fields pin the constants' space); they
are threaded down from the global converse's `hum`/`humom`/`hom`.

The band-functional continuity `LinearTiltBandFunctionalContinuity p` is NOT a
threaded premise: the note DERIVES it from the linear-tilt construction (each arm
moment up to order four is an integral of a bounded polynomial against the tilted
law `(1 + h s_a) dnu_a`, hence continuous in `h`, and the finite-dimensional
projection residual stays nonsingular near `h = 0`).  It is obtained in-proof
from `hlin`/`hp`. -/
lemma band_continuity_for_linear_tilts (um om ur : ℝ)
    -- @realizes underline_m, overline_m(joint (0,1]²: conjunction hum ∧ humom ∧ hom = 0<um<om≤1)
    (hum : 0 < um) -- @realizes underline_m(space (0,1]: lower end 0 < um)
    (humom : um < om) -- @realizes underline_m(um≤1 via um≤om≤1) @realizes overline_m(0<om via 0<um)
    (hom : om ≤ 1) -- @realizes overline_m(space (0,1]: upper end om ≤ 1)
    (nu : Measure (ℝ × ℝ))
    (hnu : MTan nu)
    (hstrict : ∀ a : Fin 2, um < rootSecondMoment nu a ∧ rootSecondMoment nu a < om
      ∧ ur < armTangentStrength nu a)
    (u : ℝ × ℝ) (p : ℝ → Measure (ℝ × ℝ))
    (hlin : IsLinearTiltPath nu u p) (hp : IsLocalPath nu u p) :
    ∃ η : ℝ, 0 < η ∧ ∀ h : ℝ, |h| ≤ η → MBand um om ur (p h) := by
  -- Band-functional continuity is DERIVED from the linear-tilt construction, not
  -- assumed: bounded-polynomial moments (order ≤ 4) and the finite-dimensional
  -- projection residual are continuous in `h` along `hlin`.
  have hcont : LinearTiltBandFunctionalContinuity p := by
    intro a
    exact ⟨linearTiltPath_rootSecondMoment_continuousAt nu hnu u p hlin a,
      linearTiltPath_armTangentStrength_continuousAt nu hnu u p hlin hp a⟩
  have hroot0 : rootSecondMoment (p 0) 0 ∈ Set.Ioo um om := by
    simpa [hp.1] using
      (show rootSecondMoment nu 0 ∈ Set.Ioo um om from
        ⟨(hstrict 0).1, (hstrict 0).2.1⟩)
  have hroot1 : rootSecondMoment (p 0) 1 ∈ Set.Ioo um om := by
    simpa [hp.1] using
      (show rootSecondMoment nu 1 ∈ Set.Ioo um om from
        ⟨(hstrict 1).1, (hstrict 1).2.1⟩)
  have htangent0 : max (0 : ℝ) ur < armTangentStrength (p 0) 0 := by
    simpa [hp.1] using
      (max_lt (hnu.tangent 0) (hstrict 0).2.2)
  have htangent1 : max (0 : ℝ) ur < armTangentStrength (p 0) 1 := by
    simpa [hp.1] using
      (max_lt (hnu.tangent 1) (hstrict 1).2.2)
  have hroot0_ev :
      ∀ᶠ h in 𝓝 (0 : ℝ), rootSecondMoment (p h) 0 ∈ Set.Ioo um om :=
    (hcont 0).1.eventually (isOpen_Ioo.mem_nhds hroot0)
  have hroot1_ev :
      ∀ᶠ h in 𝓝 (0 : ℝ), rootSecondMoment (p h) 1 ∈ Set.Ioo um om :=
    (hcont 1).1.eventually (isOpen_Ioo.mem_nhds hroot1)
  have htangent0_ev :
      ∀ᶠ h in 𝓝 (0 : ℝ), max (0 : ℝ) ur < armTangentStrength (p h) 0 :=
    (hcont 0).2.eventually (isOpen_Ioi.mem_nhds htangent0)
  have htangent1_ev :
      ∀ᶠ h in 𝓝 (0 : ℝ), max (0 : ℝ) ur < armTangentStrength (p h) 1 :=
    (hcont 1).2.eventually (isOpen_Ioi.mem_nhds htangent1)
  have hband_ev :
      ∀ᶠ h in 𝓝 (0 : ℝ),
        rootSecondMoment (p h) 0 ∈ Set.Ioo um om
          ∧ rootSecondMoment (p h) 1 ∈ Set.Ioo um om
          ∧ max (0 : ℝ) ur < armTangentStrength (p h) 0
          ∧ max (0 : ℝ) ur < armTangentStrength (p h) 1 :=
    hroot0_ev.and (hroot1_ev.and (htangent0_ev.and htangent1_ev))
  rcases Metric.eventually_nhds_iff_ball.mp hband_ev with ⟨δ, hδpos, hδ⟩
  refine ⟨δ / 2, half_pos hδpos, ?_⟩
  intro h hh
  have hδ' : dist h (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero]
    exact lt_of_le_of_lt hh (half_lt_self hδpos)
  rcases hδ h hδ' with ⟨hroot0h, hroot1h, htangent0h, htangent1h⟩
  refine
    { toMTan :=
        { toMInt :=
            { isLaw := hp.2.1 h
              bounded := hp.2.2.1 h
              interiorMoments := ?_ }
          tangent := ?_ }
      umPos := hum
      umLeOm := le_of_lt humom
      omLeOne := hom
      band := ?_
      tangentBand := ?_ }
  · intro a
    fin_cases a
    · exact lt_trans hum hroot0h.1
    · exact lt_trans hum hroot1h.1
  · intro a
    fin_cases a
    · exact lt_of_le_of_lt (le_max_left (0 : ℝ) ur) htangent0h
    · exact lt_of_le_of_lt (le_max_left (0 : ℝ) ur) htangent1h
  · intro a
    fin_cases a
    · exact ⟨le_of_lt hroot0h.1, le_of_lt hroot0h.2⟩
    · exact ⟨le_of_lt hroot1h.1, le_of_lt hroot1h.2⟩
  · intro a
    fin_cases a
    · exact le_trans (le_max_right (0 : ℝ) ur) (le_of_lt htangent0h)
    · exact le_trans (le_max_right (0 : ℝ) ur) (le_of_lt htangent1h)

end CausalSmith.Stat.NeymanRegretMinimax
