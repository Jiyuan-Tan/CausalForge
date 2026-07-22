/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bounded arm scores for the linear-tilt path

This file packages the proved score facts needed by `linear_tilt_path_valid`.
The score is the optimal projection score from the arm score program, truncated
outside `[0,1]`.  The truncation is equal to the optimizer under the arm
marginal because the arm law is supported on `[0,1]`, while making the score
globally bounded for the reusable KL-density-tilt expansion.
-/

import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.ScoreProgram
import Causalean.Mathlib.InformationTheory.KlDensityTiltExpansion.KLExpansion

namespace CausalSmith.Stat.NeymanRegretMinimax

open MeasureTheory Asymptotics
open scoped BigOperators Topology ENNReal

-- @node: boundedArmScore
/-- Globally bounded version of the optimal arm score.  It agrees a.e. with the
`optScore` under the arm marginal, but is set to zero outside `[0,1]` so the
generic KL tilt substrate can be applied with a pointwise bound on all `ℝ`. -/
noncomputable def boundedArmScore (nu : Measure (ℝ × ℝ)) (a : Fin 2)
    (x : ℝ) : ℝ → ℝ :=
  fun y =>
    if y ∈ Set.Icc (0 : ℝ) 1 then
      Causalean.Stat.MomentProblems.ScoreProgram.optScore
        (armMarginal nu a) x y
    else 0

-- @node: boundedArmScore_measurable
/-- The bounded arm score is measurable. -/
lemma boundedArmScore_measurable (nu : Measure (ℝ × ℝ)) (a : Fin 2) (x : ℝ) :
    Measurable (boundedArmScore nu a x) := by
  unfold boundedArmScore
  refine Measurable.ite measurableSet_Icc ?_ measurable_const
  unfold Causalean.Stat.MomentProblems.ScoreProgram.optScore
  unfold Causalean.Stat.MomentProblems.ResidualQuadratic.ProjectionResidual.projResidual
  fun_prop

-- @node: boundedArmScore_ae_eq_optScore
/-- Under a bounded-outcome law, the truncated score equals the optimal score
almost everywhere for the arm marginal. -/
lemma boundedArmScore_ae_eq_optScore (nu : Measure (ℝ × ℝ)) (hnu : MInt nu)
    (a : Fin 2) (x : ℝ) :
    boundedArmScore nu a x =ᵐ[armMarginal nu a]
      Causalean.Stat.MomentProblems.ScoreProgram.optScore
        (armMarginal nu a) x := by
  filter_upwards [armMarginal_support_Icc nu hnu a] with y hy
  simp [boundedArmScore, hy]

-- @node: boundedArmScore_moments
/-- The bounded arm score satisfies the three score-program moment constraints,
and its squared norm equals the arm score cost. -/
lemma boundedArmScore_moments (nu : Measure (ℝ × ℝ)) (hnu : MTan nu)
    (a : Fin 2) (x : ℝ) :
    (∫ y, boundedArmScore nu a x y ∂(armMarginal nu a) = 0)
      ∧ (∫ y, y * boundedArmScore nu a x y ∂(armMarginal nu a) = 0)
      ∧ (∫ y, y ^ 2 * boundedArmScore nu a x y ∂(armMarginal nu a) = x)
      ∧ (∫ y, (boundedArmScore nu a x y) ^ 2 ∂(armMarginal nu a)
          = armScoreCost nu a x) := by
  let μ := armMarginal nu a
  haveI : IsProbabilityMeasure μ := armMarginal_isProbabilityMeasure nu hnu.toMInt a
  have hfin : Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.FiniteMoment4 μ :=
    armMarginal_finiteMoment4 nu hnu.toMInt a
  have hnd :
      Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.moment μ 1 ^ 2
        < Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.moment μ 2 := by
    simpa [μ] using arm_variance_pos_of_tangent nu hnu a
  have hr_eq :
      armTangentStrength nu a
        = Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.l2ResidualQuadratic μ := by
    simpa [μ] using armTangentStrength_eq_l2ResidualQuadratic nu hnu a
  have hr_l2 :
      0 < Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.l2ResidualQuadratic μ := by
    simpa [← hr_eq] using hnu.tangent a
  have hfeas :=
    Causalean.Stat.MomentProblems.ScoreProgram.optScore_feasible
      μ hfin hnd hr_l2 x
  have hcost :=
    Causalean.Stat.MomentProblems.ScoreProgram.optScore_cost
      μ hfin hnd hr_l2 x
  have hscore_cost :=
    Causalean.Stat.MomentProblems.ScoreProgram.scoreCost_eq
      μ hfin hnd hr_l2 x
  have hae := boundedArmScore_ae_eq_optScore nu hnu.toMInt a x
  constructor
  · calc
      ∫ y, boundedArmScore nu a x y ∂(armMarginal nu a)
          = ∫ y,
              Causalean.Stat.MomentProblems.ScoreProgram.optScore
                (armMarginal nu a) x y ∂(armMarginal nu a) := by
            exact integral_congr_ae hae
      _ = 0 := by simpa [μ] using hfeas.mean_zero
  · constructor
    · calc
        ∫ y, y * boundedArmScore nu a x y ∂(armMarginal nu a)
            = ∫ y,
                y * Causalean.Stat.MomentProblems.ScoreProgram.optScore
                  (armMarginal nu a) x y ∂(armMarginal nu a) := by
              apply integral_congr_ae
              filter_upwards [hae] with y hy
              rw [hy]
        _ = 0 := by simpa [μ] using hfeas.cov_id_zero
    · constructor
      · calc
          ∫ y, y ^ 2 * boundedArmScore nu a x y ∂(armMarginal nu a)
              = ∫ y,
                  y ^ 2
                    * Causalean.Stat.MomentProblems.ScoreProgram.optScore
                      (armMarginal nu a) x y ∂(armMarginal nu a) := by
                apply integral_congr_ae
                filter_upwards [hae] with y hy
                rw [hy]
          _ = x := by simpa [μ] using hfeas.cov_sq
      · calc
          ∫ y, (boundedArmScore nu a x y) ^ 2 ∂(armMarginal nu a)
              = ∫ y,
                  (Causalean.Stat.MomentProblems.ScoreProgram.optScore
                    (armMarginal nu a) x y) ^ 2 ∂(armMarginal nu a) := by
                apply integral_congr_ae
                filter_upwards [hae] with y hy
                rw [hy]
          _ = armScoreCost nu a x := by
                rw [hcost, ← hscore_cost]
                rfl

-- @node: boundedArmScore_bounded
/-- The bounded arm score has a global pointwise absolute bound. -/
lemma boundedArmScore_bounded (nu : Measure (ℝ × ℝ)) (a : Fin 2) (x : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, |boundedArmScore nu a x y| ≤ C := by
  rcases projResidual_bounded_Icc (armMarginal nu a) with ⟨C, hC⟩
  let r := Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.l2ResidualQuadratic
    (armMarginal nu a)
  refine ⟨|x / r| * |C|, by positivity, ?_⟩
  intro y
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · have hCe :
        |Causalean.Stat.MomentProblems.ResidualQuadratic.ProjectionResidual.projResidual
          (armMarginal nu a) y| ≤ C := hC y hy
    have hCe_abs :
        |Causalean.Stat.MomentProblems.ResidualQuadratic.ProjectionResidual.projResidual
          (armMarginal nu a) y| ≤ |C| := le_trans hCe (le_abs_self C)
    calc
      |boundedArmScore nu a x y|
          = |x / r|
              * |Causalean.Stat.MomentProblems.ResidualQuadratic.ProjectionResidual.projResidual
                  (armMarginal nu a) y| := by
            simp [boundedArmScore, hy,
              Causalean.Stat.MomentProblems.ScoreProgram.optScore,
              r, abs_mul]
      _ ≤ |x / r| * |C| :=
            mul_le_mul_of_nonneg_left hCe_abs (abs_nonneg _)
  · have hnonneg : 0 ≤ |x / r| * |C| := by positivity
    simpa [boundedArmScore, hy, r] using hnonneg

-- @node: integral_tiltMeasure_eq_integral_mul
/-- Integral under the linear density tilt equals the base integral weighted by
the linear density whenever the density is nonnegative. -/
lemma integral_tiltMeasure_eq_integral_mul {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {s g : ℝ → ℝ} {C h : ℝ}
    (hs_meas : Measurable s) (hsC : ∀ y, |s y| ≤ C) (hh : |h| * C ≤ 1) :
    ∫ y, g y ∂(Causalean.Mathlib.InformationTheory.KlDensityTiltExpansion.tiltMeasure μ s h)
      = ∫ y, (1 + h * s y) * g y ∂μ := by
  have hf_meas : Measurable (fun y : ℝ => ENNReal.ofReal (1 + h * s y)) := by
    fun_prop
  have hf_lt_top : ∀ᵐ y ∂μ, ENNReal.ofReal (1 + h * s y) < ∞ := by
    simp
  calc
    ∫ y, g y ∂(Causalean.Mathlib.InformationTheory.KlDensityTiltExpansion.tiltMeasure μ s h)
        = ∫ y, (ENNReal.ofReal (1 + h * s y)).toReal • g y ∂μ := by
          simpa [Causalean.Mathlib.InformationTheory.KlDensityTiltExpansion.tiltMeasure] using
            (integral_withDensity_eq_integral_toReal_smul hf_meas hf_lt_top g)
    _ = ∫ y, (1 + h * s y) * g y ∂μ := by
      apply integral_congr_ae
      filter_upwards with y
      simp [ENNReal.toReal_ofReal
        (Causalean.Mathlib.InformationTheory.KlDensityTiltExpansion.tiltDensity_nonneg hsC hh y),
        smul_eq_mul]

-- @node: tiltMeasure_integral_preserve_of_orthogonal
/-- If `g` is orthogonal to the score, its integral is preserved by the tilt. -/
lemma tiltMeasure_integral_preserve_of_orthogonal {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {s g : ℝ → ℝ} {C h : ℝ}
    (hs_meas : Measurable s) (hsC : ∀ y, |s y| ≤ C) (hh : |h| * C ≤ 1)
    (hg_int : Integrable g μ) (hgs_int : Integrable (fun y => g y * s y) μ)
    (hgs_zero : ∫ y, g y * s y ∂μ = 0) :
    ∫ y, g y ∂(Causalean.Mathlib.InformationTheory.KlDensityTiltExpansion.tiltMeasure μ s h)
      = ∫ y, g y ∂μ := by
  rw [integral_tiltMeasure_eq_integral_mul hs_meas hsC hh]
  calc
    ∫ y, (1 + h * s y) * g y ∂μ
        = ∫ y, g y + h * (g y * s y) ∂μ := by
          apply integral_congr_ae
          filter_upwards with y
          ring
    _ = ∫ y, g y ∂μ + ∫ y, h * (g y * s y) ∂μ := by
          rw [integral_add hg_int (hgs_int.const_mul h)]
    _ = ∫ y, g y ∂μ := by
          rw [integral_const_mul, hgs_zero, mul_zero, add_zero]

-- @node: tiltMeasure_integral_shift_of_score_moment
/-- If `∫ g*s = x`, the tilt shifts the integral of `g` by `h*x`. -/
lemma tiltMeasure_integral_shift_of_score_moment {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {s g : ℝ → ℝ} {C h x : ℝ}
    (hs_meas : Measurable s) (hsC : ∀ y, |s y| ≤ C) (hh : |h| * C ≤ 1)
    (hg_int : Integrable g μ) (hgs_int : Integrable (fun y => g y * s y) μ)
    (hgs_eq : ∫ y, g y * s y ∂μ = x) :
    ∫ y, g y ∂(Causalean.Mathlib.InformationTheory.KlDensityTiltExpansion.tiltMeasure μ s h)
      = ∫ y, g y ∂μ + h * x := by
  rw [integral_tiltMeasure_eq_integral_mul hs_meas hsC hh]
  calc
    ∫ y, (1 + h * s y) * g y ∂μ
        = ∫ y, g y + h * (g y * s y) ∂μ := by
          apply integral_congr_ae
          filter_upwards with y
          ring
    _ = ∫ y, g y ∂μ + ∫ y, h * (g y * s y) ∂μ := by
          rw [integral_add hg_int (hgs_int.const_mul h)]
    _ = ∫ y, g y ∂μ + h * x := by
          rw [integral_const_mul, hgs_eq]

end CausalSmith.Stat.NeymanRegretMinimax
