/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Arm-score substrate bridges

Bookkeeping facts connecting the local arm-marginal notation used by the
Neyman-regret scaffold to the reusable Causalean constrained quadratic score
program.
-/

import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.Rayleigh
import Causalean.Stat.Nonparametric.MomentProblems.ScoreProgram.ScoreProgram
import Mathlib.Probability.Moments.Variance

namespace CausalSmith.Stat.NeymanRegretMinimax

open MeasureTheory
open scoped ProbabilityTheory
open Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge (FiniteMoment4 moment l2ResidualQuadratic)

-- @node: armMarginal_isProbabilityMeasure
/-- Arm marginals of an `MInt` law are probability measures. -/
lemma armMarginal_isProbabilityMeasure (nu : Measure (ℝ × ℝ)) (hnu : MInt nu)
    (a : Fin 2) : IsProbabilityMeasure (armMarginal nu a) := by
  haveI : IsProbabilityMeasure nu := hnu.isLaw
  by_cases ha : a = 0
  · rw [armMarginal, if_pos ha]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  · rw [armMarginal, if_neg ha]
    exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable

-- @node: armMarginal_support_Icc
/-- Arm marginals inherit `[0,1]` support from the joint bounded-outcomes law. -/
lemma armMarginal_support_Icc (nu : Measure (ℝ × ℝ)) (hnu : MInt nu) (a : Fin 2) :
    ∀ᵐ y ∂(armMarginal nu a), y ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases ha : a = 0
  · have hs : ∀ᵐ y ∂(Measure.map Prod.fst nu), y ∈ Set.Icc (0 : ℝ) 1 := by
      refine (MeasureTheory.ae_map_iff measurable_fst.aemeasurable measurableSet_Icc).2 ?_
      filter_upwards [hnu.bounded] with p hp
      exact hp.1
    simpa [armMarginal, ha] using hs
  · have ha1 : a = 1 := by
      fin_cases a <;> simp at ha ⊢
    have hs : ∀ᵐ y ∂(Measure.map Prod.snd nu), y ∈ Set.Icc (0 : ℝ) 1 := by
      refine (MeasureTheory.ae_map_iff measurable_snd.aemeasurable measurableSet_Icc).2 ?_
      filter_upwards [hnu.bounded] with p hp
      exact hp.2
    simpa [armMarginal, ha1] using hs

-- @node: armMarginal_integrable_pow
/-- Bounded arm support gives integrability of every nonnegative integer power. -/
lemma armMarginal_integrable_pow (nu : Measure (ℝ × ℝ)) (hnu : MInt nu) (a : Fin 2)
    (k : ℕ) : Integrable (fun y : ℝ => y ^ k) (armMarginal nu a) := by
  haveI : IsProbabilityMeasure (armMarginal nu a) :=
    armMarginal_isProbabilityMeasure nu hnu a
  refine Integrable.of_bound ((continuous_pow k).aestronglyMeasurable) 1 ?_
  filter_upwards [armMarginal_support_Icc nu hnu a] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hy.1 k)]
  exact pow_le_one₀ hy.1 hy.2

-- @node: armMarginal_finiteMoment4
/-- The arm marginals have finite fourth moments because they are supported on `[0,1]`. -/
lemma armMarginal_finiteMoment4 (nu : Measure (ℝ × ℝ)) (hnu : MInt nu) (a : Fin 2) :
    FiniteMoment4 (armMarginal nu a) := by
  refine ⟨?_, armMarginal_integrable_pow nu hnu a 2,
    armMarginal_integrable_pow nu hnu a 3,
    armMarginal_integrable_pow nu hnu a 4⟩
  simpa using armMarginal_integrable_pow nu hnu a 1

-- @node: arm_variance_pos_of_tangent
/-- Positive tangent residual forces nondegenerate arm variance. -/
lemma arm_variance_pos_of_tangent (nu : Measure (ℝ × ℝ)) (hnu : MTan nu) (a : Fin 2) :
    moment (armMarginal nu a) 1 ^ 2 < moment (armMarginal nu a) 2 := by
  let μ := armMarginal nu a
  haveI : IsProbabilityMeasure μ := armMarginal_isProbabilityMeasure nu hnu.toMInt a
  have hfin : FiniteMoment4 μ := armMarginal_finiteMoment4 nu hnu.toMInt a
  by_contra hnot
  have hle : moment μ 2 ≤ moment μ 1 ^ 2 := le_of_not_gt hnot
  have hmem : MemLp (fun y : ℝ => y) 2 μ := by
    simpa using Causalean.Stat.MomentProblems.ResidualQuadratic.ProjectionResidual.memL2_id μ hfin
  have hvar_nonneg := ProbabilityTheory.variance_nonneg (fun y : ℝ => y) μ
  have hvar_eq :
      ProbabilityTheory.variance (fun y : ℝ => y) μ = moment μ 2 - moment μ 1 ^ 2 := by
    rw [ProbabilityTheory.variance_eq_sub hmem]
    simp [moment, pow_two]
  have hvar0 : ProbabilityTheory.variance (fun y : ℝ => y) μ = 0 := by
    rw [hvar_eq]
    have hge : moment μ 1 ^ 2 ≤ moment μ 2 := by
      linarith [hvar_nonneg, hvar_eq]
    linarith
  have hevar0 : ProbabilityTheory.evariance (fun y : ℝ => y) μ = 0 := by
    have hof := ProbabilityTheory.ofReal_variance hmem
    rw [hvar0, ENNReal.ofReal_zero] at hof
    exact hof.symm
  have hconst_ae : (fun y : ℝ => y) =ᵐ[μ] fun _ => (∫ y : ℝ, y ∂μ) := by
    exact (ProbabilityTheory.evariance_eq_zero_iff hmem.aemeasurable).1 hevar0
  have hres0 : ∫ y, (y ^ 2 - 0 - (moment μ 1) * y) ^ 2 ∂μ = 0 := by
    calc
      ∫ y, (y ^ 2 - 0 - (moment μ 1) * y) ^ 2 ∂μ =
          ∫ _y : ℝ, (0 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hconst_ae] with y hy
        rw [hy]
        simp [moment]
        ring
      _ = 0 := by simp
  have hbdd :
      BddBelow
        (Set.range fun b : ℝ × ℝ => ∫ y, (y ^ 2 - b.1 - b.2 * y) ^ 2 ∂μ) := by
    exact ⟨0, by
      rintro z ⟨b, rfl⟩
      exact integral_nonneg fun y => sq_nonneg _⟩
  have hle0 :
      (⨅ b : ℝ × ℝ, ∫ y, (y ^ 2 - b.1 - b.2 * y) ^ 2 ∂μ) ≤ 0 := by
    calc
      (⨅ b : ℝ × ℝ, ∫ y, (y ^ 2 - b.1 - b.2 * y) ^ 2 ∂μ)
          ≤ ∫ y, (y ^ 2 - (0 : ℝ) - (moment μ 1) * y) ^ 2 ∂μ :=
            ciInf_le hbdd (0, moment μ 1)
      _ = 0 := hres0
  have hpos : 0 < (⨅ b : ℝ × ℝ, ∫ y, (y ^ 2 - b.1 - b.2 * y) ^ 2 ∂μ) := by
    simpa [μ, armTangentStrength] using hnu.tangent a
  linarith

-- @node: armTangentStrength_eq_l2ResidualQuadratic
/-- The local tangent-strength infimum agrees with the reusable Causalean residual. -/
lemma armTangentStrength_eq_l2ResidualQuadratic (nu : Measure (ℝ × ℝ)) (hnu : MTan nu)
    (a : Fin 2) :
    armTangentStrength nu a = l2ResidualQuadratic (armMarginal nu a) := by
  let μ := armMarginal nu a
  haveI : IsProbabilityMeasure μ := armMarginal_isProbabilityMeasure nu hnu.toMInt a
  have hfin : FiniteMoment4 μ := armMarginal_finiteMoment4 nu hnu.toMInt a
  have hnd : moment μ 1 ^ 2 < moment μ 2 := by
    simpa [μ] using arm_variance_pos_of_tangent nu hnu a
  rw [armTangentStrength]
  apply le_antisymm
  · have hbdd :
        BddBelow
          (Set.range fun b : ℝ × ℝ => ∫ y, (y ^ 2 - b.1 - b.2 * y) ^ 2 ∂μ) := by
      exact ⟨l2ResidualQuadratic μ, by
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
      _ = l2ResidualQuadratic μ := by
            exact Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.residualQuad_opt_eq μ hfin hnd
  · refine le_ciInf ?_
    intro b
    change l2ResidualQuadratic μ ≤
      ∫ y, (y ^ 2 - b.1 - b.2 * y) ^ 2 ∂armMarginal nu a
    simpa [μ] using Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.l2ResidualQuadratic_le
      μ hfin hnd b.1 b.2

-- @node: projResidual_bounded_Icc
/-- The projection residual is bounded on `[0,1]` because it is a quadratic polynomial. -/
lemma projResidual_bounded_Icc (μ : Measure ℝ) :
    ∃ C : ℝ, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |Causalean.Stat.MomentProblems.ResidualQuadratic.ProjectionResidual.projResidual μ y| ≤ C := by
  let b0 := Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.optIntercept μ
  let b1 := Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.optSlope μ
  refine ⟨1 + |b0| + |b1|, ?_⟩
  intro y hy
  have hyabs : |y| ≤ 1 := by
    rw [abs_of_nonneg hy.1]
    exact hy.2
  have hy2abs : |y ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg y)]
    exact pow_le_one₀ hy.1 hy.2
  have hmul : |b1 * y| ≤ |b1| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg b1) hyabs
  calc
    |Causalean.Stat.MomentProblems.ResidualQuadratic.ProjectionResidual.projResidual μ y|
        = |y ^ 2 - (b0 + b1 * y)| := by
          rfl
    _ ≤ |y ^ 2| + |b0 + b1 * y| := abs_sub _ _
    _ ≤ |y ^ 2| + (|b0| + |b1 * y|) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left (abs_add_le b0 (b1 * y)) |y ^ 2|
    _ ≤ 1 + (|b0| + |b1|) := by
      linarith
    _ = 1 + |b0| + |b1| := by
      ring

end CausalSmith.Stat.NeymanRegretMinimax
