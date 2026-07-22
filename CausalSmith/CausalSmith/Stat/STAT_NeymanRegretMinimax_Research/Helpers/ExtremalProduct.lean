/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Product laws from the one-dimensional residual-envelope extremal

This file builds balanced `M_tan` laws by taking the product of the
one-dimensional three-point extremal law from the moment-residual envelope.
-/

import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.ScoreProgram
import Causalean.Stat.Nonparametric.MomentProblems.BoundedOutcomeEnvelope.Attainment
import Causalean.Stat.Nonparametric.MomentProblems.BoundedOutcomeEnvelope.Bounds

namespace CausalSmith.Stat.NeymanRegretMinimax

open MeasureTheory Asymptotics Filter
open scoped BigOperators Topology

-- @node: armTangentStrength_eq_l2ResidualQuadratic_of_finite_nonconstant
/-- Non-circular bridge from the arm tangent-strength infimum to the closed-form
`L²` residual.  Unlike `armTangentStrength_eq_l2ResidualQuadratic`, this assumes
the one-dimensional marginal facts directly, so it can be used while constructing
an `MTan` witness. -/
lemma armTangentStrength_eq_l2ResidualQuadratic_of_finite_nonconstant
    (nu : Measure (ℝ × ℝ)) (a : Fin 2)
    (hprob : IsProbabilityMeasure (armMarginal nu a))
    (hfin : Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.FiniteMoment4 (armMarginal nu a))
    (hnd : Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.moment (armMarginal nu a) 1 ^ 2
        < Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.moment (armMarginal nu a) 2) :
    armTangentStrength nu a =
      Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.l2ResidualQuadratic (armMarginal nu a) := by
  let μ := armMarginal nu a
  haveI : IsProbabilityMeasure μ := hprob
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
            - Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.optSlope μ * y) ^ 2 ∂μ := by
        exact ciInf_le hbdd
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

-- @node: extremalProduct_balanced_mtan_positive_complexity
/-- The product of an interior residual-envelope extremal law with itself is a
balanced `M_tan` law with positive local complexity. -/
lemma extremalProduct_balanced_mtan_positive_complexity (v : ℝ) (hv0 : 0 < v)
    (hv1 : v < 1) :
    ∃ nu : Measure (ℝ × ℝ), MTan nu
      ∧ rootSecondMoment nu 0 = rootSecondMoment nu 1
      ∧ 0 < localComplexity nu := by
  let μ : Measure ℝ := Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope.extremalMeasure v
  let nu : Measure (ℝ × ℝ) := μ.prod μ
  have hμprob : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope.extremalMeasure_isProb v hv0 hv1
  haveI : IsProbabilityMeasure μ := hμprob
  have hνprob : IsProbabilityMeasure nu := by
    dsimp [nu]
    infer_instance
  have hmargin0 : armMarginal nu 0 = μ := by
    dsimp [nu]
    simp [armMarginal]
  have hmargin1 : armMarginal nu 1 = μ := by
    dsimp [nu]
    simp [armMarginal]
  have hμsupp : ∀ᵐ y ∂μ, y ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [μ]
    exact Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope.extremalMeasure_supp v hv0 hv1
  have hbounded : BoundedOutcomes nu := by
    dsimp [BoundedOutcomes, nu]
    have hset :
        MeasurableSet
          {p : ℝ × ℝ | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1} :=
      (measurableSet_Icc.preimage measurable_fst).inter
        (measurableSet_Icc.preimage measurable_snd)
    rw [Measure.ae_prod_iff_ae_ae hset]
    filter_upwards [hμsupp] with x hx
    filter_upwards [hμsupp] with y hy
    exact ⟨hx, hy⟩
  have hmom2_int : ∫ y, y ^ 2 ∂μ = v ^ 2 := by
    have h := Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope.extremalMeasure_moment2
      v hv0 hv1
    simpa [μ, Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.moment] using h
  have hroot0 : rootSecondMoment nu 0 = v := by
    rw [rootSecondMoment, hmargin0, hmom2_int, Real.sqrt_sq_eq_abs, abs_of_pos hv0]
  have hroot1 : rootSecondMoment nu 1 = v := by
    rw [rootSecondMoment, hmargin1, hmom2_int, Real.sqrt_sq_eq_abs, abs_of_pos hv0]
  have hfinμ : Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.FiniteMoment4 μ := by
    dsimp [μ]
    exact Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope.finiteMoment4_of_admissible
      (Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope.extremalMeasure_admissible
        v hv0 hv1)
  have hndμ :
      Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.moment μ 1 ^ 2
        < Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.moment μ 2 := by
    have hm1 := Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope.extremalMeasure_moment1
      v hv0 hv1
    have hm2 := Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope.extremalMeasure_moment2
      v hv0 hv1
    have hmem := Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope.maximizingRoot_mem
      v hv0 hv1
    have hvSqPos : 0 < v ^ 2 := by positivity
    have hu0 : 0 < Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope.maximizingRoot v :=
      lt_trans hvSqPos hmem.1
    dsimp [μ]
    rw [hm1, hm2]
    nlinarith [hmem.2, hu0, hv0]
  have htangent0 : 0 < armTangentStrength nu 0 := by
    rw [armTangentStrength_eq_l2ResidualQuadratic_of_finite_nonconstant nu 0]
    · rw [hmargin0]
      dsimp [μ]
      rw [Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope.extremalMeasure_residual v hv0 hv1]
      exact Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope.rhoEnvelope_pos v hv0 hv1
    · simpa [hmargin0] using hμprob
    · simpa [hmargin0] using hfinμ
    · simpa [hmargin0] using hndμ
  have htangent1 : 0 < armTangentStrength nu 1 := by
    rw [armTangentStrength_eq_l2ResidualQuadratic_of_finite_nonconstant nu 1]
    · rw [hmargin1]
      dsimp [μ]
      rw [Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope.extremalMeasure_residual v hv0 hv1]
      exact Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope.rhoEnvelope_pos v hv0 hv1
    · simpa [hmargin1] using hμprob
    · simpa [hmargin1] using hfinμ
    · simpa [hmargin1] using hndμ
  have hmtan : MTan nu :=
    { isLaw := hνprob
      bounded := hbounded
      interiorMoments := by
        intro a
        fin_cases a
        · simpa [hroot0] using hv0
        · simpa [hroot1] using hv0
      tangent := by
        intro a
        fin_cases a
        · simpa using htangent0
        · simpa using htangent1 }
  refine ⟨nu, hmtan, ?_, ?_⟩
  · exact hroot0.trans hroot1.symm
  · exact (feasible_directions_nonempty nu hmtan).2

end CausalSmith.Stat.NeymanRegretMinimax
