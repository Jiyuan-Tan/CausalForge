/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Arm-level helpers for the linear-tilt path construction
-/

import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.Tilt

namespace CausalSmith.Stat.NeymanRegretMinimax

open MeasureTheory Asymptotics
open scoped BigOperators Topology

-- @node: linearTiltScore
/-- The arm score used in the linear-tilt path, with the appropriate coordinate
of the direction `u`. -/
noncomputable def linearTiltScore (nu : Measure (ℝ × ℝ)) (u : ℝ × ℝ)
    (a : Fin 2) : ℝ → ℝ :=
  boundedArmScore nu a (if a = 0 then u.1 else u.2)

-- @node: linearTiltArm
/-- The arm marginal tilted by `linearTiltScore`. -/
noncomputable def linearTiltArm (nu : Measure (ℝ × ℝ)) (u : ℝ × ℝ)
    (a : Fin 2) (h : ℝ) : Measure ℝ :=
  Causalean.Mathlib.InformationTheory.KlDensityTiltExpansion.tiltMeasure
    (armMarginal nu a) (linearTiltScore nu u a) h

-- @node: linearTiltJointPath
/-- A joint-law path realizing the two tilted arm marginals near zero.  It uses
the original joint law at `h = 0`, so the path passes exactly through `nu`; away
from zero it uses the product coupling of the two tilted arm laws. -/
noncomputable def linearTiltJointPath (nu : Measure (ℝ × ℝ)) (u : ℝ × ℝ)
    (η h : ℝ) : Measure (ℝ × ℝ) :=
  if h = 0 then nu
  else if |h| ≤ η then (linearTiltArm nu u 0 h).prod (linearTiltArm nu u 1 h)
  else nu

-- @node: linearTiltScore_moments
/-- Moment constraints and score cost for `linearTiltScore`. -/
lemma linearTiltScore_moments (nu : Measure (ℝ × ℝ)) (hnu : MTan nu)
    (u : ℝ × ℝ) (a : Fin 2) :
    (∫ y, linearTiltScore nu u a y ∂(armMarginal nu a) = 0)
      ∧ (∫ y, y * linearTiltScore nu u a y ∂(armMarginal nu a) = 0)
      ∧ (∫ y, y ^ 2 * linearTiltScore nu u a y ∂(armMarginal nu a)
          = (if a = 0 then u.1 else u.2))
      ∧ (∫ y, (linearTiltScore nu u a y) ^ 2 ∂(armMarginal nu a)
          = armScoreCost nu a (if a = 0 then u.1 else u.2)) := by
  simpa [linearTiltScore] using
    boundedArmScore_moments nu hnu a (if a = 0 then u.1 else u.2)

-- @node: linearTiltScore_bounded
/-- The linear-tilt score has a global absolute bound. -/
lemma linearTiltScore_bounded (nu : Measure (ℝ × ℝ)) (u : ℝ × ℝ) (a : Fin 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, |linearTiltScore nu u a y| ≤ C := by
  simpa [linearTiltScore] using
    boundedArmScore_bounded nu a (if a = 0 then u.1 else u.2)

-- @node: linearTiltArm_isProbabilityMeasure
/-- A small linear tilt of an arm marginal is a probability measure. -/
lemma linearTiltArm_isProbabilityMeasure (nu : Measure (ℝ × ℝ)) (hnu : MTan nu)
    (u : ℝ × ℝ) (a : Fin 2) {C h : ℝ}
    (hC : ∀ y : ℝ, |linearTiltScore nu u a y| ≤ C) (hh : |h| * C ≤ 1) :
    IsProbabilityMeasure (linearTiltArm nu u a h) := by
  haveI : IsProbabilityMeasure (armMarginal nu a) :=
    armMarginal_isProbabilityMeasure nu hnu.toMInt a
  exact Causalean.Mathlib.InformationTheory.KlDensityTiltExpansion.isProbabilityMeasure_tiltMeasure
    (boundedArmScore_measurable nu a (if a = 0 then u.1 else u.2))
    (by simpa [linearTiltScore] using hC)
    (linearTiltScore_moments nu hnu u a).1 hh

-- @node: linearTiltArm_support_Icc
/-- Linear tilts preserve the arm marginal support because they are absolutely
continuous with respect to the base arm law. -/
lemma linearTiltArm_support_Icc (nu : Measure (ℝ × ℝ)) (hnu : MTan nu)
    (u : ℝ × ℝ) (a : Fin 2) (h : ℝ) :
    ∀ᵐ y ∂(linearTiltArm nu u a h), y ∈ Set.Icc (0 : ℝ) 1 := by
  have hac :
      linearTiltArm nu u a h ≪ armMarginal nu a :=
    Causalean.Mathlib.InformationTheory.KlDensityTiltExpansion.tiltMeasure_absolutelyContinuous
      (armMarginal nu a) (linearTiltScore nu u a) h
  exact (armMarginal_support_Icc nu hnu.toMInt a).filter_mono hac.ae_le

-- @node: boundedOutcomes_prod_of_arm_support
/-- The product coupling of two `[0,1]`-supported arm laws is supported on
`[0,1]²`. -/
lemma boundedOutcomes_prod_of_arm_support {μ0 μ1 : Measure ℝ}
    [SFinite μ1]
    (h0 : ∀ᵐ y ∂μ0, y ∈ Set.Icc (0 : ℝ) 1)
    (h1 : ∀ᵐ y ∂μ1, y ∈ Set.Icc (0 : ℝ) 1) :
    BoundedOutcomes (μ0.prod μ1) := by
  have hset : MeasurableSet
      {p : ℝ × ℝ | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1} :=
    (measurableSet_Icc.preimage measurable_fst).inter
      (measurableSet_Icc.preimage measurable_snd)
  exact (Measure.ae_prod_iff_ae_ae hset).2 <| by
    filter_upwards [h0] with y0 hy0
    filter_upwards [h1] with y1 hy1
    exact ⟨hy0, hy1⟩

-- @node: linearTiltJointPath_armMarginal
/-- On the local radius, the joint path has the prescribed tilted arm
marginals. -/
lemma linearTiltJointPath_armMarginal (nu : Measure (ℝ × ℝ))
    (u : ℝ × ℝ) {η h : ℝ}
    (h0prob : IsProbabilityMeasure (linearTiltArm nu u 0 h))
    (h1prob : IsProbabilityMeasure (linearTiltArm nu u 1 h))
    (hh : |h| ≤ η) (a : Fin 2) :
    armMarginal (linearTiltJointPath nu u η h) a = linearTiltArm nu u a h := by
  by_cases hz : h = 0
  · subst h
    simp [linearTiltJointPath, linearTiltArm,
      Causalean.Mathlib.InformationTheory.KlDensityTiltExpansion.tiltMeasure]
  · haveI : IsProbabilityMeasure (linearTiltArm nu u 0 h) := h0prob
    haveI : IsProbabilityMeasure (linearTiltArm nu u 1 h) := h1prob
    fin_cases a
    · simp [linearTiltJointPath, hz, hh, armMarginal]
    · simp [linearTiltJointPath, hz, hh, armMarginal]

-- @node: linearTiltScore_mul_integrable_pow
/-- Bounded tilt scores can multiply any bounded-support arm moment. -/
lemma linearTiltScore_mul_integrable_pow (nu : Measure (ℝ × ℝ)) (hnu : MTan nu)
    (u : ℝ × ℝ) (a : Fin 2) (k : ℕ) :
    Integrable (fun y : ℝ => y ^ k * linearTiltScore nu u a y) (armMarginal nu a) := by
  rcases linearTiltScore_bounded nu u a with ⟨C, _hCnonneg, hC⟩
  have hpow : Integrable (fun y : ℝ => y ^ k) (armMarginal nu a) :=
    armMarginal_integrable_pow nu hnu.toMInt a k
  have hs_meas :
      AEStronglyMeasurable (linearTiltScore nu u a) (armMarginal nu a) := by
    simpa [linearTiltScore] using
      (boundedArmScore_measurable nu a (if a = 0 then u.1 else u.2)).aestronglyMeasurable
  have hs_bound :
      ∀ᵐ y ∂(armMarginal nu a), ‖linearTiltScore nu u a y‖ ≤ C :=
    Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC y
  simpa [mul_comm] using hpow.bdd_mul hs_meas hs_bound

-- @node: linearTiltArm_integral_id
/-- The linear tilt preserves the first arm moment. -/
lemma linearTiltArm_integral_id (nu : Measure (ℝ × ℝ)) (hnu : MTan nu)
    (u : ℝ × ℝ) (a : Fin 2) {C h : ℝ}
    (hC : ∀ y : ℝ, |linearTiltScore nu u a y| ≤ C) (hh : |h| * C ≤ 1) :
    ∫ y, y ∂(linearTiltArm nu u a h) = ∫ y, y ∂(armMarginal nu a) := by
  haveI : IsProbabilityMeasure (armMarginal nu a) :=
    armMarginal_isProbabilityMeasure nu hnu.toMInt a
  exact tiltMeasure_integral_preserve_of_orthogonal
    (by simpa [linearTiltScore] using
      boundedArmScore_measurable nu a (if a = 0 then u.1 else u.2))
    hC hh (by simpa using armMarginal_integrable_pow nu hnu.toMInt a 1)
    (by simpa using linearTiltScore_mul_integrable_pow nu hnu u a 1)
    (linearTiltScore_moments nu hnu u a).2.1

-- @node: linearTiltArm_integral_sq
/-- The linear tilt shifts the second arm moment by the requested direction
coordinate. -/
lemma linearTiltArm_integral_sq (nu : Measure (ℝ × ℝ)) (hnu : MTan nu)
    (u : ℝ × ℝ) (a : Fin 2) {C h : ℝ}
    (hC : ∀ y : ℝ, |linearTiltScore nu u a y| ≤ C) (hh : |h| * C ≤ 1) :
    ∫ y, y ^ 2 ∂(linearTiltArm nu u a h)
      = ∫ y, y ^ 2 ∂(armMarginal nu a) + h * (if a = 0 then u.1 else u.2) := by
  haveI : IsProbabilityMeasure (armMarginal nu a) :=
    armMarginal_isProbabilityMeasure nu hnu.toMInt a
  exact tiltMeasure_integral_shift_of_score_moment
    (by simpa [linearTiltScore] using
      boundedArmScore_measurable nu a (if a = 0 then u.1 else u.2))
    hC hh (armMarginal_integrable_pow nu hnu.toMInt a 2)
    (linearTiltScore_mul_integrable_pow nu hnu u a 2)
    (linearTiltScore_moments nu hnu u a).2.2.1

-- @node: linearTiltArm_kl_expansion
/-- Arm-wise KL expansion for the bounded linear tilt. -/
lemma linearTiltArm_kl_expansion (nu : Measure (ℝ × ℝ)) (hnu : MTan nu)
    (u : ℝ × ℝ) (a : Fin 2) {C : ℝ}
    (hC : ∀ y : ℝ, |linearTiltScore nu u a y| ≤ C) :
    (fun h => (InformationTheory.klDiv (linearTiltArm nu u a h) (armMarginal nu a)).toReal
        - (h ^ 2 / 2) * armScoreCost nu a (if a = 0 then u.1 else u.2))
      =o[𝓝 (0 : ℝ)] fun h => h ^ 2 := by
  haveI : IsProbabilityMeasure (armMarginal nu a) :=
    armMarginal_isProbabilityMeasure nu hnu.toMInt a
  simpa [linearTiltArm, (linearTiltScore_moments nu hnu u a).2.2.2] using
    Causalean.Mathlib.InformationTheory.KlDensityTiltExpansion.klDiv_tilt_expansion
      (by simpa [linearTiltScore] using
        boundedArmScore_measurable nu a (if a = 0 then u.1 else u.2))
      hC (linearTiltScore_moments nu hnu u a).1

end CausalSmith.Stat.NeymanRegretMinimax
