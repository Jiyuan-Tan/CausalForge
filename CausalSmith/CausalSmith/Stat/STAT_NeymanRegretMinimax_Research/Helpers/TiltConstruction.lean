/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Linear-tilt path construction
-/

import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.TiltConstructionHelpers

namespace CausalSmith.Stat.NeymanRegretMinimax

open MeasureTheory Asymptotics
open scoped BigOperators Topology

-- @node: lem:linear-tilt-path-valid
/-- The moment-preserving scores from `arm_score_program_solution` define, for
small `|h|`, a linear-tilt path `dnu_a^h = (1 + h s_a) dnu_a` that is a
bounded-support `IsLocalPath` for `nu` in direction `u`.  The conclusion exhibits
the EXPLICIT linear-tilt construction (`IsLinearTiltPath`), not merely an abstract
`IsLocalPath` (added per the redirect). -/
lemma linear_tilt_path_valid (nu : Measure (ℝ × ℝ)) (hnu : MTan nu) (u : ℝ × ℝ)
    (_hu : 0 < localInformation nu u) :
    ∃ p : ℝ → Measure (ℝ × ℝ),
      IsLinearTiltPath nu u p ∧ IsLocalPath nu u p := by
  rcases linearTiltScore_bounded nu u 0 with ⟨C0, hC0nonneg, hC0⟩
  rcases linearTiltScore_bounded nu u 1 with ⟨C1, hC1nonneg, hC1⟩
  let M : ℝ := max C0 C1
  let η : ℝ := 1 / (M + 1)
  let p : ℝ → Measure (ℝ × ℝ) := linearTiltJointPath nu u η
  have hMnonneg : 0 ≤ M := le_trans hC0nonneg (le_max_left C0 C1)
  have hdenpos : 0 < M + 1 := by linarith
  have hηpos : 0 < η := by dsimp [η]; positivity
  have hC0le : C0 ≤ M + 1 := by
    dsimp [M]; exact le_trans (le_max_left C0 C1) (by linarith)
  have hC1le : C1 ≤ M + 1 := by
    dsimp [M]; exact le_trans (le_max_right C0 C1) (by linarith)
  have hsmall0 : ∀ {h : ℝ}, |h| ≤ η → |h| * C0 ≤ 1 := by
    intro h hh
    have hmul := mul_le_mul hh hC0le hC0nonneg (le_of_lt hηpos)
    have hηmul : η * (M + 1) = 1 := by dsimp [η]; field_simp [ne_of_gt hdenpos]
    linarith
  have hsmall1 : ∀ {h : ℝ}, |h| ≤ η → |h| * C1 ≤ 1 := by
    intro h hh
    have hmul := mul_le_mul hh hC1le hC1nonneg (le_of_lt hηpos)
    have hηmul : η * (M + 1) = 1 := by dsimp [η]; field_simp [ne_of_gt hdenpos]
    linarith
  have hprob0 : ∀ h : ℝ, |h| ≤ η → IsProbabilityMeasure (linearTiltArm nu u 0 h) :=
    fun h hh => linearTiltArm_isProbabilityMeasure nu hnu u 0 hC0 (hsmall0 hh)
  have hprob1 : ∀ h : ℝ, |h| ≤ η → IsProbabilityMeasure (linearTiltArm nu u 1 h) :=
    fun h hh => linearTiltArm_isProbabilityMeasure nu hnu u 1 hC1 (hsmall1 hh)
  have hmargin : ∀ h : ℝ, |h| ≤ η → ∀ a : Fin 2,
      armMarginal (p h) a = linearTiltArm nu u a h := by
    intro h hh a
    exact linearTiltJointPath_armMarginal (nu := nu) (u := u)
      (η := η) (h := h) (hprob0 h hh) (hprob1 h hh) hh a
  have hη_ev : ∀ᶠ h in 𝓝 (0 : ℝ), |h| ≤ η := by
    refine Metric.eventually_nhds_iff.2 ⟨η, hηpos, ?_⟩
    intro h hh
    exact le_of_lt (by simpa [Real.dist_eq, sub_zero] using hh)
  refine ⟨p, ?_, ?_⟩
  · refine ⟨linearTiltScore nu u, η, hηpos, ?_, ?_⟩
    · intro a
      rcases linearTiltScore_moments nu hnu u a with ⟨h0, h1, h2, _hcost⟩
      rcases linearTiltScore_bounded nu u a with ⟨C, _hCnonneg, hC⟩
      exact ⟨by
        simpa [linearTiltScore] using
          boundedArmScore_measurable nu a (if a = 0 then u.1 else u.2),
        h0, h1, h2, ⟨C, fun y _hy => hC y⟩⟩
    · intro h hh a
      rw [hmargin h hh a]
      simp [linearTiltArm, Causalean.Mathlib.InformationTheory.KlDensityTiltExpansion.tiltMeasure]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [p, linearTiltJointPath]
    · intro h
      by_cases hz : h = 0
      · subst h; simpa [p, linearTiltJointPath] using hnu.isLaw
      by_cases hh : |h| ≤ η
      · haveI : IsProbabilityMeasure (linearTiltArm nu u 0 h) := hprob0 h hh
        haveI : IsProbabilityMeasure (linearTiltArm nu u 1 h) := hprob1 h hh
        simpa [p, linearTiltJointPath, hz, hh] using
          (by infer_instance : IsProbabilityMeasure
            ((linearTiltArm nu u 0 h).prod (linearTiltArm nu u 1 h)))
      · simpa [p, linearTiltJointPath, hz, hh] using hnu.isLaw
    · intro h
      by_cases hz : h = 0
      · subst h; simpa [p, linearTiltJointPath] using hnu.bounded
      by_cases hh : |h| ≤ η
      · haveI : IsProbabilityMeasure (linearTiltArm nu u 1 h) := hprob1 h hh
        simpa [p, linearTiltJointPath, hz, hh] using
          boundedOutcomes_prod_of_arm_support
            (linearTiltArm_support_Icc nu hnu u 0 h)
            (linearTiltArm_support_Icc nu hnu u 1 h)
      · simpa [p, linearTiltJointPath, hz, hh] using hnu.bounded
    · intro h a
      by_cases hz : h = 0
      · subst h; simp [p, linearTiltJointPath]
      by_cases hh : |h| ≤ η
      · rw [hmargin h hh a]
        fin_cases a
        · exact linearTiltArm_integral_id nu hnu u 0 hC0 (hsmall0 hh)
        · exact linearTiltArm_integral_id nu hnu u 1 hC1 (hsmall1 hh)
      · simp [p, linearTiltJointPath, hz, hh]
    · intro a
      have hzero_ev :
          (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 (0 : ℝ)]
            (fun h => rootSecondMoment (p h) a ^ 2
              - (rootSecondMoment nu a ^ 2 + h * (if a = 0 then u.1 else u.2))) := by
        filter_upwards [hη_ev] with h hh
        symm
        fin_cases a
        · change rootSecondMoment (p h) 0 ^ 2
              - (rootSecondMoment nu 0 ^ 2 + h * u.1) = 0
          have htilt_nonneg : 0 ≤ ∫ y, y ^ 2 ∂(linearTiltArm nu u 0 h) :=
            integral_nonneg fun y => sq_nonneg y
          have hbase_nonneg : 0 ≤ ∫ y, y ^ 2 ∂(armMarginal nu 0) :=
            integral_nonneg fun y => sq_nonneg y
          rw [rootSecondMoment, hmargin h hh 0, Real.sq_sqrt htilt_nonneg]
          rw [rootSecondMoment, Real.sq_sqrt hbase_nonneg]
          rw [linearTiltArm_integral_sq nu hnu u 0 hC0 (hsmall0 hh)]
          simp
        · change rootSecondMoment (p h) 1 ^ 2
              - (rootSecondMoment nu 1 ^ 2 + h * u.2) = 0
          have htilt_nonneg : 0 ≤ ∫ y, y ^ 2 ∂(linearTiltArm nu u 1 h) :=
            integral_nonneg fun y => sq_nonneg y
          have hbase_nonneg : 0 ≤ ∫ y, y ^ 2 ∂(armMarginal nu 1) :=
            integral_nonneg fun y => sq_nonneg y
          rw [rootSecondMoment, hmargin h hh 1, Real.sq_sqrt htilt_nonneg]
          rw [rootSecondMoment, Real.sq_sqrt hbase_nonneg]
          rw [linearTiltArm_integral_sq nu hnu u 1 hC1 (hsmall1 hh)]
          simp
      exact (Asymptotics.isLittleO_zero (fun h : ℝ => h) (𝓝 (0 : ℝ))).congr'
        hzero_ev (Filter.Eventually.of_forall fun _ => rfl)
    · intro a
      have hbase :
          (fun h => (InformationTheory.klDiv
              (linearTiltArm nu u a h) (armMarginal nu a)).toReal
            - (h ^ 2 / 2) * armScoreCost nu a (if a = 0 then u.1 else u.2))
            =o[𝓝 (0 : ℝ)] fun h => h ^ 2 := by
        fin_cases a
        · exact linearTiltArm_kl_expansion nu hnu u 0 hC0
        · exact linearTiltArm_kl_expansion nu hnu u 1 hC1
      refine hbase.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
      filter_upwards [hη_ev] with h hh
      rw [hmargin h hh a]

-- @node: lem:path-existence
/-- Existence of a bounded-support local alternative path satisfying
`IsLocalPath` for every direction `u` with `0 < J_nu(u) < ∞`. -/
lemma path_existence (nu : Measure (ℝ × ℝ)) (hnu : MTan nu) (u : ℝ × ℝ)
    (hu : 0 < localInformation nu u) :
    ∃ p : ℝ → Measure (ℝ × ℝ), IsLocalPath nu u p := by
  rcases linear_tilt_path_valid nu hnu u hu with ⟨p, _hlin, hp⟩
  exact ⟨p, hp⟩

end CausalSmith.Stat.NeymanRegretMinimax
