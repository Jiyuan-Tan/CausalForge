/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Sample.FiniteStratumMarkedRatioMse.MissingBound
import Causalean.Stat.Sample.FiniteStratumMarkedRatioMse.CenteredNoiseBound
import Causalean.Stat.Sample.OccupancyWeightedMean.MomentBounds
import Causalean.Mathlib.Probability.IidMeanVariance
import Causalean.Mathlib.Probability.BernoulliMeasure

/-!
# MSE bounds for fixed finite-stratum marked ratios

This module proves square integrability and bounds centered ratio noise,
empirical category-mass fluctuation, and the explicit empty-arm remainder.
It combines them into single-arm and signed two-arm fixed-set MSE bounds that
remain meaningful at every totalized boundary.
-/

namespace Causalean.Stat.FiniteStratumMarkedRatioMse

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Omega kappa : Type*} [MeasurableSpace Omega]
  [Fintype kappa] [DecidableEq kappa]
  [MeasurableSpace kappa] [MeasurableSingletonClass kappa]

private lemma memLp_designWeight_coordinate_sum {m : Nat}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (group : Omega → kappa) (arm : Omega → Bool)
    (hgroup : Measurable group) (harm : Measurable arm)
    (f : Omega → Real) (hf : MemLp f 2 mu) (hfmeas : Measurable f)
    (W : (Fin m → kappa × Bool) → Real) :
    MemLp (fun z : Fin m → Omega ↦
      ∑ i : Fin m, W (Causalean.Stat.sampleDesign group arm z) * f (z i)) 2
      (Measure.pi (fun _ : Fin m ↦ mu)) := by
  classical
  let C : Real := ∑ d : Fin m → kappa × Bool, |W d|
  have hW (d : Fin m → kappa × Bool) : |W d| ≤ C := by
    exact Finset.single_le_sum (fun d' _ ↦ abs_nonneg (W d'))
      (Finset.mem_univ d)
  have hterm (i : Fin m) : MemLp (fun z : Fin m → Omega ↦
      W (Causalean.Stat.sampleDesign group arm z) * f (z i)) 2
      (Measure.pi (fun _ : Fin m ↦ mu)) := by
    have hcoord := hf.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin m ↦ mu) i)
    apply hcoord.of_le_mul
    · exact (((Measurable.of_discrete : Measurable W).comp
          (Causalean.Stat.measurable_sampleDesign group arm hgroup harm)).mul
        (hfmeas.comp (measurable_pi_apply i))).aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hW _) (abs_nonneg _)
  exact memLp_finsetSum Finset.univ fun i _ ↦ hterm i

private lemma fixedStratumArmCenterTarget_eq_target_of_measurable
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (group : Omega → kappa) (arm : Omega → Bool) (Y : Omega → Real)
    (center : Bool → kappa → Real) (H : Finset kappa) (a : Bool)
    (hgroup : Measurable group) (harm : Measurable arm)
    (hmem : ∀ k, MemLp (supportedArmResidual group arm Y center a k) 2 mu)
    (hcenter : ∀ k, ∫ omega in armCategoryEvent group arm a k,
      (Y omega - center a k) ∂mu = 0)
    (hpositive : ∀ k ∈ H, 0 < categoryMass mu group k →
      0 < armCategoryMass mu group arm a k) :
    fixedStratumArmCenterTarget mu group H center a =
      fixedStratumArmTarget mu group arm Y H a := by
  exact fixedStratumArmCenterTarget_eq_target mu group arm Y center H a
    hgroup harm hmem hcenter hpositive

private lemma memLp_designStatistic {m : Nat}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (group : Omega → kappa) (arm : Omega → Bool)
    (hgroup : Measurable group) (harm : Measurable arm)
    (F : (Fin m → kappa × Bool) → Real) :
    MemLp (fun z : Fin m → Omega ↦
      F (Causalean.Stat.sampleDesign group arm z)) 2
      (Measure.pi (fun _ : Fin m ↦ mu)) := by
  classical
  let C : Real := ∑ d : Fin m → kappa × Bool, |F d|
  apply MemLp.of_bound
    (((Measurable.of_discrete : Measurable F).comp
      (Causalean.Stat.measurable_sampleDesign group arm hgroup harm)).aestronglyMeasurable)
    C
  filter_upwards [] with z
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun d _ ↦ abs_nonneg (F d))
    (Finset.mem_univ (Causalean.Stat.sampleDesign group arm z))

private lemma fixedStratumArmScore_memLp_two {m : Nat}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (group : Omega → kappa) (arm : Omega → Bool) (Y : Omega → Real)
    (center : Bool → kappa → Real) (H : Finset kappa) (a : Bool)
    (hgroup : Measurable group) (harm : Measurable arm) (hY : Measurable Y)
    (hmem : ∀ k, MemLp (supportedArmResidual group arm Y center a k) 2 mu) :
    MemLp (fixedStratumArmScore (m := m) group arm Y H a) 2
      (Measure.pi (fun _ : Fin m ↦ mu)) := by
  classical
  have hmark (k : kappa) : MemLp (supportedArmMark group arm Y a k) 2 mu := by
    have hcell : MeasurableSet (armCategoryEvent group arm a k) :=
      Causalean.Stat.measurableSet_armGroupEvent group arm hgroup harm a k
    have hc : MemLp ((armCategoryEvent group arm a k).indicator
        (fun _ ↦ center a k)) 2 mu := (memLp_const _).indicator hcell
    have hadd := (hmem k).add hc
    convert hadd using 1
    funext omega
    by_cases ho : group omega = k ∧ arm omega = a <;>
      simp [supportedArmMark, supportedArmResidual,
        armCategoryEvent, Causalean.Stat.supportedArmGroupResidual,
        Causalean.Stat.armGroupEvent, Causalean.Stat.armGroupResidual, ho]
  have hcellTerm (k : kappa) : MemLp (fun z : Fin m → Omega ↦
      (categoryCount group arm z k : Real) / (m : Real) *
        totalizedArmMean group arm Y z a k) 2
      (Measure.pi (fun _ : Fin m ↦ mu)) := by
    let W : (Fin m → kappa × Bool) → Real := fun d ↦
      (Causalean.Stat.groupCount Prod.fst Prod.snd d k : Real) / (m : Real) *
        if 0 < Causalean.Stat.groupArmCount Prod.fst Prod.snd d a k then
          (Causalean.Stat.groupArmCount Prod.fst Prod.snd d a k : Real)⁻¹ else 0
    have hw := memLp_designWeight_coordinate_sum mu group arm hgroup harm
      (supportedArmMark group arm Y a k) (hmark k)
      (hY.indicator
        (Causalean.Stat.measurableSet_armGroupEvent group arm hgroup harm a k)) W
    convert hw using 1
    funext z
    unfold totalizedArmMean armMarkSum categoryCount categoryArmCount
    dsimp [W]
    have hgc : Causalean.Stat.groupCount Prod.fst Prod.snd
        (Causalean.Stat.sampleDesign group arm z) k =
        Causalean.Stat.groupCount group arm z k := rfl
    have hga : Causalean.Stat.groupArmCount Prod.fst Prod.snd
        (Causalean.Stat.sampleDesign group arm z) a k =
        Causalean.Stat.groupArmCount group arm z a k := rfl
    rw [hgc, hga]
    by_cases hp : 0 < Causalean.Stat.groupArmCount group arm z a k
    · rw [if_pos hp, if_pos hp, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    · rw [if_neg hp, if_neg hp]
      simp
  unfold fixedStratumArmScore
  exact memLp_finsetSum H fun k _ ↦ hcellTerm k

private lemma fixedStratumArmMassFluctuation_memLp_two {m : Nat}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (group : Omega → kappa) (arm : Omega → Bool)
    (center : Bool → kappa → Real) (H : Finset kappa) (a : Bool)
    (hgroup : Measurable group) (harm : Measurable arm) :
    MemLp (fixedStratumArmMassFluctuation (m := m) mu group arm center H a) 2
      (Measure.pi (fun _ : Fin m ↦ mu)) := by
  let F : (Fin m → kappa × Bool) → Real := fun d ↦
    ∑ k ∈ H,
      ((Causalean.Stat.groupCount Prod.fst Prod.snd d k : Real) / (m : Real) -
        categoryMass mu group k) * center a k
  convert memLp_designStatistic mu group arm hgroup harm F using 1
  funext z
  rfl

private lemma fixedStratumArmMissingRemainder_memLp_two {m : Nat}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (group : Omega → kappa) (arm : Omega → Bool)
    (center : Bool → kappa → Real) (H : Finset kappa) (a : Bool)
    (hgroup : Measurable group) (harm : Measurable arm) :
    MemLp (fixedStratumArmMissingRemainder (m := m) group arm center H a) 2
      (Measure.pi (fun _ : Fin m ↦ mu)) := by
  let F : (Fin m → kappa × Bool) → Real := fun d ↦
    fixedStratumArmMissingRemainder Prod.fst Prod.snd center H a d
  convert memLp_designStatistic mu group arm hgroup harm F using 1
  funext z
  rfl

/-- [Measurable group and arm labels and a measurable mark](hyp:hgroup,harm,hY)
together with [finite second moments for every supported residual
cell](hyp:hmem) imply [finite second moments for the treated-minus-control
fixed-set score](goal). -/
theorem fixedStratumMarkedRatio_memLp_two {m : Nat}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (group : Omega → kappa) (arm : Omega → Bool) (Y : Omega → Real)
    (center : Bool → kappa → Real) (H : Finset kappa)
    (hgroup : Measurable group) (harm : Measurable arm) (hY : Measurable Y)
    (hmem : ∀ a k, MemLp (supportedArmResidual group arm Y center a k) 2 mu) :
    MemLp (fixedStratumMarkedRatio (m := m) group arm Y H) 2
      (Measure.pi (fun _ : Fin m => mu)) := by
  classical
  have hmark (a : Bool) (k : kappa) :
      MemLp (supportedArmMark group arm Y a k) 2 mu := by
    have hcell : MeasurableSet (armCategoryEvent group arm a k) :=
      Causalean.Stat.measurableSet_armGroupEvent group arm hgroup harm a k
    have hc : MemLp ((armCategoryEvent group arm a k).indicator
        (fun _ ↦ center a k)) 2 mu := (memLp_const _).indicator hcell
    have hadd := (hmem a k).add hc
    convert hadd using 1
    funext omega
    by_cases ho : group omega = k ∧ arm omega = a <;>
      simp [supportedArmMark, supportedArmResidual,
        armCategoryEvent, Causalean.Stat.supportedArmGroupResidual,
        Causalean.Stat.armGroupEvent, Causalean.Stat.armGroupResidual, ho]
  have hcellTerm (a : Bool) (k : kappa) : MemLp (fun z : Fin m → Omega ↦
      (categoryCount group arm z k : Real) / (m : Real) *
        totalizedArmMean group arm Y z a k) 2
      (Measure.pi (fun _ : Fin m ↦ mu)) := by
    let W : (Fin m → kappa × Bool) → Real := fun d ↦
      (Causalean.Stat.groupCount Prod.fst Prod.snd d k : Real) / (m : Real) *
        if 0 < Causalean.Stat.groupArmCount Prod.fst Prod.snd d a k then
          (Causalean.Stat.groupArmCount Prod.fst Prod.snd d a k : Real)⁻¹ else 0
    have hw := memLp_designWeight_coordinate_sum mu group arm hgroup harm
      (supportedArmMark group arm Y a k) (hmark a k)
      (by
        exact (hY.indicator
          (Causalean.Stat.measurableSet_armGroupEvent group arm hgroup harm a k))) W
    convert hw using 1
    funext z
    unfold totalizedArmMean armMarkSum categoryCount categoryArmCount
    dsimp [W]
    have hgc : Causalean.Stat.groupCount Prod.fst Prod.snd
        (Causalean.Stat.sampleDesign group arm z) k =
        Causalean.Stat.groupCount group arm z k := rfl
    have hga : Causalean.Stat.groupArmCount Prod.fst Prod.snd
        (Causalean.Stat.sampleDesign group arm z) a k =
        Causalean.Stat.groupArmCount group arm z a k := rfl
    rw [hgc, hga]
    by_cases hp : 0 < Causalean.Stat.groupArmCount group arm z a k
    · rw [if_pos hp, if_pos hp]
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    · rw [if_neg hp, if_neg hp]
      simp
  have harmScore (a : Bool) :
      MemLp (fixedStratumArmScore (m := m) group arm Y H a) 2
        (Measure.pi (fun _ : Fin m ↦ mu)) := by
    unfold fixedStratumArmScore
    exact memLp_finsetSum H fun k _ ↦ hcellTerm a k
  exact (harmScore true).sub (harmScore false)

/-- [Measurable group and arm labels](hyp:hgroup,harm) and [cell centers bounded
in absolute value by the envelope](hyp:hcenterBound) imply that [the empirical
category-mass fluctuation has second moment at most the squared envelope divided
by the safe sample size, including for an empty sample](goal). -/
theorem integral_fixedStratumArmMassFluctuation_sq_le {m : Nat}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (group : Omega → kappa) (arm : Omega → Bool)
    (center : Bool → kappa → Real) (H : Finset kappa) (a : Bool) (M : Real)
    (hgroup : Measurable group) (harm : Measurable arm)
    (hcenterBound : ∀ k, |center a k| ≤ M) :
    ∫ z : Fin m → Omega,
        (fixedStratumArmMassFluctuation mu group arm center H a z) ^ 2
        ∂(Measure.pi (fun _ : Fin m => mu)) ≤
      M ^ 2 / safeSampleSize m := by
  classical
  by_cases hH : H.Nonempty
  · obtain ⟨k0, hk0⟩ := hH
    have hM : 0 ≤ M := (abs_nonneg (center a k0)).trans (hcenterBound k0)
    let xi : Omega → Real := fun omega ↦
      ∑ k ∈ H, (categoryEvent group k).indicator (fun _ ↦ center a k) omega
    have hxiMeas : Measurable xi := by
      dsimp [xi]
      apply Finset.measurable_sum
      intro k hk
      exact measurable_const.indicator
        (Causalean.Stat.measurableSet_groupEvent group hgroup k)
    have hxiBound (omega : Omega) : |xi omega| ≤ M := by
      by_cases hg : group omega ∈ H
      · rw [show xi omega = center a (group omega) by
          dsimp [xi]
          rw [Finset.sum_eq_single (group omega)]
          · simp [categoryEvent, Causalean.Stat.groupEvent]
          · intro k hk hne
            simp [categoryEvent, Causalean.Stat.groupEvent, hne.symm]
          · exact fun h ↦ (h hg).elim]
        exact hcenterBound (group omega)
      · rw [show xi omega = 0 by
          dsimp [xi]
          apply Finset.sum_eq_zero
          intro k hk
          have hne : group omega ≠ k := fun heq ↦ hg (heq ▸ hk)
          simp [categoryEvent, Causalean.Stat.groupEvent, hne]]
        simpa using hM
    have hxi : MemLp xi 2 mu :=
      MemLp.of_bound hxiMeas.aestronglyMeasurable M
        (Filter.Eventually.of_forall fun omega ↦ by
          simpa [Real.norm_eq_abs] using hxiBound omega)
    have hxiSq : ∫ omega, (xi omega) ^ 2 ∂mu ≤ M ^ 2 := by
      calc
        (∫ omega, (xi omega) ^ 2 ∂mu) ≤ ∫ _omega, M ^ 2 ∂mu := by
          apply integral_mono (hxi.integrable_sq) (integrable_const (M ^ 2))
          intro omega
          simpa only [sq_abs] using
            pow_le_pow_left₀ (abs_nonneg (xi omega)) (hxiBound omega) 2
        _ = M ^ 2 := by simp
    have hxiIntegral : (∫ omega, xi omega ∂mu) =
        ∑ k ∈ H, categoryMass mu group k * center a k := by
      dsimp [xi]
      rw [integral_finset_sum H]
      · apply Finset.sum_congr rfl
        intro k hk
        change (∫ omega,
          (Causalean.Stat.groupEvent group k).indicator
            (fun _ ↦ center a k) omega ∂mu) =
          (mu (Causalean.Stat.groupEvent group k)).toReal * center a k
        rw [integral_indicator
          (Causalean.Stat.measurableSet_groupEvent group hgroup k), setIntegral_const]
        simp [Measure.real, smul_eq_mul]
      · intro k hk
        exact (integrable_const (center a k)).indicator
          (Causalean.Stat.measurableSet_groupEvent group hgroup k)
    have hsample (z : Fin m → Omega) :
        (m : Real)⁻¹ * ∑ i, xi (z i) - ∫ omega, xi omega ∂mu =
          fixedStratumArmMassFluctuation mu group arm center H a z := by
      rw [hxiIntegral]
      unfold fixedStratumArmMassFluctuation
      have hemp : (m : Real)⁻¹ * ∑ i, xi (z i) =
            (m : Real)⁻¹ * ∑ k ∈ H,
              (categoryCount group arm z k : Real) * center a k := by
          congr 1
          dsimp [xi]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k hk
          unfold categoryCount Causalean.Stat.groupCount Causalean.Stat.groupArmCount
          simp only [Finset.card_filter, Nat.cast_add, Nat.cast_sum,
            Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
          rw [← Finset.sum_add_distrib, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          cases h : arm (z i) <;>
            by_cases hg : group (z i) = k <;>
              simp [categoryEvent, Causalean.Stat.groupEvent, Set.indicator, h, hg]
      calc
        (m : Real)⁻¹ * ∑ i, xi (z i) -
            ∑ k ∈ H, categoryMass mu group k * center a k =
            (∑ k ∈ H,
              (categoryCount group arm z k : Real) / (m : Real) * center a k) -
              ∑ k ∈ H, categoryMass mu group k * center a k := by
          rw [hemp, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ =
            ∑ k ∈ H,
              ((categoryCount group arm z k : Real) / (m : Real) -
                categoryMass mu group k) * center a k := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro k hk
          ring
    by_cases hm : m = 0
    · subst m
      have hmeanSq : (∫ omega, xi omega ∂mu) ^ 2 ≤
          ∫ omega, (xi omega) ^ 2 ∂mu := by
        have hv := ProbabilityTheory.variance_nonneg xi mu
        rw [ProbabilityTheory.variance_eq_sub hxi] at hv
        change 0 ≤ (∫ omega, (xi omega) ^ 2 ∂mu) -
          (∫ omega, xi omega ∂mu) ^ 2 at hv
        linarith
      unfold safeSampleSize
      norm_num
      change (∫ z : Fin 0 → Omega,
          (fixedStratumArmMassFluctuation mu group arm center H a z) ^ 2
          ∂(Measure.pi (fun _ : Fin 0 ↦ mu))) ≤ M ^ 2
      calc
        (∫ z : Fin 0 → Omega,
            (fixedStratumArmMassFluctuation mu group arm center H a z) ^ 2
            ∂(Measure.pi (fun _ : Fin 0 ↦ mu))) =
            ∫ _z : Fin 0 → Omega, (∫ omega, xi omega ∂mu) ^ 2
              ∂(Measure.pi (fun _ : Fin 0 ↦ mu)) := by
          apply integral_congr_ae
          filter_upwards [] with z
          rw [← hsample z]
          simp
        _ = (∫ omega, xi omega ∂mu) ^ 2 := by simp
        _ ≤ ∫ omega, (xi omega) ^ 2 ∂mu := hmeanSq
        _ ≤ M ^ 2 := hxiSq
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      calc
        (∫ z : Fin m → Omega,
            (fixedStratumArmMassFluctuation mu group arm center H a z) ^ 2
            ∂(Measure.pi (fun _ : Fin m ↦ mu))) =
            ∫ z : Fin m → Omega,
              ((m : Real)⁻¹ * ∑ i, xi (z i) - ∫ omega, xi omega ∂mu) ^ 2
              ∂(Measure.pi (fun _ : Fin m ↦ mu)) := by
          apply integral_congr_ae
          filter_upwards [] with z
          rw [hsample]
        _ ≤ (∫ omega, (xi omega) ^ 2 ∂mu) / (m : Real) :=
          Causalean.Mathlib.Probability.iid_mean_sq_le mu hmpos xi hxi
        _ ≤ M ^ 2 / (m : Real) := div_le_div_of_nonneg_right hxiSq (by positivity)
        _ = M ^ 2 / safeSampleSize m := by
          unfold safeSampleSize
          rw [max_eq_right (Nat.one_le_iff_ne_zero.mpr hm)]
  · have hH0 : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
    subst H
    simp [fixedStratumArmMassFluctuation]
    unfold safeSampleSize
    positivity

/-- [Measurable group and arm labels](hyp:hgroup,harm), [cell centers bounded in
absolute value by the envelope](hyp:hcenterBound), [a positive overlap
margin](hyp:hepsilon), and [arm mass at least that margin times category
mass](hyp:hoverlap) imply that [the normalized aggregate empty-arm remainder has
second moment bounded by a parametric diagonal term plus the squared
exponentially damped missing-arm envelope](goal). -/
theorem integral_fixedStratumArmMissingRemainder_sq_le {m : Nat}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (group : Omega → kappa) (arm : Omega → Bool)
    (center : Bool → kappa → Real) (H : Finset kappa) (a : Bool)
    (M epsilon : Real) (hgroup : Measurable group) (harm : Measurable arm)
    (hcenterBound : ∀ k, |center a k| ≤ M) (hepsilon : 0 < epsilon)
    (hoverlap : ∀ k, 0 < categoryMass mu group k →
      epsilon * categoryMass mu group k ≤ armCategoryMass mu group arm a k) :
    ∫ z : Fin m → Omega,
        (fixedStratumArmMissingRemainder group arm center H a z) ^ 2
        ∂(Measure.pi (fun _ : Fin m => mu)) ≤
      M ^ 2 * (1 / safeSampleSize m +
        (missingArmExponentialEnvelope mu group m epsilon H) ^ 2) := by
  exact integral_fixedStratumArmMissingRemainder_sq_le_aux mu group arm center H a
    M epsilon hgroup harm hcenterBound hepsilon hoverlap

/-- [Measurable group and arm labels and a measurable mark](hyp:hgroup,harm,hY),
[square-integrable supported residuals](hyp:hmem), [cellwise residual
centering](hyp:hcenter), [the stated residual second-moment envelope](hyp:hsq),
[bounded cell centers](hyp:hcenterBound), [a positive overlap
margin](hyp:hepsilon), and [arm mass at least that margin times category
mass](hyp:hoverlap) imply [a uniform one-arm fixed-set mean-squared-error bound
with an explicit exponentially damped missing-arm remainder](goal). -/
theorem integral_fixedStratumArm_error_sq_le_exponential {m : Nat}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (group : Omega → kappa) (arm : Omega → Bool) (Y : Omega → Real)
    (center : Bool → kappa → Real) (H : Finset kappa) (a : Bool)
    (M epsilon : Real) (hgroup : Measurable group) (harm : Measurable arm)
    (hY : Measurable Y)
    (hmem : ∀ k, MemLp (supportedArmResidual group arm Y center a k) 2 mu)
    (hcenter : ∀ k, ∫ omega in armCategoryEvent group arm a k,
      (Y omega - center a k) ∂mu = 0)
    (hsq : ∀ k, ∫ omega in armCategoryEvent group arm a k,
        (Y omega - center a k) ^ 2 ∂mu ≤
      armCategoryMass mu group arm a k * M ^ 2)
    (hcenterBound : ∀ k, |center a k| ≤ M) (hepsilon : 0 < epsilon)
    (hoverlap : ∀ k, 0 < categoryMass mu group k →
      epsilon * categoryMass mu group k ≤ armCategoryMass mu group arm a k) :
    ∫ z : Fin m → Omega,
        (fixedStratumArmScore group arm Y H a z -
          fixedStratumArmTarget mu group arm Y H a) ^ 2
        ∂(Measure.pi (fun _ : Fin m => mu)) ≤
      M ^ 2 *
        (8 * (∑ k ∈ H, categoryMass mu group k) /
            (safeSampleSize m * epsilon) +
          6 / safeSampleSize m +
          4 * (missingArmExponentialEnvelope mu group m epsilon H) ^ 2) := by
  -- Proof plan: identify the center target with the population target, rewrite
  -- by `fixedStratumArmScore_sub_centerTarget_decomposition`, and apply
  -- `(x+y-z)^2 ≤ 4x^2 + 2y^2 + 4z^2`.  Integrate using the three component
  -- bounds above and finish by nonnegative arithmetic, retaining the explicit
  -- missing-arm envelope.
  classical
  have hpositive : ∀ k ∈ H, 0 < categoryMass mu group k →
      0 < armCategoryMass mu group arm a k := by
    intro k hk hpk
    exact (mul_pos hepsilon hpk).trans_le (hoverlap k hpk)
  have htarget := fixedStratumArmCenterTarget_eq_target_of_measurable
    mu group arm Y center H a hgroup harm hmem hcenter hpositive
  have hscoreMem := fixedStratumArmScore_memLp_two (m := m)
    mu group arm Y center H a
    hgroup harm hY hmem
  have hmassMem := fixedStratumArmMassFluctuation_memLp_two (m := m)
    mu group arm center H a hgroup harm
  have hmissingMem := fixedStratumArmMissingRemainder_memLp_two (m := m)
    mu group arm center H a hgroup harm
  have hnoiseMem : MemLp
      (fixedStratumArmCenteredNoise (m := m) group arm Y center H a) 2
      (Measure.pi (fun _ : Fin m ↦ mu)) := by
    have hcomb := ((hscoreMem.sub (memLp_const
      (fixedStratumArmCenterTarget mu group H center a))).sub hmassMem).add hmissingMem
    convert hcomb using 1
    funext z
    change fixedStratumArmCenteredNoise group arm Y center H a z =
      (fixedStratumArmScore group arm Y H a z -
        fixedStratumArmCenterTarget mu group H center a) -
          fixedStratumArmMassFluctuation mu group arm center H a z +
            fixedStratumArmMissingRemainder group arm center H a z
    have hdecomp := fixedStratumArmScore_sub_centerTarget_decomposition
      mu group arm Y center H a z
    linarith
  have hnoise := integral_fixedStratumArmCenteredNoise_sq_le (m := m)
    mu group arm Y center H a M epsilon hgroup harm hY hmem hcenter hsq
      hepsilon hoverlap
  have hmass := integral_fixedStratumArmMassFluctuation_sq_le (m := m)
    mu group arm center H a M hgroup harm hcenterBound
  have hmissing := integral_fixedStratumArmMissingRemainder_sq_le (m := m)
    mu group arm center H a M epsilon hgroup harm hcenterBound hepsilon hoverlap
  have hpoint (z : Fin m → Omega) :
      (fixedStratumArmScore group arm Y H a z -
          fixedStratumArmTarget mu group arm Y H a) ^ 2 ≤
        4 * (fixedStratumArmCenteredNoise group arm Y center H a z) ^ 2 +
          2 * (fixedStratumArmMassFluctuation mu group arm center H a z) ^ 2 +
          4 * (fixedStratumArmMissingRemainder group arm center H a z) ^ 2 := by
    rw [← htarget,
      fixedStratumArmScore_sub_centerTarget_decomposition]
    nlinarith [sq_nonneg
        ((fixedStratumArmCenteredNoise group arm Y center H a z -
            fixedStratumArmMissingRemainder group arm center H a z) -
          fixedStratumArmMassFluctuation mu group arm center H a z),
      sq_nonneg
        (fixedStratumArmCenteredNoise group arm Y center H a z +
          fixedStratumArmMissingRemainder group arm center H a z)]
  calc
    (∫ z : Fin m → Omega,
        (fixedStratumArmScore group arm Y H a z -
          fixedStratumArmTarget mu group arm Y H a) ^ 2
        ∂(Measure.pi (fun _ : Fin m ↦ mu))) ≤
        ∫ z : Fin m → Omega,
          (4 * (fixedStratumArmCenteredNoise group arm Y center H a z) ^ 2 +
            2 * (fixedStratumArmMassFluctuation mu group arm center H a z) ^ 2 +
            4 * (fixedStratumArmMissingRemainder group arm center H a z) ^ 2)
          ∂(Measure.pi (fun _ : Fin m ↦ mu)) := by
      apply integral_mono
      · exact (hscoreMem.sub (memLp_const _)).integrable_sq
      · exact ((hnoiseMem.integrable_sq.const_mul 4).add
          (hmassMem.integrable_sq.const_mul 2)).add
            (hmissingMem.integrable_sq.const_mul 4)
      · exact hpoint
    _ = 4 * (∫ z : Fin m → Omega,
          (fixedStratumArmCenteredNoise group arm Y center H a z) ^ 2
          ∂(Measure.pi (fun _ : Fin m ↦ mu))) +
        2 * (∫ z : Fin m → Omega,
          (fixedStratumArmMassFluctuation mu group arm center H a z) ^ 2
          ∂(Measure.pi (fun _ : Fin m ↦ mu))) +
        4 * (∫ z : Fin m → Omega,
          (fixedStratumArmMissingRemainder group arm center H a z) ^ 2
          ∂(Measure.pi (fun _ : Fin m ↦ mu))) := by
      let fn : (Fin m → Omega) → Real := fun z ↦
        4 * (fixedStratumArmCenteredNoise group arm Y center H a z) ^ 2
      let ff : (Fin m → Omega) → Real := fun z ↦
        2 * (fixedStratumArmMassFluctuation mu group arm center H a z) ^ 2
      let fr : (Fin m → Omega) → Real := fun z ↦
        4 * (fixedStratumArmMissingRemainder group arm center H a z) ^ 2
      have hn4 : Integrable fn (Measure.pi (fun _ : Fin m ↦ mu)) := by
        simpa [fn] using hnoiseMem.integrable_sq.const_mul 4
      have hf2 : Integrable ff (Measure.pi (fun _ : Fin m ↦ mu)) := by
        simpa [ff] using hmassMem.integrable_sq.const_mul 2
      have hr4 : Integrable fr (Measure.pi (fun _ : Fin m ↦ mu)) := by
        simpa [fr] using hmissingMem.integrable_sq.const_mul 4
      change (∫ z : Fin m → Omega, ((fn + ff) + fr) z
          ∂(Measure.pi (fun _ : Fin m ↦ mu))) = _
      calc
        (∫ z : Fin m → Omega, ((fn + ff) + fr) z
            ∂(Measure.pi (fun _ : Fin m ↦ mu))) =
            (∫ z : Fin m → Omega, (fn + ff) z
              ∂(Measure.pi (fun _ : Fin m ↦ mu))) +
            ∫ z : Fin m → Omega, fr z
              ∂(Measure.pi (fun _ : Fin m ↦ mu)) :=
          integral_add (hn4.add hf2) hr4
        _ = ((∫ z : Fin m → Omega, fn z
                ∂(Measure.pi (fun _ : Fin m ↦ mu))) +
              ∫ z : Fin m → Omega, ff z
                ∂(Measure.pi (fun _ : Fin m ↦ mu))) +
            ∫ z : Fin m → Omega, fr z
              ∂(Measure.pi (fun _ : Fin m ↦ mu)) := by
          have hadd : (∫ z : Fin m → Omega, (fn + ff) z
                ∂(Measure.pi (fun _ : Fin m ↦ mu))) =
              (∫ z : Fin m → Omega, fn z
                ∂(Measure.pi (fun _ : Fin m ↦ mu))) +
              ∫ z : Fin m → Omega, ff z
                ∂(Measure.pi (fun _ : Fin m ↦ mu)) := by
            simpa only [Pi.add_apply] using integral_add hn4 hf2
          rw [hadd]
        _ = _ := by
          simp only [fn, ff, fr, integral_const_mul]
    _ ≤ 4 * (2 * M ^ 2 * (∑ k ∈ H, categoryMass mu group k) /
          (safeSampleSize m * epsilon)) +
        2 * (M ^ 2 / safeSampleSize m) +
        4 * (M ^ 2 * (1 / safeSampleSize m +
          (missingArmExponentialEnvelope mu group m epsilon H) ^ 2)) := by
      linarith
    _ = M ^ 2 *
        (8 * (∑ k ∈ H, categoryMass mu group k) /
            (safeSampleSize m * epsilon) +
          6 / safeSampleSize m +
          4 * (missingArmExponentialEnvelope mu group m epsilon H) ^ 2) := by
      ring

/-- [Measurable group and arm labels and a measurable mark](hyp:hgroup,harm,hY),
[square-integrable supported residuals](hyp:hmem), [cellwise residual
centering](hyp:hcenter), [the stated residual second-moment envelope](hyp:hsq),
[bounded cell centers](hyp:hcenterBound), [a positive overlap
margin](hyp:hepsilon), [arm mass at least that margin times category
mass](hyp:hoverlap), and [a deterministic lower bound on every selected
category mass](hyp:hp) imply [the boundary-safe one-arm mean-squared-error bound
with an inverse-polynomial missing-arm envelope](goal). -/
theorem integral_fixedStratumArm_error_sq_le {m : Nat}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (group : Omega → kappa) (arm : Omega → Bool) (Y : Omega → Real)
    (center : Bool → kappa → Real) (H : Finset kappa) (a : Bool)
    (M epsilon B : Real) (hgroup : Measurable group) (harm : Measurable arm)
    (hY : Measurable Y)
    (hmem : ∀ k, MemLp (supportedArmResidual group arm Y center a k) 2 mu)
    (hcenter : ∀ k, ∫ omega in armCategoryEvent group arm a k,
      (Y omega - center a k) ∂mu = 0)
    (hsq : ∀ k, ∫ omega in armCategoryEvent group arm a k,
        (Y omega - center a k) ^ 2 ∂mu ≤
      armCategoryMass mu group arm a k * M ^ 2)
    (hcenterBound : ∀ k, |center a k| ≤ M) (hepsilon : 0 < epsilon)
    (hoverlap : ∀ k, 0 < categoryMass mu group k →
      epsilon * categoryMass mu group k ≤ armCategoryMass mu group arm a k)
    (hp : ∀ k ∈ H, B ≤ categoryMass mu group k) :
    ∫ z : Fin m → Omega,
        (fixedStratumArmScore group arm Y H a z -
          fixedStratumArmTarget mu group arm Y H a) ^ 2
        ∂(Measure.pi (fun _ : Fin m => mu)) ≤
      M ^ 2 *
        (8 * (∑ k ∈ H, categoryMass mu group k) /
            (safeSampleSize m * epsilon) +
          6 / safeSampleSize m +
          4 * (lowerMassMissingEnvelope mu group m epsilon B H) ^ 2) := by
  -- Proof plan: apply the exponential one-arm theorem, then use
  -- `missingArmExponentialEnvelope_le_lowerMass`; prove both envelopes are
  -- nonnegative before squaring the comparison.
  classical
  have hbase := integral_fixedStratumArm_error_sq_le_exponential (m := m)
    mu group arm Y center H a M epsilon hgroup harm hY hmem hcenter hsq
      hcenterBound hepsilon hoverlap
  have henv := missingArmExponentialEnvelope_le_lowerMass
    mu group hgroup m epsilon B H hepsilon hp
  have hexp0 : 0 ≤ missingArmExponentialEnvelope mu group m epsilon H := by
    unfold missingArmExponentialEnvelope
    exact Finset.sum_nonneg fun k _ ↦
      mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le
  have hlower0 : 0 ≤ lowerMassMissingEnvelope mu group m epsilon B H := by
    unfold lowerMassMissingEnvelope
    dsimp only
    split_ifs with hD
    · exact div_nonneg (Nat.cast_nonneg _) hD.le
    · exact Finset.sum_nonneg fun k _ ↦ ENNReal.toReal_nonneg
  have hsqenv :
      (missingArmExponentialEnvelope mu group m epsilon H) ^ 2 ≤
        (lowerMassMissingEnvelope mu group m epsilon B H) ^ 2 :=
    pow_le_pow_left₀ hexp0 henv 2
  calc
    (∫ z : Fin m → Omega,
        (fixedStratumArmScore group arm Y H a z -
          fixedStratumArmTarget mu group arm Y H a) ^ 2
        ∂(Measure.pi (fun _ : Fin m ↦ mu))) ≤
      M ^ 2 *
        (8 * (∑ k ∈ H, categoryMass mu group k) /
            (safeSampleSize m * epsilon) +
          6 / safeSampleSize m +
          4 * (missingArmExponentialEnvelope mu group m epsilon H) ^ 2) := hbase
    _ ≤ M ^ 2 *
        (8 * (∑ k ∈ H, categoryMass mu group k) /
            (safeSampleSize m * epsilon) +
          6 / safeSampleSize m +
          4 * (lowerMassMissingEnvelope mu group m epsilon B H) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg M)
      linarith

/-- [Measurable group and arm labels and a measurable mark](hyp:hgroup,harm,hY),
[square-integrable supported residuals in both arms](hyp:hmem), [cellwise
residual centering](hyp:hcenter), [the stated residual second-moment
envelope](hyp:hsq), [bounded cell centers](hyp:hcenterBound), [a positive
overlap margin](hyp:hepsilon), [both arm masses at least that margin times
category mass](hyp:hoverlap), and [a deterministic lower bound on every
selected category mass](hyp:hp) imply that [the treated-minus-control fixed-set
score obeys the boundary-safe mean-squared-error bound at the same parametric
and missing-arm scale, up to the universal two-arm factor](goal). -/
theorem integral_fixedStratumMarkedRatio_error_sq_le {m : Nat}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (group : Omega → kappa) (arm : Omega → Bool) (Y : Omega → Real)
    (center : Bool → kappa → Real) (H : Finset kappa)
    (M epsilon B : Real) (hgroup : Measurable group) (harm : Measurable arm)
    (hY : Measurable Y)
    (hmem : ∀ a k, MemLp (supportedArmResidual group arm Y center a k) 2 mu)
    (hcenter : ∀ a k, ∫ omega in armCategoryEvent group arm a k,
      (Y omega - center a k) ∂mu = 0)
    (hsq : ∀ a k, ∫ omega in armCategoryEvent group arm a k,
        (Y omega - center a k) ^ 2 ∂mu ≤
      armCategoryMass mu group arm a k * M ^ 2)
    (hcenterBound : ∀ a k, |center a k| ≤ M) (hepsilon : 0 < epsilon)
    (hoverlap : ∀ k, 0 < categoryMass mu group k → ∀ a,
      epsilon * categoryMass mu group k ≤ armCategoryMass mu group arm a k)
    (hp : ∀ k ∈ H, B ≤ categoryMass mu group k) :
    ∫ z : Fin m → Omega,
        (fixedStratumMarkedRatio group arm Y H z -
          fixedStratumMarkedTarget mu group arm Y H) ^ 2
        ∂(Measure.pi (fun _ : Fin m => mu)) ≤
      4 * M ^ 2 *
        (8 * (∑ k ∈ H, categoryMass mu group k) /
            (safeSampleSize m * epsilon) +
          6 / safeSampleSize m +
          4 * (lowerMassMissingEnvelope mu group m epsilon B H) ^ 2) := by
  -- Proof plan: write the signed error as the treated arm error minus the
  -- control arm error, use `(x-y)^2 ≤ 2x^2+2y^2`, integrate, and invoke the
  -- one-arm lower-mass theorem twice; the two factor-`2` contributions give
  -- the advertised universal factor `4`.
  classical
  have ht := integral_fixedStratumArm_error_sq_le (m := m)
    mu group arm Y center H true M epsilon B hgroup harm hY (hmem true)
      (hcenter true) (hsq true) (hcenterBound true) hepsilon
      (fun k hk ↦ hoverlap k hk true) hp
  have hf := integral_fixedStratumArm_error_sq_le (m := m)
    mu group arm Y center H false M epsilon B hgroup harm hY (hmem false)
      (hcenter false) (hsq false) (hcenterBound false) hepsilon
      (fun k hk ↦ hoverlap k hk false) hp
  let et : (Fin m → Omega) → Real := fun z ↦
    fixedStratumArmScore group arm Y H true z -
      fixedStratumArmTarget mu group arm Y H true
  let ef : (Fin m → Omega) → Real := fun z ↦
    fixedStratumArmScore group arm Y H false z -
      fixedStratumArmTarget mu group arm Y H false
  have htMem : MemLp et 2 (Measure.pi (fun _ : Fin m ↦ mu)) := by
    exact (fixedStratumArmScore_memLp_two (m := m) mu group arm Y center H true
      hgroup harm hY (hmem true)).sub (memLp_const _)
  have hfMem : MemLp ef 2 (Measure.pi (fun _ : Fin m ↦ mu)) := by
    exact (fixedStratumArmScore_memLp_two (m := m) mu group arm Y center H false
      hgroup harm hY (hmem false)).sub (memLp_const _)
  have hpoint (z : Fin m → Omega) :
      (fixedStratumMarkedRatio group arm Y H z -
          fixedStratumMarkedTarget mu group arm Y H) ^ 2 ≤
        2 * (et z) ^ 2 + 2 * (ef z) ^ 2 := by
    have heq : fixedStratumMarkedRatio group arm Y H z -
        fixedStratumMarkedTarget mu group arm Y H = et z - ef z := by
      simp only [et, ef, fixedStratumMarkedRatio, fixedStratumMarkedTarget]
      ring
    rw [heq]
    nlinarith [sq_nonneg (et z + ef z)]
  have ht2 : Integrable (fun z ↦ 2 * (et z) ^ 2)
      (Measure.pi (fun _ : Fin m ↦ mu)) := htMem.integrable_sq.const_mul 2
  have hf2 : Integrable (fun z ↦ 2 * (ef z) ^ 2)
      (Measure.pi (fun _ : Fin m ↦ mu)) := hfMem.integrable_sq.const_mul 2
  calc
    (∫ z : Fin m → Omega,
        (fixedStratumMarkedRatio group arm Y H z -
          fixedStratumMarkedTarget mu group arm Y H) ^ 2
        ∂(Measure.pi (fun _ : Fin m ↦ mu))) ≤
      ∫ z : Fin m → Omega, (2 * (et z) ^ 2 + 2 * (ef z) ^ 2)
        ∂(Measure.pi (fun _ : Fin m ↦ mu)) := by
      apply integral_mono
      · have hmarked := fixedStratumMarkedRatio_memLp_two (m := m)
          mu group arm Y center H hgroup harm hY hmem
        exact (hmarked.sub (memLp_const _)).integrable_sq
      · exact ht2.add hf2
      · exact hpoint
    _ = 2 * (∫ z : Fin m → Omega, (et z) ^ 2
          ∂(Measure.pi (fun _ : Fin m ↦ mu))) +
        2 * (∫ z : Fin m → Omega, (ef z) ^ 2
          ∂(Measure.pi (fun _ : Fin m ↦ mu))) := by
      rw [integral_add ht2 hf2, integral_const_mul, integral_const_mul]
    _ ≤ 2 * (M ^ 2 *
          (8 * (∑ k ∈ H, categoryMass mu group k) /
              (safeSampleSize m * epsilon) +
            6 / safeSampleSize m +
            4 * (lowerMassMissingEnvelope mu group m epsilon B H) ^ 2)) +
        2 * (M ^ 2 *
          (8 * (∑ k ∈ H, categoryMass mu group k) /
              (safeSampleSize m * epsilon) +
            6 / safeSampleSize m +
            4 * (lowerMassMissingEnvelope mu group m epsilon B H) ^ 2)) := by
      change 2 * (∫ z : Fin m → Omega,
          (fixedStratumArmScore group arm Y H true z -
            fixedStratumArmTarget mu group arm Y H true) ^ 2
          ∂(Measure.pi (fun _ : Fin m ↦ mu))) +
        2 * (∫ z : Fin m → Omega,
          (fixedStratumArmScore group arm Y H false z -
            fixedStratumArmTarget mu group arm Y H false) ^ 2
          ∂(Measure.pi (fun _ : Fin m ↦ mu))) ≤ _
      linarith
    _ = 4 * M ^ 2 *
        (8 * (∑ k ∈ H, categoryMass mu group k) /
            (safeSampleSize m * epsilon) +
          6 / safeSampleSize m +
          4 * (lowerMassMissingEnvelope mu group m epsilon B H) ^ 2) := by
      ring

end Causalean.Stat.FiniteStratumMarkedRatioMse
