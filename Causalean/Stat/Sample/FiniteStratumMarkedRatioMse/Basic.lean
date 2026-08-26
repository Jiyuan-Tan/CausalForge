/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Sample.OccupancyWeightedMean.Basic

/-!
# Fixed finite-stratum marked ratio statistics

This module defines zero-safe empirical arm means, their occupancy-weighted
fixed-set scores, the corresponding population quantities, and the exact
centered-noise/mass-fluctuation/missing-arm decomposition.  Empty samples,
empty cells, and zero population cell masses are totalized by the definitions.
-/

namespace Causalean.Stat.FiniteStratumMarkedRatioMse

open MeasureTheory
open scoped BigOperators ENNReal

variable {Omega kappa : Type*} [MeasurableSpace Omega]
  [Fintype kappa] [DecidableEq kappa]
  [MeasurableSpace kappa] [MeasurableSingletonClass kappa]

/-- The safe real sample size is one at an empty sample and otherwise equals
the ordinary sample size. -/
def safeSampleSize (m : Nat) : Real := ((max 1 m : Nat) : Real)

/-- The empirical arm/category count is the number of coordinates with the
specified Boolean arm and finite category. -/
def categoryArmCount {m : Nat} (group : Omega → kappa) (arm : Omega → Bool)
    (z : Fin m → Omega) (a : Bool) (k : kappa) : Nat :=
  Causalean.Stat.groupArmCount group arm z a k

/-- The empirical category count includes both Boolean arms. -/
def categoryCount {m : Nat} (group : Omega → kappa) (arm : Omega → Bool)
    (z : Fin m → Omega) (k : kappa) : Nat :=
  Causalean.Stat.groupCount group arm z k

/-- The arm/category event contains observations with the requested arm and
category labels. -/
def armCategoryEvent (group : Omega → kappa) (arm : Omega → Bool)
    (a : Bool) (k : kappa) : Set Omega :=
  Causalean.Stat.armGroupEvent group arm a k

/-- The category event contains observations with the requested category,
irrespective of arm. -/
def categoryEvent (group : Omega → kappa) (k : kappa) : Set Omega :=
  Causalean.Stat.groupEvent group k

/-- The population category mass is the real mass of the category event. -/
noncomputable def categoryMass (mu : Measure Omega) (group : Omega → kappa)
    (k : kappa) : Real :=
  (mu (categoryEvent group k)).toReal

/-- The population arm/category mass is the real mass of the joint label
event. -/
noncomputable def armCategoryMass (mu : Measure Omega) (group : Omega → kappa)
    (arm : Omega → Bool) (a : Bool) (k : kappa) : Real :=
  (mu (armCategoryEvent group arm a k)).toReal

/-- The supported mark equals the real mark on one arm/category cell and zero
off that cell. -/
noncomputable def supportedArmMark (group : Omega → kappa) (arm : Omega → Bool)
    (Y : Omega → Real) (a : Bool) (k : kappa) : Omega → Real :=
  (armCategoryEvent group arm a k).indicator Y

/-- The empirical arm/category mark sum adds the supported mark over all
sample coordinates. -/
noncomputable def armMarkSum {m : Nat} (group : Omega → kappa)
    (arm : Omega → Bool) (Y : Omega → Real) (z : Fin m → Omega)
    (a : Bool) (k : kappa) : Real :=
  ∑ i, supportedArmMark group arm Y a k (z i)

/-- The totalized empirical arm mean is the mark sum divided by its positive
arm/category count, and is zero when that count is empty. -/
noncomputable def totalizedArmMean {m : Nat} (group : Omega → kappa)
    (arm : Omega → Bool) (Y : Omega → Real) (z : Fin m → Omega)
    (a : Bool) (k : kappa) : Real :=
  if 0 < categoryArmCount group arm z a k then
    (categoryArmCount group arm z a k : Real)⁻¹ * armMarkSum group arm Y z a k
  else 0

/-- The population arm/category mark mean is the cell mark integral divided
by its positive cell mass, and is zero on a zero-mass cell. -/
noncomputable def populationArmMean (mu : Measure Omega) (group : Omega → kappa)
    (arm : Omega → Bool) (Y : Omega → Real) (a : Bool) (k : kappa) : Real :=
  if 0 < armCategoryMass mu group arm a k then
    (armCategoryMass mu group arm a k)⁻¹ *
      ∫ omega in armCategoryEvent group arm a k, Y omega ∂mu
  else 0

/-- The fixed-set single-arm score weights each zero-safe empirical arm mean
by its empirical category occupancy divided by the nominal sample size. -/
noncomputable def fixedStratumArmScore {m : Nat} (group : Omega → kappa)
    (arm : Omega → Bool) (Y : Omega → Real) (H : Finset kappa)
    (a : Bool) (z : Fin m → Omega) : Real :=
  ∑ k ∈ H, (categoryCount group arm z k : Real) / (m : Real) *
    totalizedArmMean group arm Y z a k

/-- The fixed-set marked ratio score is the treated single-arm score minus the
control single-arm score. -/
noncomputable def fixedStratumMarkedRatio {m : Nat} (group : Omega → kappa)
    (arm : Omega → Bool) (Y : Omega → Real) (H : Finset kappa)
    (z : Fin m → Omega) : Real :=
  fixedStratumArmScore group arm Y H true z -
    fixedStratumArmScore group arm Y H false z

/-- The population fixed-set single-arm target weights conditional arm means
by population category masses. -/
noncomputable def fixedStratumArmTarget (mu : Measure Omega) (group : Omega → kappa)
    (arm : Omega → Bool) (Y : Omega → Real) (H : Finset kappa)
    (a : Bool) : Real :=
  ∑ k ∈ H, categoryMass mu group k * populationArmMean mu group arm Y a k

/-- The population fixed-set marked target is the treated arm target minus
the control arm target. -/
noncomputable def fixedStratumMarkedTarget (mu : Measure Omega)
    (group : Omega → kappa) (arm : Omega → Bool) (Y : Omega → Real)
    (H : Finset kappa) : Real :=
  fixedStratumArmTarget mu group arm Y H true -
    fixedStratumArmTarget mu group arm Y H false

/-- The center-weighted population target is the auxiliary form used by the
residual decomposition. -/
noncomputable def fixedStratumArmCenterTarget (mu : Measure Omega)
    (group : Omega → kappa) (H : Finset kappa) (center : Bool → kappa → Real)
    (a : Bool) : Real :=
  ∑ k ∈ H, categoryMass mu group k * center a k

/-- The centered arm/category residual is the mark minus its supplied cell
center, supported on that cell. -/
noncomputable def supportedArmResidual (group : Omega → kappa)
    (arm : Omega → Bool) (Y : Omega → Real) (center : Bool → kappa → Real)
    (a : Bool) (k : kappa) : Omega → Real :=
  Causalean.Stat.supportedArmGroupResidual group arm Y center a k

/-- The totalized empirical residual mean is zero on an empty arm/category
cell and otherwise averages its supported centered residuals. -/
noncomputable def totalizedArmResidualMean {m : Nat} (group : Omega → kappa)
    (arm : Omega → Bool) (Y : Omega → Real) (center : Bool → kappa → Real)
    (z : Fin m → Omega) (a : Bool) (k : kappa) : Real :=
  Causalean.Stat.armResidualMean group arm Y center z a k

/-- A missing-arm count is the category occupancy when the requested empirical
arm count is zero, and is zero otherwise. -/
noncomputable def missingArmCount {m : Nat} (group : Omega → kappa)
    (arm : Omega → Bool) (z : Fin m → Omega) (a : Bool) (k : kappa) : Nat :=
  if categoryArmCount group arm z a k = 0 then categoryCount group arm z k else 0

/-- The fixed-arm centered noise is the occupancy-weighted sum of totalized
cell residual means. -/
noncomputable def fixedStratumArmCenteredNoise {m : Nat} (group : Omega → kappa)
    (arm : Omega → Bool) (Y : Omega → Real) (center : Bool → kappa → Real)
    (H : Finset kappa) (a : Bool) (z : Fin m → Omega) : Real :=
  ∑ k ∈ H, (categoryCount group arm z k : Real) / (m : Real) *
    totalizedArmResidualMean group arm Y center z a k

/-- The fixed-arm missing remainder is the normalized sum of cell centers
times category occupancies whose requested arm is absent. -/
noncomputable def fixedStratumArmMissingRemainder {m : Nat}
    (group : Omega → kappa) (arm : Omega → Bool)
    (center : Bool → kappa → Real) (H : Finset kappa) (a : Bool)
    (z : Fin m → Omega) : Real :=
  ∑ k ∈ H, center a k * (missingArmCount group arm z a k : Real) / (m : Real)

/-- The empirical-mass fluctuation is the centered sample category weighting
of the supplied arm/category centers. -/
noncomputable def fixedStratumArmMassFluctuation {m : Nat} (mu : Measure Omega)
    (group : Omega → kappa) (arm : Omega → Bool)
    (center : Bool → kappa → Real) (H : Finset kappa) (a : Bool)
    (z : Fin m → Omega) : Real :=
  ∑ k ∈ H,
    ((categoryCount group arm z k : Real) / (m : Real) - categoryMass mu group k) *
      center a k

/-- [Measurable group and arm labels](hyp:hgroup,harm) make [every fixed
empirical arm/category count measurable on the product sample space](goal). -/
theorem measurable_categoryArmCount {m : Nat} (group : Omega → kappa)
    (arm : Omega → Bool) (hgroup : Measurable group) (harm : Measurable arm)
    (a : Bool) (k : kappa) :
    Measurable (fun z : Fin m → Omega => categoryArmCount group arm z a k) := by
  exact Causalean.Stat.measurable_groupArmCount group arm hgroup harm a k

/-- [Measurable group and arm labels](hyp:hgroup,harm) make [every fixed
empirical category count measurable on the product sample space](goal). -/
theorem measurable_categoryCount {m : Nat} (group : Omega → kappa)
    (arm : Omega → Bool) (hgroup : Measurable group) (harm : Measurable arm)
    (k : kappa) : Measurable (fun z : Fin m → Omega => categoryCount group arm z k) := by
  exact Causalean.Stat.measurable_groupCount group arm hgroup harm k

/-- [Measurable group and arm labels and a measurable mark](hyp:hgroup,harm,hY)
make [every empirical arm/category mark sum measurable](goal). -/
theorem measurable_armMarkSum {m : Nat} (group : Omega → kappa)
    (arm : Omega → Bool) (Y : Omega → Real) (hgroup : Measurable group)
    (harm : Measurable arm) (hY : Measurable Y) (a : Bool) (k : kappa) :
    Measurable (fun z : Fin m → Omega => armMarkSum group arm Y z a k) := by
  classical
  unfold armMarkSum supportedArmMark
  apply Finset.measurable_sum
  intro i hi
  exact (hY.indicator
    (Causalean.Stat.measurableSet_armGroupEvent group arm hgroup harm a k)).comp
      (measurable_pi_apply i : Measurable fun z : Fin m → Omega => z i)

/-- [Measurable group and arm labels and a measurable mark](hyp:hgroup,harm,hY)
make [every totalized empirical arm/category mark mean measurable, including
at zero count](goal). -/
theorem measurable_totalizedArmMean {m : Nat} (group : Omega → kappa)
    (arm : Omega → Bool) (Y : Omega → Real) (hgroup : Measurable group)
    (harm : Measurable arm) (hY : Measurable Y) (a : Bool) (k : kappa) :
    Measurable (fun z : Fin m → Omega => totalizedArmMean group arm Y z a k) := by
  have hcount := measurable_categoryArmCount (m := m) group arm hgroup harm a k
  have hpos : MeasurableSet {z : Fin m → Omega |
      0 < categoryArmCount group arm z a k} :=
    measurableSet_lt measurable_const hcount
  have hcast : Measurable (fun z : Fin m → Omega =>
      (categoryArmCount group arm z a k : Real)) :=
    (Measurable.of_discrete : Measurable fun n : Nat => (n : Real)).comp hcount
  unfold totalizedArmMean
  exact Measurable.ite hpos
    (hcast.inv.mul (measurable_armMarkSum group arm Y hgroup harm hY a k))
    measurable_const

/-- [Measurable group and arm labels and a measurable mark](hyp:hgroup,harm,hY)
make [the fixed-set marked ratio score measurable](goal). -/
theorem measurable_fixedStratumMarkedRatio {m : Nat} (group : Omega → kappa)
    (arm : Omega → Bool) (Y : Omega → Real) (H : Finset kappa)
    (hgroup : Measurable group) (harm : Measurable arm) (hY : Measurable Y) :
    Measurable (fixedStratumMarkedRatio (m := m) group arm Y H) := by
  classical
  have harmScore : ∀ a : Bool,
      Measurable (fixedStratumArmScore (m := m) group arm Y H a) := by
    intro a
    unfold fixedStratumArmScore
    apply Finset.measurable_sum
    intro k hk
    have hcount := measurable_categoryCount (m := m) group arm hgroup harm k
    have hcast : Measurable (fun z : Fin m → Omega =>
        (categoryCount group arm z k : Real)) :=
      (Measurable.of_discrete : Measurable fun n : Nat => (n : Real)).comp hcount
    exact (hcast.div_const (m : Real)).mul
      (measurable_totalizedArmMean group arm Y hgroup harm hY a k)
  unfold fixedStratumMarkedRatio
  exact (harmScore true).sub (harmScore false)

/-- [Measurable group and arm labels](hyp:hgroup,harm) make [each missing-arm
category count measurable](goal). -/
theorem measurable_missingArmCount {m : Nat} (group : Omega → kappa)
    (arm : Omega → Bool) (hgroup : Measurable group) (harm : Measurable arm)
    (a : Bool) (k : kappa) :
    Measurable (fun z : Fin m → Omega => missingArmCount group arm z a k) := by
  have harmCount := measurable_categoryArmCount (m := m) group arm hgroup harm a k
  have hzero : MeasurableSet {z : Fin m → Omega |
      categoryArmCount group arm z a k = 0} :=
    measurableSet_eq_fun harmCount measurable_const
  unfold missingArmCount
  exact Measurable.ite hzero
    (measurable_categoryCount (m := m) group arm hgroup harm k) measurable_const

private lemma armMarkSum_eq_residualSum_add_count_mul {m : Nat}
    (group : Omega → kappa) (arm : Omega → Bool) (Y : Omega → Real)
    (center : Bool → kappa → Real) (z : Fin m → Omega) (a : Bool) (k : kappa) :
    armMarkSum group arm Y z a k =
      Causalean.Stat.armResidualSum group arm Y center z a k +
        (categoryArmCount group arm z a k : Real) * center a k := by
  classical
  simp only [armMarkSum, supportedArmMark, Causalean.Stat.armResidualSum,
    Causalean.Stat.supportedArmGroupResidual, categoryArmCount,
    Causalean.Stat.groupArmCount]
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_mul]
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : group (z i) = k ∧ arm (z i) = a <;>
    simp [armCategoryEvent, Causalean.Stat.armGroupEvent,
      Causalean.Stat.armGroupResidual, h]

private lemma armCell_sub_center_decomposition {m : Nat}
    (mu : Measure Omega) (group : Omega → kappa) (arm : Omega → Bool)
    (Y : Omega → Real) (center : Bool → kappa → Real)
    (a : Bool) (k : kappa) (z : Fin m → Omega) :
    (categoryCount group arm z k : Real) / (m : Real) *
          totalizedArmMean group arm Y z a k -
        categoryMass mu group k * center a k =
      (categoryCount group arm z k : Real) / (m : Real) *
          totalizedArmResidualMean group arm Y center z a k +
        ((categoryCount group arm z k : Real) / (m : Real) -
          categoryMass mu group k) * center a k -
        center a k * (missingArmCount group arm z a k : Real) / (m : Real) := by
  by_cases hzero : categoryArmCount group arm z a k = 0
  · have hz : Causalean.Stat.groupArmCount group arm z a k = 0 := by
      simpa [categoryArmCount] using hzero
    simp [totalizedArmMean, totalizedArmResidualMean,
      Causalean.Stat.armResidualMean, missingArmCount, hzero, hz]
    ring
  · have hpos : 0 < categoryArmCount group arm z a k := Nat.pos_of_ne_zero hzero
    have hcast : (categoryArmCount group arm z a k : Real) ≠ 0 := by
      exact_mod_cast hzero
    have hpbase : 0 < Causalean.Stat.groupArmCount group arm z a k := by
      simpa [categoryArmCount] using hpos
    have hcastBase : (Causalean.Stat.groupArmCount group arm z a k : Real) ≠ 0 := by
      simpa [categoryArmCount] using hcast
    simp only [totalizedArmMean]
    rw [if_pos hpos]
    rw [armMarkSum_eq_residualSum_add_count_mul group arm Y center z a k]
    simp only [totalizedArmResidualMean, Causalean.Stat.armResidualMean]
    rw [if_pos hpbase]
    simp [missingArmCount, hzero]
    simp only [categoryArmCount]
    field_simp [hcast, hcastBase]
    ring

/-- [The single-arm empirical score error around a supplied center target is
exactly centered ratio noise plus empirical-mass fluctuation minus the explicit
missing-arm remainder](goal). -/
theorem fixedStratumArmScore_sub_centerTarget_decomposition {m : Nat}
    (mu : Measure Omega) (group : Omega → kappa) (arm : Omega → Bool)
    (Y : Omega → Real) (center : Bool → kappa → Real) (H : Finset kappa)
    (a : Bool) (z : Fin m → Omega) :
    fixedStratumArmScore group arm Y H a z -
        fixedStratumArmCenterTarget mu group H center a =
      fixedStratumArmCenteredNoise group arm Y center H a z +
        fixedStratumArmMassFluctuation mu group arm center H a z -
          fixedStratumArmMissingRemainder group arm center H a z := by
  classical
  unfold fixedStratumArmScore fixedStratumArmCenterTarget
    fixedStratumArmCenteredNoise fixedStratumArmMassFluctuation
    fixedStratumArmMissingRemainder
  rw [← Finset.sum_sub_distrib]
  calc
    ∑ k ∈ H,
        ((categoryCount group arm z k : Real) / (m : Real) *
            totalizedArmMean group arm Y z a k -
          categoryMass mu group k * center a k) =
        ∑ k ∈ H,
          ((categoryCount group arm z k : Real) / (m : Real) *
              totalizedArmResidualMean group arm Y center z a k +
            ((categoryCount group arm z k : Real) / (m : Real) -
              categoryMass mu group k) * center a k -
            center a k * (missingArmCount group arm z a k : Real) / (m : Real)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact armCell_sub_center_decomposition mu group arm Y center a k z
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- [Measurable group and arm labels](hyp:hgroup,harm), [square-integrable
supported residuals](hyp:hmem), [cellwise residual centering](hyp:hcenter), and
[positive arm mass in every selected positive-mass category](hyp:hpositive)
ensure that [the center-weighted target equals the population arm target](goal). -/
theorem fixedStratumArmCenterTarget_eq_target
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
  classical
  unfold fixedStratumArmCenterTarget fixedStratumArmTarget
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hp : 0 < categoryMass mu group k
  · have hq := hpositive k hk hp
    have hcell : MeasurableSet (armCategoryEvent group arm a k) :=
      Causalean.Stat.measurableSet_armGroupEvent group arm hgroup harm a k
    have hres : IntegrableOn (fun omega ↦ Y omega - center a k)
        (armCategoryEvent group arm a k) mu := by
      apply (integrable_indicator_iff hcell).mp
      change Integrable (supportedArmResidual group arm Y center a k) mu
      exact (hmem k).integrable (by norm_num)
    have hYint : IntegrableOn Y (armCategoryEvent group arm a k) mu := by
      have := hres.add (integrableOn_const (C := center a k))
      exact this.congr (Filter.Eventually.of_forall fun omega ↦ sub_add_cancel _ _)
    have heq : ∫ omega in armCategoryEvent group arm a k, Y omega ∂mu =
        armCategoryMass mu group arm a k * center a k := by
      have hz := hcenter k
      rw [integral_sub hYint (integrableOn_const (C := center a k)),
        setIntegral_const] at hz
      change (∫ omega in armCategoryEvent group arm a k, Y omega ∂mu) -
        armCategoryMass mu group arm a k * center a k = 0 at hz
      linarith
    unfold populationArmMean
    rw [if_pos hq, heq]
    field_simp [hq.ne']
  · have hp0 : categoryMass mu group k = 0 :=
      le_antisymm (le_of_not_gt hp) ENNReal.toReal_nonneg
    rw [hp0]
    simp

end Causalean.Stat.FiniteStratumMarkedRatioMse
