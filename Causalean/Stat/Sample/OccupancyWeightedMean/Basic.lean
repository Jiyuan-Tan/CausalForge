/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Sample.PiTransport
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Occupancy-weighted residual means: design statistics

This module defines totalized group/arm counts and residual sample means for a
finite product sample.  Every zero-count boundary is part of the definition,
including the completely empty sample and an empty group type.  It also exposes
the measurability API needed to integrate the statistics under a product law.
-/

namespace Causalean.Stat

open MeasureTheory
open scoped BigOperators ENNReal

variable {Omega kappa : Type*} [MeasurableSpace Omega]
  [Fintype kappa] [DecidableEq kappa]
  [MeasurableSpace kappa] [MeasurableSingletonClass kappa]

/-- The arm/group event consists of observations having the requested finite
group label and Boolean arm label. -/
def armGroupEvent (group : Omega -> kappa) (arm : Omega -> Bool)
    (a : Bool) (k : kappa) : Set Omega :=
  {omega | group omega = k ∧ arm omega = a}

/-- The group event consists of observations having the requested finite group
label, irrespective of arm. -/
def groupEvent (group : Omega -> kappa) (k : kappa) : Set Omega :=
  {omega | group omega = k}

/-- The residual at an arm/group label is the outcome minus its supplied
arm/group center. -/
def armGroupResidual (Y : Omega -> Real) (center : Bool -> kappa -> Real)
    (a : Bool) (k : kappa) (omega : Omega) : Real :=
  Y omega - center a k

/-- The supported residual equals the arm/group residual on its own label event
and is zero elsewhere. -/
noncomputable def supportedArmGroupResidual (group : Omega -> kappa) (arm : Omega -> Bool)
    (Y : Omega -> Real) (center : Bool -> kappa -> Real)
    (a : Bool) (k : kappa) : Omega -> Real :=
  (armGroupEvent group arm a k).indicator (armGroupResidual Y center a k)

/-- The finite design records only the group and arm label of each sample
coordinate. -/
def sampleDesign {n : Nat} (group : Omega -> kappa) (arm : Omega -> Bool)
    (z : Fin n -> Omega) : Fin n -> kappa × Bool :=
  fun i => (group (z i), arm (z i))

/-- The arm/group count is the number of sample coordinates with both the
requested group and requested arm. -/
def groupArmCount {n : Nat} (group : Omega -> kappa) (arm : Omega -> Bool)
    (z : Fin n -> Omega) (a : Bool) (k : kappa) : Nat :=
  (Finset.univ.filter fun i => group (z i) = k ∧ arm (z i) = a).card

/-- The group count is the sum of its control and treated arm counts. -/
def groupCount {n : Nat} (group : Omega -> kappa) (arm : Omega -> Bool)
    (z : Fin n -> Omega) (k : kappa) : Nat :=
  groupArmCount group arm z false k + groupArmCount group arm z true k

/-- A sample group is usable exactly when both of its empirical arm counts are
positive. -/
def usableGroup {n : Nat} (group : Omega -> kappa) (arm : Omega -> Bool)
    (z : Fin n -> Omega) (k : kappa) : Prop :=
  0 < groupArmCount group arm z false k ∧
    0 < groupArmCount group arm z true k

/-- The usable-group total is the total empirical occupancy of groups having
both arms represented. -/
noncomputable def usableGroupTotal {n : Nat} (group : Omega -> kappa) (arm : Omega -> Bool)
    (z : Fin n -> Omega) : Nat := by
  classical
  exact ∑ k, if usableGroup group arm z k then groupCount group arm z k else 0

/-- The residual sum in an arm/group cell adds only coordinates belonging to
that cell. -/
noncomputable def armResidualSum {n : Nat} (group : Omega -> kappa) (arm : Omega -> Bool)
    (Y : Omega -> Real) (center : Bool -> kappa -> Real)
    (z : Fin n -> Omega) (a : Bool) (k : kappa) : Real :=
  ∑ i, supportedArmGroupResidual group arm Y center a k (z i)

/-- The totalized arm residual mean is the cell residual sum divided by its
count when that count is positive, and zero when the count is zero. -/
noncomputable def armResidualMean {n : Nat} (group : Omega -> kappa) (arm : Omega -> Bool)
    (Y : Omega -> Real) (center : Bool -> kappa -> Real)
    (z : Fin n -> Omega) (a : Bool) (k : kappa) : Real :=
  if 0 < groupArmCount group arm z a k then
    (groupArmCount group arm z a k : Real)⁻¹ *
      armResidualSum group arm Y center z a k
  else 0

/-- The occupancy-weighted residual statistic averages, over usable groups,
each group occupancy times the treated-minus-control residual mean.  It is zero
when no group is usable.  The law argument fixes the intended public API but
does not alter this sample statistic. -/
noncomputable def occupancyWeightedResidual {n : Nat} (_mu : Measure Omega)
    (group : Omega -> kappa) (arm : Omega -> Bool) (Y : Omega -> Real)
    (center : Bool -> kappa -> Real) (z : Fin n -> Omega) : Real := by
  classical
  exact if 0 < usableGroupTotal group arm z then
      (usableGroupTotal group arm z : Real)⁻¹ *
        ∑ k, if usableGroup group arm z k then
          (groupCount group arm z k : Real) *
            (armResidualMean group arm Y center z true k -
              armResidualMean group arm Y center z false k)
        else 0
    else 0

/-- The inverse usable occupancy is the reciprocal of the usable-group total
when positive, and zero at the empirical zero boundary. -/
noncomputable def inverseUsableGroupTotal {n : Nat} (group : Omega -> kappa)
    (arm : Omega -> Bool) (z : Fin n -> Omega) : Real :=
  if 0 < usableGroupTotal group arm z then
    (usableGroupTotal group arm z : Real)⁻¹
  else 0

/-- The design variance factor is the usable-group sum of squared occupancy
weights times the two reciprocal arm counts, totalized to zero when no group is
usable. -/
noncomputable def occupancyDesignVarianceFactor {n : Nat} (group : Omega -> kappa)
    (arm : Omega -> Bool) (z : Fin n -> Omega) : Real := by
  classical
  exact if 0 < usableGroupTotal group arm z then
      (usableGroupTotal group arm z : Real)⁻¹ ^ 2 *
        ∑ k, if usableGroup group arm z k then
          (groupCount group arm z k : Real) ^ 2 *
            ((groupArmCount group arm z true k : Real)⁻¹ +
              (groupArmCount group arm z false k : Real)⁻¹)
        else 0
    else 0

/-- A [measurable group label](hyp:hgroup) has [measurable group fibers](goal). -/
lemma measurableSet_groupEvent (group : Omega -> kappa) (hgroup : Measurable group)
    (k : kappa) : MeasurableSet (groupEvent group k) := by
  change MeasurableSet (group ⁻¹' {k})
  exact (measurableSet_singleton k).preimage hgroup

/-- [Measurable group and arm labels](hyp:hgroup,harm) have [measurable joint
arm/group fibers](goal). -/
lemma measurableSet_armGroupEvent (group : Omega -> kappa) (arm : Omega -> Bool)
    (hgroup : Measurable group) (harm : Measurable arm) (a : Bool) (k : kappa) :
    MeasurableSet (armGroupEvent group arm a k) := by
  rw [show armGroupEvent group arm a k =
      groupEvent group k ∩ {omega | arm omega = a} by ext omega; simp [armGroupEvent, groupEvent]]
  exact (measurableSet_groupEvent group hgroup k).inter
    ((measurableSet_singleton a).preimage harm)

/-- [Measurable group and arm labels](hyp:hgroup,harm) make [the coordinatewise
finite design measurable](goal). -/
lemma measurable_sampleDesign {n : Nat} (group : Omega -> kappa)
    (arm : Omega -> Bool) (hgroup : Measurable group) (harm : Measurable arm) :
    Measurable (sampleDesign (n := n) group arm) := by
  apply measurable_pi_lambda
  intro i
  exact (hgroup.comp (measurable_pi_apply i :
    Measurable fun z : Fin n -> Omega => z i)).prodMk
    (harm.comp (measurable_pi_apply i :
      Measurable fun z : Fin n -> Omega => z i))

/-- [Measurable group and arm labels](hyp:hgroup,harm) make [each fixed
arm/group count measurable on a finite product sample](goal). -/
lemma measurable_groupArmCount {n : Nat} (group : Omega -> kappa)
    (arm : Omega -> Bool) (hgroup : Measurable group) (harm : Measurable arm)
    (a : Bool) (k : kappa) :
    Measurable (fun z : Fin n -> Omega => groupArmCount group arm z a k) := by
  let count : (Fin n -> kappa × Bool) -> Nat := fun d =>
    (Finset.univ.filter fun i => (d i).1 = k ∧ (d i).2 = a).card
  have hcount : Measurable count := Measurable.of_discrete
  change Measurable (count ∘ sampleDesign group arm)
  exact hcount.comp (measurable_sampleDesign group arm hgroup harm)

/-- [Measurable group and arm labels](hyp:hgroup,harm) make [each fixed group
count measurable on the finite product sample space](goal). -/
lemma measurable_groupCount {n : Nat} (group : Omega -> kappa)
    (arm : Omega -> Bool) (hgroup : Measurable group) (harm : Measurable arm)
    (k : kappa) :
    Measurable (fun z : Fin n -> Omega => groupCount group arm z k) := by
  unfold groupCount
  change Measurable ((fun z : Fin n -> Omega => groupArmCount group arm z false k) +
    fun z => groupArmCount group arm z true k)
  exact (measurable_groupArmCount group arm hgroup harm false k).add
    (measurable_groupArmCount group arm hgroup harm true k)

/-- [Measurable group and arm labels](hyp:hgroup,harm) make [the event that a
fixed empirical group has both arms represented measurable](goal). -/
lemma measurableSet_usableGroup {n : Nat} (group : Omega -> kappa)
    (arm : Omega -> Bool) (hgroup : Measurable group) (harm : Measurable arm)
    (k : kappa) :
    MeasurableSet {z : Fin n -> Omega | usableGroup group arm z k} := by
  have hfalse := measurable_groupArmCount (n := n) group arm hgroup harm false k
  have htrue := measurable_groupArmCount (n := n) group arm hgroup harm true k
  exact (measurableSet_lt measurable_const hfalse).inter
    (measurableSet_lt measurable_const htrue)

/-- [Measurable group and arm labels](hyp:hgroup,harm) make [the total occupancy
in empirically usable groups measurable](goal). -/
lemma measurable_usableGroupTotal {n : Nat} (group : Omega -> kappa)
    (arm : Omega -> Bool) (hgroup : Measurable group) (harm : Measurable arm) :
    Measurable (fun z : Fin n -> Omega => usableGroupTotal group arm z) := by
  classical
  unfold usableGroupTotal
  apply Finset.measurable_sum
  intro k hk
  exact Measurable.ite (measurableSet_usableGroup group arm hgroup harm k)
    (measurable_groupCount group arm hgroup harm k) measurable_const

/-- A [measurable outcome](hyp:hY) makes [each arm/group-centered residual
measurable](goal). -/
lemma measurable_armGroupResidual (Y : Omega -> Real)
    (center : Bool -> kappa -> Real) (hY : Measurable Y) (a : Bool) (k : kappa) :
    Measurable (armGroupResidual Y center a k) := by
  unfold armGroupResidual
  change Measurable (Y - fun _ => center a k)
  exact hY.sub measurable_const

/-- [Measurable group labels, arm labels, and outcomes](hyp:hgroup,harm,hY) make
[each residual restricted to its own arm/group cell measurable](goal). -/
lemma measurable_supportedArmGroupResidual (group : Omega -> kappa)
    (arm : Omega -> Bool) (Y : Omega -> Real)
    (center : Bool -> kappa -> Real) (hgroup : Measurable group)
    (harm : Measurable arm) (hY : Measurable Y) (a : Bool) (k : kappa) :
    Measurable (supportedArmGroupResidual group arm Y center a k) := by
  unfold supportedArmGroupResidual
  exact (measurable_armGroupResidual Y center hY a k).indicator
    (measurableSet_armGroupEvent group arm hgroup harm a k)

/-- [Measurable group labels, arm labels, and outcomes](hyp:hgroup,harm,hY) make
[each arm/group residual sum measurable on the finite product sample
space](goal). -/
lemma measurable_armResidualSum {n : Nat} (group : Omega -> kappa)
    (arm : Omega -> Bool) (Y : Omega -> Real)
    (center : Bool -> kappa -> Real) (hgroup : Measurable group)
    (harm : Measurable arm) (hY : Measurable Y) (a : Bool) (k : kappa) :
    Measurable (fun z : Fin n -> Omega =>
      armResidualSum group arm Y center z a k) := by
  classical
  unfold armResidualSum
  apply Finset.measurable_sum
  intro i hi
  exact (measurable_supportedArmGroupResidual group arm Y center hgroup harm hY a k).comp
    (measurable_pi_apply i : Measurable fun z : Fin n -> Omega => z i)

/-- [Measurable group labels, arm labels, and outcomes](hyp:hgroup,harm,hY) make
[each zero-safe arm/group residual mean measurable on the finite product sample
space](goal). -/
lemma measurable_armResidualMean {n : Nat} (group : Omega -> kappa)
    (arm : Omega -> Bool) (Y : Omega -> Real)
    (center : Bool -> kappa -> Real) (hgroup : Measurable group)
    (harm : Measurable arm) (hY : Measurable Y) (a : Bool) (k : kappa) :
    Measurable (fun z : Fin n -> Omega =>
      armResidualMean group arm Y center z a k) := by
  let count := fun z : Fin n -> Omega => groupArmCount group arm z a k
  have hcount : Measurable count :=
    measurable_groupArmCount group arm hgroup harm a k
  have hpos : MeasurableSet {z | 0 < count z} :=
    measurableSet_lt measurable_const hcount
  have hcast : Measurable (fun z => (count z : Real)) :=
    (Measurable.of_discrete : Measurable fun m : Nat => (m : Real)).comp hcount
  unfold armResidualMean
  exact Measurable.ite hpos
    (hcast.inv.mul (measurable_armResidualSum group arm Y center hgroup harm hY a k))
    measurable_const

/-- [Measurable group labels, arm labels, and outcomes](hyp:hgroup,harm,hY) make
[the zero-safe occupancy-weighted residual measurable on the finite product
sample space](goal). -/
lemma measurable_occupancyWeightedResidual {n : Nat} (mu : Measure Omega)
    (group : Omega -> kappa) (arm : Omega -> Bool) (Y : Omega -> Real)
    (center : Bool -> kappa -> Real) (hgroup : Measurable group)
    (harm : Measurable arm) (hY : Measurable Y) :
    Measurable (occupancyWeightedResidual (n := n) mu group arm Y center) := by
  classical
  have htotal : Measurable (fun z : Fin n -> Omega => usableGroupTotal group arm z) :=
    measurable_usableGroupTotal group arm hgroup harm
  have hpos : MeasurableSet {z : Fin n -> Omega |
      0 < usableGroupTotal group arm z} :=
    measurableSet_lt measurable_const htotal
  have htotalCast : Measurable (fun z : Fin n -> Omega =>
      (usableGroupTotal group arm z : Real)) :=
    (Measurable.of_discrete : Measurable fun m : Nat => (m : Real)).comp htotal
  have hsum : Measurable (fun z : Fin n -> Omega =>
      ∑ k, if usableGroup group arm z k then
        (groupCount group arm z k : Real) *
          (armResidualMean group arm Y center z true k -
            armResidualMean group arm Y center z false k)
      else 0) := by
    apply Finset.measurable_sum
    intro k hk
    have hgroupCount := measurable_groupCount (n := n) group arm hgroup harm k
    have hgroupCountCast : Measurable (fun z : Fin n -> Omega =>
        (groupCount group arm z k : Real)) :=
      (Measurable.of_discrete : Measurable fun m : Nat => (m : Real)).comp hgroupCount
    exact Measurable.ite (measurableSet_usableGroup group arm hgroup harm k)
      (hgroupCountCast.mul
        ((measurable_armResidualMean group arm Y center hgroup harm hY true k).sub
          (measurable_armResidualMean group arm Y center hgroup harm hY false k)))
      measurable_const
  unfold occupancyWeightedResidual
  exact Measurable.ite hpos (htotalCast.inv.mul hsum) measurable_const

/-- [Measurable group and arm labels](hyp:hgroup,harm) make [the zero-safe
reciprocal usable occupancy measurable on the finite product sample
space](goal). -/
lemma measurable_inverseUsableGroupTotal {n : Nat} (group : Omega -> kappa)
    (arm : Omega -> Bool) (hgroup : Measurable group) (harm : Measurable arm) :
    Measurable (inverseUsableGroupTotal (n := n) group arm) := by
  have htotal : Measurable (fun z : Fin n -> Omega => usableGroupTotal group arm z) :=
    measurable_usableGroupTotal group arm hgroup harm
  have hpos : MeasurableSet {z : Fin n -> Omega |
      0 < usableGroupTotal group arm z} :=
    measurableSet_lt measurable_const htotal
  have htotalCast : Measurable (fun z : Fin n -> Omega =>
      (usableGroupTotal group arm z : Real)) :=
    (Measurable.of_discrete : Measurable fun m : Nat => (m : Real)).comp htotal
  unfold inverseUsableGroupTotal
  exact Measurable.ite hpos htotalCast.inv measurable_const

/-- [Measurable group and arm labels](hyp:hgroup,harm) make [the zero-safe
occupancy design variance factor measurable on the finite product sample
space](goal). -/
lemma measurable_occupancyDesignVarianceFactor {n : Nat}
    (group : Omega -> kappa) (arm : Omega -> Bool)
    (hgroup : Measurable group) (harm : Measurable arm) :
    Measurable (occupancyDesignVarianceFactor (n := n) group arm) := by
  classical
  have htotal : Measurable (fun z : Fin n -> Omega => usableGroupTotal group arm z) :=
    measurable_usableGroupTotal group arm hgroup harm
  have hpos : MeasurableSet {z : Fin n -> Omega |
      0 < usableGroupTotal group arm z} :=
    measurableSet_lt measurable_const htotal
  have htotalCast : Measurable (fun z : Fin n -> Omega =>
      (usableGroupTotal group arm z : Real)) :=
    (Measurable.of_discrete : Measurable fun m : Nat => (m : Real)).comp htotal
  have hsum : Measurable (fun z : Fin n -> Omega =>
      ∑ k, if usableGroup group arm z k then
        (groupCount group arm z k : Real) ^ 2 *
          ((groupArmCount group arm z true k : Real)⁻¹ +
            (groupArmCount group arm z false k : Real)⁻¹)
      else 0) := by
    apply Finset.measurable_sum
    intro k hk
    have hgroupCount := measurable_groupCount (n := n) group arm hgroup harm k
    have hgroupCountCast : Measurable (fun z : Fin n -> Omega =>
        (groupCount group arm z k : Real)) :=
      (Measurable.of_discrete : Measurable fun m : Nat => (m : Real)).comp hgroupCount
    have htrue := measurable_groupArmCount (n := n) group arm hgroup harm true k
    have hfalse := measurable_groupArmCount (n := n) group arm hgroup harm false k
    have htrueCast : Measurable (fun z : Fin n -> Omega =>
        (groupArmCount group arm z true k : Real)) :=
      (Measurable.of_discrete : Measurable fun m : Nat => (m : Real)).comp htrue
    have hfalseCast : Measurable (fun z : Fin n -> Omega =>
        (groupArmCount group arm z false k : Real)) :=
      (Measurable.of_discrete : Measurable fun m : Nat => (m : Real)).comp hfalse
    exact Measurable.ite (measurableSet_usableGroup group arm hgroup harm k)
      ((hgroupCountCast.pow measurable_const).mul
        (htrueCast.inv.add hfalseCast.inv)) measurable_const
  unfold occupancyDesignVarianceFactor
  exact Measurable.ite hpos
    ((htotalCast.inv.pow measurable_const).mul hsum) measurable_const

end Causalean.Stat
