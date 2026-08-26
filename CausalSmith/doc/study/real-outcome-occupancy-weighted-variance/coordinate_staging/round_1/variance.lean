/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Sample.OccupancyWeightedMean.MomentBounds

/-!
# Weak-moment variance bound for occupancy-weighted residual means

This module represents the occupancy-weighted statistic as a finite sum of
supported residuals, proves its square integrability, and bounds its second
moment by expected reciprocal usable occupancy. Outcomes need only supported
arm/group second moments; all empirical zero-count cases are totalized.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Omega kappa : Type*} [MeasurableSpace Omega]
  [Fintype kappa] [DecidableEq kappa]
  [MeasurableSpace kappa] [MeasurableSingletonClass kappa]

private noncomputable def occupancyResidualWeight {n : Nat}
    (d : Fin n → kappa × Bool) (a : Bool) (k : kappa) : Real := by
  classical
  exact if 0 < usableGroupTotal Prod.fst Prod.snd d then
      (usableGroupTotal Prod.fst Prod.snd d : Real)⁻¹ *
        if usableGroup Prod.fst Prod.snd d k then
          (groupCount Prod.fst Prod.snd d k : Real) *
            (if a then (groupArmCount Prod.fst Prod.snd d true k : Real)⁻¹
              else -(groupArmCount Prod.fst Prod.snd d false k : Real)⁻¹)
        else 0
    else 0

private lemma sum_coordinate_indicator_eq_groupArmCount {n : Nat}
    (group : Omega → kappa) (arm : Omega → Bool) (z : Fin n → Omega)
    (a : Bool) (k : kappa) :
    (∑ i : Fin n,
      (armGroupEvent group arm a k).indicator (fun _ => (1 : Real)) (z i)) =
      (groupArmCount group arm z a k : Real) := by
  classical
  unfold groupArmCount
  calc
    (∑ i : Fin n,
        (armGroupEvent group arm a k).indicator (fun _ => (1 : Real)) (z i)) =
        ∑ i ∈ Finset.univ.filter (fun i => group (z i) = k ∧ arm (z i) = a),
          (1 : Real) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : group (z i) = k ∧ arm (z i) = a <;>
        simp [armGroupEvent, h]
    _ = ((Finset.univ.filter
          (fun i => group (z i) = k ∧ arm (z i) = a)).card : Real) := by
      simp

private lemma sum_occupancyResidualWeight_sq_indicator_eq_factor {n : Nat}
    (group : Omega → kappa) (arm : Omega → Bool) (z : Fin n → Omega) :
    (∑ t : kappa × Bool × Fin n,
      occupancyResidualWeight (sampleDesign group arm z) t.2.1 t.1 ^ 2 *
        (armGroupEvent group arm t.2.1 t.1).indicator
          (fun _ => (1 : Real)) (z t.2.2)) =
      occupancyDesignVarianceFactor group arm z := by
  classical
  have htotal_sample : usableGroupTotal Prod.fst Prod.snd
      (sampleDesign group arm z) = usableGroupTotal group arm z := rfl
  have hweight_sample (a : Bool) (k : kappa) :
      occupancyResidualWeight (sampleDesign group arm z) a k =
        if 0 < usableGroupTotal group arm z then
          (usableGroupTotal group arm z : Real)⁻¹ *
            if usableGroup group arm z k then
              (groupCount group arm z k : Real) *
                (if a then (groupArmCount group arm z true k : Real)⁻¹
                  else -(groupArmCount group arm z false k : Real)⁻¹)
            else 0
        else 0 := by
    rfl
  by_cases htotal : 0 < usableGroupTotal group arm z
  · unfold occupancyDesignVarianceFactor
    rw [if_pos htotal, Finset.mul_sum]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Fintype.sum_prod_type]
    by_cases huk : usableGroup group arm z k
    · have hf : 0 < groupArmCount group arm z false k := huk.1
      have ht : 0 < groupArmCount group arm z true k := huk.2
      rw [if_pos huk, Fintype.sum_bool]
      simp only [hweight_sample, htotal, huk, if_pos,
        Bool.false_eq_true, if_false]
      rw [← Finset.mul_sum, sum_coordinate_indicator_eq_groupArmCount,
        ← Finset.mul_sum, sum_coordinate_indicator_eq_groupArmCount]
      have hfR : (groupArmCount group arm z false k : Real) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hf)
      have htR : (groupArmCount group arm z true k : Real) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt ht)
      field_simp
    · simp [huk, hweight_sample, htotal]
  · have htotal_sample_neg : ¬ 0 < usableGroupTotal Prod.fst Prod.snd
        (sampleDesign group arm z) := by simpa [htotal_sample] using htotal
    simp [occupancyDesignVarianceFactor, occupancyResidualWeight, htotal,
      htotal_sample_neg]

private lemma occupancyWeightedResidual_eq_sum_weight {n : Nat}
    (mu : Measure Omega) (group : Omega → kappa) (arm : Omega → Bool)
    (Y : Omega → Real) (center : Bool → kappa → Real) (z : Fin n → Omega) :
    occupancyWeightedResidual mu group arm Y center z =
      ∑ k : kappa, ∑ a : Bool, ∑ i : Fin n,
        occupancyResidualWeight (sampleDesign group arm z) a k *
          supportedArmGroupResidual group arm Y center a k (z i) := by
  classical
  unfold occupancyWeightedResidual
  change (if 0 < usableGroupTotal group arm z then
      (usableGroupTotal group arm z : Real)⁻¹ *
        ∑ k, if usableGroup group arm z k then
          (groupCount group arm z k : Real) *
            (armResidualMean group arm Y center z true k -
              armResidualMean group arm Y center z false k)
        else 0
    else 0) = _
  have hweight_sample (a : Bool) (k : kappa) :
      occupancyResidualWeight (sampleDesign group arm z) a k =
        if 0 < usableGroupTotal group arm z then
          (usableGroupTotal group arm z : Real)⁻¹ *
            if usableGroup group arm z k then
              (groupCount group arm z k : Real) *
                (if a then (groupArmCount group arm z true k : Real)⁻¹
                  else -(groupArmCount group arm z false k : Real)⁻¹)
            else 0
        else 0 := by
    rfl
  simp_rw [hweight_sample]
  split_ifs with htotal
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases huk : usableGroup group arm z k
    · have hf : 0 < groupArmCount group arm z false k := huk.1
      have ht : 0 < groupArmCount group arm z true k := huk.2
      simp only [huk, if_pos, Fintype.sum_bool, armResidualMean,
        armResidualSum, hf, ht]
      simp only [Bool.false_eq_true, if_false]
      rw [mul_sub]
      simp_rw [Finset.mul_sum]
      ring_nf
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_neg_distrib]
      ring_nf
    · simp [huk]
  · simp

/-- If [group labels, arm labels, and outcomes are measurable](hyp:hgroup,harm,hY)
and [every arm/group-supported residual has a finite second moment](hyp:hmem),
[the zero-safe occupancy-weighted residual has a finite second moment under
every finite independent product sample](goal). -/
theorem occupancyWeightedResidual_memLp_two
    {n : Nat} (mu : Measure Omega) [IsProbabilityMeasure mu]
    (group : Omega -> kappa) (arm : Omega -> Bool) (Y : Omega -> Real)
    (center : Bool -> kappa -> Real)
    (hgroup : Measurable group) (harm : Measurable arm) (hY : Measurable Y)
    (hmem : ∀ a k,
      MemLp (supportedArmGroupResidual group arm Y center a k) 2 mu) :
    MemLp (occupancyWeightedResidual (n := n) mu group arm Y center) 2
      (Measure.pi (fun _ : Fin n => mu)) := by
  -- Expand the statistic as a finite sum of supported residual coordinates.
  -- Its design coefficients range over a finite set, hence are bounded;
  -- close under finite sums and bounded scalar multiplication in `MemLp`.
  classical
  let weight : (Fin n → kappa × Bool) → Bool → kappa → Real :=
    occupancyResidualWeight
  let bound : Real := ∑ d : Fin n → kappa × Bool, ∑ a : Bool, ∑ k : kappa, |weight d a k|
  have hweight_bound (d : Fin n → kappa × Bool) (a : Bool) (k : kappa) :
      |weight d a k| ≤ bound := by
    dsimp [bound]
    calc
      |weight d a k| ≤ ∑ k' : kappa, |weight d a k'| :=
        Finset.single_le_sum (fun k' _ => abs_nonneg (weight d a k')) (Finset.mem_univ k)
      _ ≤ ∑ a' : Bool, ∑ k' : kappa, |weight d a' k'| :=
        Finset.single_le_sum
          (fun a' _ => Finset.sum_nonneg fun k' _ => abs_nonneg (weight d a' k'))
          (Finset.mem_univ a)
      _ ≤ ∑ d' : Fin n → kappa × Bool,
          ∑ a' : Bool, ∑ k' : kappa, |weight d' a' k'| :=
        Finset.single_le_sum
          (fun d' _ => Finset.sum_nonneg fun a' _ =>
            Finset.sum_nonneg fun k' _ => abs_nonneg (weight d' a' k'))
          (Finset.mem_univ d)
  have hterm (i : Fin n) (a : Bool) (k : kappa) :
      MemLp (fun z : Fin n → Omega =>
        weight (sampleDesign group arm z) a k *
          supportedArmGroupResidual group arm Y center a k (z i)) 2
        (Measure.pi (fun _ : Fin n => mu)) := by
    have hr := (hmem a k).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => mu) i)
    have hw : Measurable (fun d : Fin n → kappa × Bool => weight d a k) :=
      Measurable.of_discrete
    apply hr.of_le_mul
    · have hm : AEStronglyMeasurable
          (((fun d : Fin n → kappa × Bool => weight d a k) ∘
              sampleDesign group arm) *
            (supportedArmGroupResidual group arm Y center a k ∘ fun z => z i))
          (Measure.pi (fun _ : Fin n => mu)) :=
        ((hw.comp (measurable_sampleDesign group arm hgroup harm)).mul
          ((measurable_supportedArmGroupResidual group arm Y center
            hgroup harm hY a k).comp (measurable_pi_apply i))).aestronglyMeasurable
      refine hm.congr ?_
      filter_upwards [] with z
      rfl
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hweight_bound _ _ _) (abs_nonneg _)
  have hsum : MemLp (fun z : Fin n → Omega =>
      ∑ k : kappa, ∑ a : Bool, ∑ i : Fin n,
        weight (sampleDesign group arm z) a k *
          supportedArmGroupResidual group arm Y center a k (z i)) 2
      (Measure.pi (fun _ : Fin n => mu)) := by
    exact memLp_finsetSum Finset.univ fun k _ =>
      memLp_finsetSum Finset.univ fun a _ =>
        memLp_finsetSum Finset.univ fun i _ => hterm i a k
  convert hsum using 1
  funext z
  unfold occupancyWeightedResidual
  dsimp [weight, occupancyResidualWeight]
  change (if 0 < usableGroupTotal group arm z then
      (usableGroupTotal group arm z : Real)⁻¹ *
        ∑ k, if usableGroup group arm z k then
          (groupCount group arm z k : Real) *
            (armResidualMean group arm Y center z true k -
              armResidualMean group arm Y center z false k)
        else 0
    else 0) =
    ∑ k : kappa, ∑ a : Bool, ∑ i : Fin n,
      (if 0 < usableGroupTotal group arm z then
        (usableGroupTotal group arm z : Real)⁻¹ *
          if usableGroup group arm z k then
            (groupCount group arm z k : Real) *
              (if a then (groupArmCount group arm z true k : Real)⁻¹
                else -(groupArmCount group arm z false k : Real)⁻¹)
          else 0
      else 0) * supportedArmGroupResidual group arm Y center a k (z i)
  split_ifs with htotal
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases huk : usableGroup group arm z k
    · have hf : 0 < groupArmCount group arm z false k := huk.1
      have ht : 0 < groupArmCount group arm z true k := huk.2
      simp only [huk, if_pos, Fintype.sum_bool, armResidualMean,
        armResidualSum, hf, ht]
      simp only [Bool.false_eq_true, if_false]
      rw [mul_sub]
      simp_rw [Finset.mul_sum]
      ring_nf
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_neg_distrib]
      ring_nf
    · simp [huk]
  · simp

/-- If [group labels, arm labels, and outcomes are measurable](hyp:hgroup,harm,hY),
[every supported residual has a finite second moment](hyp:hmem), [residuals are
centered within every arm/group cell](hyp:hcenter), [their cellwise second
moments obey the stated envelope](hyp:hsq), [the overlap margin is positive and
at most one half](hyp:hepsilon,hepsilon_half), and [both arms receive at least
that share in every positive-mass group](hyp:hoverlap), [the squared
occupancy-weighted residual has product-law expectation at most sixteen divided
by the squared margin times one minus the margin, multiplied by the squared
envelope and expected reciprocal usable occupancy](goal). -/
theorem integral_occupancyWeightedResidual_sq_le_reciprocal
    {n : Nat} (mu : Measure Omega) [IsProbabilityMeasure mu]
    (group : Omega -> kappa) (arm : Omega -> Bool) (Y : Omega -> Real)
    (center : Bool -> kappa -> Real) (V epsilon : Real)
    (hgroup : Measurable group) (harm : Measurable arm) (hY : Measurable Y)
    (hmem : ∀ a k,
      MemLp (supportedArmGroupResidual group arm Y center a k) 2 mu)
    (hcenter : ∀ a k,
      ∫ omega in armGroupEvent group arm a k,
        armGroupResidual Y center a k omega ∂mu = 0)
    (hsq : ∀ a k,
      ∫ omega in armGroupEvent group arm a k,
          (armGroupResidual Y center a k omega) ^ 2 ∂mu ≤
        (mu (armGroupEvent group arm a k)).toReal * V ^ 2)
    (hepsilon : 0 < epsilon)
    (hepsilon_half : epsilon ≤ (1 / 2 : Real))
    (hoverlap : ∀ k, 0 < (mu (groupEvent group k)).toReal -> ∀ a,
      epsilon * (mu (groupEvent group k)).toReal ≤
        (mu (armGroupEvent group arm a k)).toReal) :
    ∫ z : Fin n -> Omega,
        (occupancyWeightedResidual mu group arm Y center z) ^ 2
        ∂(Measure.pi (fun _ : Fin n => mu)) ≤
      (16 / (epsilon ^ 2 * (1 - epsilon))) * V ^ 2 *
        ∫ z : Fin n -> Omega,
          (if 0 < usableGroupTotal group arm z then
            (usableGroupTotal group arm z : Real)⁻¹ else 0)
          ∂(Measure.pi (fun _ : Fin n => mu)) := by
  -- Expand the square into coordinate/label pairs.  Different coordinates
  -- vanish by finite-product centering and different labels at one coordinate
  -- vanish pointwise.  Bound the remaining diagonal terms by `hsq`, identify
  -- the resulting design factor, and apply the design-only reciprocal theorem.
  -- Concretely, reuse the finite-design coefficient `weight` from the preceding
  -- L2 proof and write the statistic as `sum k,a,i weight * supportedResidual`.
  -- Each summand is L2 (the same bounded-coefficient argument), so every pair
  -- product is integrable by `MemLp.integrable_mul` and the finite sums may pass
  -- through the integral.  For `i != j`, apply
  -- `integral_designWeight_residual_cross_coordinates_eq_zero` with the product
  -- of the two design coefficients.  For `i = j` but unequal labels, use
  -- `supportedArmGroupResidual_mul_eq_zero_of_ne`.  Apply
  -- `integral_designWeight_residual_sq_le_indicator` to the equal-label terms
  -- with squared coefficient.  The remaining pointwise finite sum is exactly
  -- `occupancyDesignVarianceFactor`; split on positive usable total and
  -- usability, and rewrite the coordinate indicator sums as arm/group counts.
  classical
  let weight : (Fin n → kappa × Bool) → Bool → kappa → Real :=
    occupancyResidualWeight
  let bound : Real :=
    ∑ d : Fin n → kappa × Bool, ∑ a : Bool, ∑ k : kappa, |weight d a k|
  have hweight_bound (d : Fin n → kappa × Bool) (a : Bool) (k : kappa) :
      |weight d a k| ≤ bound := by
    dsimp [bound]
    calc
      |weight d a k| ≤ ∑ k' : kappa, |weight d a k'| :=
        Finset.single_le_sum (fun k' _ => abs_nonneg (weight d a k'))
          (Finset.mem_univ k)
      _ ≤ ∑ a' : Bool, ∑ k' : kappa, |weight d a' k'| :=
        Finset.single_le_sum
          (fun a' _ => Finset.sum_nonneg fun k' _ => abs_nonneg (weight d a' k'))
          (Finset.mem_univ a)
      _ ≤ ∑ d' : Fin n → kappa × Bool,
          ∑ a' : Bool, ∑ k' : kappa, |weight d' a' k'| :=
        Finset.single_le_sum
          (fun d' _ => Finset.sum_nonneg fun a' _ =>
            Finset.sum_nonneg fun k' _ => abs_nonneg (weight d' a' k'))
          (Finset.mem_univ d)
  let term : (kappa × Bool × Fin n) → (Fin n → Omega) → Real := fun t z =>
    weight (sampleDesign group arm z) t.2.1 t.1 *
      supportedArmGroupResidual group arm Y center t.2.1 t.1 (z t.2.2)
  have hterm (t : kappa × Bool × Fin n) :
      MemLp (term t) 2 (Measure.pi (fun _ : Fin n => mu)) := by
    have hr := (hmem t.2.1 t.1).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => mu) t.2.2)
    have hw : Measurable
        (fun d : Fin n → kappa × Bool => weight d t.2.1 t.1) :=
      Measurable.of_discrete
    apply hr.of_le_mul
    · have hm : AEStronglyMeasurable
          (((fun d : Fin n → kappa × Bool => weight d t.2.1 t.1) ∘
              sampleDesign group arm) *
            (supportedArmGroupResidual group arm Y center t.2.1 t.1 ∘
              fun z => z t.2.2))
          (Measure.pi (fun _ : Fin n => mu)) :=
        ((hw.comp (measurable_sampleDesign group arm hgroup harm)).mul
          ((measurable_supportedArmGroupResidual group arm Y center
            hgroup harm hY t.2.1 t.1).comp
              (measurable_pi_apply t.2.2))).aestronglyMeasurable
      refine hm.congr ?_
      filter_upwards [] with z
      rfl
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hweight_bound _ _ _) (abs_nonneg _)
  have hpair_integrable (t u : kappa × Bool × Fin n) :
      Integrable (fun z => term t z * term u z)
        (Measure.pi (fun _ : Fin n => mu)) := by
    change Integrable (term t * term u) (Measure.pi (fun _ : Fin n => mu))
    exact (hterm t).integrable_mul (hterm u)
  have hresidual_sum (z : Fin n → Omega) :
      occupancyWeightedResidual mu group arm Y center z = ∑ t, term t z := by
    rw [occupancyWeightedResidual_eq_sum_weight]
    simp only [term, weight, Fintype.sum_prod_type]
  have hpair_zero (t u : kappa × Bool × Fin n) (htu : u ≠ t) :
      ∫ z, term t z * term u z ∂(Measure.pi (fun _ : Fin n => mu)) = 0 := by
    by_cases hij : t.2.2 = u.2.2
    · have hlabel : (t.2.1, t.1) ≠ (u.2.1, u.1) := by
        intro hlabel
        apply htu
        apply Prod.ext
        · exact (congrArg Prod.snd hlabel).symm
        · apply Prod.ext
          · exact (congrArg Prod.fst hlabel).symm
          · exact hij.symm
      apply integral_eq_zero_of_ae
      filter_upwards [] with z
      dsimp [term]
      rw [hij]
      have hzres := supportedArmGroupResidual_mul_eq_zero_of_ne group arm Y center
        t.2.1 u.2.1 t.1 u.1 hlabel (z u.2.2)
      calc
        weight (sampleDesign group arm z) t.2.1 t.1 *
              supportedArmGroupResidual group arm Y center t.2.1 t.1 (z u.2.2) *
            (weight (sampleDesign group arm z) u.2.1 u.1 *
              supportedArmGroupResidual group arm Y center u.2.1 u.1 (z u.2.2)) =
            (weight (sampleDesign group arm z) t.2.1 t.1 *
              weight (sampleDesign group arm z) u.2.1 u.1) *
              (supportedArmGroupResidual group arm Y center t.2.1 t.1 (z u.2.2) *
                supportedArmGroupResidual group arm Y center u.2.1 u.1 (z u.2.2)) := by
          ring
        _ = 0 := by rw [hzres]; ring
    · have hcross := integral_designWeight_residual_cross_coordinates_eq_zero
        mu group arm Y center hgroup harm hY hmem hcenter
        (fun d => weight d t.2.1 t.1 * weight d u.2.1 u.1)
        t.2.2 u.2.2 hij t.2.1 u.2.1 t.1 u.1
      simpa [term, mul_assoc, mul_left_comm, mul_comm] using hcross
  have hdiagonal (t : kappa × Bool × Fin n) :
      (∫ z, term t z * term t z ∂(Measure.pi (fun _ : Fin n => mu))) ≤
        V ^ 2 * ∫ z,
          weight (sampleDesign group arm z) t.2.1 t.1 ^ 2 *
            (armGroupEvent group arm t.2.1 t.1).indicator
              (fun _ => (1 : Real)) (z t.2.2)
          ∂(Measure.pi (fun _ : Fin n => mu)) := by
    have hdiag := integral_designWeight_residual_sq_le_indicator
      mu group arm Y center V hgroup harm hY hmem hsq
      (fun d => weight d t.2.1 t.1 ^ 2) (fun d => sq_nonneg _) t.2.2 t.2.1 t.1
    simpa [term, pow_two, mul_assoc, mul_left_comm, mul_comm] using hdiag
  have hsum_bound :
      (∑ t : kappa × Bool × Fin n, ∑ u : kappa × Bool × Fin n,
        ∫ z, term t z * term u z ∂(Measure.pi (fun _ : Fin n => mu))) ≤
      ∑ t : kappa × Bool × Fin n, V ^ 2 * ∫ z,
        weight (sampleDesign group arm z) t.2.1 t.1 ^ 2 *
          (armGroupEvent group arm t.2.1 t.1).indicator
            (fun _ => (1 : Real)) (z t.2.2)
        ∂(Measure.pi (fun _ : Fin n => mu)) := by
    apply Finset.sum_le_sum
    intro t ht
    calc
      (∑ u : kappa × Bool × Fin n,
          ∫ z, term t z * term u z ∂(Measure.pi (fun _ : Fin n => mu))) =
          ∫ z, term t z * term t z ∂(Measure.pi (fun _ : Fin n => mu)) := by
        rw [Finset.sum_eq_single t]
        · intro u hu hut
          exact hpair_zero t u hut
        · simp
      _ ≤ _ := hdiagonal t
  have hbound_nonneg : 0 ≤ bound := by
    dsimp [bound]
    positivity
  have hindicator_integrable (t : kappa × Bool × Fin n) :
      Integrable (fun z : Fin n → Omega =>
        weight (sampleDesign group arm z) t.2.1 t.1 ^ 2 *
          (armGroupEvent group arm t.2.1 t.1).indicator
            (fun _ => (1 : Real)) (z t.2.2))
        (Measure.pi (fun _ : Fin n => mu)) := by
    have hw : Measurable
        (fun d : Fin n → kappa × Bool => weight d t.2.1 t.1) :=
      Measurable.of_discrete
    have hi : Measurable (fun z : Fin n → Omega =>
        (armGroupEvent group arm t.2.1 t.1).indicator
          (fun _ => (1 : Real)) (z t.2.2)) :=
      ((measurable_const : Measurable (fun _ : Omega => (1 : Real))).indicator
        (measurableSet_armGroupEvent group arm hgroup harm t.2.1 t.1)).comp
          (measurable_pi_apply t.2.2)
    apply Integrable.of_bound
      (((hw.comp (measurable_sampleDesign group arm hgroup harm)).pow
        measurable_const).mul hi).aestronglyMeasurable (bound ^ 2)
    filter_upwards [] with z
    change ‖weight (sampleDesign group arm z) t.2.1 t.1 ^ 2 *
      (armGroupEvent group arm t.2.1 t.1).indicator
        (fun _ => (1 : Real)) (z t.2.2)‖ ≤ bound ^ 2
    have hwabs := hweight_bound (sampleDesign group arm z) t.2.1 t.1
    have hwsq : weight (sampleDesign group arm z) t.2.1 t.1 ^ 2 ≤ bound ^ 2 := by
      exact (sq_le_sq).2 (by simpa [abs_of_nonneg hbound_nonneg] using hwabs)
    by_cases hz : z t.2.2 ∈ armGroupEvent group arm t.2.1 t.1
    · rw [Set.indicator_of_mem hz, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg
          (weight (sampleDesign group arm z) t.2.1 t.1))]
      exact hwsq
    · simp [Set.indicator_of_notMem hz, sq_nonneg bound]
  have hsum_integral :
      (∑ t : kappa × Bool × Fin n, V ^ 2 * ∫ z,
        weight (sampleDesign group arm z) t.2.1 t.1 ^ 2 *
          (armGroupEvent group arm t.2.1 t.1).indicator
            (fun _ => (1 : Real)) (z t.2.2)
        ∂(Measure.pi (fun _ : Fin n => mu))) =
      V ^ 2 * ∫ z, occupancyDesignVarianceFactor group arm z
        ∂(Measure.pi (fun _ : Fin n => mu)) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [← integral_finsetSum Finset.univ]
    · apply integral_congr_ae
      filter_upwards [] with z
      exact sum_occupancyResidualWeight_sq_indicator_eq_factor group arm z
    · intro t ht
      exact hindicator_integrable t
  have hdesign := integral_occupancyDesignVarianceFactor_le_reciprocal
    (n := n) mu group arm hgroup harm epsilon hepsilon hepsilon_half hoverlap
  calc
    (∫ z : Fin n -> Omega,
        (occupancyWeightedResidual mu group arm Y center z) ^ 2
        ∂(Measure.pi (fun _ : Fin n => mu))) =
        ∫ z : Fin n → Omega, ∑ t : kappa × Bool × Fin n,
          ∑ u : kappa × Bool × Fin n, term t z * term u z
          ∂(Measure.pi (fun _ : Fin n => mu)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hresidual_sum z, pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = ∑ t : kappa × Bool × Fin n,
        ∫ z : Fin n → Omega, ∑ u : kappa × Bool × Fin n,
          term t z * term u z ∂(Measure.pi (fun _ : Fin n => mu)) := by
      apply integral_finsetSum
      intro t ht
      exact integrable_finsetSum Finset.univ fun u hu => hpair_integrable t u
    _ = ∑ t : kappa × Bool × Fin n, ∑ u : kappa × Bool × Fin n,
        ∫ z : Fin n → Omega, term t z * term u z
          ∂(Measure.pi (fun _ : Fin n => mu)) := by
      apply Finset.sum_congr rfl
      intro t ht
      apply integral_finsetSum
      intro u hu
      exact hpair_integrable t u
    _ ≤ ∑ t : kappa × Bool × Fin n, V ^ 2 * ∫ z,
        weight (sampleDesign group arm z) t.2.1 t.1 ^ 2 *
          (armGroupEvent group arm t.2.1 t.1).indicator
            (fun _ => (1 : Real)) (z t.2.2)
        ∂(Measure.pi (fun _ : Fin n => mu)) := hsum_bound
    _ = V ^ 2 * ∫ z, occupancyDesignVarianceFactor group arm z
        ∂(Measure.pi (fun _ : Fin n => mu)) := hsum_integral
    _ ≤ V ^ 2 * ((16 / (epsilon ^ 2 * (1 - epsilon))) *
        ∫ z, inverseUsableGroupTotal group arm z
          ∂(Measure.pi (fun _ : Fin n => mu))) :=
      mul_le_mul_of_nonneg_left hdesign (sq_nonneg V)
    _ = (16 / (epsilon ^ 2 * (1 - epsilon))) * V ^ 2 *
        ∫ z : Fin n -> Omega,
          (if 0 < usableGroupTotal group arm z then
            (usableGroupTotal group arm z : Real)⁻¹ else 0)
          ∂(Measure.pi (fun _ : Fin n => mu)) := by
      simp only [inverseUsableGroupTotal]
      ring

end Causalean.Stat
