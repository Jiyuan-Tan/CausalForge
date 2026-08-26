/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Sample.FiniteStratumMarkedRatioMse.MissingMoments
import Causalean.Stat.Sample.FiniteStratumMarkedRatioMse.NestedCountBound
import Causalean.Stat.Sample.OccupancyWeightedMean.MomentBounds

/-!
# Selected-arm centered ratio-noise bound

This module proves the fixed-stratum selected-arm centered-noise second-moment
bound. It uses a zero extension on the unselected arm, coordinate orthogonality,
and a nested finite-product inverse-count estimate.
-/

namespace Causalean.Stat.FiniteStratumMarkedRatioMse

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Omega kappa : Type*} [MeasurableSpace Omega]
  [Fintype kappa] [DecidableEq kappa]
  [MeasurableSpace kappa] [MeasurableSingletonClass kappa]


/-- [Measurable group and arm labels and a measurable mark](hyp:hgroup,harm,hY),
[square-integrable supported residuals](hyp:hmem), [cellwise residual
centering](hyp:hcenter), [the stated cellwise second-moment envelope](hyp:hsq),
[a positive overlap margin](hyp:hepsilon), and [arm mass at least that margin
times category mass](hyp:hoverlap) imply that [the occupancy-weighted centered
ratio noise has second moment at most twice the squared envelope times selected
mass, divided by safe sample size and overlap](goal). -/
theorem integral_fixedStratumArmCenteredNoise_sq_le {m : Nat}
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
    (hepsilon : 0 < epsilon)
    (hoverlap : ∀ k, 0 < categoryMass mu group k →
      epsilon * categoryMass mu group k ≤ armCategoryMass mu group arm a k) :
    ∫ z : Fin m → Omega,
        (fixedStratumArmCenteredNoise group arm Y center H a z) ^ 2
        ∂(Measure.pi (fun _ : Fin m => mu)) ≤
      2 * M ^ 2 * (∑ k ∈ H, categoryMass mu group k) /
        (safeSampleSize m * epsilon) := by
  -- Proof plan: split off `m = 0`.  For positive `m`, expand the statistic as
  -- a finite sum over `(k,i)` with a design-only coefficient.  Cross-coordinate
  -- terms vanish by cell centering, while distinct cells at one coordinate are
  -- disjoint.  Bound the diagonal by `hsq`, condition on the finite design, and
  -- apply the zero-safe inverse-binomial count bound.  The public helpers in
  -- `OccupancyWeightedMean.MomentBounds` are models for this argument, but their
  -- all-arm `hmem` premise must not be used to strengthen this single-arm API.
  classical
  by_cases hm : m = 0
  · subst m
    simp [fixedStratumArmCenteredNoise, totalizedArmResidualMean,
      Causalean.Stat.armResidualMean, Causalean.Stat.groupArmCount,
      categoryCount, Causalean.Stat.groupCount]
    have hmass : 0 ≤ ∑ k ∈ H, categoryMass mu group k := by
      apply Finset.sum_nonneg
      intro k hk
      exact ENNReal.toReal_nonneg
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg M)) hmass
    · simpa [safeSampleSize] using hepsilon.le
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hmR : (0 : Real) < m := by exact_mod_cast hmpos
    let Y₀ : Omega → Real := fun omega => if arm omega = a then Y omega else 0
    let center₀ : Bool → kappa → Real := fun b k => if b = a then center a k else 0
    have hY₀ : Measurable Y₀ := by
      dsimp [Y₀]
      exact Measurable.ite (measurableSet_eq_fun harm measurable_const) hY measurable_const
    have hresidual₀ (k : kappa) (omega : Omega) :
        Causalean.Stat.supportedArmGroupResidual group arm Y₀ center₀ a k omega =
          supportedArmResidual group arm Y center a k omega := by
      by_cases ho : group omega = k ∧ arm omega = a <;>
        simp [Y₀, center₀, supportedArmResidual,
          Causalean.Stat.supportedArmGroupResidual,
          Causalean.Stat.armGroupResidual, Causalean.Stat.armGroupEvent, ho]
    have hresidual₀_other (b : Bool) (k : kappa) (hba : b ≠ a) (omega : Omega) :
        Causalean.Stat.supportedArmGroupResidual group arm Y₀ center₀ b k omega = 0 := by
      by_cases ho : group omega = k ∧ arm omega = b <;>
        simp [Y₀, center₀, Causalean.Stat.supportedArmGroupResidual,
          Causalean.Stat.armGroupResidual, Causalean.Stat.armGroupEvent, ho, hba]
    have hmem₀ : ∀ b k,
        MemLp (Causalean.Stat.supportedArmGroupResidual group arm Y₀ center₀ b k) 2 mu := by
      intro b k
      by_cases hba : b = a
      · subst b
        convert hmem k using 1
        funext omega
        exact hresidual₀ k omega
      · convert (MemLp.zero : MemLp (fun _ : Omega => (0 : Real)) 2 mu) using 1
        funext omega
        exact hresidual₀_other b k hba omega
    have hcenter₀ : ∀ b k,
        ∫ omega in Causalean.Stat.armGroupEvent group arm b k,
          Causalean.Stat.armGroupResidual Y₀ center₀ b k omega ∂mu = 0 := by
      intro b k
      by_cases hba : b = a
      · subst b
        rw [show (∫ omega in Causalean.Stat.armGroupEvent group arm a k,
            Causalean.Stat.armGroupResidual Y₀ center₀ a k omega ∂mu) =
            ∫ omega in armCategoryEvent group arm a k,
              (Y omega - center a k) ∂mu by
          apply setIntegral_congr_fun
            (Causalean.Stat.measurableSet_armGroupEvent group arm hgroup harm a k)
          intro omega homega
          simp [Y₀, center₀, Causalean.Stat.armGroupResidual, homega.2]]
        exact hcenter k
      · apply setIntegral_eq_zero_of_ae_eq_zero
        filter_upwards [] with omega homega
        simp [Y₀, center₀, Causalean.Stat.armGroupResidual, homega.2, hba]
    have hsq₀ : ∀ b k,
        ∫ omega in Causalean.Stat.armGroupEvent group arm b k,
            (Causalean.Stat.armGroupResidual Y₀ center₀ b k omega) ^ 2 ∂mu ≤
          (mu (Causalean.Stat.armGroupEvent group arm b k)).toReal * M ^ 2 := by
      intro b k
      by_cases hba : b = a
      · subst b
        convert hsq k using 1
        · apply setIntegral_congr_fun
            (Causalean.Stat.measurableSet_armGroupEvent group arm hgroup harm a k)
          intro omega homega
          simp [Y₀, center₀, Causalean.Stat.armGroupResidual, homega.2]
        · rfl
      · have hzero : (∫ omega in Causalean.Stat.armGroupEvent group arm b k,
            (Causalean.Stat.armGroupResidual Y₀ center₀ b k omega) ^ 2 ∂mu) = 0 := by
          apply setIntegral_eq_zero_of_ae_eq_zero
          filter_upwards [] with omega homega
          simp [Y₀, center₀, Causalean.Stat.armGroupResidual, homega.2, hba]
        rw [hzero]
        positivity
    let weight : (Fin m → kappa × Bool) → kappa → Real := fun d k =>
      if k ∈ H then
        (Causalean.Stat.groupCount Prod.fst Prod.snd d k : Real) / (m : Real) *
          if 0 < Causalean.Stat.groupArmCount Prod.fst Prod.snd d a k then
            (Causalean.Stat.groupArmCount Prod.fst Prod.snd d a k : Real)⁻¹
          else 0
      else 0
    let bound : Real := ∑ d : Fin m → kappa × Bool, ∑ k : kappa, |weight d k|
    have hweight_bound (d : Fin m → kappa × Bool) (k : kappa) :
        |weight d k| ≤ bound := by
      dsimp [bound]
      calc
        |weight d k| ≤ ∑ l : kappa, |weight d l| :=
          Finset.single_le_sum (fun l _ => abs_nonneg (weight d l)) (Finset.mem_univ k)
        _ ≤ ∑ d' : Fin m → kappa × Bool, ∑ l : kappa, |weight d' l| :=
          Finset.single_le_sum (fun d' _ => Finset.sum_nonneg fun l _ =>
            abs_nonneg (weight d' l)) (Finset.mem_univ d)
    let term : (kappa × Fin m) → (Fin m → Omega) → Real := fun t z =>
      weight (Causalean.Stat.sampleDesign group arm z) t.1 *
        supportedArmResidual group arm Y center a t.1 (z t.2)
    have hterm (t : kappa × Fin m) :
        MemLp (term t) 2 (Measure.pi (fun _ : Fin m => mu)) := by
      have hr := (hmem t.1).comp_measurePreserving
        (measurePreserving_eval (fun _ : Fin m => mu) t.2)
      apply hr.of_le_mul
      · exact (((Measurable.of_discrete : Measurable fun d : Fin m → kappa × Bool =>
            weight d t.1).comp
          (Causalean.Stat.measurable_sampleDesign group arm hgroup harm)).mul
          ((Causalean.Stat.measurable_supportedArmGroupResidual group arm Y center
            hgroup harm hY a t.1).comp (measurable_pi_apply t.2))).aestronglyMeasurable
      · filter_upwards [] with z
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hweight_bound _ _) (abs_nonneg _)
    have hpair_integrable (t u : kappa × Fin m) :
        Integrable (fun z => term t z * term u z)
          (Measure.pi (fun _ : Fin m => mu)) := by
      change Integrable (term t * term u) _
      exact (hterm t).integrable_mul (hterm u)
    have hnoise_sum (z : Fin m → Omega) :
        fixedStratumArmCenteredNoise group arm Y center H a z = ∑ t, term t z := by
      unfold fixedStratumArmCenteredNoise totalizedArmResidualMean
      simp only [term, weight, Fintype.sum_prod_type]
      change (∑ k ∈ H, (categoryCount group arm z k : Real) / (m : Real) *
          Causalean.Stat.armResidualMean group arm Y center z a k) =
        ∑ k : kappa, ∑ i : Fin m,
          (if k ∈ H then
            (categoryCount group arm z k : Real) / (m : Real) *
              (if 0 < categoryArmCount group arm z a k then
                (categoryArmCount group arm z a k : Real)⁻¹ else 0)
           else 0) * supportedArmResidual group arm Y center a k (z i)
      rw [show (∑ k : kappa, ∑ i : Fin m,
          (if k ∈ H then
            (categoryCount group arm z k : Real) / (m : Real) *
              (if 0 < categoryArmCount group arm z a k then
                (categoryArmCount group arm z a k : Real)⁻¹ else 0)
           else 0) * supportedArmResidual group arm Y center a k (z i)) =
          ∑ k ∈ H, ∑ i : Fin m,
            ((categoryCount group arm z k : Real) / (m : Real) *
              (if 0 < categoryArmCount group arm z a k then
                (categoryArmCount group arm z a k : Real)⁻¹ else 0)) *
              supportedArmResidual group arm Y center a k (z i) by
        symm
        calc
          (∑ k ∈ H, ∑ i : Fin m,
              ((categoryCount group arm z k : Real) / (m : Real) *
                (if 0 < categoryArmCount group arm z a k then
                  (categoryArmCount group arm z a k : Real)⁻¹ else 0)) *
                supportedArmResidual group arm Y center a k (z i)) =
              ∑ k ∈ H, ∑ i : Fin m,
                (if k ∈ H then
                  (categoryCount group arm z k : Real) / (m : Real) *
                    (if 0 < categoryArmCount group arm z a k then
                      (categoryArmCount group arm z a k : Real)⁻¹ else 0)
                 else 0) * supportedArmResidual group arm Y center a k (z i) := by
            apply Finset.sum_congr rfl
            intro k hk
            simp [hk]
          _ = _ := by
            apply Finset.sum_subset (Finset.subset_univ _)
            intro k hk hnot
            simp [hnot]]
      unfold Causalean.Stat.armResidualMean Causalean.Stat.armResidualSum
      unfold categoryArmCount supportedArmResidual
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hpos : 0 < categoryArmCount group arm z a k
      · change 0 < Causalean.Stat.groupArmCount group arm z a k at hpos
        rw [if_pos hpos]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp [hpos]
        ring
      · change ¬0 < Causalean.Stat.groupArmCount group arm z a k at hpos
        rw [if_neg hpos]
        simp [hpos]
    have hpair_zero (t u : kappa × Fin m) (htu : u ≠ t) :
        ∫ z, term t z * term u z ∂(Measure.pi (fun _ : Fin m => mu)) = 0 := by
      by_cases hij : t.2 = u.2
      · have hkl : t.1 ≠ u.1 := by
          intro h
          apply htu
          exact Prod.ext h.symm hij.symm
        apply integral_eq_zero_of_ae
        filter_upwards [] with z
        dsimp [term]
        rw [hij]
        have hz := Causalean.Stat.supportedArmGroupResidual_mul_eq_zero_of_ne
          group arm Y center a a t.1 u.1 (by simpa using hkl) (z u.2)
        change supportedArmResidual group arm Y center a t.1 (z u.2) *
          supportedArmResidual group arm Y center a u.1 (z u.2) = 0 at hz
        change _ * supportedArmResidual group arm Y center a t.1 (z u.2) *
          (_ * supportedArmResidual group arm Y center a u.1 (z u.2)) = 0
        calc
          _ = (weight (Causalean.Stat.sampleDesign group arm z) t.1 *
              weight (Causalean.Stat.sampleDesign group arm z) u.1) *
              (supportedArmResidual group arm Y center a t.1 (z u.2) *
                supportedArmResidual group arm Y center a u.1 (z u.2)) := by ring
          _ = 0 := by rw [hz]; ring
      · have hcross := Causalean.Stat.integral_designWeight_residual_cross_coordinates_eq_zero
          mu group arm Y₀ center₀ hgroup harm hY₀ hmem₀ hcenter₀
          (fun d => weight d t.1 * weight d u.1) t.2 u.2 hij a a t.1 u.1
        simpa only [term, hresidual₀, mul_assoc, mul_left_comm, mul_comm] using hcross
    have hdiagonal (t : kappa × Fin m) :
        (∫ z, term t z * term t z ∂(Measure.pi (fun _ : Fin m => mu))) ≤
          M ^ 2 * ∫ z,
            weight (Causalean.Stat.sampleDesign group arm z) t.1 ^ 2 *
              (armCategoryEvent group arm a t.1).indicator (fun _ => (1 : Real)) (z t.2)
            ∂(Measure.pi (fun _ : Fin m => mu)) := by
      have hdiag := Causalean.Stat.integral_designWeight_residual_sq_le_indicator
        mu group arm Y₀ center₀ M hgroup harm hY₀ hmem₀ hsq₀
        (fun d => weight d t.1 ^ 2) (fun d => sq_nonneg _) t.2 a t.1
      simpa only [term, hresidual₀, armCategoryEvent, pow_two, mul_assoc,
        mul_left_comm, mul_comm] using hdiag
    have hsum_bound :
        (∑ t : kappa × Fin m, ∑ u : kappa × Fin m,
          ∫ z, term t z * term u z ∂(Measure.pi (fun _ : Fin m => mu))) ≤
        ∑ t : kappa × Fin m, M ^ 2 * ∫ z,
          weight (Causalean.Stat.sampleDesign group arm z) t.1 ^ 2 *
            (armCategoryEvent group arm a t.1).indicator (fun _ => (1 : Real)) (z t.2)
          ∂(Measure.pi (fun _ : Fin m => mu)) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [Finset.sum_eq_single t]
      · exact hdiagonal t
      · intro u hu hut
        exact hpair_zero t u hut
      · simp
    have hindicator_integrable (t : kappa × Fin m) : Integrable (fun z : Fin m → Omega =>
        weight (Causalean.Stat.sampleDesign group arm z) t.1 ^ 2 *
          (armCategoryEvent group arm a t.1).indicator (fun _ => (1 : Real)) (z t.2))
        (Measure.pi (fun _ : Fin m => mu)) := by
      let B : Real := bound ^ 2
      apply Integrable.of_bound
        (((((Measurable.of_discrete : Measurable fun d : Fin m → kappa × Bool =>
          weight d t.1).comp
            (Causalean.Stat.measurable_sampleDesign group arm hgroup harm)).pow
              measurable_const).mul
          (((measurable_const : Measurable fun _ : Omega => (1 : Real)).indicator
            (Causalean.Stat.measurableSet_armGroupEvent group arm hgroup harm a t.1)).comp
              (measurable_pi_apply t.2))).aestronglyMeasurable) B
      filter_upwards [] with z
      change ‖weight (Causalean.Stat.sampleDesign group arm z) t.1 ^ 2 *
        (armCategoryEvent group arm a t.1).indicator
          (fun _ => (1 : Real)) (z t.2)‖ ≤ B
      have hb0 : 0 ≤ bound := by dsimp [bound]; positivity
      have hw := hweight_bound (Causalean.Stat.sampleDesign group arm z) t.1
      by_cases hz : z t.2 ∈ armCategoryEvent group arm a t.1
      · rw [Set.indicator_of_mem hz, mul_one, Real.norm_eq_abs,
          abs_of_nonneg (sq_nonneg _)]
        exact (sq_le_sq).2 (by simpa [abs_of_nonneg hb0] using hw)
      · simp [Set.indicator_of_notMem hz, B, sq_nonneg bound]
    have hsum_integral :
        (∑ t : kappa × Fin m, M ^ 2 * ∫ z,
          weight (Causalean.Stat.sampleDesign group arm z) t.1 ^ 2 *
            (armCategoryEvent group arm a t.1).indicator (fun _ => (1 : Real)) (z t.2)
          ∂(Measure.pi (fun _ : Fin m => mu))) =
        M ^ 2 * ∑ k ∈ H, ∫ z,
          ((categoryCount group arm z k : Real) / (m : Real)) ^ 2 *
            (if 0 < categoryArmCount group arm z a k then
              (categoryArmCount group arm z a k : Real)⁻¹ else 0)
          ∂(Measure.pi (fun _ : Fin m => mu)) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Fintype.sum_prod_type]
      calc
        (∑ k : kappa, ∑ i : Fin m, ∫ z,
            weight (Causalean.Stat.sampleDesign group arm z) k ^ 2 *
              (armCategoryEvent group arm a k).indicator
                (fun _ => (1 : Real)) (z i)
            ∂(Measure.pi (fun _ : Fin m => mu))) =
          ∑ k : kappa, ∫ z, ∑ i : Fin m,
            weight (Causalean.Stat.sampleDesign group arm z) k ^ 2 *
              (armCategoryEvent group arm a k).indicator
                (fun _ => (1 : Real)) (z i)
            ∂(Measure.pi (fun _ : Fin m => mu)) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [integral_finsetSum]
              intro i hi
              exact hindicator_integrable (k, i)
        _ = ∑ k ∈ H, ∫ z,
            ((categoryCount group arm z k : Real) / (m : Real)) ^ 2 *
              (if 0 < categoryArmCount group arm z a k then
                (categoryArmCount group arm z a k : Real)⁻¹ else 0)
            ∂(Measure.pi (fun _ : Fin m => mu)) := by
          rw [show (∑ k : kappa, ∫ z, ∑ i : Fin m,
              weight (Causalean.Stat.sampleDesign group arm z) k ^ 2 *
                (armCategoryEvent group arm a k).indicator
                  (fun _ => (1 : Real)) (z i)
              ∂(Measure.pi (fun _ : Fin m => mu))) =
              ∑ k ∈ H, ∫ z, ∑ i : Fin m,
                weight (Causalean.Stat.sampleDesign group arm z) k ^ 2 *
                  (armCategoryEvent group arm a k).indicator
                    (fun _ => (1 : Real)) (z i)
                ∂(Measure.pi (fun _ : Fin m => mu)) by
            symm
            apply Finset.sum_subset (Finset.subset_univ _)
            intro k hk hnot
            simp [weight, hnot]]
          apply Finset.sum_congr rfl
          intro k hk
          apply integral_congr_ae
          filter_upwards [] with z
          have hsum : (∑ i : Fin m,
              (armCategoryEvent group arm a k).indicator
                (fun _ => (1 : Real)) (z i)) =
              (categoryArmCount group arm z a k : Real) := by
            unfold categoryArmCount Causalean.Stat.groupArmCount
            rw [Finset.card_eq_sum_ones]
            push_cast
            simp_rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hcell : group (z i) = k ∧ arm (z i) = a <;>
              simp [armCategoryEvent, Causalean.Stat.armGroupEvent, hcell]
          rw [← Finset.mul_sum, hsum]
          dsimp [weight]
          rw [show Causalean.Stat.groupCount Prod.fst Prod.snd
              (Causalean.Stat.sampleDesign group arm z) k =
                categoryCount group arm z k by rfl]
          rw [show Causalean.Stat.groupArmCount Prod.fst Prod.snd
              (Causalean.Stat.sampleDesign group arm z) a k =
                categoryArmCount group arm z a k by rfl]
          by_cases hpos : 0 < categoryArmCount group arm z a k
          · simp [hk, hpos]
            have hne : (categoryArmCount group arm z a k : Real) ≠ 0 := by
              exact_mod_cast (Nat.ne_of_gt hpos)
            field_simp
          · simp [hk, hpos]
    have hfactor (k : kappa) :
        (∫ z : Fin m → Omega,
          ((categoryCount group arm z k : Real) / (m : Real)) ^ 2 *
            (if 0 < categoryArmCount group arm z a k then
              (categoryArmCount group arm z a k : Real)⁻¹ else 0)
          ∂(Measure.pi (fun _ : Fin m => mu))) ≤
        2 * categoryMass mu group k / ((m : Real) * epsilon) := by
      have hraw := integral_nested_count_sq_mul_totalized_inverse_le
        (m := m) mu (categoryEvent group k) (armCategoryEvent group arm a k)
        (Causalean.Stat.measurableSet_groupEvent group hgroup k)
        (Causalean.Stat.measurableSet_armGroupEvent group arm hgroup harm a k)
        (by intro omega h; exact h.1) epsilon hepsilon
        (by
          by_cases hp : 0 < categoryMass mu group k
          · exact hoverlap k hp
          · have hp0 : categoryMass mu group k = 0 :=
              le_antisymm (le_of_not_gt hp) (by
                unfold categoryMass
                exact ENNReal.toReal_nonneg)
            change epsilon * categoryMass mu group k ≤ armCategoryMass mu group arm a k
            rw [hp0]
            simp only [mul_zero]
            unfold armCategoryMass
            exact ENNReal.toReal_nonneg)
      have hraw' :
          (∫ z : Fin m → Omega,
            (categoryCount group arm z k : Real) ^ 2 *
              (if 0 < categoryArmCount group arm z a k then
                (categoryArmCount group arm z a k : Real)⁻¹ else 0)
            ∂(Measure.pi (fun _ : Fin m => mu))) ≤
          2 * (m : Real) * categoryMass mu group k / epsilon := by
        convert hraw using 1
        · apply integral_congr_ae
          filter_upwards [] with z
          have hgroupCount : categoryCount group arm z k =
              (sampleIndexSet z (categoryEvent group k)).card := by
            unfold categoryCount Causalean.Stat.groupCount
            unfold Causalean.Stat.groupArmCount sampleIndexSet
            unfold categoryEvent Causalean.Stat.groupEvent
            rw [← Finset.card_union_of_disjoint]
            · congr 1
              ext i
              simp
              cases h : arm (z i) <;> simp [h]
            · simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ,
                true_and]
              intro i hf ht
              simp_all
          have harmCount : categoryArmCount group arm z a k =
              (sampleIndexSet z (armCategoryEvent group arm a k)).card := by
            unfold categoryArmCount Causalean.Stat.groupArmCount
            unfold sampleIndexSet armCategoryEvent Causalean.Stat.armGroupEvent
            congr 1
            ext i
            simp [and_comm]
          rw [hgroupCount, harmCount]
        · rfl
      rw [show (∫ z : Fin m → Omega,
          ((categoryCount group arm z k : Real) / (m : Real)) ^ 2 *
            (if 0 < categoryArmCount group arm z a k then
              (categoryArmCount group arm z a k : Real)⁻¹ else 0)
          ∂(Measure.pi (fun _ : Fin m => mu))) =
          (m : Real)⁻¹ ^ 2 * ∫ z : Fin m → Omega,
            (categoryCount group arm z k : Real) ^ 2 *
              (if 0 < categoryArmCount group arm z a k then
                (categoryArmCount group arm z a k : Real)⁻¹ else 0)
            ∂(Measure.pi (fun _ : Fin m => mu)) by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with z
        field_simp
        ]
      calc
        _ ≤ (m : Real)⁻¹ ^ 2 *
            (2 * (m : Real) * categoryMass mu group k / epsilon) :=
          mul_le_mul_of_nonneg_left hraw' (sq_nonneg _)
        _ = 2 * categoryMass mu group k / ((m : Real) * epsilon) := by
          field_simp
    have hfactors :
        (∑ k ∈ H, ∫ z : Fin m → Omega,
          ((categoryCount group arm z k : Real) / (m : Real)) ^ 2 *
            (if 0 < categoryArmCount group arm z a k then
              (categoryArmCount group arm z a k : Real)⁻¹ else 0)
          ∂(Measure.pi (fun _ : Fin m => mu))) ≤
        2 * (∑ k ∈ H, categoryMass mu group k) / ((m : Real) * epsilon) := by
      calc
        _ ≤ ∑ k ∈ H, 2 * categoryMass mu group k / ((m : Real) * epsilon) := by
          exact Finset.sum_le_sum fun k hk => hfactor k
        _ = _ := by
          rw [← Finset.sum_div]
          congr 1
          rw [← Finset.mul_sum]
    calc
      (∫ z : Fin m → Omega,
          (fixedStratumArmCenteredNoise group arm Y center H a z) ^ 2
          ∂(Measure.pi (fun _ : Fin m => mu))) =
          ∫ z : Fin m → Omega, ∑ t : kappa × Fin m, ∑ u : kappa × Fin m,
            term t z * term u z ∂(Measure.pi (fun _ : Fin m => mu)) := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [hnoise_sum z, pow_two, Finset.sum_mul]
        simp_rw [Finset.mul_sum]
      _ = ∑ t : kappa × Fin m, ∑ u : kappa × Fin m,
          ∫ z, term t z * term u z ∂(Measure.pi (fun _ : Fin m => mu)) := by
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro t ht
          rw [integral_finsetSum]
          intro u hu
          exact hpair_integrable t u
        · intro t ht
          exact integrable_finsetSum Finset.univ fun u hu => hpair_integrable t u
      _ ≤ ∑ t : kappa × Fin m, M ^ 2 * ∫ z,
          weight (Causalean.Stat.sampleDesign group arm z) t.1 ^ 2 *
            (armCategoryEvent group arm a t.1).indicator (fun _ => (1 : Real)) (z t.2)
          ∂(Measure.pi (fun _ : Fin m => mu)) := hsum_bound
      _ = M ^ 2 * ∑ k ∈ H, ∫ z,
          ((categoryCount group arm z k : Real) / (m : Real)) ^ 2 *
            (if 0 < categoryArmCount group arm z a k then
              (categoryArmCount group arm z a k : Real)⁻¹ else 0)
          ∂(Measure.pi (fun _ : Fin m => mu)) := hsum_integral
      _ ≤ M ^ 2 *
          (2 * (∑ k ∈ H, categoryMass mu group k) / ((m : Real) * epsilon)) :=
        mul_le_mul_of_nonneg_left hfactors (sq_nonneg M)
      _ = 2 * M ^ 2 * (∑ k ∈ H, categoryMass mu group k) /
          (safeSampleSize m * epsilon) := by
        rw [show safeSampleSize m = (m : Real) by
          unfold safeSampleSize
          congr 1
          exact max_eq_right (Nat.one_le_iff_ne_zero.mpr hm)]
        ring

end Causalean.Stat.FiniteStratumMarkedRatioMse
