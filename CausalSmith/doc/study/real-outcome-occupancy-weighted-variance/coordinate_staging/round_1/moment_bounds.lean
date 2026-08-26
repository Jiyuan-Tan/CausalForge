/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Sample.OccupancyWeightedMean.FiniteDesign
import Causalean.Mathlib.Probability.VarianceProd

/-!
# Product-moment bounds for occupancy-weighted residual means

This module proves finite-product orthogonality, a one-coordinate second-moment
comparison, and the design-only reciprocal-count estimate for
occupancy-weighted differences of within-group residual means. Outcomes are
real-valued and need only the stated supported second-moment bounds.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Omega kappa : Type*} [MeasurableSpace Omega]
  [Fintype kappa] [DecidableEq kappa]
  [MeasurableSpace kappa] [MeasurableSingletonClass kappa]

/-- When [two arm/group labels differ](hyp:hne), [their supported residuals have
zero pointwise product because their supports are disjoint](goal). -/
lemma supportedArmGroupResidual_mul_eq_zero_of_ne
    (group : Omega -> kappa) (arm : Omega -> Bool) (Y : Omega -> Real)
    (center : Bool -> kappa -> Real) (a b : Bool) (k l : kappa)
    (hne : (a, k) ≠ (b, l)) (omega : Omega) :
    supportedArmGroupResidual group arm Y center a k omega *
      supportedArmGroupResidual group arm Y center b l omega = 0 := by
  classical
  simp only [supportedArmGroupResidual, Set.indicator_apply]
  by_cases h₁ : omega ∈ armGroupEvent group arm a k
  · by_cases h₂ : omega ∈ armGroupEvent group arm b l
    · exact False.elim
        (hne (Prod.ext (h₁.2.symm.trans h₂.2) (h₁.1.symm.trans h₂.1)))
    · simp [h₁, h₂]
  · simp [h₁]

private lemma integral_designWeight_mul_prod
    {n : Nat} (mu : Measure Omega) [IsProbabilityMeasure mu]
    (group : Omega -> kappa) (arm : Omega -> Bool)
    (hgroup : Measurable group) (harm : Measurable arm)
    (W : (Fin n -> kappa × Bool) -> Real)
    (f : Fin n -> Omega -> Real) (hf : ∀ q, Integrable (f q) mu) :
    ∫ z : Fin n -> Omega,
        W (sampleDesign group arm z) * ∏ q, f q (z q)
      ∂(Measure.pi (fun _ : Fin n => mu)) =
      ∑ d : Fin n -> kappa × Bool, W d * ∏ q,
        ∫ omega in armGroupEvent group arm (d q).2 (d q).1, f q omega ∂mu := by
  classical
  have hcell (d : Fin n -> kappa × Bool) (q : Fin n) :
      MeasurableSet (armGroupEvent group arm (d q).2 (d q).1) :=
    measurableSet_armGroupEvent group arm hgroup harm (d q).2 (d q).1
  have hfactor (d : Fin n -> kappa × Bool) (q : Fin n) :
      Integrable
        ((armGroupEvent group arm (d q).2 (d q).1).indicator (f q)) mu :=
    (hf q).indicator (hcell d q)
  have hprod (d : Fin n -> kappa × Bool) :
      Integrable (fun z : Fin n -> Omega => ∏ q,
        (armGroupEvent group arm (d q).2 (d q).1).indicator (f q) (z q))
        (Measure.pi (fun _ : Fin n => mu)) :=
    Integrable.fintype_prod (hfactor d)
  have hpoint (z : Fin n -> Omega) :
      W (sampleDesign group arm z) * ∏ q, f q (z q) =
        ∑ d : Fin n -> kappa × Bool, W d * ∏ q,
          (armGroupEvent group arm (d q).2 (d q).1).indicator (f q) (z q) := by
    rw [Finset.sum_eq_single (sampleDesign group arm z)]
    · congr 1
      apply Finset.prod_congr rfl
      intro q hq
      rw [Set.indicator_of_mem]
      exact ⟨rfl, rfl⟩
    · intro d hd hne
      obtain ⟨q, hq⟩ := Function.ne_iff.mp hne
      have hznot : z q ∉ armGroupEvent group arm (d q).2 (d q).1 := by
        intro hz
        apply hq
        exact Prod.ext hz.1.symm hz.2.symm
      have hzero :
          (armGroupEvent group arm (d q).2 (d q).1).indicator (f q) (z q) =
            (0 : Real) := Set.indicator_of_notMem hznot _
      rw [Finset.prod_eq_zero (Finset.mem_univ q) hzero]
      simp
    · simp
  calc
    (∫ z : Fin n -> Omega,
        W (sampleDesign group arm z) * ∏ q, f q (z q)
      ∂(Measure.pi (fun _ : Fin n => mu))) =
        ∫ z : Fin n -> Omega, ∑ d : Fin n -> kappa × Bool,
          W d * ∏ q,
            (armGroupEvent group arm (d q).2 (d q).1).indicator (f q) (z q)
          ∂(Measure.pi (fun _ : Fin n => mu)) :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∑ d : Fin n -> kappa × Bool, ∫ z : Fin n -> Omega,
          W d * ∏ q,
            (armGroupEvent group arm (d q).2 (d q).1).indicator (f q) (z q)
          ∂(Measure.pi (fun _ : Fin n => mu)) := by
      apply integral_finsetSum
      intro d hd
      exact (hprod d).const_mul (W d)
    _ = ∑ d : Fin n -> kappa × Bool, W d * ∏ q,
        ∫ omega in armGroupEvent group arm (d q).2 (d q).1, f q omega ∂mu := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [integral_const_mul, integral_fintype_prod_eq_prod]
      apply congrArg (W d * ·)
      apply Finset.prod_congr rfl
      intro q hq
      rw [integral_indicator (hcell d q)]

private lemma setIntegral_supported_eq_zero
    (mu : Measure Omega) (group : Omega -> kappa) (arm : Omega -> Bool)
    (Y : Omega -> Real) (center : Bool -> kappa -> Real)
    (hgroup : Measurable group) (harm : Measurable arm)
    (hcenter : ∀ a k,
      ∫ omega in armGroupEvent group arm a k,
        armGroupResidual Y center a k omega ∂mu = 0)
    (a c : Bool) (k m : kappa) :
    ∫ omega in armGroupEvent group arm c m,
      supportedArmGroupResidual group arm Y center a k omega ∂mu = 0 := by
  classical
  by_cases hlabel : (a, k) = (c, m)
  · have hac : a = c := congrArg Prod.fst hlabel
    have hkm : k = m := congrArg Prod.snd hlabel
    subst c
    subst m
    calc
      (∫ omega in armGroupEvent group arm a k,
          supportedArmGroupResidual group arm Y center a k omega ∂mu) =
          ∫ omega in armGroupEvent group arm a k,
            armGroupResidual Y center a k omega ∂mu := by
        apply setIntegral_congr_fun
          (measurableSet_armGroupEvent group arm hgroup harm a k)
        intro omega homega
        exact Set.indicator_of_mem homega _
      _ = 0 := hcenter a k
  · apply setIntegral_eq_zero_of_ae_eq_zero
    filter_upwards [] with omega homega
    by_cases htarget : omega ∈ armGroupEvent group arm a k
    · exfalso
      apply hlabel
      exact Prod.ext (htarget.2.symm.trans homega.2) (htarget.1.symm.trans homega.1)
    · exact Set.indicator_of_notMem htarget _

private lemma setIntegral_supported_sq_le_indicator
    (mu : Measure Omega) (group : Omega -> kappa) (arm : Omega -> Bool)
    (Y : Omega -> Real) (center : Bool -> kappa -> Real) (V : Real)
    (hgroup : Measurable group) (harm : Measurable arm)
    (hsq : ∀ a k,
      ∫ omega in armGroupEvent group arm a k,
          (armGroupResidual Y center a k omega) ^ 2 ∂mu ≤
        (mu (armGroupEvent group arm a k)).toReal * V ^ 2)
    (a c : Bool) (k m : kappa) :
    ∫ omega in armGroupEvent group arm c m,
        (supportedArmGroupResidual group arm Y center a k omega) ^ 2 ∂mu ≤
      ∫ omega in armGroupEvent group arm c m,
        V ^ 2 * (armGroupEvent group arm a k).indicator (fun _ => (1 : Real)) omega ∂mu := by
  classical
  have hcell : MeasurableSet (armGroupEvent group arm c m) :=
    measurableSet_armGroupEvent group arm hgroup harm c m
  by_cases hlabel : (a, k) = (c, m)
  · have hac : a = c := congrArg Prod.fst hlabel
    have hkm : k = m := congrArg Prod.snd hlabel
    subst c
    subst m
    calc
      (∫ omega in armGroupEvent group arm a k,
          (supportedArmGroupResidual group arm Y center a k omega) ^ 2 ∂mu) =
          ∫ omega in armGroupEvent group arm a k,
            (armGroupResidual Y center a k omega) ^ 2 ∂mu := by
        apply setIntegral_congr_fun hcell
        intro omega homega
        change ((armGroupEvent group arm a k).indicator
          (armGroupResidual Y center a k) omega) ^ 2 = _
        rw [Set.indicator_of_mem homega]
      _ ≤ (mu (armGroupEvent group arm a k)).toReal * V ^ 2 := hsq a k
      _ = ∫ omega in armGroupEvent group arm a k,
          V ^ 2 * (armGroupEvent group arm a k).indicator (fun _ => (1 : Real)) omega ∂mu := by
        symm
        calc
          (∫ omega in armGroupEvent group arm a k,
              V ^ 2 * (armGroupEvent group arm a k).indicator
                (fun _ => (1 : Real)) omega ∂mu) =
              ∫ _omega in armGroupEvent group arm a k, V ^ 2 ∂mu := by
            apply setIntegral_congr_fun hcell
            intro omega homega
            change V ^ 2 * (armGroupEvent group arm a k).indicator
              (fun _ => (1 : Real)) omega = V ^ 2
            rw [Set.indicator_of_mem homega]
            simp
          _ = (mu (armGroupEvent group arm a k)).toReal * V ^ 2 := by
            rw [setIntegral_const]
            rfl
  · have hleft :
        (∫ omega in armGroupEvent group arm c m,
          (supportedArmGroupResidual group arm Y center a k omega) ^ 2 ∂mu) = 0 := by
      apply setIntegral_eq_zero_of_ae_eq_zero
      filter_upwards [] with omega homega
      have htarget : omega ∉ armGroupEvent group arm a k := by
        intro ht
        apply hlabel
        exact Prod.ext (ht.2.symm.trans homega.2) (ht.1.symm.trans homega.1)
      rw [supportedArmGroupResidual, Set.indicator_of_notMem htarget]
      simp
    have hright :
        (∫ omega in armGroupEvent group arm c m,
          V ^ 2 * (armGroupEvent group arm a k).indicator
            (fun _ => (1 : Real)) omega ∂mu) = 0 := by
      apply setIntegral_eq_zero_of_ae_eq_zero
      filter_upwards [] with omega homega
      have htarget : omega ∉ armGroupEvent group arm a k := by
        intro ht
        apply hlabel
        exact Prod.ext (ht.2.symm.trans homega.2) (ht.1.symm.trans homega.1)
      rw [Set.indicator_of_notMem htarget]
      simp
    rw [hleft, hright]

/-- If [group labels, arm labels, and outcomes are measurable](hyp:hgroup,harm,hY),
[every supported residual has a finite second moment](hyp:hmem), [each residual
is centered within its arm/group cell](hyp:hcenter), and [the two sample
coordinates differ](hyp:hij), [any finite-design weight times their two
supported residuals has product-law integral zero](goal). -/
lemma integral_designWeight_residual_cross_coordinates_eq_zero
    {n : Nat} (mu : Measure Omega) [IsProbabilityMeasure mu]
    (group : Omega -> kappa) (arm : Omega -> Bool) (Y : Omega -> Real)
    (center : Bool -> kappa -> Real)
    (hgroup : Measurable group) (harm : Measurable arm) (hY : Measurable Y)
    (hmem : ∀ a k,
      MemLp (supportedArmGroupResidual group arm Y center a k) 2 mu)
    (hcenter : ∀ a k,
      ∫ omega in armGroupEvent group arm a k,
        armGroupResidual Y center a k omega ∂mu = 0)
    (W : (Fin n -> kappa × Bool) -> Real)
    (i j : Fin n) (hij : i ≠ j) (a b : Bool) (k l : kappa) :
    ∫ z : Fin n -> Omega,
      W (sampleDesign group arm z) *
        supportedArmGroupResidual group arm Y center a k (z i) *
        supportedArmGroupResidual group arm Y center b l (z j)
      ∂(Measure.pi (fun _ : Fin n => mu)) = 0 := by
  -- Split off coordinate `i` with `piEquivPiSubtypeProd`.  For every fixed
  -- complement, the weight and the `j` residual depend on `omega_i` only
  -- through its finite design label.  Partition that one-coordinate integral
  -- by labels and use `hcenter` on each fiber.
  classical
  let f : Fin n -> Omega -> Real := fun q =>
    if q = i then supportedArmGroupResidual group arm Y center a k
    else if q = j then supportedArmGroupResidual group arm Y center b l
    else fun _ => 1
  have hf : ∀ q, Integrable (f q) mu := by
    intro q
    dsimp [f]
    split_ifs
    · exact (hmem a k).integrable (by norm_num)
    · exact (hmem b l).integrable (by norm_num)
    · exact integrable_const 1
  have hformula := integral_designWeight_mul_prod mu group arm hgroup harm W f hf
  have hrhs :
      (∑ d : Fin n -> kappa × Bool, W d * ∏ q,
        ∫ omega in armGroupEvent group arm (d q).2 (d q).1, f q omega ∂mu) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    have hzero :
        (∫ omega in armGroupEvent group arm (d i).2 (d i).1, f i omega ∂mu) = 0 := by
      simpa [f] using setIntegral_supported_eq_zero mu group arm Y center
        hgroup harm hcenter a (d i).2 k (d i).1
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero]
    simp
  have hprod_eval (z : Fin n -> Omega) :
      (∏ q, f q (z q)) =
        supportedArmGroupResidual group arm Y center a k (z i) *
          supportedArmGroupResidual group arm Y center b l (z j) := by
    calc
      (∏ q, f q (z q)) = ∏ q,
          (if q = i then supportedArmGroupResidual group arm Y center a k (z q) else 1) *
          (if q = j then supportedArmGroupResidual group arm Y center b l (z q) else 1) := by
        apply Finset.prod_congr rfl
        intro q hq
        by_cases hqi : q = i
        · subst q
          simp [f, hij]
        · by_cases hqj : q = j
          · subst q
            simp [f, hqi]
          · simp [f, hqi, hqj]
      _ = (∏ q, if q = i then
              supportedArmGroupResidual group arm Y center a k (z q) else 1) *
            ∏ q, if q = j then
              supportedArmGroupResidual group arm Y center b l (z q) else 1 := by
        rw [Finset.prod_mul_distrib]
      _ = supportedArmGroupResidual group arm Y center a k (z i) *
          supportedArmGroupResidual group arm Y center b l (z j) := by
        simp
  calc
    (∫ z : Fin n -> Omega,
      W (sampleDesign group arm z) *
        supportedArmGroupResidual group arm Y center a k (z i) *
        supportedArmGroupResidual group arm Y center b l (z j)
      ∂(Measure.pi (fun _ : Fin n => mu))) =
      ∫ z : Fin n -> Omega,
        W (sampleDesign group arm z) * ∏ q, f q (z q)
      ∂(Measure.pi (fun _ : Fin n => mu)) := by
        congr 1
        funext z
        rw [hprod_eval]
        ring
    _ = ∑ d : Fin n -> kappa × Bool, W d * ∏ q,
        ∫ omega in armGroupEvent group arm (d q).2 (d q).1, f q omega ∂mu := hformula
    _ = 0 := hrhs

/-- If [group labels, arm labels, and outcomes are measurable](hyp:hgroup,harm,hY),
[every supported residual has a finite second moment](hyp:hmem), [each cell's
residual second moment obeys the stated envelope](hyp:hsq), and [the design
weight is nonnegative](hyp:hW), [the weighted residual square at one sample
coordinate is bounded in expectation by the corresponding weighted cell
indicator envelope](goal). -/
lemma integral_designWeight_residual_sq_le_indicator
    {n : Nat} (mu : Measure Omega) [IsProbabilityMeasure mu]
    (group : Omega -> kappa) (arm : Omega -> Bool) (Y : Omega -> Real)
    (center : Bool -> kappa -> Real) (V : Real)
    (hgroup : Measurable group) (harm : Measurable arm) (hY : Measurable Y)
    (hmem : ∀ a k,
      MemLp (supportedArmGroupResidual group arm Y center a k) 2 mu)
    (hsq : ∀ a k,
      ∫ omega in armGroupEvent group arm a k,
          (armGroupResidual Y center a k omega) ^ 2 ∂mu ≤
        (mu (armGroupEvent group arm a k)).toReal * V ^ 2)
    (W : (Fin n -> kappa × Bool) -> Real) (hW : ∀ d, 0 ≤ W d)
    (i : Fin n) (a : Bool) (k : kappa) :
    ∫ z : Fin n -> Omega,
      W (sampleDesign group arm z) *
        (supportedArmGroupResidual group arm Y center a k (z i)) ^ 2
      ∂(Measure.pi (fun _ : Fin n => mu)) ≤
    V ^ 2 * ∫ z : Fin n -> Omega,
      W (sampleDesign group arm z) *
        (armGroupEvent group arm a k).indicator (fun _ => (1 : Real)) (z i)
      ∂(Measure.pi (fun _ : Fin n => mu)) := by
  -- Use the same replacement-coordinate split.  On each fixed design fiber
  -- `W` is constant; pull it out and apply `hsq`.  `hmem` supplies all Fubini
  -- and integrability obligations for the unbounded residual.
  classical
  let f : Fin n -> Omega -> Real := fun q =>
    if q = i then fun omega =>
      (supportedArmGroupResidual group arm Y center a k omega) ^ 2
    else fun _ => 1
  let g : Fin n -> Omega -> Real := fun q =>
    if q = i then fun omega =>
      V ^ 2 * (armGroupEvent group arm a k).indicator (fun _ => (1 : Real)) omega
    else fun _ => 1
  have hf : ∀ q, Integrable (f q) mu := by
    intro q
    dsimp [f]
    split_ifs
    · exact (hmem a k).integrable_sq
    · exact integrable_const 1
  have hg : ∀ q, Integrable (g q) mu := by
    intro q
    dsimp [g]
    split_ifs
    · exact ((integrable_const (1 : Real)).indicator
        (measurableSet_armGroupEvent group arm hgroup harm a k)).const_mul (V ^ 2)
    · exact integrable_const 1
  have hformula_f := integral_designWeight_mul_prod mu group arm hgroup harm W f hf
  have hformula_g := integral_designWeight_mul_prod mu group arm hgroup harm W g hg
  have hsum_le :
      (∑ d : Fin n -> kappa × Bool, W d * ∏ q,
        ∫ omega in armGroupEvent group arm (d q).2 (d q).1, f q omega ∂mu) ≤
      ∑ d : Fin n -> kappa × Bool, W d * ∏ q,
        ∫ omega in armGroupEvent group arm (d q).2 (d q).1, g q omega ∂mu := by
    apply Finset.sum_le_sum
    intro d hd
    apply mul_le_mul_of_nonneg_left _ (hW d)
    apply Finset.prod_le_prod
    · intro q hq
      apply integral_nonneg
      intro omega
      dsimp [f]
      split_ifs <;> positivity
    · intro q hq
      by_cases hqi : q = i
      · subst q
        simpa [f, g] using setIntegral_supported_sq_le_indicator mu group arm Y center V
          hgroup harm hsq a (d i).2 k (d i).1
      · simp [f, g, hqi]
  have hprod_f (z : Fin n -> Omega) :
      (∏ q, f q (z q)) =
        (supportedArmGroupResidual group arm Y center a k (z i)) ^ 2 := by
    calc
      (∏ q, f q (z q)) = ∏ q, if q = i then
          (supportedArmGroupResidual group arm Y center a k (z q)) ^ 2 else 1 := by
        apply Finset.prod_congr rfl
        intro q hq
        by_cases hqi : q = i <;> simp [f, hqi]
      _ = (supportedArmGroupResidual group arm Y center a k (z i)) ^ 2 := by
        simpa using (Finset.prod_ite_eq' Finset.univ i
          (fun q => (supportedArmGroupResidual group arm Y center a k (z q)) ^ 2))
  have hprod_g (z : Fin n -> Omega) :
      (∏ q, g q (z q)) =
        V ^ 2 * (armGroupEvent group arm a k).indicator (fun _ => (1 : Real)) (z i) := by
    calc
      (∏ q, g q (z q)) = ∏ q, if q = i then V ^ 2 *
          (armGroupEvent group arm a k).indicator (fun _ => (1 : Real)) (z q) else 1 := by
        apply Finset.prod_congr rfl
        intro q hq
        by_cases hqi : q = i <;> simp [g, hqi]
      _ = V ^ 2 * (armGroupEvent group arm a k).indicator
          (fun _ => (1 : Real)) (z i) := by
        simpa using (Finset.prod_ite_eq' Finset.univ i
          (fun q => V ^ 2 *
            (armGroupEvent group arm a k).indicator (fun _ => (1 : Real)) (z q)))
  calc
    (∫ z : Fin n -> Omega,
      W (sampleDesign group arm z) *
        (supportedArmGroupResidual group arm Y center a k (z i)) ^ 2
      ∂(Measure.pi (fun _ : Fin n => mu))) =
      ∫ z : Fin n -> Omega, W (sampleDesign group arm z) * ∏ q, f q (z q)
        ∂(Measure.pi (fun _ : Fin n => mu)) := by
          congr 1
          funext z
          rw [hprod_f]
    _ = ∑ d : Fin n -> kappa × Bool, W d * ∏ q,
        ∫ omega in armGroupEvent group arm (d q).2 (d q).1, f q omega ∂mu := hformula_f
    _ ≤ ∑ d : Fin n -> kappa × Bool, W d * ∏ q,
        ∫ omega in armGroupEvent group arm (d q).2 (d q).1, g q omega ∂mu := hsum_le
    _ = ∫ z : Fin n -> Omega, W (sampleDesign group arm z) * ∏ q, g q (z q)
        ∂(Measure.pi (fun _ : Fin n => mu)) := hformula_g.symm
    _ = V ^ 2 * ∫ z : Fin n -> Omega,
      W (sampleDesign group arm z) *
        (armGroupEvent group arm a k).indicator (fun _ => (1 : Real)) (z i)
      ∂(Measure.pi (fun _ : Fin n => mu)) := by
        rw [← integral_const_mul]
        congr 1
        funext z
        rw [hprod_g]
        ring

/-- If [group and arm labels are measurable](hyp:hgroup,harm), [the overlap
margin is positive and at most one half](hyp:hepsilon,hepsilon_half), and [both
arms receive at least that share in every positive-mass group](hyp:hoverlap),
[the expected design variance factor is at most sixteen divided by the squared
margin times one minus the margin, multiplied by expected reciprocal usable
occupancy](goal). This includes zero-mass groups, empty samples, empty group
types, and every zero-count boundary. -/
lemma integral_occupancyDesignVarianceFactor_le_reciprocal
    {n : Nat} (mu : Measure Omega) [IsProbabilityMeasure mu]
    (group : Omega -> kappa) (arm : Omega -> Bool)
    (hgroup : Measurable group) (harm : Measurable arm)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilon_half : epsilon ≤ (1 / 2 : Real))
    (hoverlap : ∀ k, 0 < (mu (groupEvent group k)).toReal -> ∀ a,
      epsilon * (mu (groupEvent group k)).toReal ≤
        (mu (armGroupEvent group arm a k)).toReal) :
    ∫ z : Fin n -> Omega, occupancyDesignVarianceFactor group arm z
        ∂(Measure.pi (fun _ : Fin n => mu)) ≤
      (16 / (epsilon ^ 2 * (1 - epsilon))) *
        ∫ z : Fin n -> Omega, inverseUsableGroupTotal group arm z
          ∂(Measure.pi (fun _ : Fin n => mu)) := by
  -- Push the sample to its finite `(group,arm)` design.  Enumerate group
  -- assignments and then arm subsets within each group.  Conditional on a
  -- group count `m`, use `binomial_inverse_two_arms_interior_le`; compare the
  -- change in the global usable denominator at the two endpoint designs and
  -- sum over groups.  Zero-mass fibers contribute zero before division.
  classical
  let q : kappa → Bool → Real := fun k a =>
    (mu (armGroupEvent group arm a k)).toReal
  let g : kappa → Real := fun k => (mu (groupEvent group k)).toReal
  have hq (k : kappa) (a : Bool) : 0 ≤ q k a := by
    dsimp [q]
    positivity
  have hsum (k : kappa) : q k false + q k true = g k := by
    have hpart : groupEvent group k =
        armGroupEvent group arm false k ∪ armGroupEvent group arm true k := by
      ext omega
      cases h : arm omega <;> simp [groupEvent, armGroupEvent, h]
    have hdisj : Disjoint (armGroupEvent group arm false k)
        (armGroupEvent group arm true k) := by
      rw [Set.disjoint_left]
      intro omega hf ht
      exact Bool.false_ne_true (hf.2.symm.trans ht.2)
    have hmeas : MeasurableSet (armGroupEvent group arm true k) :=
      measurableSet_armGroupEvent group arm hgroup harm true k
    have hadd : mu (armGroupEvent group arm false k) +
        mu (armGroupEvent group arm true k) = mu (groupEvent group k) := by
      rw [← measure_union hdisj hmeas, hpart]
    dsimp [q, g]
    rw [← ENNReal.toReal_add (measure_ne_top mu _) (measure_ne_top mu _), hadd]
  have hoverlap' (k : kappa) (hk : 0 < g k) (a : Bool) :
      epsilon * g k ≤ q k a := by
    exact hoverlap k (by simpa [g] using hk) a
  let Wv : (Fin n → kappa × Bool) → Real := fun d =>
    occupancyDesignVarianceFactor Prod.fst Prod.snd d
  let Wi : (Fin n → kappa × Bool) → Real := fun d =>
    inverseUsableGroupTotal Prod.fst Prod.snd d
  have hone : ∀ i : Fin n, Integrable (fun _ : Omega => (1 : Real)) mu := by
    intro i
    exact integrable_const 1
  have hformula (W : (Fin n → kappa × Bool) → Real) :
      (∫ z : Fin n → Omega, W (sampleDesign group arm z)
        ∂(Measure.pi (fun _ : Fin n => mu))) =
      ∑ d : Fin n → kappa × Bool, W d * ∏ i, q (d i).1 (d i).2 := by
    have h := integral_designWeight_mul_prod mu group arm hgroup harm W
      (fun _ _ => (1 : Real)) hone
    simpa [q, Measure.real] using h
  have hsample_v (z : Fin n → Omega) :
      Wv (sampleDesign group arm z) = occupancyDesignVarianceFactor group arm z := by
    rfl
  have hsample_i (z : Fin n → Omega) :
      Wi (sampleDesign group arm z) = inverseUsableGroupTotal group arm z := by
    rfl
  have hfinite := sum_jointWeight_variance_le_inverse (n := n) q g epsilon
    hq hsum hepsilon hepsilon_half hoverlap'
  have hsum_nonneg :
      0 ≤ ∑ d : Fin n → kappa × Bool, (∏ i, q (d i).1 (d i).2) * Wi d := by
    apply Finset.sum_nonneg
    intro d hd
    apply mul_nonneg
    · exact Finset.prod_nonneg fun i _ => hq (d i).1 (d i).2
    · unfold Wi inverseUsableGroupTotal
      split <;> positivity
  have heps1 : 0 < 1 - epsilon := by linarith
  have hden : 0 < epsilon ^ 2 * (1 - epsilon) := by positivity
  have hconst : 4 / (epsilon ^ 2 * (1 - epsilon)) ≤
      16 / (epsilon ^ 2 * (1 - epsilon)) := by
    exact div_le_div_of_nonneg_right (by norm_num) hden.le
  calc
    (∫ z : Fin n → Omega, occupancyDesignVarianceFactor group arm z
        ∂(Measure.pi (fun _ : Fin n => mu))) =
        ∑ d : Fin n → kappa × Bool, Wv d * ∏ i, q (d i).1 (d i).2 := by
      rw [← hformula Wv]
      apply integral_congr_ae
      filter_upwards [] with z
      exact (hsample_v z).symm
    _ = ∑ d : Fin n → kappa × Bool,
        (∏ i, q (d i).1 (d i).2) * Wv d := by
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ (4 / (epsilon ^ 2 * (1 - epsilon))) *
        ∑ d : Fin n → kappa × Bool,
          (∏ i, q (d i).1 (d i).2) * Wi d := hfinite
    _ ≤ (16 / (epsilon ^ 2 * (1 - epsilon))) *
        ∑ d : Fin n → kappa × Bool,
          (∏ i, q (d i).1 (d i).2) * Wi d :=
      mul_le_mul_of_nonneg_right hconst hsum_nonneg
    _ = (16 / (epsilon ^ 2 * (1 - epsilon))) *
        ∫ z : Fin n → Omega, inverseUsableGroupTotal group arm z
          ∂(Measure.pi (fun _ : Fin n => mu)) := by
      have hi :
          (∫ z : Fin n → Omega, inverseUsableGroupTotal group arm z
            ∂(Measure.pi (fun _ : Fin n => mu))) =
            ∑ d : Fin n → kappa × Bool, Wi d * ∏ i, q (d i).1 (d i).2 := by
        calc
          (∫ z : Fin n → Omega, inverseUsableGroupTotal group arm z
            ∂(Measure.pi (fun _ : Fin n => mu))) =
              ∫ z : Fin n → Omega, Wi (sampleDesign group arm z)
                ∂(Measure.pi (fun _ : Fin n => mu)) := by
            apply integral_congr_ae
            filter_upwards [] with z
            exact (hsample_i z).symm
          _ = _ := hformula Wi
      rw [hi]
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      ring

end Causalean.Stat
