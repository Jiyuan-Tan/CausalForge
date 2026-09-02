import Causalean.Stat.FiniteRaoBlackwell.Core

/-!
# Finite factorization sufficiency

This module gives a finite Fisher--Neyman factorization criterion for the statistic of a
`FiniteUniformExperiment`.  A state-dependent factor through the statistic and a nonnegative
state-independent carrier weight determine a common conditional distribution of the full data
given the statistic.  Null carrier fibers are totalized by the experiment's fallback point.
-/

open scoped BigOperators

namespace Causalean.Stat.FiniteRaoBlackwell

variable {Latent Allocation Observation Statistic : Type*}
variable [Fintype Latent] [Fintype Allocation] [Fintype Observation] [Fintype Statistic]
variable [DecidableEq Allocation] [DecidableEq Observation] [DecidableEq Statistic]

namespace FiniteUniformExperiment

variable (E : FiniteUniformExperiment Latent Allocation Observation Statistic)

/-- A common finite conditional law assigns normalized nonnegative full-data weights to every
statistic value and agrees with each statewise Bayes conditional on every positive-mass fiber. -/
structure CommonConditionalKernel where
  /-- The state-independent conditional full-data weights. -/
  weight : Statistic → Allocation × Observation → ℝ
  /-- Common conditional weights are nonnegative. -/
  weight_nonneg : ∀ s z, 0 ≤ weight s z
  /-- Common conditional weights are normalized at every statistic value. -/
  weight_sum : ∀ s, ∑ z, weight s z = 1
  /-- Positive statewise fibers have the common conditional weights. -/
  eq_conditionalWeight : ∀ θ s, 0 < E.statisticMass θ s →
    ∀ z, weight s z = E.conditionalWeight θ s z

/-- A sufficient factorization writes every full-data mass as a nonnegative factor depending
on the state and data only through the statistic, times a nonnegative state-independent carrier
weight on the full data. -/
structure SufficientFactorization where
  /-- The state-independent carrier weight on full-data points. -/
  carrierWeight : Allocation × Observation → ℝ
  /-- Carrier weights are nonnegative. -/
  carrierWeight_nonneg : ∀ z, 0 ≤ carrierWeight z
  /-- The state-and-statistic likelihood factor. -/
  statisticFactor : Latent → Statistic → ℝ
  /-- State-and-statistic factors are nonnegative. -/
  statisticFactor_nonneg : ∀ θ s, 0 ≤ statisticFactor θ s
  /-- The full-data mass factors through the statistic. -/
  jointMass_factor : ∀ θ z,
    E.jointMass θ z = statisticFactor θ (E.sampleStatistic z) * carrierWeight z

namespace SufficientFactorization

variable {E : FiniteUniformExperiment Latent Allocation Observation Statistic}
variable (F : E.SufficientFactorization)

/-- The carrier mass of a statistic fiber is the sum of the state-independent carrier weights
over full-data points having that statistic value. -/
noncomputable def fiberCarrierMass (s : Statistic) : ℝ :=
  ∑ z : Allocation × Observation,
    if E.sampleStatistic z = s then F.carrierWeight z else 0

/-- Every carrier fiber mass is nonnegative. -/
theorem fiberCarrierMass_nonneg (s : Statistic) : 0 ≤ F.fiberCarrierMass s := by
  /- Expand the fiber sum and use carrierWeight_nonneg in the matching branch. -/
  classical
  exact Finset.sum_nonneg fun z _ => by
    split_ifs
    · exact F.carrierWeight_nonneg z
    · exact le_rfl

/-- The statistic mass factors as the state-and-statistic factor times the carrier fiber mass. -/
theorem statisticMass_eq_factor_mul_fiberCarrierMass (θ : Latent) (s : Statistic) :
    E.statisticMass θ s = F.statisticFactor θ s * F.fiberCarrierMass s := by
  /- Rewrite every joint atom by jointMass_factor; on the selected fiber the statistic factor
  is constant, so Finset.mul_sum factors it out. -/
  classical
  simp only [FiniteUniformExperiment.statisticMass, fiberCarrierMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : E.sampleStatistic z = s
  · simp [hz, F.jointMass_factor]
  · simp [hz]

/-- Positive statistic mass forces the state-independent carrier fiber to have positive mass. -/
theorem fiberCarrierMass_pos_of_statisticMass_pos {θ : Latent} {s : Statistic}
    (h : 0 < E.statisticMass θ s) :
    0 < F.fiberCarrierMass s := by
  /- Rewrite statisticMass using the product formula.  Both factors are nonnegative, so a
  positive product forces the carrier factor to be positive. -/
  have hprod : 0 < F.statisticFactor θ s * F.fiberCarrierMass s := by
    rwa [← F.statisticMass_eq_factor_mul_fiberCarrierMass θ s]
  exact pos_of_mul_pos_right hprod (F.statisticFactor_nonneg θ s)

/-- The factorization-induced conditional weight normalizes the carrier weight on positive
carrier fibers and uses the experiment's fallback point mass on null carrier fibers. -/
noncomputable def commonConditionalWeight (s : Statistic)
    (z : Allocation × Observation) : ℝ :=
  if 0 < F.fiberCarrierMass s then
    if E.sampleStatistic z = s then F.carrierWeight z / F.fiberCarrierMass s else 0
  else if z = E.fallbackSample then 1 else 0

/-- Factorization-induced common conditional weights are nonnegative on every fiber. -/
theorem commonConditionalWeight_nonneg (s : Statistic)
    (z : Allocation × Observation) :
    0 ≤ F.commonConditionalWeight s z := by
  /- Split on positive carrier fiber mass and on fiber membership; use div_nonneg in the
  positive branch and the fallback Kronecker mass in the null branch. -/
  classical
  by_cases hs : 0 < F.fiberCarrierMass s
  · simp only [commonConditionalWeight, hs, if_pos]
    split_ifs
    · exact div_nonneg (F.carrierWeight_nonneg z) (le_of_lt hs)
    · exact le_rfl
  · simp only [commonConditionalWeight, hs, if_false]
    split_ifs <;> norm_num

/-- Factorization-induced common conditional weights sum to one on every fiber. -/
theorem commonConditionalWeight_sum (s : Statistic) :
    ∑ z, F.commonConditionalWeight s z = 1 := by
  /- On a positive carrier fiber, the numerator sum is fiberCarrierMass and division cancels.
  On a null fiber, sum the fallback point mass. -/
  classical
  by_cases hs : 0 < F.fiberCarrierMass s
  · simp only [commonConditionalWeight, hs, if_pos]
    simp_rw [div_eq_mul_inv]
    have hfactor (z : Allocation × Observation) :
        (if E.sampleStatistic z = s then
            F.carrierWeight z * (F.fiberCarrierMass s)⁻¹ else 0) =
          (if E.sampleStatistic z = s then F.carrierWeight z else 0) *
            (F.fiberCarrierMass s)⁻¹ := by
      split_ifs <;> simp
    simp_rw [hfactor]
    rw [← Finset.sum_mul, show
      (∑ z : Allocation × Observation,
        if E.sampleStatistic z = s then F.carrierWeight z else 0) =
          F.fiberCarrierMass s from rfl]
    exact mul_inv_cancel₀ (ne_of_gt hs)
  · simp [commonConditionalWeight, hs]

/-- On [every positive statewise statistic fiber](hyp:h), [factorization identifies the common
conditional weight with the guarded Bayes conditional weight](goal). -/
theorem commonConditionalWeight_eq_conditionalWeight
    (θ : Latent) (s : Statistic) (h : 0 < E.statisticMass θ s)
    (z : Allocation × Observation) :
    F.commonConditionalWeight s z = E.conditionalWeight θ s z := by
  /- Positive statistic mass makes both factor terms positive.  Expand both guarded weights,
  rewrite statisticMass and jointMass by factorization, then cancel the statistic factor. -/
  classical
  have hcarrier : 0 < F.fiberCarrierMass s :=
    F.fiberCarrierMass_pos_of_statisticMass_pos h
  have hprod : 0 < F.statisticFactor θ s * F.fiberCarrierMass s := by
    rwa [← F.statisticMass_eq_factor_mul_fiberCarrierMass θ s]
  have hfactor : 0 < F.statisticFactor θ s :=
    pos_of_mul_pos_left hprod (F.fiberCarrierMass_nonneg s)
  rw [E.conditionalWeight_of_pos h]
  simp only [commonConditionalWeight, hcarrier, if_pos]
  by_cases hz : E.sampleStatistic z = s
  · simp only [hz, if_pos]
    rw [F.jointMass_factor, F.statisticMass_eq_factor_mul_fiberCarrierMass, hz]
    exact (mul_div_mul_left (F.carrierWeight z) (F.fiberCarrierMass s)
      (ne_of_gt hfactor)).symm
  · simp [hz]

/-- A sufficient factorization canonically produces a state-independent common conditional
kernel for the full data given the statistic, including a normalized value on null fibers. -/
noncomputable def toCommonConditionalKernel : E.CommonConditionalKernel where
  weight := F.commonConditionalWeight
  weight_nonneg := F.commonConditionalWeight_nonneg
  weight_sum := F.commonConditionalWeight_sum
  eq_conditionalWeight := F.commonConditionalWeight_eq_conditionalWeight

end SufficientFactorization

end FiniteUniformExperiment

end Causalean.Stat.FiniteRaoBlackwell
