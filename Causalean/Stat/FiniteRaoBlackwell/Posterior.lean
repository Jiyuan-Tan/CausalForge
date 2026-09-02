import Causalean.Stat.FiniteRaoBlackwell.Core

/-!
# Finite prior joint laws and guarded posterior kernels

This module mixes a finite latent-state prior with the statistic law of a
`FiniteUniformExperiment`.  It defines the resulting state--statistic joint mass, statistic
marginal, and guarded posterior law of the latent state given the statistic.  On a null
statistic fiber the posterior is totalized by the original prior, which preserves normalization
and does not affect disintegration.
-/

open scoped BigOperators

namespace Causalean.Stat.FiniteRaoBlackwell

open Causalean.Experimentation.DesignBased

variable {Latent Allocation Observation Statistic : Type*}
variable [Fintype Latent] [Fintype Allocation] [Fintype Observation] [Fintype Statistic]
variable [DecidableEq Allocation] [DecidableEq Observation] [DecidableEq Statistic]

namespace FiniteUniformExperiment

variable (E : FiniteUniformExperiment Latent Allocation Observation Statistic)

/-- Under a finite prior, the joint mass of a latent state and statistic value is prior mass
times the statewise statistic mass. -/
noncomputable def priorJointStatisticMass (prior : FiniteDesign Latent)
    (θ : Latent) (s : Statistic) : ℝ :=
  prior.p θ * E.statisticMass θ s

/-- Every prior state--statistic joint mass is nonnegative. -/
theorem priorJointStatisticMass_nonneg (prior : FiniteDesign Latent)
    (θ : Latent) (s : Statistic) :
    0 ≤ E.priorJointStatisticMass prior θ s := by
  /- Multiply prior and statewise-statistic nonnegativity. -/
  exact mul_nonneg (prior.p_nonneg θ) (E.statisticMass_nonneg θ s)

/-- The prior state--statistic joint masses sum to one. -/
theorem priorJointStatisticMass_sum (prior : FiniteDesign Latent) :
    ∑ p : Latent × Statistic, E.priorJointStatisticMass prior p.1 p.2 = 1 := by
  /- Expand the product sum, use statisticMass_sum at each state, then prior.p_sum. -/
  classical
  rw [Fintype.sum_prod_type]
  simp_rw [priorJointStatisticMass, ← Finset.mul_sum, E.statisticMass_sum, mul_one]
  exact prior.p_sum

/-- The prior-predictive statistic mass is the latent-state marginal of the prior joint law. -/
noncomputable def priorStatisticMass (prior : FiniteDesign Latent) (s : Statistic) : ℝ :=
  ∑ θ, E.priorJointStatisticMass prior θ s

/-- Every prior-predictive statistic mass is nonnegative. -/
theorem priorStatisticMass_nonneg (prior : FiniteDesign Latent) (s : Statistic) :
    0 ≤ E.priorStatisticMass prior s := by
  /- Sum the nonnegative prior joint atoms over latent states. -/
  classical
  exact Finset.sum_nonneg fun θ _ => E.priorJointStatisticMass_nonneg prior θ s

/-- The prior-predictive statistic masses sum to one. -/
theorem priorStatisticMass_sum (prior : FiniteDesign Latent) :
    ∑ s, E.priorStatisticMass prior s = 1 := by
  /- Swap the statistic/state sums and reuse the joint normalization calculation. -/
  classical
  simp_rw [priorStatisticMass]
  rw [Finset.sum_comm]
  simpa only [Fintype.sum_prod_type] using E.priorJointStatisticMass_sum prior

/-- The guarded posterior weight is Bayes' ratio on a positive prior-predictive fiber and the
original prior on a null fiber. -/
noncomputable def posteriorWeight (prior : FiniteDesign Latent)
    (s : Statistic) (θ : Latent) : ℝ :=
  if 0 < E.priorStatisticMass prior s then
    E.priorJointStatisticMass prior θ s / E.priorStatisticMass prior s
  else prior.p θ

/-- On a positive prior-predictive fiber, the guarded posterior is the usual Bayes ratio. -/
theorem posteriorWeight_of_pos (prior : FiniteDesign Latent) {s : Statistic}
    (h : 0 < E.priorStatisticMass prior s) (θ : Latent) :
    E.posteriorWeight prior s θ =
      E.priorJointStatisticMass prior θ s / E.priorStatisticMass prior s := by
  /- Unfold posteriorWeight and simplify the positive guard. -/
  simp [posteriorWeight, h]

/-- On a null prior-predictive fiber, the guarded posterior is the original prior. -/
theorem posteriorWeight_of_eq_zero (prior : FiniteDesign Latent) {s : Statistic}
    (h : E.priorStatisticMass prior s = 0) (θ : Latent) :
    E.posteriorWeight prior s θ = prior.p θ := by
  /- Unfold posteriorWeight; nonnegativity plus zero mass rules out the positive guard. -/
  simp [posteriorWeight, h]

/-- Every guarded posterior weight is nonnegative. -/
theorem posteriorWeight_nonneg (prior : FiniteDesign Latent)
    (s : Statistic) (θ : Latent) :
    0 ≤ E.posteriorWeight prior s θ := by
  /- Split on positive priorStatisticMass; use div_nonneg or prior.p_nonneg. -/
  classical
  by_cases h : 0 < E.priorStatisticMass prior s
  · rw [E.posteriorWeight_of_pos prior h]
    exact div_nonneg (E.priorJointStatisticMass_nonneg prior θ s) (le_of_lt h)
  · have hs : E.priorStatisticMass prior s = 0 :=
      le_antisymm (le_of_not_gt h) (E.priorStatisticMass_nonneg prior s)
    rw [E.posteriorWeight_of_eq_zero prior hs]
    exact prior.p_nonneg θ

/-- Guarded posterior weights sum to one on positive and null prior-predictive fibers. -/
theorem posteriorWeight_sum (prior : FiniteDesign Latent) (s : Statistic) :
    ∑ θ, E.posteriorWeight prior s θ = 1 := by
  /- Positive fibers divide the defining marginal sum by itself; null fibers use prior.p_sum. -/
  classical
  by_cases h : 0 < E.priorStatisticMass prior s
  · simp_rw [E.posteriorWeight_of_pos prior h, div_eq_mul_inv]
    rw [← Finset.sum_mul, show
      (∑ θ, E.priorJointStatisticMass prior θ s) =
        E.priorStatisticMass prior s from rfl]
    exact mul_inv_cancel₀ (ne_of_gt h)
  · have hs : E.priorStatisticMass prior s = 0 :=
      le_antisymm (le_of_not_gt h) (E.priorStatisticMass_nonneg prior s)
    simp [E.posteriorWeight_of_eq_zero prior hs, prior.p_sum]

/-- Multiplying the statistic marginal by its guarded posterior weight recovers each
state--statistic joint atom, including on null fibers. -/
theorem priorStatisticMass_mul_posteriorWeight (prior : FiniteDesign Latent)
    (s : Statistic) (θ : Latent) :
    E.priorStatisticMass prior s * E.posteriorWeight prior s θ =
      E.priorJointStatisticMass prior θ s := by
  /- Positive mass is cancellation.  If the marginal is zero, nonnegativity of every joint
  summand forces the selected joint atom to vanish. -/
  classical
  by_cases h : 0 < E.priorStatisticMass prior s
  · rw [E.posteriorWeight_of_pos prior h]
    exact mul_div_cancel₀ _ (ne_of_gt h)
  · have hs : E.priorStatisticMass prior s = 0 :=
      le_antisymm (le_of_not_gt h) (E.priorStatisticMass_nonneg prior s)
    rw [hs, zero_mul]
    have hsum :
        (∑ θ', E.priorJointStatisticMass prior θ' s) = 0 := by
      simpa [priorStatisticMass] using hs
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun θ' _ =>
      E.priorJointStatisticMass_nonneg prior θ' s)).mp hsum θ (Finset.mem_univ θ)
    exact hterm.symm

/-- The guarded posterior weights define a finite latent-state design for every statistic value. -/
noncomputable def posteriorDesign (prior : FiniteDesign Latent) (s : Statistic) :
    FiniteDesign Latent where
  p := E.posteriorWeight prior s
  p_nonneg := E.posteriorWeight_nonneg prior s
  p_sum := E.posteriorWeight_sum prior s

/-- The prior-predictive statistic masses define a finite statistic design. -/
noncomputable def priorStatisticDesign (prior : FiniteDesign Latent) :
    FiniteDesign Statistic where
  p := E.priorStatisticMass prior
  p_nonneg := E.priorStatisticMass_nonneg prior
  p_sum := E.priorStatisticMass_sum prior

/-- Every real test function of latent state and statistic has [the same prior-joint expectation
as prior-predictive statistic expectation of posterior conditional expectation](goal); null
fibers contribute exactly zero. -/
theorem posterior_disintegrate_sum (prior : FiniteDesign Latent)
    (f : Latent → Statistic → ℝ) :
    ∑ θ, ∑ s, E.priorJointStatisticMass prior θ s * f θ s =
      ∑ s, E.priorStatisticMass prior s *
        (∑ θ, E.posteriorWeight prior s θ * f θ s) := by
  /- Distribute the outer marginal through each inner sum, apply the atomwise posterior
  factorization, and swap the two finite sums. -/
  classical
  simp_rw [Finset.mul_sum, ← mul_assoc,
    E.priorStatisticMass_mul_posteriorWeight prior]
  rw [Finset.sum_comm]

end FiniteUniformExperiment

end Causalean.Stat.FiniteRaoBlackwell
