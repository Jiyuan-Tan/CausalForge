import Causalean.Stat.Minimax.FiniteKernelBayes
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Finite posterior means and continuous-mixture Bayes risk

This module conditions a finite prior through an arbitrary finite Markov observation kernel.
It provides zero-guarded posterior weights, exact finite disintegration and squared-loss
completion, and identifies the resulting real-valued Bayes-risk infimum.

It also transports the construction through a continuous prior mixed into the finite latent
space, reusing the induced finite design to transfer estimator-wise integral lower bounds to
finite and continuous-mixture Bayes risks.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Causalean.Stat

open Causalean.Experimentation.DesignBased

variable {S X : Type*} [Fintype S] [Fintype X]
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSingletonClass X]

/-- The real singleton mass assigned to an observation by a finite-state Markov kernel. -/
noncomputable def kernelMass (L : Kernel S X) (s : S) (x : X) : ℝ :=
  (L s).real {x}

/-- [Every singleton observation mass emitted by a Markov kernel is nonnegative](goal). -/
theorem kernelMass_nonneg (L : Kernel S X) (s : S) (x : X) :
    0 ≤ kernelMass L s x := by
  exact measureReal_nonneg

/-- [The singleton observation masses emitted in each latent state sum to one](goal). -/
theorem kernelMass_sum (L : Kernel S X) [IsMarkovKernel L] (s : S) :
    ∑ x, kernelMass L s x = 1 := by
  -- Rewrite the finite singleton sum as the real mass of `univ`, then use Markov normalization.
  simpa [kernelMass] using
    (sum_measureReal_singleton (μ := L s) (Finset.univ : Finset X))

/-- The joint mass of a latent state and observation is prior mass times conditional
observation mass. -/
noncomputable def jointMass (ν : FiniteDesign S) (L : Kernel S X) (s : S) (x : X) : ℝ :=
  ν.p s * kernelMass L s x

/-- [Every latent-state--observation joint mass is nonnegative](goal). -/
theorem jointMass_nonneg (ν : FiniteDesign S) (L : Kernel S X) (s : S) (x : X) :
    0 ≤ jointMass ν L s x := by
  exact mul_nonneg (ν.p_nonneg s) (kernelMass_nonneg L s x)

/-- [The joint masses of a normalized finite prior and Markov observation kernel sum to
one](goal). -/
theorem jointMass_sum (ν : FiniteDesign S) (L : Kernel S X) [IsMarkovKernel L] :
    ∑ s, ∑ x, jointMass ν L s x = 1 := by
  classical
  simp_rw [jointMass, ← Finset.mul_sum, kernelMass_sum, mul_one]
  exact ν.p_sum

/-- The observation marginal is the sum of joint masses over the latent state. -/
noncomputable def observationMass (ν : FiniteDesign S) (L : Kernel S X) (x : X) : ℝ :=
  ∑ s, jointMass ν L s x

/-- [Every observation marginal mass is nonnegative](goal). -/
theorem observationMass_nonneg (ν : FiniteDesign S) (L : Kernel S X) (x : X) :
    0 ≤ observationMass ν L x := by
  exact Finset.sum_nonneg fun s _ => jointMass_nonneg ν L s x

/-- [The observation marginal masses sum to one](goal). -/
theorem observationMass_sum (ν : FiniteDesign S) (L : Kernel S X) [IsMarkovKernel L] :
    ∑ x, observationMass ν L x = 1 := by
  classical
  simp_rw [observationMass]
  rw [Finset.sum_comm]
  exact jointMass_sum ν L

/-- The guarded posterior weight is the Bayes ratio on a nonzero observation fiber and zero
on a null fiber. -/
noncomputable def posteriorWeight (ν : FiniteDesign S) (L : Kernel S X) (x : X) (s : S) : ℝ :=
  if observationMass ν L x = 0 then 0 else jointMass ν L s x / observationMass ν L x

/-- On [a nonzero observation fiber](hyp:hx), [the guarded posterior weight is the usual Bayes
ratio](goal). -/
theorem posteriorWeight_of_ne_zero (ν : FiniteDesign S) (L : Kernel S X) {x : X}
    (hx : observationMass ν L x ≠ 0) (s : S) :
    posteriorWeight ν L x s = jointMass ν L s x / observationMass ν L x := by
  simp [posteriorWeight, hx]

/-- On [a null observation fiber](hyp:hx), [every guarded posterior weight is zero](goal). -/
theorem posteriorWeight_of_eq_zero (ν : FiniteDesign S) (L : Kernel S X) {x : X}
    (hx : observationMass ν L x = 0) (s : S) :
    posteriorWeight ν L x s = 0 := by
  simp [posteriorWeight, hx]

/-- [Every guarded posterior weight is nonnegative](goal). -/
theorem posteriorWeight_nonneg (ν : FiniteDesign S) (L : Kernel S X) (x : X) (s : S) :
    0 ≤ posteriorWeight ν L x s := by
  classical
  by_cases hx : observationMass ν L x = 0
  · rw [posteriorWeight_of_eq_zero ν L hx]
  · rw [posteriorWeight_of_ne_zero ν L hx]
    exact div_nonneg (jointMass_nonneg ν L s x) (observationMass_nonneg ν L x)

/-- On [a positive-mass observation fiber](hyp:hx), [the guarded posterior weights sum to
one](goal). -/
theorem posteriorWeight_sum_of_pos (ν : FiniteDesign S) (L : Kernel S X) {x : X}
    (hx : 0 < observationMass ν L x) :
    ∑ s, posteriorWeight ν L x s = 1 := by
  classical
  simp_rw [posteriorWeight_of_ne_zero ν L (ne_of_gt hx), div_eq_mul_inv]
  rw [← Finset.sum_mul]
  change observationMass ν L x * (observationMass ν L x)⁻¹ = 1
  exact mul_inv_cancel₀ (ne_of_gt hx)

/-- On [a null observation fiber](hyp:hx), [the guarded posterior weights sum to zero](goal). -/
theorem posteriorWeight_sum_of_eq_zero (ν : FiniteDesign S) (L : Kernel S X) {x : X}
    (hx : observationMass ν L x = 0) :
    ∑ s, posteriorWeight ν L x s = 0 := by
  simp [posteriorWeight_of_eq_zero ν L hx]

/-- [Multiplying an observation marginal by its guarded posterior weight recovers the joint
atom, including on null fibers](goal). -/
theorem observationMass_mul_posteriorWeight (ν : FiniteDesign S) (L : Kernel S X)
    (x : X) (s : S) :
    observationMass ν L x * posteriorWeight ν L x s = jointMass ν L s x := by
  -- Split on the marginal.  The nonzero branch cancels; in the zero branch, nonnegativity and
  -- `sum_eq_zero_iff_of_nonneg` force every joint atom in the defining marginal sum to vanish.
  classical
  by_cases hx : observationMass ν L x = 0
  · rw [hx, zero_mul]
    have hsum : (∑ s', jointMass ν L s' x) = 0 := by
      simpa [observationMass] using hx
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun s' _ => jointMass_nonneg ν L s' x)).mp hsum s (Finset.mem_univ s)
    exact hterm.symm
  · rw [posteriorWeight_of_ne_zero ν L hx]
    exact mul_div_cancel₀ _ hx

/-- [Every real test function has the same joint expectation as the marginally weighted guarded
posterior expectation](goal). -/
theorem disintegrate_sum (ν : FiniteDesign S) (L : Kernel S X) (f : S → X → ℝ) :
    ∑ s, ∑ x, jointMass ν L s x * f s x =
      ∑ x, observationMass ν L x * (∑ s, posteriorWeight ν L x s * f s x) := by
  -- Distribute the marginal through the inner sum, use atomwise factorization, and swap sums.
  classical
  simp_rw [Finset.mul_sum, ← mul_assoc,
    observationMass_mul_posteriorWeight ν L]
  rw [Finset.sum_comm]

/-- The guarded posterior mean is the posterior-weighted average of an observation-dependent
real target. -/
noncomputable def posteriorMean (ν : FiniteDesign S) (L : Kernel S X)
    (t : S → X → ℝ) (x : X) : ℝ :=
  ∑ s, posteriorWeight ν L x s * t s x

/-- [Observation mass times the guarded posterior mean equals the corresponding joint weighted
target numerator, including on null fibers](goal). -/
theorem observationMass_mul_posteriorMean (ν : FiniteDesign S) (L : Kernel S X)
    (t : S → X → ℝ) (x : X) :
    observationMass ν L x * posteriorMean ν L t x =
      ∑ s, jointMass ν L s x * t s x := by
  classical
  simp_rw [posteriorMean, Finset.mul_sum, ← mul_assoc,
    observationMass_mul_posteriorWeight ν L]

/-- On [a positive-mass observation fiber](hyp:hx), [posterior target residuals have weighted
mean zero](goal). -/
theorem posterior_centered_sum_of_pos (ν : FiniteDesign S) (L : Kernel S X)
    (t : S → X → ℝ) {x : X} (hx : 0 < observationMass ν L x) :
    ∑ s, posteriorWeight ν L x s * (t s x - posteriorMean ν L t x) = 0 := by
  -- Expand subtraction and use positive-fiber posterior normalization plus the mean definition.
  classical
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [posteriorWeight_sum_of_pos ν L hx, one_mul]
  rw [posteriorMean]
  exact sub_self _

/-- The finite-design squared risk averages observation-dependent squared error over the joint
latent-state/observation law. -/
noncomputable def squaredRisk (ν : FiniteDesign S) (L : Kernel S X)
    (t : S → X → ℝ) (T : X → ℝ) : ℝ :=
  ∑ s, ∑ x, jointMass ν L s x * (T x - t s x) ^ 2

/-- The posterior residual risk averages squared deviations of the target from its guarded
posterior mean. -/
noncomputable def posteriorResidual (ν : FiniteDesign S) (L : Kernel S X)
    (t : S → X → ℝ) : ℝ :=
  ∑ x, observationMass ν L x *
    (∑ s, posteriorWeight ν L x s * (t s x - posteriorMean ν L t x) ^ 2)

/-- [Every estimator's squared risk equals posterior residual risk plus its marginally weighted
squared distance from the posterior mean](goal). -/
theorem squaredRisk_eq_posteriorResidual_add (ν : FiniteDesign S) (L : Kernel S X)
    (t : S → X → ℝ) (T : X → ℝ) :
    squaredRisk ν L t T = posteriorResidual ν L t +
      ∑ x, observationMass ν L x * (T x - posteriorMean ν L t x) ^ 2 := by
  -- Disintegrate the risk.  On positive fibers, expand the square around the posterior mean and
  -- kill the cross term with `posterior_centered_sum_of_pos`; null fibers vanish by their mass.
  classical
  rw [squaredRisk, disintegrate_sum ν L]
  unfold posteriorResidual
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx0 : observationMass ν L x = 0
  · simp [hx0]
  · have hx : 0 < observationMass ν L x :=
      lt_of_le_of_ne (observationMass_nonneg ν L x) (Ne.symm hx0)
    rw [← mul_add]
    congr 1
    calc
      (∑ s, posteriorWeight ν L x s * (T x - t s x) ^ 2) =
          ∑ s, (posteriorWeight ν L x s *
              (t s x - posteriorMean ν L t x) ^ 2 +
            posteriorWeight ν L x s *
              (T x - posteriorMean ν L t x) ^ 2 -
            (2 * (T x - posteriorMean ν L t x)) *
              (posteriorWeight ν L x s *
                (t s x - posteriorMean ν L t x))) := by
            apply Finset.sum_congr rfl
            intro s _
            ring
      _ = (∑ s, posteriorWeight ν L x s *
              (t s x - posteriorMean ν L t x) ^ 2) +
            (∑ s, posteriorWeight ν L x s) *
              (T x - posteriorMean ν L t x) ^ 2 -
            (2 * (T x - posteriorMean ν L t x)) *
              (∑ s, posteriorWeight ν L x s *
                (t s x - posteriorMean ν L t x)) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
              Finset.sum_mul, ← Finset.mul_sum]
      _ = (∑ s, posteriorWeight ν L x s *
              (t s x - posteriorMean ν L t x) ^ 2) +
            (T x - posteriorMean ν L t x) ^ 2 := by
            rw [posteriorWeight_sum_of_pos ν L hx,
              posterior_centered_sum_of_pos ν L t hx]
            ring

/-- [The guarded posterior-mean estimator has squared risk exactly equal to posterior residual
risk](goal). -/
theorem squaredRisk_posteriorMean (ν : FiniteDesign S) (L : Kernel S X)
    (t : S → X → ℝ) :
    squaredRisk ν L t (posteriorMean ν L t) = posteriorResidual ν L t := by
  rw [squaredRisk_eq_posteriorResidual_add]
  simp

/-- [The guarded posterior mean minimizes squared risk among all real estimators](goal). -/
theorem posteriorMean_minimizes (ν : FiniteDesign S) (L : Kernel S X)
    (t : S → X → ℝ) (T : X → ℝ) :
    squaredRisk ν L t (posteriorMean ν L t) ≤ squaredRisk ν L t T := by
  rw [squaredRisk_posteriorMean, squaredRisk_eq_posteriorResidual_add]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun x _ =>
    mul_nonneg (observationMass_nonneg ν L x) (sq_nonneg _))

/-- [The infimum over all real estimators of finite squared risk is exactly the posterior
residual Bayes risk](goal). -/
theorem iInf_squaredRisk_eq_posteriorResidual (ν : FiniteDesign S) (L : Kernel S X)
    (t : S → X → ℝ) :
    (⨅ T : X → ℝ, squaredRisk ν L t T) = posteriorResidual ν L t := by
  -- The minimizer supplies the upper bound.  For the lower bound use `le_ciInf` and
  -- `posteriorMean_minimizes`; no compactness or ENNReal conversion is needed.
  have hb : BddBelow (Set.range fun T : X → ℝ => squaredRisk ν L t T) := by
    refine ⟨posteriorResidual ν L t, ?_⟩
    rintro _ ⟨T, rfl⟩
    calc
      posteriorResidual ν L t = squaredRisk ν L t (posteriorMean ν L t) :=
        (squaredRisk_posteriorMean ν L t).symm
      _ ≤ squaredRisk ν L t T := posteriorMean_minimizes ν L t T
  apply le_antisymm
  · calc
      (⨅ T : X → ℝ, squaredRisk ν L t T) ≤
          squaredRisk ν L t (posteriorMean ν L t) := ciInf_le hb _
      _ = posteriorResidual ν L t := squaredRisk_posteriorMean ν L t
  · exact le_ciInf fun T => by
      calc
        posteriorResidual ν L t = squaredRisk ν L t (posteriorMean ν L t) :=
          (squaredRisk_posteriorMean ν L t).symm
        _ ≤ squaredRisk ν L t T := posteriorMean_minimizes ν L t T

/-- The statewise squared loss of an estimator averages over the observation kernel. -/
noncomputable def statewiseSquaredLoss (L : Kernel S X) (t : S → X → ℝ)
    (T : X → ℝ) (s : S) : ℝ :=
  ∑ x, kernelMass L s x * (T x - t s x) ^ 2

/-- [Finite-design expected statewise squared loss is the joint-law squared risk](goal). -/
theorem finiteDesign_expectedLoss_statewiseSquaredLoss (ν : FiniteDesign S) (L : Kernel S X)
    (t : S → X → ℝ) (T : X → ℝ) :
    ν.E (statewiseSquaredLoss L t T) = squaredRisk ν L t T := by
  simp only [FiniteDesign.E, statewiseSquaredLoss, squaredRisk, jointMass]
  simp_rw [Finset.mul_sum, ← mul_assoc]

/-- [The real-valued finite-design Bayes-risk infimum for observation-dependent squared loss is
exactly the posterior residual risk](goal). -/
theorem finiteDesignBayesRisk_statewiseSquaredLoss (ν : FiniteDesign S) (L : Kernel S X)
    (t : S → X → ℝ) :
    Causalean.Stat.finiteDesignBayesRisk ν (statewiseSquaredLoss L t) =
      posteriorResidual ν L t := by
  -- Unfold the generic Bayes risk, rewrite each design expectation as `squaredRisk`, and apply
  -- `iInf_squaredRisk_eq_posteriorResidual`.
  simp only [Causalean.Stat.finiteDesignBayesRisk,
    finiteDesign_expectedLoss_statewiseSquaredLoss]
  exact iInf_squaredRisk_eq_posteriorResidual ν L t

variable {Θ S X A : Type*}
variable [MeasurableSpace Θ] [Fintype S] [Nonempty S] [MeasurableSpace S]
variable [MeasurableSingletonClass S]
variable [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]

/-- [The continuous-prior mixture of an estimator's finite-observation squared loss is the
real-valued squared risk under the induced finite design](goal). -/
theorem mixedKernelLoss_statewiseSquaredLoss_eq_inducedSquaredRisk
    (π : Measure Θ) [IsProbabilityMeasure π]
    (K : Kernel Θ S) [IsMarkovKernel K] (L : Kernel S X)
    (t : S → X → ℝ) (T : X → ℝ) :
    Causalean.Stat.mixedKernelLoss π K (statewiseSquaredLoss L t) T =
      squaredRisk (Causalean.Stat.inducedFiniteDesign π K) L t T := by
  rw [← inducedFiniteDesign_expectedLoss_eq_mixedKernelLoss]
  exact finiteDesign_expectedLoss_statewiseSquaredLoss _ L t T

/-- [The real Bayes risk of continuously mixed finite-state squared loss equals the posterior
residual risk computed from the induced finite design](goal). -/
theorem realBayesRisk_statewiseSquaredLoss_eq_posteriorResidual
    (π : Measure Θ) [IsProbabilityMeasure π]
    (K : Kernel Θ S) [IsMarkovKernel K] (L : Kernel S X)
    (t : S → X → ℝ) :
    Causalean.Stat.realBayesRisk π K (statewiseSquaredLoss L t) =
      posteriorResidual (Causalean.Stat.inducedFiniteDesign π K) L t := by
  -- Chain `realBayesRisk_eq_inducedFiniteDesignBayesRisk` with the finite posterior theorem.
  rw [Causalean.Stat.realBayesRisk_eq_inducedFiniteDesignBayesRisk]
  exact finiteDesignBayesRisk_statewiseSquaredLoss _ L t

/-- If [an integrated continuous-prior risk agrees estimator by estimator with the induced
finite squared risk](hyp:hcompat) and [has a common lower bound](hyp:hlower), [that constant
lower-bounds the real-valued finite-design Bayes-risk infimum](goal). -/
theorem integratedLowerBound_le_inducedFiniteDesignBayesRisk
    (π : Measure Θ) [IsProbabilityMeasure π]
    (K : Kernel Θ S) [IsMarkovKernel K] (L : Kernel S X)
    (t : S → X → ℝ) (integratedRisk : (X → ℝ) → ℝ) (B : ℝ)
    (hcompat : ∀ T, integratedRisk T = squaredRisk (Causalean.Stat.inducedFiniteDesign π K) L t T)
    (hlower : ∀ T, B ≤ integratedRisk T) :
    B ≤ Causalean.Stat.finiteDesignBayesRisk (Causalean.Stat.inducedFiniteDesign π K)
      (statewiseSquaredLoss L t) := by
  -- Rewrite the generic finite Bayes risk as the infimum of `squaredRisk`; apply `le_ciInf` to
  -- the lower bound after rewriting each estimator through `hcompat`.
  unfold Causalean.Stat.finiteDesignBayesRisk
  simp_rw [finiteDesign_expectedLoss_statewiseSquaredLoss]
  exact le_ciInf fun T => (hlower T).trans_eq (hcompat T)

/-- If [an integrated continuous-prior risk agrees estimator by estimator with the induced
finite squared risk](hyp:hcompat) and [has a common lower bound](hyp:hlower), [that bound is at
most the posterior residual risk of the induced finite experiment](goal). -/
theorem integratedLowerBound_le_inducedPosteriorResidual
    (π : Measure Θ) [IsProbabilityMeasure π]
    (K : Kernel Θ S) [IsMarkovKernel K] (L : Kernel S X)
    (t : S → X → ℝ) (integratedRisk : (X → ℝ) → ℝ) (B : ℝ)
    (hcompat : ∀ T, integratedRisk T = squaredRisk (Causalean.Stat.inducedFiniteDesign π K) L t T)
    (hlower : ∀ T, B ≤ integratedRisk T) :
    B ≤ posteriorResidual (Causalean.Stat.inducedFiniteDesign π K) L t := by
  rw [← finiteDesignBayesRisk_statewiseSquaredLoss]
  exact integratedLowerBound_le_inducedFiniteDesignBayesRisk
    π K L t integratedRisk B hcompat hlower

/-- If [an integrated risk agrees estimator by estimator with the generic continuous mixture
](hyp:hcompat) and [has a common lower bound](hyp:hlower), [that bound transfers to the
corresponding real-valued induced finite-design Bayes risk](goal). -/
theorem mixedIntegratedLowerBound_le_inducedFiniteDesignBayesRisk
    (π : Measure Θ) [IsProbabilityMeasure π]
    (K : Kernel Θ S) [IsMarkovKernel K] (L : Kernel S X)
    (t : S → X → ℝ) (integratedRisk : (X → ℝ) → ℝ) (B : ℝ)
    (hcompat : ∀ T, integratedRisk T =
      Causalean.Stat.mixedKernelLoss π K (statewiseSquaredLoss L t) T)
    (hlower : ∀ T, B ≤ integratedRisk T) :
    B ≤ Causalean.Stat.finiteDesignBayesRisk (Causalean.Stat.inducedFiniteDesign π K)
      (statewiseSquaredLoss L t) := by
  -- Convert mixture compatibility estimator-by-estimator using the induced-design bridge, then
  -- invoke `integratedLowerBound_le_inducedFiniteDesignBayesRisk`.
  apply integratedLowerBound_le_inducedFiniteDesignBayesRisk
    π K L t integratedRisk B _ hlower
  intro T
  exact (hcompat T).trans
    (mixedKernelLoss_statewiseSquaredLoss_eq_inducedSquaredRisk π K L t T)

/-- If [an integrated risk agrees estimator by estimator with the generic continuous mixture
](hyp:hcompat) and [has a common lower bound](hyp:hlower), [that bound transfers to the
real-valued continuous-mixture Bayes risk](goal). -/
theorem mixedIntegratedLowerBound_le_realBayesRisk
    (π : Measure Θ) [IsProbabilityMeasure π]
    (K : Kernel Θ S) [IsMarkovKernel K] (L : Kernel S X)
    (t : S → X → ℝ) (integratedRisk : (X → ℝ) → ℝ) (B : ℝ)
    (hcompat : ∀ T, integratedRisk T =
      Causalean.Stat.mixedKernelLoss π K (statewiseSquaredLoss L t) T)
    (hlower : ∀ T, B ≤ integratedRisk T) :
    B ≤ Causalean.Stat.realBayesRisk π K (statewiseSquaredLoss L t) := by
  rw [Causalean.Stat.realBayesRisk_eq_inducedFiniteDesignBayesRisk]
  exact mixedIntegratedLowerBound_le_inducedFiniteDesignBayesRisk
    π K L t integratedRisk B hcompat hlower

end Causalean.Stat
