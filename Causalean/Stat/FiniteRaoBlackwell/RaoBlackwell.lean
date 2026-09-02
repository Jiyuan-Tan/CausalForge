import Causalean.Stat.FiniteRaoBlackwell.Sufficiency
import Causalean.Stat.Minimax.MinimaxValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Finite Rao--Blackwell reduction for squared loss

This module averages a real estimator over the guarded conditional design from `Core` and proves
finite Jensen and squared-risk contraction.  The state-indexed conditional mean is retained as
an analytic fiberwise device.  The usable Rao--Blackwell estimator is a single statistic-only
function constructed from a sufficient factorization, and it yields statewise, finite-prior,
worst-case, and minimax-compatible corollaries.
-/

open scoped BigOperators

namespace Causalean.Stat.FiniteRaoBlackwell

open Causalean.Experimentation.DesignBased

variable {Latent Allocation Observation Statistic : Type*}
variable [Fintype Latent] [Fintype Allocation] [Fintype Observation] [Fintype Statistic]
variable [DecidableEq Allocation] [DecidableEq Observation] [DecidableEq Statistic]

namespace FiniteUniformExperiment

variable (E : FiniteUniformExperiment Latent Allocation Observation Statistic)

/-- The conditional mean of a full-data estimator is its finite expectation under the guarded
conditional design at a state and statistic value. -/
noncomputable def conditionalMean (est : Allocation × Observation → ℝ)
    (θ : Latent) (s : Statistic) : ℝ :=
  ∑ z, E.conditionalWeight θ s z * est z

/-- On a finite statistic space, the state-indexed conditional mean is measurable for the
discrete sigma algebra. -/
theorem measurable_conditionalMean
    [MeasurableSpace Statistic] [MeasurableSingletonClass Statistic]
    (est : Allocation × Observation → ℝ) (θ : Latent) :
    Measurable (E.conditionalMean est θ) := by
  exact measurable_of_finite _

/-- The full-data squared-error risk is joint expected squared loss at a fixed latent state. -/
noncomputable def fullRisk (target : Latent → ℝ)
    (est : Allocation × Observation → ℝ) (θ : Latent) : ℝ :=
  ∑ z, E.jointMass θ z * (est z - target θ) ^ 2

/-- The squared-error risk of a statistic-only estimator is evaluated by composing it with the
sample statistic under the original joint law. -/
noncomputable def statisticRisk (target : Latent → ℝ)
    (est : Statistic → ℝ) (θ : Latent) : ℝ :=
  ∑ z, E.jointMass θ z * (est (E.sampleStatistic z) - target θ) ^ 2

/-- Full-data squared-error risk is nonnegative at every latent state. -/
theorem fullRisk_nonneg (target : Latent → ℝ)
    (est : Allocation × Observation → ℝ) (θ : Latent) :
    0 ≤ E.fullRisk target est θ := by
  exact Finset.sum_nonneg fun z _ ↦
    mul_nonneg (E.jointMass_nonneg θ z) (sq_nonneg _)

/-- Statistic-only squared-error risk is nonnegative at every latent state. -/
theorem statisticRisk_nonneg (target : Latent → ℝ)
    (est : Statistic → ℝ) (θ : Latent) :
    0 ≤ E.statisticRisk target est θ := by
  exact Finset.sum_nonneg fun z _ ↦
    mul_nonneg (E.jointMass_nonneg θ z) (sq_nonneg _)

/-- Conditional Jensen for squared loss: the squared error of the conditional mean is at most
the conditional mean squared error on every guarded fiber. -/
theorem conditionalMean_sq_le (target : ℝ)
    (est : Allocation × Observation → ℝ) (θ : Latent) (s : Statistic) :
    (E.conditionalMean est θ s - target) ^ 2 ≤
      ∑ z, E.conditionalWeight θ s z * (est z - target) ^ 2 := by
  /- Apply ConvexOn.map_sum_le to x ↦ x^2 with the conditional weights.  Linearity and
  conditionalWeight_sum identify the weighted centered mean with conditionalMean - target. -/
  classical
  have hJ := (Even.convexOn_pow (by norm_num : Even (2 : ℕ)) :
      ConvexOn ℝ Set.univ (fun x : ℝ ↦ x ^ 2)).map_sum_le
    (t := Finset.univ) (w := fun z ↦ E.conditionalWeight θ s z)
    (p := fun z ↦ est z - target)
    (fun z _ ↦ E.conditionalWeight_nonneg θ s z)
    (by simpa using E.conditionalWeight_sum θ s)
    (fun _ _ ↦ Set.mem_univ _)
  have hcenter :
      (∑ z, E.conditionalWeight θ s z • (est z - target)) =
        E.conditionalMean est θ s - target := by
    simp only [smul_eq_mul, mul_sub, Finset.sum_sub_distrib, conditionalMean,
      ← Finset.sum_mul, E.conditionalWeight_sum, one_mul]
  rw [hcenter] at hJ
  simpa only [smul_eq_mul] using hJ

/-- At any fixed state, composing that state's conditional mean with the statistic has no larger
squared-error risk than the original estimator.  This is a fiberwise analytic inequality; the
conditional mean in this statement is not asserted to be one estimator shared across states. -/
theorem statisticRisk_conditionalMean_le_fullRisk
    (target : Latent → ℝ) (est : Allocation × Observation → ℝ) (θ : Latent) :
    E.statisticRisk target (E.conditionalMean est θ) θ ≤ E.fullRisk target est θ := by
  /- Rewrite both risks through disintegrate_sum and sum conditionalMean_sq_le with the
  nonnegative statistic masses. -/
  classical
  have hstat :
      E.statisticRisk target (E.conditionalMean est θ) θ =
        ∑ s, E.statisticMass θ s *
          (E.conditionalMean est θ s - target θ) ^ 2 := by
    simp only [statisticRisk, statisticMass, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp
  rw [hstat, fullRisk, E.disintegrate_sum]
  exact Finset.sum_le_sum fun s _ ↦
    mul_le_mul_of_nonneg_left
      (E.conditionalMean_sq_le (target θ) est θ s)
      (E.statisticMass_nonneg θ s)

/-- Given a common conditional kernel, the Rao--Blackwell estimator averages the full-data
estimator with its state-independent weights and therefore depends only on the statistic. -/
noncomputable def commonRaoBlackwellEstimator
    (K : E.CommonConditionalKernel)
    (est : Allocation × Observation → ℝ) : Statistic → ℝ :=
  fun s ↦ ∑ z, K.weight s z * est z

/-- On every positive statewise fiber, the state-indexed conditional mean equals the common
Rao--Blackwell estimator supplied by the sufficient conditional kernel. -/
theorem conditionalMean_eq_commonRaoBlackwellEstimator
    (K : E.CommonConditionalKernel)
    (est : Allocation × Observation → ℝ) (θ : Latent) (s : Statistic)
    (hpos : 0 < E.statisticMass θ s) :
    E.conditionalMean est θ s = E.commonRaoBlackwellEstimator K est s := by
  apply Finset.sum_congr rfl
  intro z _
  rw [K.eq_conditionalWeight θ s hpos z]

/-- On finite statistic spaces, the common Rao--Blackwell estimator is measurable for the
discrete sigma algebra. -/
theorem measurable_commonRaoBlackwellEstimator
    [MeasurableSpace Statistic] [MeasurableSingletonClass Statistic]
    (K : E.CommonConditionalKernel) (est : Allocation × Observation → ℝ) :
    Measurable (E.commonRaoBlackwellEstimator K est) := by
  exact measurable_of_finite _

/-- A common sufficient conditional kernel produces one statistic-only Rao--Blackwell estimator
whose squared-error risk is no larger at every latent state. -/
theorem statisticRisk_commonRaoBlackwellEstimator_le_fullRisk
    (K : E.CommonConditionalKernel)
    (target : Latent → ℝ) (est : Allocation × Observation → ℝ) (θ : Latent) :
    E.statisticRisk target (E.commonRaoBlackwellEstimator K est) θ ≤
      E.fullRisk target est θ := by
  /- Apply the state-indexed contraction on positive statistic fibers.  Null fibers vanish
  after multiplication by statisticMass, so no cross-state support assumption is needed. -/
  classical
  have hrb :
      E.statisticRisk target (E.commonRaoBlackwellEstimator K est) θ =
        ∑ s, E.statisticMass θ s *
          (E.commonRaoBlackwellEstimator K est s - target θ) ^ 2 := by
    simp only [statisticRisk, statisticMass, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp
  have hcm :
      E.statisticRisk target (E.conditionalMean est θ) θ =
        ∑ s, E.statisticMass θ s *
          (E.conditionalMean est θ s - target θ) ^ 2 := by
    simp only [statisticRisk, statisticMass, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp
  have heq :
      E.statisticRisk target (E.commonRaoBlackwellEstimator K est) θ =
        E.statisticRisk target (E.conditionalMean est θ) θ := by
    rw [hrb, hcm]
    apply Finset.sum_congr rfl
    intro s _
    by_cases hpos : 0 < E.statisticMass θ s
    · rw [E.conditionalMean_eq_commonRaoBlackwellEstimator K est θ s hpos]
    · have hzero : E.statisticMass θ s = 0 :=
        le_antisymm (le_of_not_gt hpos) (E.statisticMass_nonneg θ s)
      simp [hzero]
  rw [heq]
  exact E.statisticRisk_conditionalMean_le_fullRisk target est θ

/-- Under any finite prior on latent states, the common Rao--Blackwell estimator has no larger
prior-averaged squared-error risk than the original estimator. -/
theorem priorRisk_commonRaoBlackwellEstimator_le
    (K : E.CommonConditionalKernel)
    (prior : FiniteDesign Latent) (target : Latent → ℝ)
    (est : Allocation × Observation → ℝ) :
    prior.E (E.statisticRisk target (E.commonRaoBlackwellEstimator K est)) ≤
      prior.E (E.fullRisk target est) := by
  /- Sum the statewise contraction against the nonnegative prior weights. -/
  exact Finset.sum_le_sum fun θ _ ↦
    mul_le_mul_of_nonneg_left
      (E.statisticRisk_commonRaoBlackwellEstimator_le_fullRisk K target est θ)
      (prior.p_nonneg θ)

/-- Under state-independent conditional laws, Rao--Blackwellization weakly decreases the finite
worst-case squared risk, in the real-valued `worstCaseRisk` API. -/
theorem worstCaseRisk_commonRaoBlackwellEstimator_le
    (K : E.CommonConditionalKernel)
    (target : Latent → ℝ) (est : Allocation × Observation → ℝ) :
    Causalean.Stat.worstCaseRisk (E.statisticRisk target)
        (E.commonRaoBlackwellEstimator K est) ≤
      Causalean.Stat.worstCaseRisk (E.fullRisk target) est := by
  /- Finite state spaces bound both risk ranges.  Apply worstCaseRisk_le to the statewise
  contraction followed by le_worstCaseRisk for the full estimator. -/
  cases isEmpty_or_nonempty Latent with
  | inl _ =>
      simp only [Causalean.Stat.worstCaseRisk_of_isEmpty_class]
      exact le_rfl
  | inr _ =>
      apply Causalean.Stat.worstCaseRisk_le
      intro θ
      exact (E.statisticRisk_commonRaoBlackwellEstimator_le_fullRisk K target est θ).trans
        (Causalean.Stat.le_worstCaseRisk (Set.finite_range _ |>.bddAbove) θ)

/-- If every full-data estimator is Rao--Blackwellized through state-independent conditionals,
the minimax value over statistic-only estimators is no larger than the full-data minimax value. -/
theorem minimaxValue_statistic_le_full_of_commonConditionalKernel
    (K : E.CommonConditionalKernel) (target : Latent → ℝ) :
    Causalean.Stat.minimaxValue (E.statisticRisk target) ≤
      Causalean.Stat.minimaxValue (E.fullRisk target) := by
  /- Use minimaxValue_le_minimaxValue, pairing each full estimator with its common
  raoBlackwellEstimator.  Nonnegativity supplies the lower bound for statistic risks. -/
  apply Causalean.Stat.minimaxValue_le_minimaxValue
    (Causalean.Stat.bddBelow_range_worstCaseRisk fun est θ ↦
      E.statisticRisk_nonneg target est θ)
  intro est
  exact ⟨E.commonRaoBlackwellEstimator K est,
    E.worstCaseRisk_commonRaoBlackwellEstimator_le K target est⟩

/-! ## Primary factorization-based Rao--Blackwell API -/

/-- The Rao--Blackwell estimator supplied by a sufficient factorization is one real-valued
function of the statistic, obtained from the factorization's derived common conditional law. -/
noncomputable def raoBlackwellEstimator
    (F : E.SufficientFactorization)
    (est : Allocation × Observation → ℝ) : Statistic → ℝ :=
  E.commonRaoBlackwellEstimator F.toCommonConditionalKernel est

/-- The factorization-based Rao--Blackwell estimator is measurable on a finite discrete
statistic space. -/
theorem measurable_raoBlackwellEstimator
    [MeasurableSpace Statistic] [MeasurableSingletonClass Statistic]
    (F : E.SufficientFactorization) (est : Allocation × Observation → ℝ) :
    Measurable (E.raoBlackwellEstimator F est) := by
  exact E.measurable_commonRaoBlackwellEstimator F.toCommonConditionalKernel est

/-- A sufficient factorization produces [one statistic-only Rao--Blackwell estimator whose
squared-error risk is no larger than the full-data estimator at every latent state](goal). -/
theorem statisticRisk_raoBlackwellEstimator_le_fullRisk
    (F : E.SufficientFactorization)
    (target : Latent → ℝ) (est : Allocation × Observation → ℝ) (θ : Latent) :
    E.statisticRisk target (E.raoBlackwellEstimator F est) θ ≤
      E.fullRisk target est θ := by
  exact E.statisticRisk_commonRaoBlackwellEstimator_le_fullRisk
    F.toCommonConditionalKernel target est θ

/-- Under any finite prior, the one statistic-only estimator derived from a sufficient
factorization has no larger prior-averaged squared-error risk than the full-data estimator. -/
theorem priorRisk_raoBlackwellEstimator_le
    (F : E.SufficientFactorization)
    (prior : FiniteDesign Latent) (target : Latent → ℝ)
    (est : Allocation × Observation → ℝ) :
    prior.E (E.statisticRisk target (E.raoBlackwellEstimator F est)) ≤
      prior.E (E.fullRisk target est) := by
  exact E.priorRisk_commonRaoBlackwellEstimator_le
    F.toCommonConditionalKernel prior target est

/-- Under a sufficient factorization, the one statistic-only Rao--Blackwell estimator has no
larger finite worst-case squared risk than the full-data estimator. -/
theorem worstCaseRisk_raoBlackwellEstimator_le
    (F : E.SufficientFactorization)
    (target : Latent → ℝ) (est : Allocation × Observation → ℝ) :
    Causalean.Stat.worstCaseRisk (E.statisticRisk target) (E.raoBlackwellEstimator F est) ≤
      Causalean.Stat.worstCaseRisk (E.fullRisk target) est := by
  exact E.worstCaseRisk_commonRaoBlackwellEstimator_le
    F.toCommonConditionalKernel target est

/-- If the statistic satisfies the finite factorization criterion, its estimator class has
minimax squared-risk value no larger than the full-data estimator class. -/
theorem minimaxValue_statistic_le_full
    (F : E.SufficientFactorization) (target : Latent → ℝ) :
    Causalean.Stat.minimaxValue (E.statisticRisk target) ≤
      Causalean.Stat.minimaxValue (E.fullRisk target) := by
  exact E.minimaxValue_statistic_le_full_of_commonConditionalKernel
    F.toCommonConditionalKernel target

end FiniteUniformExperiment

end Causalean.Stat.FiniteRaoBlackwell
