import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Localization.BoundedLinearLocalization.Adapters
import Causalean.Stat.Concentration.ConditionalKernel

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Conditional-to-unconditional projection adapter
-/

namespace CausalSmith.Stat.ReverseKLTwoCoverage.BoundedLinearLocalizationProjection

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

open CausalSmith.Substrate.MeasurableFiniteLinearERM
open CausalSmith.Stat.ReverseKLTwoCoverage.LinearExactShellTypeFit
open CausalSmith.Stat.ReverseKLTwoCoverage.BoundedLinearLocalizationAdapters

variable {d n : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [LinearOrder 𝒳] [LinearOrder 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]

noncomputable def projectionEnergy
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E)
    (sample : LoggedSample n 𝒳 𝒜) : ℝ :=
  ∑ i, (∑ j, rangeProjector (designMatrix E sample) i j *
    rewardNoise E P j sample) ^ 2

noncomputable def projectionThreshold (d : ℕ) (zeta : ℝ) : ℝ :=
  8 * (d * Real.log 5 + Real.log (2 / zeta))

def projectionBadEvent
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (zeta : ℝ) :
    Set (LoggedSample n 𝒳 𝒜) :=
  {sample | projectionThreshold d zeta < projectionEnergy E P sample}

def projectionGoodEvent
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (zeta : ℝ) :
    Set (LoggedSample n 𝒳 𝒜) :=
  {sample | projectionEnergy E P sample ≤ projectionThreshold d zeta}

lemma projectionEnergy_measurable
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) :
    Measurable (projectionEnergy E P :
      LoggedSample n 𝒳 𝒜 → ℝ) := by
  unfold projectionEnergy
  apply Finset.measurable_sum
  intro i _
  apply Measurable.pow_const
  apply Finset.measurable_sum
  intro j _
  exact (designProjector_spec E).1 i j |>.mul
    (rewardNoise_measurable E P j)

lemma projectionBadEvent_measurable
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (zeta : ℝ) :
    MeasurableSet (projectionBadEvent (n := n) E P zeta) :=
  measurableSet_lt measurable_const (projectionEnergy_measurable E P)

lemma projectionGoodEvent_measurable
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (zeta : ℝ) :
    MeasurableSet (projectionGoodEvent (n := n) E P zeta) :=
  measurableSet_le (projectionEnergy_measurable E P) measurable_const

lemma projectionGoodEvent_eq_compl
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (zeta : ℝ) :
    projectionGoodEvent (n := n) E P zeta =
      (projectionBadEvent (n := n) E P zeta)ᶜ := by
  ext sample
  simp [projectionGoodEvent, projectionBadEvent, not_lt]

lemma projectionBadEvent_probability_le
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (C D zeta : ℝ)
    (hshell : ExactShell E P C D) (hzeta : 0 < zeta) :
    (productLaw E P n).real
      (projectionBadEvent (n := n) E P zeta) ≤ zeta := by
  letI : IsProbabilityMeasure (productLaw E P n) :=
    productLaw_isProbability E P
  letI : StandardBorelSpace (LoggedSample n 𝒳 𝒜) :=
    loggedSampleStandardBorel
  have hcond :=
    productLaw_rewardNoise_conditional (n := n) E P C D hshell
  have hgram :
      ∀ᵐ sample ∂(productLaw E P n).trim designSigma_le,
        ProjectorRankAtMost
          (rangeProjector (designMatrix E sample)) d :=
    Filter.Eventually.of_forall (designProjector_rankAtMost E)
  have hrank :
      ∀ᵐ sample ∂(productLaw E P n).trim designSigma_le,
        Matrix.rank (rangeProjector (designMatrix E sample)) ≤ d := by
    filter_upwards [hgram] with sample hs
    rcases hs with ⟨vectors, hfactor⟩
    exact Causalean.Stat.Concentration.matrix_rank_le_of_gram_factor
      (rangeProjector (designMatrix E sample)) vectors hfactor
  have htail :=
    Causalean.Stat.Concentration.ae_condExpKernel_projection_energy_gt_le
      (μ := productLaw E P n) designSigma_le
      (rewardNoise E P)
      (fun sample => rangeProjector (designMatrix E sample))
      (rewardNoise_measurable E P)
      (rewardNoise_ae_bound E P C D hshell)
      hcond.1 hcond.2
      (designProjector_measurable_coord_designSigma E)
      (Filter.Eventually.of_forall fun sample =>
        rangeProjector_transpose (designMatrix E sample))
      (Filter.Eventually.of_forall fun sample =>
        rangeProjector_mul_self (designMatrix E sample))
      hrank hzeta
  have htail' :
      ∀ᵐ sample ∂(productLaw E P n).trim designSigma_le,
        (condExpKernel (mΩ := MeasurableSpace.pi)
          (productLaw E P n) designSigma sample).real
            (projectionBadEvent (n := n) E P zeta) ≤ zeta := by
    simpa only [projectionBadEvent, projectionThreshold, projectionEnergy]
      using htail
  let κ := condExpKernel (mΩ := MeasurableSpace.pi)
    (productLaw E P n) designSigma
  have hkernel :
      ∀ᵐ sample ∂(productLaw E P n).trim designSigma_le,
        κ sample (projectionBadEvent (n := n) E P zeta) ≤
          ENNReal.ofReal zeta := by
    filter_upwards [htail'] with sample hs
    apply (ENNReal.toReal_le_toReal
      (measure_ne_top _ _)
      (by simp : ENNReal.ofReal zeta ≠ ∞)).1
    simpa [κ, ENNReal.toReal_ofReal hzeta.le] using hs
  have hcomp :
      κ ∘ₘ (productLaw E P n).trim designSigma_le =
        productLaw E P n := by
    exact condExpKernel_comp_trim (mΩ := MeasurableSpace.pi) designSigma_le
  have hENN :
      (productLaw E P n) (projectionBadEvent (n := n) E P zeta) ≤
        ENNReal.ofReal zeta := by
    calc
      (productLaw E P n) (projectionBadEvent (n := n) E P zeta) =
          (κ ∘ₘ (productLaw E P n).trim designSigma_le)
            (projectionBadEvent (n := n) E P zeta) := by rw [hcomp]
      _ = ∫⁻ sample,
          κ sample (projectionBadEvent (n := n) E P zeta)
            ∂(productLaw E P n).trim designSigma_le := by
        change Measure.bind ((productLaw E P n).trim designSigma_le) κ
            (projectionBadEvent (n := n) E P zeta) = _
        rw [Measure.bind_apply
          (projectionBadEvent_measurable (n := n) E P zeta)
          κ.aemeasurable]
      _ ≤ ∫⁻ _sample,
          ENNReal.ofReal zeta
            ∂(productLaw E P n).trim designSigma_le :=
        lintegral_mono_ae hkernel
      _ = ENNReal.ofReal zeta := by
        rw [lintegral_const, trim_measurableSet_eq designSigma_le
          (@MeasurableSet.univ _ designSigma), measure_univ,
          mul_one]
  have hreal := ENNReal.toReal_mono
    (by simp : ENNReal.ofReal zeta ≠ ∞) hENN
  simpa [ENNReal.toReal_ofReal hzeta.le] using hreal

lemma projectionGoodEvent_probability
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (C D zeta : ℝ)
    (hshell : ExactShell E P C D) (hzeta : 0 < zeta) :
    (productLaw E P n).real
      (projectionGoodEvent (n := n) E P zeta) ≥
      1 - zeta := by
  letI : IsProbabilityMeasure (productLaw E P n) :=
    productLaw_isProbability E P
  rw [projectionGoodEvent_eq_compl (n := n),
    measureReal_compl (projectionBadEvent_measurable (n := n) E P zeta)]
  have hbad :=
    projectionBadEvent_probability_le (n := n) E P C D zeta hshell hzeta
  rw [probReal_univ]
  linarith

lemma empiricalSqNorm_projector_eq
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E)
    (sample : LoggedSample n 𝒳 𝒜) :
    empiricalSqNorm
        (euclideanProjector E sample (centeredNoise E P sample)) =
      (n : ℝ)⁻¹ * projectionEnergy E P sample := by
  unfold empiricalSqNorm projectionEnergy
  congr 1

lemma selectedERM_projection_bound_on_good
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (C D zeta : ℝ)
    (hshell : ExactShell E P C D) (hn : 0 < n)
    (sample : LoggedSample n 𝒳 𝒜)
    (hsample : sample ∈ projectionGoodEvent (n := n) E P zeta) :
    empiricalSqNorm
        (sampleEvaluation sample (selectedERM E sample) -
          sampleEvaluation sample (linearReward P)) ≤
      4 * ((n : ℝ)⁻¹ * projectionThreshold d zeta) := by
  calc
    empiricalSqNorm
        (sampleEvaluation sample (selectedERM E sample) -
          sampleEvaluation sample (linearReward P)) ≤
        4 * empiricalSqNorm
          (euclideanProjector E sample (centeredNoise E P sample)) :=
      selectedERM_empirical_projection_bound E P C D hshell sample hn
    _ = 4 * ((n : ℝ)⁻¹ * projectionEnergy E P sample) := by
      rw [empiricalSqNorm_projector_eq]
    _ ≤ 4 * ((n : ℝ)⁻¹ * projectionThreshold d zeta) := by
      have hninv : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsample hninv) (by norm_num)

end CausalSmith.Stat.ReverseKLTwoCoverage.BoundedLinearLocalizationProjection
