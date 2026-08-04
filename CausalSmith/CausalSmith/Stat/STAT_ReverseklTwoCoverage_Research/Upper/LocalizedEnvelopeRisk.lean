import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Upper.LocalizedEnvelopeCore

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory ProbabilityTheory
open LinearExactShellTypeFit
open BoundedLinearLocalizationAdapters
open CausalSmith.Substrate.FiniteExponentialTiltCalculus

variable {d n : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [LinearOrder 𝒳] [LinearOrder 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]

lemma selectedERM_mem_confidencePolytope
    (E : CommonExperiment d 𝒳 𝒜) (sample : LoggedSample n 𝒳 𝒜)
    (hn : 0 < n) :
    selectedERM E sample ∈ confidencePolytope E 64 sample := by
  refine ⟨(selectedERM_isLexicographicERM E sample).1, ?_⟩
  have hrate :
      0 ≤ 64 *
        ((d : ℝ) * Real.log (Real.exp 1 * n) +
          Real.log (2 * (n : ℝ) ^ 2)) / (n : ℝ) := by
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog1 : 0 ≤ Real.log (Real.exp 1 * (n : ℝ)) := by
      apply Real.log_nonneg
      have hexp : 1 ≤ Real.exp 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by norm_num)
      nlinarith [mul_le_mul hexp (show (1 : ℝ) ≤ n by exact_mod_cast hn)
        (by norm_num : (0 : ℝ) ≤ 1) (Real.exp_pos 1).le]
    have hlog2 : 0 ≤ Real.log (2 * (n : ℝ) ^ 2) := by
      apply Real.log_nonneg
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
    positivity
  simpa [empiricalSeminormSq] using hrate

lemma lowerEnvelope_good_sample_regret_le
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (C D : ℝ)
    (hshell : ExactShell E P C D)
    (sample : LoggedSample n 𝒳 𝒜)
    (hlocal :
      linearReward P ∈ confidencePolytope E 64 sample ∧
      ∀ f ∈ confidencePolytope E 64 sample,
        ∑ x, contextMass P x * ∑ a, E.reference x a *
            (f x a - linearReward P x a) ^ 2 ≤
          (4 * 64 + 291) *
            (d * Real.log (Real.exp 1 * n) +
              Real.log (2 * (n : ℝ) ^ 2)) / n)
    (hn : 0 < n) :
    regularizedWelfare E P (gibbsPolicy E P) -
        regularizedWelfare E P (lowerEnvelopePolicy E 64 sample) ≤
      min
        (300 * E.eta * (d : ℝ) * D *
          ((d : ℝ) * Real.log (Real.exp 1 * n) +
            Real.log (2 * (n : ℝ) ^ 2)) / n)
        (Real.sqrt
          (600 * (d : ℝ) * D *
            (((d : ℝ) * Real.log (Real.exp 1 * n) +
              Real.log (2 * (n : ℝ) ^ 2)) / n))) := by
  let r := linearReward P
  let g := lowerEnvelope E 64 sample
  let aN :=
    (d : ℝ) * Real.log (Real.exp 1 * n) +
      Real.log (2 * (n : ℝ) ^ 2)
  let R := 600 * aN / (n : ℝ)
  let L := loggingCovariance E P
  let M : Matrix (Fin d) (Fin d) ℝ := R • L⁻¹
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have haN : 0 ≤ aN := by
    dsimp [aN]
    have hlog1 : 0 ≤ Real.log (Real.exp 1 * (n : ℝ)) := by
      apply Real.log_nonneg
      have hexp : 1 ≤ Real.exp 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by norm_num)
      nlinarith [mul_le_mul hexp (show (1 : ℝ) ≤ n by exact_mod_cast hn)
        (by norm_num : (0 : ℝ) ≤ 1) (Real.exp_pos 1).le]
    have hlog2 : 0 ≤ Real.log (2 * (n : ℝ) ^ 2) := by
      apply Real.log_nonneg
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
    positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hlocalR :
      ∀ f ∈ confidencePolytope E 64 sample,
        policySecondMoment E P E.reference
            (fun x a => f x a - r x a) ≤ R := by
    intro f hf
    have hfbound := hlocal.2 f hf
    change
      policySecondMoment E P E.reference
          (fun x a => f x a - r x a) ≤ R
    calc
      _ ≤ (4 * 64 + 291) * aN / (n : ℝ) := by
        simpa [policySecondMoment, r, aN] using hfbound
      _ ≤ 600 * aN / (n : ℝ) := by
        apply (div_le_div_iff_of_pos_right hnreal).2
        exact mul_le_mul_of_nonneg_right (by norm_num) haN
      _ = R := rfl
  have hpoint :
      ∀ x a, (g x a - r x a) ^ 2 ≤ quadraticForm M (E.feature x a) := by
    intro x a
    have hp := lowerEnvelope_sq_le_inverse_majorant
      E P C D 64 R sample hshell hlocal.1 hR hlocalR x a
    simpa [g, r, M, L, quadraticForm_smul_matrix] using hp
  have hM : Matrix.PosSemidef M := by
    dsimp [M, L]
    exact hshell.nonsingularLoggingGeometry.inv.posSemidef.smul hR
  have htransfer :=
    quadratic_majorant_transfer E P C D hshell M hM
      (fun x a => g x a - r x a) hpoint
  have hDelta :
      policySecondMoment E P (gibbsPolicy E P)
          (fun x a => g x a - r x a) ≤
        600 * (d : ℝ) * D * (aN / (n : ℝ)) := by
    calc
      _ ≤ matrixFeatureMoment E P (gibbsPolicy E P) M := htransfer.1
      _ ≤ featureCoverage E P *
          matrixFeatureMoment E P E.reference M := htransfer.2
      _ = D * (R * (d : ℝ)) := by
        rw [hshell.featureExactShell.2]
        rw [show M = R • L⁻¹ by rfl, matrixFeatureMoment_smul,
          matrixFeatureMoment_reference_inverse E P
            hshell.nonsingularLoggingGeometry]
      _ = 600 * (d : ℝ) * D * (aN / (n : ℝ)) := by
        dsimp [R]
        ring
  have hr : ∀ x a, r x a ∈ Set.Icc (0 : ℝ) 1 := hlocal.1.1.1
  have hg : ∀ x a, g x a ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [g] using
      lowerEnvelope_mem_Icc_of_confidence_member E 64 sample r hlocal.1
  have hpess : ∀ x a, g x a - r x a ≤ 0 := by
    intro x a
    let S : Set ℝ :=
      {z | ∃ f ∈ confidencePolytope E 64 sample, z = f x a}
    have hSbdd : BddBelow S := by
      refine ⟨0, ?_⟩
      rintro z ⟨f, hf, rfl⟩
      exact (hf.1.1 x a).1
    have hrS : r x a ∈ S := ⟨r, hlocal.1, rfl⟩
    change sInf S - r x a ≤ 0
    linarith [csInf_le hSbdd hrS]
  have hconversion :=
    gibbs_pessimism_conversion E (contextMass P) r g
      (contextMass_nonneg E P) (contextMass_sum_one E P)
      hr hg hpess
  have hlinear :
      ∑ x, contextMass P x *
          ∑ a, gibbsFromPotential E r x a * (-(g x a - r x a)) ≤
        Real.sqrt
          (policySecondMoment E P (gibbsPolicy E P)
            (fun x a => g x a - r x a)) := by
    simpa [policySecondMoment, gibbsPolicy, gibbsFromPotential,
      gibbsNormalizer, r] using
      weighted_policy_linear_le_sqrt_secondMoment
        (contextMass P) (gibbsFromPotential E r)
        (fun x a => g x a - r x a)
        (contextMass_nonneg E P) (contextMass_sum_one E P)
        (gibbsFromPotential_isPolicy E r).1
        (gibbsFromPotential_isPolicy E r).2
  have hconverted :
      welfareFromPotential E (contextMass P) r (gibbsFromPotential E r) -
          welfareFromPotential E (contextMass P) r (gibbsFromPotential E g) ≤
        min
          (300 * E.eta * (d : ℝ) * D * aN / (n : ℝ))
          (Real.sqrt (600 * (d : ℝ) * D * (aN / (n : ℝ)))) := by
    calc
      _ ≤ min
          (∑ x, contextMass P x *
            ∑ a, gibbsFromPotential E r x a * (-(g x a - r x a)))
          (E.eta / 2 *
            ∑ x, contextMass P x *
              ∑ a, gibbsFromPotential E r x a * (g x a - r x a) ^ 2) :=
        hconversion
      _ = min
          (E.eta / 2 *
            ∑ x, contextMass P x *
              ∑ a, gibbsFromPotential E r x a * (g x a - r x a) ^ 2)
          (∑ x, contextMass P x *
            ∑ a, gibbsFromPotential E r x a * (-(g x a - r x a))) :=
        min_comm _ _
      _ ≤ min
          (300 * E.eta * (d : ℝ) * D * aN / (n : ℝ))
          (Real.sqrt (600 * (d : ℝ) * D * (aN / (n : ℝ)))) := by
        apply min_le_min
        · calc
            E.eta / 2 *
                (∑ x, contextMass P x *
                  ∑ a, gibbsFromPotential E r x a *
                    (g x a - r x a) ^ 2) =
                E.eta / 2 *
                  policySecondMoment E P (gibbsPolicy E P)
                    (fun x a => g x a - r x a) := by
                      simp [policySecondMoment, gibbsPolicy, gibbsFromPotential,
                        gibbsNormalizer, r]
            _ ≤ E.eta / 2 *
                (600 * (d : ℝ) * D * (aN / (n : ℝ))) :=
              mul_le_mul_of_nonneg_left hDelta
                (div_nonneg E.eta_pos.le (by norm_num))
            _ = 300 * E.eta * (d : ℝ) * D * aN / (n : ℝ) := by ring
        · exact hlinear.trans (Real.sqrt_le_sqrt hDelta)
  have hw :
      regularizedWelfare E P (gibbsPolicy E P) -
          regularizedWelfare E P (lowerEnvelopePolicy E 64 sample) ≤
        min
          (300 * E.eta * (d : ℝ) * D * aN / (n : ℝ))
          (Real.sqrt (600 * (d : ℝ) * D * (aN / (n : ℝ)))) := by
    simpa [regularizedWelfare, welfareFromPotential, gibbsPolicy,
      gibbsNormalizer, gibbsFromPotential, lowerEnvelopePolicy, r, g] using
      hconverted
  convert hw using 1 <;> dsimp [aN] <;> ring

lemma lowerEnvelopeLearnerRisk_le_sharp
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (C D : ℝ)
    (hshell : ExactShell E P C D)
    (hZhao : ZhaoUniformSquareComparison (𝒳 := 𝒳) (𝒜 := 𝒜))
    (hn : 0 < n) :
    learnerRisk E P n
        (predictionPolytopeLearner E 64 (by norm_num) (n := n)).deployed ≤
      min
        (300 * E.eta * (d : ℝ) * D *
          (((d : ℝ) * Real.log (Real.exp 1 * n) +
            Real.log (2 * (n : ℝ) ^ 2)) / n))
        (Real.sqrt
          (600 * (d : ℝ) * D *
            (((d : ℝ) * Real.log (Real.exp 1 * n) +
              Real.log (2 * (n : ℝ) ^ 2)) / n))) +
      failureProbability n hn / 2 * min 2 (E.eta / 2) := by
  let μ := productLaw E P n
  let goodBound :=
    min
      (300 * E.eta * (d : ℝ) * D *
        (((d : ℝ) * Real.log (Real.exp 1 * n) +
          Real.log (2 * (n : ℝ) ^ 2)) / n))
      (Real.sqrt
        (600 * (d : ℝ) * D *
          (((d : ℝ) * Real.log (Real.exp 1 * n) +
            Real.log (2 * (n : ℝ) ^ 2)) / n)))
  letI : IsProbabilityMeasure μ := productLaw_isProbability E P
  obtain ⟨event, hevent, hprob, hlocal⟩ :=
    bounded_linear_localization E P C D hshell hZhao hn 64 (by norm_num)
  have haN :
      0 ≤ (d : ℝ) * Real.log (Real.exp 1 * (n : ℝ)) +
        Real.log (2 * (n : ℝ) ^ 2) := by
    have hlog1 : 0 ≤ Real.log (Real.exp 1 * (n : ℝ)) := by
      apply Real.log_nonneg
      have hexp : 1 ≤ Real.exp 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by norm_num)
      nlinarith [mul_le_mul hexp (show (1 : ℝ) ≤ n by exact_mod_cast hn)
        (by norm_num : (0 : ℝ) ≤ 1) (Real.exp_pos 1).le]
    have hlog2 : 0 ≤ Real.log (2 * (n : ℝ) ^ 2) := by
      apply Real.log_nonneg
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
    positivity
  have hgoodBound : 0 ≤ goodBound := by
    dsimp [goodBound]
    have hD : 0 ≤ D := hshell.featureExactShell.1.le
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    apply le_min
    · exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) E.eta_pos.le)
            (Nat.cast_nonneg d))
          hD)
        (div_nonneg haN hn0)
    · exact Real.sqrt_nonneg _
  have hcompl : μ.real eventᶜ ≤ failureProbability n hn / 2 := by
    rw [measureReal_compl hevent, probReal_univ]
    dsimp [μ] at hprob ⊢
    linarith
  have hpoint_good (sample : LoggedSample n 𝒳 𝒜)
      (hsample : BoundedLoggedSample sample) (hsample_event : sample ∈ event) :
      regularizedWelfare E P (gibbsPolicy E P) -
          regularizedWelfare E P
            ((predictionPolytopeLearner E 64 (by norm_num)
              (n := n)).deployed sample hsample) ≤ goodBound := by
    have hp := lowerEnvelope_good_sample_regret_le E P C D hshell sample
      (hlocal sample hsample_event) hn
    simp only [predictionPolytopeLearner] at hp ⊢
    dsimp [goodBound]
    convert hp using 1 <;> ring
  have hpoint_cap (sample : LoggedSample n 𝒳 𝒜)
      (hsample : BoundedLoggedSample sample) :
      regularizedWelfare E P (gibbsPolicy E P) -
          regularizedWelfare E P
            ((predictionPolytopeLearner E 64 (by norm_num)
              (n := n)).deployed sample hsample) ≤ 2 := by
    let r := linearReward P
    let g := lowerEnvelope E 64 sample
    have hsel := selectedERM_mem_confidencePolytope E sample hn
    have hr : ∀ x a, r x a ∈ Set.Icc (0 : ℝ) 1 :=
      (linearReward_mem_predictionPolytope E P C D hshell).1
    have hg : ∀ x a, g x a ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [g] using
        lowerEnvelope_mem_Icc_of_confidence_member
          E 64 sample (selectedERM E sample) hsel
    have hcap :=
      bounded_gibbs_welfare_regret_le_two E (contextMass P) r g
        (contextMass_nonneg E P) (contextMass_sum_one E P) hr hg
    simpa [regularizedWelfare, welfareFromPotential, gibbsPolicy,
      gibbsNormalizer, gibbsFromPotential, predictionPolytopeLearner,
      lowerEnvelopePolicy, r, g] using hcap
  have hpoint_eta (sample : LoggedSample n 𝒳 𝒜)
      (hsample : BoundedLoggedSample sample) :
      regularizedWelfare E P (gibbsPolicy E P) -
          regularizedWelfare E P
            ((predictionPolytopeLearner E 64 (by norm_num)
              (n := n)).deployed sample hsample) ≤ E.eta / 2 := by
    let r := linearReward P
    let g := lowerEnvelope E 64 sample
    have hsel := selectedERM_mem_confidencePolytope E sample hn
    have hr : ∀ x a, r x a ∈ Set.Icc (0 : ℝ) 1 :=
      (linearReward_mem_predictionPolytope E P C D hshell).1
    have hg : ∀ x a, g x a ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [g] using
        lowerEnvelope_mem_Icc_of_confidence_member
          E 64 sample (selectedERM E sample) hsel
    have hcap :=
      bounded_gibbs_welfare_regret_le_eta_half E (contextMass P) r g
        (contextMass_nonneg E P) (contextMass_sum_one E P) hr hg
    simpa [regularizedWelfare, welfareFromPotential, gibbsPolicy,
      gibbsNormalizer, gibbsFromPotential, predictionPolytopeLearner,
      lowerEnvelopePolicy, r, g] using hcap
  have hae_bounded := productLaw_bounded_sample E P n
  have hregret_nonneg :
      ∀ᵐ sample ∂μ,
        0 ≤ regularizedWelfare E P (gibbsPolicy E P) -
          regularizedWelfare E P
            (learnerPolicyOnSample E
              (predictionPolytopeLearner E 64 (by norm_num)
                (n := n)).deployed sample) := by
    filter_upwards [hae_bounded] with sample hsample
    simp only [learnerPolicyOnSample, dif_pos hsample]
    rw [gibbs_regret_identity E P C D hshell
      ((predictionPolytopeLearner E 64 (by norm_num)
        (n := n)).deployed sample hsample)
      ((predictionPolytopeLearner_measurable (n := n) E 64
        (by norm_num)).2 sample hsample |>.1)
      (by
        intro x a hpa
        by_contra href
        exact hpa ((predictionPolytopeLearner_measurable (n := n) E 64
          (by norm_num)).2 sample hsample |>.2 x a href))]
    apply mul_nonneg
    · exact inv_nonneg.mpr E.eta_pos.le
    · apply Finset.sum_nonneg
      intro x _
      apply mul_nonneg (contextMass_nonneg E P x)
      simpa only [predictionPolytopeLearner, lowerEnvelopePolicy, gibbsPolicy,
        gibbsFromPotential] using
        (policyKL_gibbsPotentials_nonneg (E := E)
          (linearReward P) (lowerEnvelope E 64 sample) x)
  have hmajorant :
      ∀ᵐ sample ∂μ,
        regularizedWelfare E P (gibbsPolicy E P) -
            regularizedWelfare E P
              (learnerPolicyOnSample E
                (predictionPolytopeLearner E 64 (by norm_num)
                  (n := n)).deployed sample) ≤
          goodBound +
            eventᶜ.indicator (fun _ => min 2 (E.eta / 2)) sample := by
    filter_upwards [hae_bounded] with sample hsample
    simp only [learnerPolicyOnSample, dif_pos hsample]
    by_cases hs : sample ∈ event
    · simp only [Set.indicator_of_notMem (show sample ∉ eventᶜ by simpa)]
      simpa using hpoint_good sample hsample hs
    · rw [Set.indicator_of_mem (show sample ∈ eventᶜ by simpa)]
      have hcapmin :
          regularizedWelfare E P (gibbsPolicy E P) -
              regularizedWelfare E P
                ((predictionPolytopeLearner E 64 (by norm_num)
                  (n := n)).deployed sample hsample) ≤
            min 2 (E.eta / 2) :=
        le_min (hpoint_cap sample hsample) (hpoint_eta sample hsample)
      exact hcapmin.trans (by linarith [hgoodBound])
  have hmajorant_integrable :
      Integrable (fun sample : LoggedSample n 𝒳 𝒜 =>
        goodBound +
          eventᶜ.indicator (fun _ => min 2 (E.eta / 2)) sample) μ :=
    (integrable_const goodBound).add
      ((integrable_const (min 2 (E.eta / 2))).indicator hevent.compl)
  rw [learnerRisk]
  change (∫ sample,
    (regularizedWelfare E P (gibbsPolicy E P) -
      regularizedWelfare E P
        (learnerPolicyOnSample E
          (predictionPolytopeLearner E 64 (by norm_num)
            (n := n)).deployed sample)) ∂μ) ≤ _
  calc
    _ ≤ ∫ sample,
        (goodBound +
          eventᶜ.indicator (fun _ => min 2 (E.eta / 2)) sample) ∂μ :=
      integral_mono_of_nonneg hregret_nonneg hmajorant_integrable hmajorant
    _ = goodBound + μ.real eventᶜ * min 2 (E.eta / 2) := by
      rw [integral_add (integrable_const goodBound)
        ((integrable_const (min 2 (E.eta / 2))).indicator hevent.compl)]
      simp [hevent.compl]
    _ ≤ goodBound +
        failureProbability n hn / 2 * min 2 (E.eta / 2) := by
      have hcap_nonneg : 0 ≤ min 2 (E.eta / 2) := by
        exact le_min (by norm_num) (div_nonneg E.eta_pos.le (by norm_num))
      gcongr
    _ = _ := rfl

lemma lowerEnvelopeLearnerRisk_le
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (C D : ℝ)
    (hshell : ExactShell E P C D)
    (hZhao : ZhaoUniformSquareComparison (𝒳 := 𝒳) (𝒜 := 𝒜))
    (hn : 0 < n) :
    learnerRisk E P n
        (predictionPolytopeLearner E 64 (by norm_num) (n := n)).deployed ≤
      min
        (300 * E.eta * (d : ℝ) * D *
          (((d : ℝ) * Real.log (Real.exp 1 * n) +
            Real.log (2 * (n : ℝ) ^ 2)) / n))
        (Real.sqrt
          (600 * (d : ℝ) * D *
            (((d : ℝ) * Real.log (Real.exp 1 * n) +
              Real.log (2 * (n : ℝ) ^ 2)) / n))) +
      failureProbability n hn := by
  refine (lowerEnvelopeLearnerRisk_le_sharp E P C D hshell hZhao hn).trans ?_
  have hfail : 0 ≤ failureProbability n hn := by
    simp only [failureProbability]
    positivity
  have hcap : min 2 (E.eta / 2) ≤ 2 := min_le_left _ _
  nlinarith

lemma lowerEnvelopeLearnerRisk_le_eta_half
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (C D : ℝ)
    (hshell : ExactShell E P C D) (hn : 0 < n) :
    learnerRisk E P n
        (predictionPolytopeLearner E 64 (by norm_num) (n := n)).deployed ≤
      E.eta / 2 := by
  let μ := productLaw E P n
  letI : IsProbabilityMeasure μ := productLaw_isProbability E P
  have hpoint (sample : LoggedSample n 𝒳 𝒜)
      (hsample : BoundedLoggedSample sample) :
      regularizedWelfare E P (gibbsPolicy E P) -
          regularizedWelfare E P
            ((predictionPolytopeLearner E 64 (by norm_num)
              (n := n)).deployed sample hsample) ≤ E.eta / 2 := by
    let r := linearReward P
    let g := lowerEnvelope E 64 sample
    have hsel := selectedERM_mem_confidencePolytope E sample hn
    have hr : ∀ x a, r x a ∈ Set.Icc (0 : ℝ) 1 :=
      (linearReward_mem_predictionPolytope E P C D hshell).1
    have hg : ∀ x a, g x a ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [g] using
        lowerEnvelope_mem_Icc_of_confidence_member
          E 64 sample (selectedERM E sample) hsel
    have hcap :=
      bounded_gibbs_welfare_regret_le_eta_half E (contextMass P) r g
        (contextMass_nonneg E P) (contextMass_sum_one E P) hr hg
    simpa [regularizedWelfare, welfareFromPotential, gibbsPolicy,
      gibbsNormalizer, gibbsFromPotential, predictionPolytopeLearner,
      lowerEnvelopePolicy, r, g] using hcap
  have hae_bounded := productLaw_bounded_sample E P n
  have hregret_nonneg :
      ∀ᵐ sample ∂μ,
        0 ≤ regularizedWelfare E P (gibbsPolicy E P) -
          regularizedWelfare E P
            (learnerPolicyOnSample E
              (predictionPolytopeLearner E 64 (by norm_num)
                (n := n)).deployed sample) := by
    filter_upwards [hae_bounded] with sample hsample
    simp only [learnerPolicyOnSample, dif_pos hsample]
    rw [gibbs_regret_identity E P C D hshell
      ((predictionPolytopeLearner E 64 (by norm_num)
        (n := n)).deployed sample hsample)
      ((predictionPolytopeLearner_measurable (n := n) E 64
        (by norm_num)).2 sample hsample |>.1)
      (by
        intro x a hpa
        by_contra href
        exact hpa ((predictionPolytopeLearner_measurable (n := n) E 64
          (by norm_num)).2 sample hsample |>.2 x a href))]
    apply mul_nonneg
    · exact inv_nonneg.mpr E.eta_pos.le
    · apply Finset.sum_nonneg
      intro x _
      apply mul_nonneg (contextMass_nonneg E P x)
      simpa only [predictionPolytopeLearner, lowerEnvelopePolicy, gibbsPolicy,
        gibbsFromPotential] using
        (policyKL_gibbsPotentials_nonneg (E := E)
          (linearReward P) (lowerEnvelope E 64 sample) x)
  rw [learnerRisk]
  change (∫ sample,
    (regularizedWelfare E P (gibbsPolicy E P) -
      regularizedWelfare E P
        (learnerPolicyOnSample E
          (predictionPolytopeLearner E 64 (by norm_num)
            (n := n)).deployed sample)) ∂μ) ≤ E.eta / 2
  calc
    _ ≤ ∫ _sample, E.eta / 2 ∂μ := by
      apply integral_mono_of_nonneg
      · exact hregret_nonneg
      · exact integrable_const _
      · filter_upwards [hae_bounded] with sample hsample
        simpa only [learnerPolicyOnSample, dif_pos hsample] using
          hpoint sample hsample
    _ = E.eta / 2 := by simp

end CausalSmith.Stat.ReverseKLTwoCoverage
