import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Upper.ERMPluginCore

/-!
# Expected risk of the ERM Gibbs plug-in learner

This module integrates the localized deterministic regret bound over the good
localization event and its complement.
-/

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

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

lemma ermGibbsPluginLearnerRisk_le
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (C D : ℝ)
    (hshell : ExactShell E P C D)
    (hZhao : ZhaoUniformSquareComparison (𝒳 := 𝒳) (𝒜 := 𝒜))
    (hn : 0 < n) :
    learnerRisk E P n (ermGibbsPluginLearner (n := n) E) ≤
      min
        (600 * kappa E.eta * D * localizationComplexity d n / n)
        (Real.sqrt 600 * (1 + Real.exp (2 * E.eta)) *
          Real.sqrt (D * localizationComplexity d n / n)) +
      failureProbability n hn / 2 * min 2 (E.eta / 2) := by
  let μ := productLaw E P n
  let Q := D * localizationComplexity d n / (n : ℝ)
  let goodBound :=
    min
      (600 * kappa E.eta * D * localizationComplexity d n / (n : ℝ))
      (Real.sqrt 600 * (1 + Real.exp (2 * E.eta)) *
        Real.sqrt (D * localizationComplexity d n / (n : ℝ)))
  let cap := min 2 (E.eta / 2)
  letI : IsProbabilityMeasure μ := productLaw_isProbability E P
  obtain ⟨event, hevent, hprob, hlocal⟩ :=
    bounded_linear_localization E P C D hshell hZhao hn 64 (by norm_num)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcomplexity :
      0 < localizationComplexity d n := by
    simpa [localizationComplexity,
      BoundedLinearLocalizationArithmetic.localizationRate] using
      BoundedLinearLocalizationArithmetic.localizationRate_pos E hn
  have hD : 0 < D := hshell.featureExactShell.1
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hkappa : 0 ≤ kappa E.eta :=
    le_trans (div_nonneg E.eta_pos.le (by norm_num))
      (kappa_half_le E.eta E.eta_pos)
  have hgoodBound : 0 ≤ goodBound := by
    dsimp [goodBound]
    apply le_min
    · positivity
    · positivity
  have hcap : 0 ≤ cap := by
    dsimp [cap]
    exact le_min (by norm_num) (div_nonneg E.eta_pos.le (by norm_num))
  have hcompl : μ.real eventᶜ ≤ failureProbability n hn / 2 := by
    rw [measureReal_compl hevent, probReal_univ]
    dsimp [μ] at hprob ⊢
    linarith
  have hpoint_good (sample : LoggedSample n 𝒳 𝒜)
      (hsample : BoundedLoggedSample sample) (hsample_event : sample ∈ event) :
      regularizedWelfare E P (gibbsPolicy E P) -
          regularizedWelfare E P
            (ermGibbsPluginLearner (n := n) E sample hsample) ≤
        goodBound := by
    let r := linearReward P
    let g := selectedERM E sample
    have hrpoly : r ∈ predictionPolytope E :=
      linearReward_mem_predictionPolytope E P C D hshell
    have hgpoly : g ∈ predictionPolytope E :=
      (selectedERM_isLexicographicERM E sample).1
    have hselected : g ∈ confidencePolytope E 64 sample := by
      refine ⟨hgpoly, ?_⟩
      have hrate :
          0 ≤ 64 *
            ((d : ℝ) * Real.log (Real.exp 1 * n) +
              Real.log (2 * (n : ℝ) ^ 2)) / (n : ℝ) := by
        positivity
      simpa [g, empiricalSeminormSq] using hrate
    have hrefMoment :=
      (hlocal sample hsample_event).2 g hselected
    have hspan : InFeatureSpan E (fun x a => g x a - r x a) := by
      rcases hgpoly.2 with ⟨bg, hbg⟩
      rcases hrpoly.2 with ⟨br, hbr⟩
      refine ⟨fun i => bg i - br i, ?_⟩
      intro x a
      change g x a - r x a = _
      rw [hbg, hbr, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hfeature :=
      feature_coverage_domination E P C D hshell
        (fun x a => g x a - r x a) hspan
    have hDelta :
        ∑ x, contextMass P x *
              ∑ a, gibbsFromPotential E r x a * (g x a - r x a) ^ 2 ≤
          600 * Q := by
      have hfeature' :
          ∑ x, contextMass P x *
                ∑ a, gibbsFromPotential E r x a * (g x a - r x a) ^ 2 ≤
            D * ((4 * 64 + 291) * localizationComplexity d n / (n : ℝ)) := by
        calc
          _ = policySecondMoment E P (gibbsPolicy E P)
              (fun x a => g x a - r x a) := by
                simp [policySecondMoment, gibbsPolicy, gibbsFromPotential,
                  gibbsNormalizer, r]
          _ ≤ featureCoverage E P *
              policySecondMoment E P E.reference
                (fun x a => g x a - r x a) := hfeature
          _ = D * policySecondMoment E P E.reference
                (fun x a => g x a - r x a) := by
              rw [hshell.featureExactShell.2]
          _ ≤ D * ((4 * 64 + 291) * localizationComplexity d n /
                (n : ℝ)) := by
              apply mul_le_mul_of_nonneg_left _ hD.le
              simpa [policySecondMoment, localizationComplexity, r, g] using
                hrefMoment
      calc
        _ ≤ D * ((4 * 64 + 291) * localizationComplexity d n /
              (n : ℝ)) := hfeature'
        _ ≤ 600 * Q := by
          dsimp [Q]
          have ht :
              0 ≤ localizationComplexity d n / (n : ℝ) :=
            div_nonneg hcomplexity.le hnreal.le
          calc
            D * ((4 * 64 + 291) * localizationComplexity d n / (n : ℝ)) =
                (4 * 64 + 291) *
                  (D * (localizationComplexity d n / (n : ℝ))) := by ring
            _ ≤ 600 * (D * (localizationComplexity d n / (n : ℝ))) :=
              mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hD.le ht)
            _ = 600 * (D * localizationComplexity d n / (n : ℝ)) := by ring
    have hr : ∀ x a, r x a ∈ Set.Icc (0 : ℝ) 1 := hrpoly.1
    have hg : ∀ x a, g x a ∈ Set.Icc (0 : ℝ) 1 := hgpoly.1
    have hconversion :=
      gibbs_plugin_conversion E (contextMass P) r g
        (contextMass_nonneg E P) (contextMass_sum_one E P) hr hg
    have hconverted :
        welfareFromPotential E (contextMass P) r (gibbsFromPotential E r) -
            welfareFromPotential E (contextMass P) r (gibbsFromPotential E g) ≤
          goodBound := by
      apply hconversion.trans
      dsimp [goodBound]
      apply min_le_min
      · calc
          kappa E.eta *
              (∑ x, contextMass P x *
                ∑ a, gibbsFromPotential E r x a *
                  (g x a - r x a) ^ 2) ≤
              kappa E.eta * (600 * Q) :=
            mul_le_mul_of_nonneg_left hDelta hkappa
          _ = 600 * kappa E.eta * D *
              localizationComplexity d n / (n : ℝ) := by
            dsimp [Q]
            ring
      · calc
          (1 + Real.exp (2 * E.eta)) *
              Real.sqrt
                (∑ x, contextMass P x *
                  ∑ a, gibbsFromPotential E r x a *
                    (g x a - r x a) ^ 2) ≤
              (1 + Real.exp (2 * E.eta)) * Real.sqrt (600 * Q) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hDelta) (by positivity)
          _ = Real.sqrt 600 * (1 + Real.exp (2 * E.eta)) *
              Real.sqrt (D * localizationComplexity d n / (n : ℝ)) := by
            rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 600)]
            dsimp [Q]
            ring
    simpa [regularizedWelfare, welfareFromPotential, gibbsPolicy,
      gibbsNormalizer, gibbsFromPotential, ermGibbsPluginLearner, r, g] using
      hconverted
  have hpoint_cap (sample : LoggedSample n 𝒳 𝒜)
      (hsample : BoundedLoggedSample sample) :
      regularizedWelfare E P (gibbsPolicy E P) -
          regularizedWelfare E P
            (ermGibbsPluginLearner (n := n) E sample hsample) ≤ cap := by
    let r := linearReward P
    let g := selectedERM E sample
    have hr : ∀ x a, r x a ∈ Set.Icc (0 : ℝ) 1 :=
      (linearReward_mem_predictionPolytope E P C D hshell).1
    have hg : ∀ x a, g x a ∈ Set.Icc (0 : ℝ) 1 :=
      (selectedERM_isLexicographicERM E sample).1.1
    have hmin :
        welfareFromPotential E (contextMass P) r (gibbsFromPotential E r) -
            welfareFromPotential E (contextMass P) r (gibbsFromPotential E g) ≤
          min 2 (E.eta / 2) :=
      le_min
        (gibbs_welfare_regret_le_two E (contextMass P) r g
          (contextMass_nonneg E P) (contextMass_sum_one E P) hr hg)
        (gibbs_welfare_regret_le_eta_half E (contextMass P) r g
          (contextMass_nonneg E P) (contextMass_sum_one E P) hr hg)
    simpa [cap, regularizedWelfare, welfareFromPotential, gibbsPolicy,
      gibbsNormalizer, gibbsFromPotential, ermGibbsPluginLearner, r, g] using
      hmin
  have hae_bounded := productLaw_bounded_sample E P n
  have hregret_nonneg :
      ∀ᵐ sample ∂μ,
        0 ≤ regularizedWelfare E P (gibbsPolicy E P) -
          regularizedWelfare E P
            (learnerPolicyOnSample E
              (ermGibbsPluginLearner (n := n) E) sample) := by
    filter_upwards [hae_bounded] with sample hsample
    simp only [learnerPolicyOnSample, dif_pos hsample]
    rw [gibbs_regret_identity E P C D hshell
      (ermGibbsPluginLearner (n := n) E sample hsample)
      ((ermGibbsPluginLearner_measurable (n := n) E).2 sample hsample |>.1)
      (by
        intro x a hpa
        by_contra href
        exact hpa ((ermGibbsPluginLearner_measurable (n := n) E).2
          sample hsample |>.2 x a href))]
    apply mul_nonneg
    · exact inv_nonneg.mpr E.eta_pos.le
    · apply Finset.sum_nonneg
      intro x _
      apply mul_nonneg (contextMass_nonneg E P x)
      simpa only [ermGibbsPluginLearner, gibbsPolicy,
        gibbsFromPotential] using
        (policyKL_gibbsPotentials_nonneg (E := E)
          (linearReward P) (selectedERM E sample) x)
  have hmajorant :
      ∀ᵐ sample ∂μ,
        regularizedWelfare E P (gibbsPolicy E P) -
            regularizedWelfare E P
              (learnerPolicyOnSample E
                (ermGibbsPluginLearner (n := n) E) sample) ≤
          goodBound + eventᶜ.indicator (fun _ => cap) sample := by
    filter_upwards [hae_bounded] with sample hsample
    simp only [learnerPolicyOnSample, dif_pos hsample]
    by_cases hs : sample ∈ event
    · simp only [Set.indicator_of_notMem (show sample ∉ eventᶜ by simpa)]
      simpa using hpoint_good sample hsample hs
    · rw [Set.indicator_of_mem (show sample ∈ eventᶜ by simpa)]
      exact (hpoint_cap sample hsample).trans (by linarith)
  have hmajorant_integrable :
      Integrable (fun sample : LoggedSample n 𝒳 𝒜 =>
        goodBound + eventᶜ.indicator (fun _ => cap) sample) μ :=
    (integrable_const goodBound).add
      ((integrable_const cap).indicator hevent.compl)
  rw [learnerRisk]
  change (∫ sample,
    (regularizedWelfare E P (gibbsPolicy E P) -
      regularizedWelfare E P
        (learnerPolicyOnSample E
          (ermGibbsPluginLearner (n := n) E) sample)) ∂μ) ≤ _
  calc
    _ ≤ ∫ sample, (goodBound + eventᶜ.indicator (fun _ => cap) sample) ∂μ :=
      integral_mono_of_nonneg hregret_nonneg hmajorant_integrable hmajorant
    _ = goodBound + μ.real eventᶜ * cap := by
      rw [integral_add (integrable_const goodBound)
        ((integrable_const cap).indicator hevent.compl)]
      simp [hevent.compl]
    _ ≤ goodBound + failureProbability n hn / 2 * cap := by
      gcongr
    _ = _ := by
      rfl

end CausalSmith.Stat.ReverseKLTwoCoverage
