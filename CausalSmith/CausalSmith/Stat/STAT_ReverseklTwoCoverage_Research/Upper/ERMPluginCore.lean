import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Upper.ERMPluginDefs
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Localization.BoundedLinearLocalization.LinearExactShell
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Localization.BoundedLinearLocalization.Adapters

/-!
# Core deterministic helpers for the ERM Gibbs plug-in bound

This module provides minimax-risk inversion and the deterministic Gibbs regret
caps used by the finite-sample expected-risk argument.
-/

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open LinearExactShellTypeFit
open BoundedLinearLocalizationAdapters
open MeasureTheory ProbabilityTheory
open CausalSmith.Substrate.FiniteExponentialTiltCalculus

variable {d n : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [LinearOrder 𝒳] [LinearOrder 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]

lemma sampleComplexity_le_of_learnerRisk_le
    (E : CommonExperiment d 𝒳 𝒜) (P0 : BanditLaw E) (C D eps : ℝ)
    (heps : 0 < eps) (heps_one : eps < 1)
    (hshell : ExactShell E P0 C D)
    (L : Learner n (𝒳 := 𝒳) (𝒜 := 𝒜))
    (hn : 0 < n) (hmeas : IsMeasurableLearner E L)
    (hrisk : ∀ P ∈ exactShellSet E C D, learnerRisk E P n L ≤ eps) :
    sampleComplexity E eps C D heps heps_one ≤ (n : WithTop ℕ) := by
  have hmodel : (exactShellSet E C D).Nonempty := ⟨P0, hshell⟩
  change sampleComplexityPositive E eps C D heps ≤ (n : WithTop ℕ)
  rw [sampleComplexityPositive, if_pos hmodel]
  apply csInf_le
  · exact ⟨1, by
      rintro m ⟨k, hk, rfl, _⟩
      exact_mod_cast hk⟩
  · refine ⟨n, hn, rfl, ?_⟩
    unfold minimaxRisk
    by_cases hb : BddBelow
        {r : ℝ | ∃ L : Learner n (𝒳 := 𝒳) (𝒜 := 𝒜),
          IsMeasurableLearner E L ∧
          r = sSup {q : ℝ | ∃ P : BanditLaw E,
            P ∈ exactShellSet E C D ∧ q = learnerRisk E P n L}}
    · calc
        sInf {r : ℝ | ∃ L : Learner n (𝒳 := 𝒳) (𝒜 := 𝒜),
            IsMeasurableLearner E L ∧
            r = sSup {q : ℝ | ∃ P : BanditLaw E,
              P ∈ exactShellSet E C D ∧ q = learnerRisk E P n L}} ≤
            sSup {q : ℝ | ∃ P : BanditLaw E, P ∈ exactShellSet E C D ∧
              q = learnerRisk E P n L} := by
          apply csInf_le hb
          exact ⟨L, hmeas, rfl⟩
        _ ≤ eps := by
          apply csSup_le
          · exact ⟨learnerRisk E P0 n L, P0, hshell, rfl⟩
          · rintro q ⟨P, hP, rfl⟩
            exact hrisk P hP
    · rw [csInf_of_not_bddBelow hb]
      simpa using heps.le

lemma ermPluginLearnerRisk_le_two_eta
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (C D : ℝ)
    (hshell : ExactShell E P C D) (n : ℕ) :
    learnerRisk E P n (ermGibbsPluginLearner (n := n) E) ≤ 2 * E.eta := by
  have hpoint (sample : LoggedSample n 𝒳 𝒜)
      (hsample : BoundedLoggedSample sample) :
      regularizedWelfare E P (gibbsPolicy E P) -
          regularizedWelfare E P
            (ermGibbsPluginLearner (n := n) E sample hsample) ≤
        2 * E.eta := by
    let r := linearReward P
    let g := selectedERM E sample
    have hr : ∀ x a, r x a ∈ Set.Icc (0 : ℝ) 1 :=
      (linearReward_mem_predictionPolytope E P C D hshell).1
    have hg : ∀ x a, g x a ∈ Set.Icc (0 : ℝ) 1 :=
      (selectedERM_isLexicographicERM E sample).1.1
    have hdelta : ∀ x a, (g x a - r x a) ^ 2 ≤ 1 := by
      intro x a
      nlinarith [hr x a |>.1, hr x a |>.2, hg x a |>.1, hg x a |>.2]
    have hmoment (s : 𝒳 → 𝒜 → ℝ) :
        ∑ x, contextMass P x *
            ∑ a, gibbsFromPotential E s x a * (g x a - r x a) ^ 2 ≤ 1 := by
      calc
        _ ≤ ∑ x, contextMass P x * 1 := by
          apply Finset.sum_le_sum
          intro x _
          apply mul_le_mul_of_nonneg_left _ (contextMass_nonneg E P x)
          calc
            _ ≤ ∑ a, gibbsFromPotential E s x a * 1 := by
              apply Finset.sum_le_sum
              intro a _
              exact mul_le_mul_of_nonneg_left (hdelta x a)
                ((gibbsFromPotential_isPolicy E s).1 x a)
            _ = 1 := by simp [(gibbsFromPotential_isPolicy E s).2 x]
        _ = 1 := by simp [contextMass_sum_one E P]
    have hfast :=
      two_endpoint_gibbs_fast E (contextMass P) r g
        (contextMass_nonneg E P)
    have hwelfare :
        welfareFromPotential E (contextMass P) r (gibbsFromPotential E r) -
            welfareFromPotential E (contextMass P) r (gibbsFromPotential E g) ≤
          2 * E.eta := by
      calc
        _ ≤ E.eta *
            ((∑ x, contextMass P x *
                ∑ a, gibbsFromPotential E r x a * (g x a - r x a) ^ 2) +
              ∑ x, contextMass P x *
                ∑ a, gibbsFromPotential E g x a * (g x a - r x a) ^ 2) :=
          hfast
        _ ≤ E.eta * (1 + 1) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (hmoment r) (hmoment g)) E.eta_pos.le
        _ = 2 * E.eta := by ring
    simpa [regularizedWelfare, welfareFromPotential, gibbsPolicy,
      gibbsNormalizer, gibbsFromPotential, ermGibbsPluginLearner, r, g] using
      hwelfare
  rw [learnerRisk]
  letI : MeasureTheory.IsProbabilityMeasure (productLaw E P n) :=
    productLaw_isProbability E P
  have hae := productLaw_bounded_sample E P n
  calc
    (∫ sample,
        (regularizedWelfare E P (gibbsPolicy E P) -
          regularizedWelfare E P
            (learnerPolicyOnSample E
              (ermGibbsPluginLearner (n := n) E) sample))
        ∂productLaw E P n) ≤
        ∫ _sample, (2 * E.eta) ∂productLaw E P n := by
      apply MeasureTheory.integral_mono_of_nonneg
      · filter_upwards [hae] with sample hsample
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
      · exact MeasureTheory.integrable_const _
      · filter_upwards [hae] with sample hsample
        simpa only [learnerPolicyOnSample, dif_pos hsample] using
          hpoint sample hsample
    _ = 2 * E.eta := by simp

lemma gibbs_welfare_regret_le_eta_half
    (E : CommonExperiment d 𝒳 𝒜)
    (rho : 𝒳 → ℝ) (r g : 𝒳 → 𝒜 → ℝ)
    (hrho_nonneg : ∀ x, 0 ≤ rho x) (hrho_mass : ∑ x, rho x = 1)
    (hr : ∀ x a, r x a ∈ Set.Icc (0 : ℝ) 1)
    (hg : ∀ x a, g x a ∈ Set.Icc (0 : ℝ) 1) :
    welfareFromPotential E rho r (gibbsFromPotential E r) -
        welfareFromPotential E rho r (gibbsFromPotential E g) ≤
      E.eta / 2 := by
  rw [gibbs_regret_eq_weighted_endpoint_remainder E]
  have hrem : ∀ x,
      mean (gibbsFromPotential E r x)
            (fun a => E.eta * (g x a - r x a)) 1 -
        (Real.log
            (partition (gibbsFromPotential E r x)
              (fun a => E.eta * (g x a - r x a)) 1) -
          Real.log
            (partition (gibbsFromPotential E r x)
              (fun a => E.eta * (g x a - r x a)) 0)) ≤
        E.eta ^ 2 / 2 := by
    intro x
    let w := gibbsFromPotential E r x
    let h : 𝒜 → ℝ := fun a => E.eta * (g x a - r x a)
    have hw : ∀ a, 0 ≤ w a := (gibbsFromPotential_isPolicy E r).1 x
    have hmass : ∑ a, w a = 1 := (gibbsFromPotential_isPolicy E r).2 x
    have hh : ∀ a, |h a| ≤ E.eta := by
      intro a
      dsimp [h]
      rw [abs_mul, abs_of_pos E.eta_pos]
      have : |g x a - r x a| ≤ 1 := by
        rw [abs_le]
        constructor <;>
          nlinarith [hr x a |>.1, hr x a |>.2, hg x a |>.1, hg x a |>.2]
      exact mul_le_of_le_one_right E.eta_pos.le this
    rw [endpointRemainder_eq_intervalIntegral w h hw hmass]
    have hleft : IntervalIntegrable (fun t : ℝ => t * variance w h t)
        volume 0 1 :=
      (continuous_id.mul (continuous_variance w h hw hmass)).intervalIntegrable 0 1
    have hright : IntervalIntegrable (fun t : ℝ => t * E.eta ^ 2)
        volume 0 1 := (continuous_id.mul continuous_const).intervalIntegrable 0 1
    calc
      (∫ t in (0 : ℝ)..1, t * variance w h t) ≤
          ∫ t in (0 : ℝ)..1, t * E.eta ^ 2 := by
        exact intervalIntegral.integral_mono_on zero_le_one hleft hright
          fun t ht => by
            apply mul_le_mul_of_nonneg_left _ ht.1
            calc
              variance w h t ≤ secondMoment w h t := by
                change secondMoment w h t - mean w h t ^ 2 ≤
                  secondMoment w h t
                nlinarith [sq_nonneg (mean w h t)]
              _ = ∑ a, tilt w h t a * h a ^ 2 :=
                secondMoment_eq_sum_tilt w h t
              _ ≤ ∑ a, tilt w h t a * E.eta ^ 2 := by
                apply Finset.sum_le_sum
                intro a _
                have hs : h a ^ 2 ≤ E.eta ^ 2 := by
                  have habs :
                      |h a| ^ 2 ≤ E.eta ^ 2 :=
                    (sq_le_sq₀ (abs_nonneg (h a)) E.eta_pos.le).2 (hh a)
                  simpa [sq_abs] using habs
                exact mul_le_mul_of_nonneg_left hs
                  (tilt_nonneg w h t hw hmass a)
              _ = E.eta ^ 2 := by
                rw [← Finset.sum_mul, sum_tilt w h t hw hmass]
                ring
      _ = E.eta ^ 2 / 2 := by
        rw [intervalIntegral.integral_mul_const, integral_id]
        ring
  have hsum :
      ∑ x, rho x *
          (mean (gibbsFromPotential E r x)
                (fun a => E.eta * (g x a - r x a)) 1 -
            (Real.log
                (partition (gibbsFromPotential E r x)
                  (fun a => E.eta * (g x a - r x a)) 1) -
              Real.log
                (partition (gibbsFromPotential E r x)
                  (fun a => E.eta * (g x a - r x a)) 0))) ≤
        E.eta ^ 2 / 2 := by
    calc
      _ ≤ ∑ x, rho x * (E.eta ^ 2 / 2) := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_left (hrem x) (hrho_nonneg x)
      _ = E.eta ^ 2 / 2 := by rw [← Finset.sum_mul, hrho_mass]; ring
  have heta : E.eta ≠ 0 := ne_of_gt E.eta_pos
  calc
    E.eta⁻¹ * _ ≤ E.eta⁻¹ * (E.eta ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr E.eta_pos.le)
    _ = E.eta / 2 := by field_simp

lemma gibbs_welfare_regret_le_two
    (E : CommonExperiment d 𝒳 𝒜)
    (rho : 𝒳 → ℝ) (r g : 𝒳 → 𝒜 → ℝ)
    (hrho_nonneg : ∀ x, 0 ≤ rho x) (hrho_mass : ∑ x, rho x = 1)
    (hr : ∀ x a, r x a ∈ Set.Icc (0 : ℝ) 1)
    (hg : ∀ x a, g x a ∈ Set.Icc (0 : ℝ) 1) :
    welfareFromPotential E rho r (gibbsFromPotential E r) -
        welfareFromPotential E rho r (gibbsFromPotential E g) ≤ 2 := by
  rw [welfareFromPotential_regret_eq_kl E]
  have hkl : ∀ x,
      policyKL (gibbsFromPotential E g) (gibbsFromPotential E r) x ≤
        2 * E.eta := by
    intro x
    rw [policyKL_gibbsPotentials_expansion E]
    have hmean :
        ∑ a, gibbsFromPotential E g x a * (g x a - r x a) ≤ 1 := by
      calc
        _ ≤ ∑ a, gibbsFromPotential E g x a * 1 := by
          apply Finset.sum_le_sum
          intro a _
          exact mul_le_mul_of_nonneg_left
            (by linarith [hr x a |>.1, hg x a |>.2])
            ((gibbsFromPotential_isPolicy E g).1 x a)
        _ = 1 := by simp [(gibbsFromPotential_isPolicy E g).2 x]
    have hZr :
        ∑ b, E.reference x b * Real.exp (E.eta * r x b) ≤
          Real.exp E.eta := by
      calc
        _ ≤ ∑ b, E.reference x b * Real.exp E.eta := by
          apply Finset.sum_le_sum
          intro b _
          apply mul_le_mul_of_nonneg_left _ (E.reference_isPolicy.1 x b)
          exact Real.exp_le_exp.mpr
            (by nlinarith [E.eta_pos, hr x b |>.2])
        _ = Real.exp E.eta := by
          rw [← Finset.sum_mul, E.reference_isPolicy.2 x]
          ring
    have hZg :
        1 ≤ ∑ b, E.reference x b * Real.exp (E.eta * g x b) := by
      calc
        1 = ∑ b, E.reference x b * 1 := by
          rw [← Finset.sum_mul, E.reference_isPolicy.2 x]
          ring
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro b _
          apply mul_le_mul_of_nonneg_left _ (E.reference_isPolicy.1 x b)
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr
            (mul_nonneg E.eta_pos.le (hg x b |>.1))
    have hlogr :
        Real.log (∑ b, E.reference x b * Real.exp (E.eta * r x b)) ≤
          E.eta := by
      calc
        _ ≤ Real.log (Real.exp E.eta) :=
          Real.strictMonoOn_log.monotoneOn
            (gibbsPotentialNormalizer_pos E r x)
            (Real.exp_pos _) hZr
        _ = E.eta := Real.log_exp _
    have hlogg :
        0 ≤ Real.log
          (∑ b, E.reference x b * Real.exp (E.eta * g x b)) :=
      Real.log_nonneg hZg
    nlinarith [mul_le_mul_of_nonneg_left hmean E.eta_pos.le]
  have hsum :
      ∑ x, rho x *
          policyKL (gibbsFromPotential E g) (gibbsFromPotential E r) x ≤
        2 * E.eta := by
    calc
      _ ≤ ∑ x, rho x * (2 * E.eta) := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_left (hkl x) (hrho_nonneg x)
      _ = 2 * E.eta := by rw [← Finset.sum_mul, hrho_mass]; ring
  calc
    E.eta⁻¹ * _ ≤ E.eta⁻¹ * (2 * E.eta) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr E.eta_pos.le)
    _ = 2 := by field_simp [ne_of_gt E.eta_pos]

lemma kappa_half_le (eta : ℝ) (heta : 0 < eta) :
    eta / 2 ≤ kappa eta := by
  have hint :
      (1 / 2 : ℝ) ≤
        ∫ t in Set.Icc (0 : ℝ) 1, t * Real.exp (2 * eta * t) := by
    calc
      (1 / 2 : ℝ) = ∫ t in Set.Icc (0 : ℝ) 1, t := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
        rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        rw [integral_id]
        norm_num
      _ ≤ ∫ t in Set.Icc (0 : ℝ) 1, t * Real.exp (2 * eta * t) := by
        have hf : MeasureTheory.IntegrableOn (fun t : ℝ => t)
            (Set.Icc 0 1) := continuous_id.integrableOn_Icc
        have hg : MeasureTheory.IntegrableOn
            (fun t : ℝ => t * Real.exp (2 * eta * t)) (Set.Icc 0 1) :=
          (continuous_id.mul
            (Real.continuous_exp.comp
              (continuous_const.mul continuous_id))).integrableOn_Icc
        exact MeasureTheory.setIntegral_mono_on hf hg measurableSet_Icc (fun t ht => by
          have he : 1 ≤ Real.exp (2 * eta * t) := by
            rw [← Real.exp_zero]
            apply Real.exp_le_exp.mpr
            exact mul_nonneg (mul_nonneg (by norm_num) heta.le) ht.1
          nlinarith [ht.1])
  unfold kappa
  nlinarith [mul_le_mul_of_nonneg_left hint heta.le]

lemma kappa_lt_four_mul (eta : ℝ) (heta : 0 < eta) (heta_one : eta < 1) :
    kappa eta < 4 * eta := by
  have hexp2 : Real.exp 2 < 8 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1,
      sq_nonneg (Real.exp 1 - 2.7182818286)]
  have hint :
      (∫ t in Set.Icc (0 : ℝ) 1, t * Real.exp (2 * eta * t)) <
        4 := by
    have hmono :
        (∫ t in Set.Icc (0 : ℝ) 1, t * Real.exp (2 * eta * t)) ≤
          ∫ t in Set.Icc (0 : ℝ) 1, t * Real.exp 2 := by
      have hf : MeasureTheory.IntegrableOn
          (fun t : ℝ => t * Real.exp (2 * eta * t)) (Set.Icc 0 1) :=
        (continuous_id.mul
          (Real.continuous_exp.comp
            (continuous_const.mul continuous_id))).integrableOn_Icc
      have hg : MeasureTheory.IntegrableOn
          (fun t : ℝ => t * Real.exp 2) (Set.Icc 0 1) :=
        (continuous_id.mul (continuous_const : Continuous fun _ : ℝ =>
          Real.exp 2)).integrableOn_Icc
      exact MeasureTheory.setIntegral_mono_on hf hg measurableSet_Icc (fun t ht => by
        have he : Real.exp (2 * eta * t) ≤ Real.exp 2 := by
          apply Real.exp_le_exp.mpr
          nlinarith [ht.1, ht.2]
        exact mul_le_mul_of_nonneg_left he ht.1)
    calc
      _ ≤ ∫ t in Set.Icc (0 : ℝ) 1, t * Real.exp 2 := hmono
      _ = Real.exp 2 / 2 := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
        rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        rw [intervalIntegral.integral_mul_const,
          integral_id]
        ring
      _ < 4 := by linarith
  unfold kappa
  nlinarith

end CausalSmith.Stat.ReverseKLTwoCoverage
