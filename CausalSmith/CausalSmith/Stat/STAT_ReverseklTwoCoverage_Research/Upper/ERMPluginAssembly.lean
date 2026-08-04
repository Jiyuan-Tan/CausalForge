import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Upper.ERMPluginLocalizedGap
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Upper.ERMPluginExpectedRisk

/-!
# Assembly of the ERM Gibbs plug-in upper bound

This module combines the exact expected-risk leaf with the plug-in and
localized sample-size inversions.
-/

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

theorem erm_plugin_upper_proof :
    ∃ K : ℝ, 0 < K ∧
      ∀ (d : ℕ) (𝒳 𝒜 : Type*)
        [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
        [LinearOrder 𝒳] [LinearOrder 𝒜]
        [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
        [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
        (E : CommonExperiment d 𝒳 𝒜) (P0 : BanditLaw E) (C D : ℝ),
        ExactShell E P0 C D →
        ZhaoUniformSquareComparison (𝒳 := 𝒳) (𝒜 := 𝒜) →
        (∀ n, ∀ hn : 0 < n,
          IsMeasurableLearner E (ermGibbsPluginLearner (n := n) E) ∧
          ∀ P ∈ exactShellSet E C D,
            learnerRisk E P n (ermGibbsPluginLearner (n := n) E) ≤
              min
                (600 * kappa E.eta * D * localizationComplexity d n / n)
                (Real.sqrt 600 * (1 + Real.exp (2 * E.eta)) *
                  Real.sqrt (D * localizationComplexity d n / n)) +
              failureProbability n hn / 2 * min 2 (E.eta / 2)) ∧
        ∀ eps, ∀ heps : 0 < eps, ∀ heps_one : eps < 1,
          let qPlugin := (d : ℝ) * D *
            min (kappa E.eta / eps)
              ((1 + Real.exp (2 * E.eta)) ^ 2 / eps ^ 2)
          let qEnvelope := (d : ℝ) * D *
            min (d * E.eta / eps)
              (min (d / eps ^ 2)
                (min (kappa E.eta / eps)
                  ((1 + Real.exp (2 * E.eta)) ^ 2 / eps ^ 2)))
          (2 ≤ K * qPlugin * pluginLogFactor E.eta eps qPlugin →
            sampleComplexity E eps C D heps heps_one ≤
              (↑⌈K * qPlugin * pluginLogFactor E.eta eps qPlugin⌉₊ : WithTop ℕ)) ∧
          (2 ≤ K * qEnvelope * pluginLogFactor E.eta eps qEnvelope →
            sampleComplexity E eps C D heps heps_one ≤
              (↑⌈K * qEnvelope * pluginLogFactor E.eta eps qEnvelope⌉₊ : WithTop ℕ)) := by
  obtain ⟨Kloc, hKloc, hlocalized, _⟩ := localized_upper
  let K := (10 : ℝ) ^ 8 * max 1 Kloc
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro d 𝒳 𝒜 _ _ _ _ _ _ _ _ _ _ E P0 C D hshell hZhao
  have hrisk :
      ∀ n, ∀ hn : 0 < n,
        IsMeasurableLearner E (ermGibbsPluginLearner (n := n) E) ∧
        ∀ P ∈ exactShellSet E C D,
          learnerRisk E P n (ermGibbsPluginLearner (n := n) E) ≤
            min
              (600 * kappa E.eta * D * localizationComplexity d n / n)
              (Real.sqrt 600 * (1 + Real.exp (2 * E.eta)) *
                Real.sqrt (D * localizationComplexity d n / n)) +
            failureProbability n hn / 2 * min 2 (E.eta / 2) := by
    intro n hn
    refine ⟨ermGibbsPluginLearner_measurable (n := n) E, ?_⟩
    intro P hP
    exact ermGibbsPluginLearnerRisk_le E P C D hP hZhao hn
  refine ⟨hrisk, ?_⟩
  intro eps heps heps_one
  dsimp only
  let qPlugin := (d : ℝ) * D *
    min (kappa E.eta / eps)
      ((1 + Real.exp (2 * E.eta)) ^ 2 / eps ^ 2)
  let qLocal := (d : ℝ) ^ 2 * D *
    min (E.eta / eps) ((eps ^ 2)⁻¹)
  let qEnvelope := (d : ℝ) * D *
    min (d * E.eta / eps)
      (min (d / eps ^ 2)
        (min (kappa E.eta / eps)
          ((1 + Real.exp (2 * E.eta)) ^ 2 / eps ^ 2)))
  have hD : 1 ≤ D := (feasible_index_region (E := E)).1 P0 C D hshell |>.1
  have hKlarge : (10 : ℝ) ^ 8 ≤ K := by
    dsimp [K]
    have := le_max_left (1 : ℝ) Kloc
    nlinarith
  have hplugin :
      2 ≤ K * qPlugin * pluginLogFactor E.eta eps qPlugin →
        sampleComplexity E eps C D heps heps_one ≤
          (↑⌈K * qPlugin * pluginLogFactor E.eta eps qPlugin⌉₊ :
            WithTop ℕ) := by
    intro htarget
    let N : ℕ := ⌈K * qPlugin * pluginLogFactor E.eta eps qPlugin⌉₊
    have hNreal :
        K * qPlugin * pluginLogFactor E.eta eps qPlugin ≤ (N : ℝ) :=
      Nat.le_ceil _
    have hN : 0 < N := by
      have hNreal_pos : (0 : ℝ) < (N : ℝ) :=
        lt_of_lt_of_le (by linarith [htarget]) hNreal
      exact_mod_cast hNreal_pos
    by_cases hsmall : 2 * E.eta ≤ eps
    · calc
        sampleComplexity E eps C D heps heps_one ≤ (1 : WithTop ℕ) := by
          apply sampleComplexity_le_of_learnerRisk_le E P0 C D eps
            heps heps_one hshell (ermGibbsPluginLearner (n := 1) E)
            (by norm_num) (ermGibbsPluginLearner_measurable (n := 1) E)
          intro P hP
          exact (ermPluginLearnerRisk_le_two_eta E P C D hP 1).trans hsmall
        _ ≤ N := by exact_mod_cast hN
    · have heta_eps : eps < 2 * E.eta := lt_of_not_ge hsmall
      have hkappa := kappa_half_le E.eta E.eta_pos
      have hqFast :
          1 ≤ (d : ℝ) * D * (kappa E.eta / eps) := by
        have hd : (4 : ℝ) ≤ d := by exact_mod_cast E.dim_ge_four
        have hratio : 1 / 4 < kappa E.eta / eps := by
          apply (lt_div_iff₀ heps).2
          nlinarith
        have hdD : (4 : ℝ) ≤ (d : ℝ) * D := by
          calc
            (4 : ℝ) = 4 * 1 := by ring
            _ ≤ (d : ℝ) * D :=
              mul_le_mul hd hD (by norm_num) (by positivity)
        have hone : (1 : ℝ) < 4 * (kappa E.eta / eps) := by
          nlinarith
        exact hone.le.trans
          (mul_le_mul_of_nonneg_right hdD (by linarith))
      have hqSlow :
          1 ≤ (d : ℝ) * D *
            ((1 + Real.exp (2 * E.eta)) ^ 2 / eps ^ 2) := by
        have hd : (4 : ℝ) ≤ d := by exact_mod_cast E.dim_ge_four
        have hexp : 1 ≤ Real.exp (2 * E.eta) := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by nlinarith [E.eta_pos])
        have hratio :
            4 < (1 + Real.exp (2 * E.eta)) ^ 2 / eps ^ 2 := by
          apply (lt_div_iff₀ (sq_pos_of_pos heps)).2
          nlinarith [sq_nonneg (Real.exp (2 * E.eta) - 1), heps_one]
        have hdD : (4 : ℝ) ≤ (d : ℝ) * D := by
          calc
            (4 : ℝ) = 4 * 1 := by ring
            _ ≤ (d : ℝ) * D :=
              mul_le_mul hd hD (by norm_num) (by positivity)
        have hone :
            (1 : ℝ) < 4 *
              ((1 + Real.exp (2 * E.eta)) ^ 2 / eps ^ 2) := by
          nlinarith
        exact hone.le.trans
          (mul_le_mul_of_nonneg_right hdD (by linarith))
      have hq : 1 ≤ qPlugin := by
        dsimp [qPlugin]
        rw [mul_min_of_nonneg _ _
          (mul_nonneg (by positivity) (le_trans zero_le_one hD))]
        exact le_min hqFast hqSlow
      have hL : 2 ≤ pluginLogFactor E.eta eps qPlugin := by
        unfold pluginLogFactor
        have hlogq : 0 ≤ Real.log qPlugin := Real.log_nonneg hq
        have hthird :
            0 ≤ Real.log (1 + (1 + E.eta) * qPlugin / eps) := by
          apply Real.log_nonneg
          have : 0 ≤ (1 + E.eta) * qPlugin / eps :=
            div_nonneg
              (mul_nonneg (by linarith [E.eta_pos])
                (le_trans zero_le_one hq))
              heps.le
          linarith
        rw [Real.log_mul (Real.exp_ne_zero 1)
          (ne_of_gt (lt_of_lt_of_le zero_lt_one hq)), Real.log_exp]
        linarith
      have hbase :
          2 ≤ (10 : ℝ) ^ 8 * qPlugin *
            pluginLogFactor E.eta eps qPlugin := by
        nlinarith
      have hp := plugin_sampleComplexity_bound E P0 C D eps hshell
        heps heps_one hrisk hbase
      calc
        sampleComplexity E eps C D heps heps_one ≤
            (↑⌈(10 : ℝ) ^ 8 * qPlugin *
              pluginLogFactor E.eta eps qPlugin⌉₊ : WithTop ℕ) := hp
        _ ≤ (↑⌈K * qPlugin *
              pluginLogFactor E.eta eps qPlugin⌉₊ : WithTop ℕ) := by
          exact_mod_cast Nat.ceil_mono (by
            have hnonneg :
                0 ≤ qPlugin * pluginLogFactor E.eta eps qPlugin :=
              mul_nonneg (le_trans zero_le_one hq)
                (le_trans zero_le_two hL)
            have hKlarge' : ((10 ^ 8 : ℕ) : ℝ) ≤ K := by
              norm_num at hKlarge ⊢
              exact hKlarge
            calc
              ((10 ^ 8 : ℕ) : ℝ) * qPlugin *
                  pluginLogFactor E.eta eps qPlugin =
                ((10 ^ 8 : ℕ) : ℝ) *
                  (qPlugin * pluginLogFactor E.eta eps qPlugin) := by ring
              _ ≤ K * (qPlugin * pluginLogFactor E.eta eps qPlugin) :=
                mul_le_mul_of_nonneg_right hKlarge' hnonneg
              _ = K * qPlugin *
                  pluginLogFactor E.eta eps qPlugin := by ring)
  refine ⟨hplugin, ?_⟩
  intro henvelope
  have hqEnvelope :
      qEnvelope = min qLocal qPlugin := by
    dsimp [qEnvelope, qLocal, qPlugin]
    have hd0 : 0 ≤ (d : ℝ) := by positivity
    have hD0 : 0 ≤ D := le_trans zero_le_one hD
    have hdD0 : 0 ≤ (d : ℝ) * D := mul_nonneg hd0 hD0
    have hd2D0 : 0 ≤ (d : ℝ) ^ 2 * D :=
      mul_nonneg (sq_nonneg _) hD0
    rw [mul_min_of_nonneg _ _ hdD0]
    rw [mul_min_of_nonneg _ _ hdD0]
    rw [mul_min_of_nonneg _ _ hdD0]
    rw [mul_min_of_nonneg _ _ hd2D0]
    ring_nf
    simp only [min_assoc]
  change
    2 ≤ K * qEnvelope * pluginLogFactor E.eta eps qEnvelope at henvelope
  change
    sampleComplexity E eps C D heps heps_one ≤
      (↑⌈K * qEnvelope * pluginLogFactor E.eta eps qEnvelope⌉₊ :
        WithTop ℕ)
  rw [hqEnvelope] at henvelope ⊢
  rcases le_total qLocal qPlugin with hbranch | hbranch
  · rw [min_eq_left hbranch] at henvelope ⊢
    have heta_eps : eps ≤ E.eta := by
      by_contra h
      have heta_lt : E.eta < eps := lt_of_not_ge h
      have hkappa_lt : kappa E.eta < d * E.eta := by
        have hk4 := kappa_lt_four_mul E.eta E.eta_pos
          (lt_trans heta_lt heps_one)
        have hd : (4 : ℝ) ≤ d := by exact_mod_cast E.dim_ge_four
        exact hk4.trans_le
          (mul_le_mul_of_nonneg_right hd E.eta_pos.le)
      have hlocalFast :
          qLocal = (d : ℝ) ^ 2 * D * (E.eta / eps) := by
        dsimp [qLocal]
        rw [min_eq_left (by
          field_simp [ne_of_gt heps]
          nlinarith [heta_lt, heps_one, E.eta_pos])]
      have hpluginLt : qPlugin < qLocal := by
        calc
          qPlugin ≤ (d : ℝ) * D * (kappa E.eta / eps) := by
            dsimp [qPlugin]
            gcongr
            exact min_le_left _ _
          _ < (d : ℝ) ^ 2 * D * (E.eta / eps) := by
            have hd : (4 : ℝ) ≤ d := by exact_mod_cast E.dim_ge_four
            have hdpos : 0 < (d : ℝ) := lt_of_lt_of_le (by norm_num) hd
            have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
            calc
              (d : ℝ) * D * (kappa E.eta / eps) <
                  (d : ℝ) * D * (((d : ℝ) * E.eta) / eps) :=
                mul_lt_mul_of_pos_left
                  ((div_lt_div_iff_of_pos_right heps).2 hkappa_lt)
                  (mul_pos hdpos hDpos)
              _ = (d : ℝ) ^ 2 * D * (E.eta / eps) := by ring
          _ = qLocal := hlocalFast.symm
      exact (not_lt_of_ge hbranch) hpluginLt
    have hlocData :=
      hlocalized d 𝒳 𝒜 E P0 C D hshell hZhao
    have heta_one : 1 ≤ E.eta := by
      by_contra h
      have heta_lt : E.eta < 1 := lt_of_not_ge h
      have hkappa_lt : kappa E.eta < (d : ℝ) * E.eta := by
        have hk4 := kappa_lt_four_mul E.eta E.eta_pos heta_lt
        have hd : (4 : ℝ) ≤ d := by exact_mod_cast E.dim_ge_four
        exact hk4.trans_le
          (mul_le_mul_of_nonneg_right hd E.eta_pos.le)
      have hpluginFastLocalFast :
          (d : ℝ) * D * (kappa E.eta / eps) <
            (d : ℝ) ^ 2 * D * (E.eta / eps) := by
        have hd : (4 : ℝ) ≤ d := by exact_mod_cast E.dim_ge_four
        have hdpos : 0 < (d : ℝ) := lt_of_lt_of_le (by norm_num) hd
        have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
        calc
          (d : ℝ) * D * (kappa E.eta / eps) <
              (d : ℝ) * D * (((d : ℝ) * E.eta) / eps) :=
            mul_lt_mul_of_pos_left
              ((div_lt_div_iff_of_pos_right heps).2 hkappa_lt)
              (mul_pos hdpos hDpos)
          _ = (d : ℝ) ^ 2 * D * (E.eta / eps) := by ring
      have hpluginFastLocalSlow :
          (d : ℝ) * D * (kappa E.eta / eps) <
            (d : ℝ) ^ 2 * D * (eps ^ 2)⁻¹ := by
        have hd : (4 : ℝ) ≤ d := by exact_mod_cast E.dim_ge_four
        have hdpos : 0 < (d : ℝ) := lt_of_lt_of_le (by norm_num) hd
        have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
        have hk4 := kappa_lt_four_mul E.eta E.eta_pos heta_lt
        have heta_eps_one : E.eta * eps < 1 := by
          calc
            E.eta * eps < 1 * eps :=
              mul_lt_mul_of_pos_right heta_lt heps
            _ < 1 := by simpa using heps_one
        have hkappa_eps : kappa E.eta * eps < (d : ℝ) := by
          have := mul_lt_mul_of_pos_right hk4 heps
          nlinarith
        calc
          (d : ℝ) * D * (kappa E.eta / eps) <
              (d : ℝ) * D * ((d : ℝ) / eps ^ 2) := by
            apply mul_lt_mul_of_pos_left _ (mul_pos hdpos hDpos)
            field_simp [ne_of_gt heps]
            exact hkappa_eps
          _ = (d : ℝ) ^ 2 * D * (eps ^ 2)⁻¹ := by ring
      have hpluginLt : qPlugin < qLocal := by
        calc
          qPlugin ≤ (d : ℝ) * D * (kappa E.eta / eps) := by
            dsimp [qPlugin]
            exact mul_le_mul_of_nonneg_left (min_le_left _ _)
              (mul_nonneg (by positivity) (le_trans zero_le_one hD))
          _ < qLocal := by
            dsimp [qLocal]
            rw [mul_min_of_nonneg _ _
              (mul_nonneg (sq_nonneg _) (le_trans zero_le_one hD))]
            exact lt_min hpluginFastLocalFast hpluginFastLocalSlow
      exact (not_lt_of_ge hbranch) hpluginLt
    have hqeps : 2 / eps ≤ qLocal := by
      dsimp [qLocal]
      rw [mul_min_of_nonneg _ _
        (mul_nonneg (sq_nonneg _) (le_trans zero_le_one hD))]
      apply le_min
      · have hd : (4 : ℝ) ≤ d := by exact_mod_cast E.dim_ge_four
        have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
        field_simp [ne_of_gt heps]
        nlinarith [sq_nonneg ((d : ℝ) - 4), mul_pos E.eta_pos hDpos]
      · have hd : (4 : ℝ) ≤ d := by exact_mod_cast E.dim_ge_four
        have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
        field_simp [ne_of_gt heps]
        nlinarith [sq_nonneg ((d : ℝ) - 4), mul_pos heps hDpos]
    exact localized_sampleComplexity_bound_scaled E P0 C D eps Kloc
      hshell heps heps_one hKloc hlocData hqeps henvelope
  · rw [min_eq_right hbranch] at henvelope ⊢
    exact hplugin henvelope

end CausalSmith.Stat.ReverseKLTwoCoverage
