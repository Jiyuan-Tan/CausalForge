import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Upper.ERMPluginInversion

/-!
# Localized-envelope fallback for the ERM plug-in upper bound

This module rescales the localized learner theorem to the common explicit
polylogarithmic factor used by the final envelope bound.
-/

namespace CausalSmith.Stat.ReverseKLTwoCoverage

variable {d : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [LinearOrder 𝒳] [LinearOrder 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]

set_option maxHeartbeats 800000 in
lemma localized_sampleComplexity_bound_scaled
    (E : CommonExperiment d 𝒳 𝒜) (P0 : BanditLaw E) (C D eps Kloc : ℝ)
    (hshell : ExactShell E P0 C D)
    (heps : 0 < eps) (heps_one : eps < 1)
    (hKloc : 0 < Kloc)
    (hloc :
      ∀ n, ∀ hn : 0 < n,
        IsMeasurableLearner E
            (predictionPolytopeLearner E 64 (by norm_num) (n := n)).deployed ∧
        (∀ P ∈ exactShellSet E C D,
          learnerRisk E P n
              (predictionPolytopeLearner E 64 (by norm_num) (n := n)).deployed ≤
            Kloc * localizedRate E.eta D d n + failureProbability n hn) ∧
        ∀ eps, ∀ heps : 0 < eps, ∀ heps_one : eps < 1,
          let q := (d : ℝ) ^ 2 * D *
            min (E.eta / eps) ((eps ^ 2)⁻¹)
          2 ≤ Kloc * q * localizedLogFactor E.eta eps q →
          sampleComplexity E eps C D heps heps_one ≤
            (↑⌈Kloc * q * localizedLogFactor E.eta eps q⌉₊ : WithTop ℕ))
    (hqeps :
      2 / eps ≤
        (d : ℝ) ^ 2 * D * min (E.eta / eps) ((eps ^ 2)⁻¹)) :
    let q := (d : ℝ) ^ 2 * D * min (E.eta / eps) ((eps ^ 2)⁻¹)
    let K := (10 : ℝ) ^ 8 * max 1 Kloc
    2 ≤ K * q * pluginLogFactor E.eta eps q →
      sampleComplexity E eps C D heps heps_one ≤
        (↑⌈K * q * pluginLogFactor E.eta eps q⌉₊ : WithTop ℕ) := by
  dsimp only
  let qFast := (d : ℝ) ^ 2 * D * (E.eta / eps)
  let qSlow := (d : ℝ) ^ 2 * D * (eps ^ 2)⁻¹
  let q := (d : ℝ) ^ 2 * D * min (E.eta / eps) ((eps ^ 2)⁻¹)
  let L := pluginLogFactor E.eta eps q
  let K := (10 : ℝ) ^ 8 * max 1 Kloc
  let T := K * q * L
  let N : ℕ := ⌈T⌉₊
  intro hT
  have hD : 1 ≤ D := (feasible_index_region (E := E)).1 P0 C D hshell |>.1
  have hdDnonneg : 0 ≤ (d : ℝ) ^ 2 * D :=
    mul_nonneg (sq_nonneg _) (le_trans zero_le_one hD)
  have hqeq : q = min qFast qSlow := by
    dsimp only [q, qFast, qSlow]
    exact mul_min_of_nonneg _ _ hdDnonneg
  have hq : 1 ≤ q := by
    have he : 2 < 2 / eps := by
      apply (lt_div_iff₀ heps).2
      nlinarith
    linarith
  have hL : 2 ≤ L := by
    dsimp [L, pluginLogFactor]
    have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq
    have hthird :
        0 ≤ Real.log (1 + (1 + E.eta) * q / eps) := by
      apply Real.log_nonneg
      have hfrac : 0 ≤ (1 + E.eta) * q / eps :=
        div_nonneg
          (mul_nonneg (by linarith [E.eta_pos]) (le_trans zero_le_one hq))
          heps.le
      linarith
    rw [Real.log_mul (Real.exp_ne_zero 1)
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hq)), Real.log_exp]
    linarith
  by_cases horiginal : 2 ≤ Kloc * q * localizedLogFactor E.eta eps q
  · have hbound := (hloc 1 (by norm_num)).2.2 eps heps heps_one horiginal
    calc
      sampleComplexity E eps C D heps heps_one ≤
          (↑⌈Kloc * q * localizedLogFactor E.eta eps q⌉₊ : WithTop ℕ) := hbound
      _ ≤ (↑⌈T⌉₊ : WithTop ℕ) := by
        exact_mod_cast Nat.ceil_mono (by
          dsimp [T, K]
          change Kloc * q * L ≤ 10 ^ 8 * max 1 Kloc * q * L
          have hmax : Kloc ≤ max 1 Kloc := le_max_right _ _
          have hqL : 0 ≤ q * L := mul_nonneg
            (le_trans zero_le_one hq) (le_trans zero_le_two hL)
          nlinarith [mul_le_mul_of_nonneg_right hmax hqL])
  · have hKloc_one : Kloc < 1 := by
      by_contra h
      have hKone : 1 ≤ Kloc := le_of_not_gt h
      have hprod : 1 ≤ Kloc * q := by
        calc
          (1 : ℝ) = 1 * 1 := by ring
          _ ≤ Kloc * q := mul_le_mul hKone hq
            (by norm_num) hKloc.le
      exact horiginal (by
        change 2 ≤ Kloc * q * L
        nlinarith [mul_le_mul_of_nonneg_left hL
          (le_trans zero_le_one hprod)])
    have hK : K = (10 : ℝ) ^ 8 := by
      dsimp [K]
      rw [max_eq_left (le_of_lt hKloc_one)]
      norm_num
    have hNreal : T ≤ (N : ℝ) := Nat.le_ceil _
    have hN : 0 < N := by
      have hNr : (0 : ℝ) < (N : ℝ) :=
        lt_of_lt_of_le (by linarith [hT]) hNreal
      exact_mod_cast hNr
    have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
    have hNupper : (N : ℝ) ≤ 2 * T := by
      have hceil := Nat.ceil_lt_add_one hTpos.le
      calc
        (N : ℝ) ≤ T + 1 := hceil.le
        _ ≤ 2 * T := by nlinarith [hT]
    have hlocN :
        localizationComplexity d N ≤ 20 * (d + 2 : ℝ) * L := by
      apply localizationComplexity_le_of_pluginLog d N E.eta eps q
        E.dim_ge_four E.eta_pos heps hq
      · simpa [T, hK] using hNreal
      · simpa [T, hK] using hNupper
    have hden : 0 < (N : ℝ) := by exact_mod_cast hN
    have hbase := hloc N hN
    have hfail : failureProbability N hN ≤ eps / 4 := by
      rw [failureProbability]
      have hNeps : 2 / eps ≤ (N : ℝ) := by
        calc
          2 / eps ≤ q := hqeps
          _ ≤ T := by
            dsimp [T]
            rw [hK]
            have hscale : 2 * q ≤ L * q :=
              mul_le_mul_of_nonneg_right hL (le_trans zero_le_one hq)
            nlinarith
          _ ≤ N := hNreal
      have hsq : (2 / eps) ^ 2 ≤ (N : ℝ) ^ 2 :=
        (sq_le_sq₀ (div_nonneg (by norm_num) heps.le)
          (Nat.cast_nonneg N)).2 hNeps
      have hinv : ((N : ℝ) ^ 2)⁻¹ ≤ (eps / 2) ^ 2 := by
        calc
          ((N : ℝ) ^ 2)⁻¹ ≤ ((2 / eps) ^ 2)⁻¹ :=
            inv_anti₀ (sq_pos_of_pos (div_pos (by norm_num) heps)) hsq
          _ = (eps / 2) ^ 2 := by field_simp [ne_of_gt heps]
      exact hinv.trans (by nlinarith [heps_one])
    have hinside : 0 ≤ d * D * localizationComplexity d N / N := by
      have hloc0 : 0 ≤ localizationComplexity d N := by
        unfold localizationComplexity
        have hncast : (1 : ℝ) ≤ N := by exact_mod_cast hN
        have hexp : 1 ≤ Real.exp 1 * (N : ℝ) := by
          have he : 1 ≤ Real.exp 1 := by
            rw [← Real.exp_zero]
            exact Real.exp_le_exp.mpr (by norm_num)
          nlinarith [mul_le_mul he hncast (by norm_num : (0 : ℝ) ≤ 1)
            (Real.exp_pos 1).le]
        have hlog1 : 0 ≤ Real.log (Real.exp 1 * (N : ℝ)) :=
          Real.log_nonneg hexp
        have hlog2 : 0 ≤ Real.log (2 * (N : ℝ) ^ 2) := by
          apply Real.log_nonneg
          nlinarith [sq_nonneg ((N : ℝ) - 1)]
        exact add_nonneg (mul_nonneg (Nat.cast_nonneg d) hlog1) hlog2
      positivity
    rcases le_total qFast qSlow with hbranch | hbranch
    · have hqbranch : min qFast qSlow = qFast := min_eq_left hbranch
      have hgood :
          Kloc * localizedRate E.eta D d N ≤ eps / 2 := by
        unfold localizedRate
        refine (mul_le_mul_of_nonneg_left (min_le_left _ _) hKloc.le).trans ?_
        change
          Kloc * (E.eta * (d : ℝ) * D *
            localizationComplexity d N / (N : ℝ)) ≤ eps / 2
        rw [show
          Kloc * (E.eta * (d : ℝ) * D *
              localizationComplexity d N / (N : ℝ)) =
            (Kloc * (E.eta * (d : ℝ) * D *
              localizationComplexity d N)) / N by ring]
        apply (div_le_iff₀ hden).2
        calc
          Kloc * (E.eta * (d : ℝ) * D * localizationComplexity d N) ≤
              Kloc * (E.eta * (d : ℝ) * D *
                (20 * (d + 2 : ℝ) * L)) := by
            have hcoef :
                0 ≤ Kloc * (E.eta * (d : ℝ) * D) := by
              exact mul_nonneg hKloc.le
                (mul_nonneg
                  (mul_nonneg E.eta_pos.le (Nat.cast_nonneg d))
                  (le_trans zero_le_one hD))
            convert mul_le_mul_of_nonneg_left hlocN hcoef using 1 <;> ring
          _ ≤ eps / 2 * T := by
            dsimp [T]
            rw [hK, hqeq, hqbranch]
            dsimp [qFast]
            field_simp [ne_of_gt heps]
            have hd : (4 : ℝ) ≤ d := by exact_mod_cast E.dim_ge_four
            have hshape :
                Kloc * ((d : ℝ) * ((d : ℝ) + 2)) ≤
                  2 * (d : ℝ) ^ 2 := by
              have hkd : Kloc * (d : ℝ) ≤ (d : ℝ) := by
                nlinarith [mul_nonneg
                  (show (0 : ℝ) ≤ d by positivity)
                  (show (0 : ℝ) ≤ 1 - Kloc by linarith)]
              have hdshape :
                  (d : ℝ) * ((d : ℝ) + 2) ≤ 2 * (d : ℝ) ^ 2 := by
                nlinarith [mul_nonneg
                  (show (0 : ℝ) ≤ d by positivity)
                  (show (0 : ℝ) ≤ (d : ℝ) - 2 by linarith)]
              calc
                Kloc * ((d : ℝ) * ((d : ℝ) + 2)) =
                    (Kloc * (d : ℝ)) * ((d : ℝ) + 2) := by ring
                _ ≤ (d : ℝ) * ((d : ℝ) + 2) :=
                  mul_le_mul_of_nonneg_right hkd (by positivity)
                _ ≤ _ := hdshape
            have hetaShape := mul_le_mul_of_nonneg_left hshape E.eta_pos.le
            have hleft :
                Kloc * E.eta * (d : ℝ) * 20 * 2 * ((d : ℝ) + 2) ≤
                  80 * (E.eta * (d : ℝ) ^ 2) := by
              have ht := mul_le_mul_of_nonneg_left hetaShape
                (by norm_num : (0 : ℝ) ≤ 40)
              convert ht using 1 <;> ring
            have hhuge :
                80 * (E.eta * (d : ℝ) ^ 2) ≤
                  (10 : ℝ) ^ 8 * (E.eta * (d : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_right (by norm_num)
                (mul_nonneg E.eta_pos.le (sq_nonneg _))
            nlinarith
          _ ≤ eps / 2 * N :=
            mul_le_mul_of_nonneg_left hNreal
              (div_nonneg heps.le (by norm_num))
      apply sampleComplexity_le_of_learnerRisk_le E P0 C D eps
        heps heps_one hshell
        (predictionPolytopeLearner E 64 (by norm_num) (n := N)).deployed
        hN hbase.1
      intro P hP
      exact (hbase.2.1 P hP).trans (by linarith)
    · have hqbranch : min qFast qSlow = qSlow := min_eq_right hbranch
      have hgood :
          Kloc * localizedRate E.eta D d N ≤ eps / 2 := by
        unfold localizedRate
        refine (mul_le_mul_of_nonneg_left (min_le_right _ _) hKloc.le).trans ?_
        have hsquare :
            (Kloc * Real.sqrt (d * D * localizationComplexity d N / N)) ^ 2 ≤
              (eps / 2) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hinside]
          rw [show
            Kloc ^ 2 * ((d : ℝ) * D * localizationComplexity d N / (N : ℝ)) =
              (Kloc ^ 2 * ((d : ℝ) * D * localizationComplexity d N)) / N by
                ring]
          apply (div_le_iff₀ hden).2
          calc
            Kloc ^ 2 * ((d : ℝ) * D * localizationComplexity d N) ≤
                Kloc ^ 2 * ((d : ℝ) * D *
                  (20 * (d + 2 : ℝ) * L)) := by gcongr
            _ ≤ (eps / 2) ^ 2 * T := by
              dsimp [T]
              rw [hK, hqeq, hqbranch]
              dsimp [qSlow]
              field_simp [ne_of_gt heps]
              have hd : (4 : ℝ) ≤ d := by exact_mod_cast E.dim_ge_four
              have hKsq : Kloc ^ 2 ≤ 1 := by
                nlinarith [sq_nonneg Kloc]
              have hshape :
                  (d : ℝ) * ((d : ℝ) + 2) ≤ 2 * (d : ℝ) ^ 2 := by
                nlinarith [mul_nonneg
                  (show (0 : ℝ) ≤ d by positivity)
                  (show (0 : ℝ) ≤ (d : ℝ) - 2 by linarith)]
              have hscaled :
                  Kloc ^ 2 * ((d : ℝ) * ((d : ℝ) + 2)) ≤
                    2 * (d : ℝ) ^ 2 := by
                calc
                  _ ≤ 1 * ((d : ℝ) * ((d : ℝ) + 2)) :=
                    mul_le_mul_of_nonneg_right hKsq (by positivity)
                  _ ≤ _ := by simpa using hshape
              nlinarith [mul_nonneg (le_trans zero_le_one hD)
                (le_trans zero_le_two hL)]
            _ ≤ (eps / 2) ^ 2 * N :=
              mul_le_mul_of_nonneg_left hNreal (sq_nonneg _)
        have hy :
            0 ≤ Kloc * Real.sqrt (d * D * localizationComplexity d N / N) := by
          exact mul_nonneg hKloc.le (Real.sqrt_nonneg _)
        change
          Kloc * Real.sqrt ((d : ℝ) * D *
            localizationComplexity d N / (N : ℝ)) ≤ eps / 2
        nlinarith [heps]
      apply sampleComplexity_le_of_learnerRisk_le E P0 C D eps
        heps heps_one hshell
        (predictionPolytopeLearner E 64 (by norm_num) (n := N)).deployed
        hN hbase.1
      intro P hP
      exact (hbase.2.1 P hP).trans (by linarith)

end CausalSmith.Stat.ReverseKLTwoCoverage
