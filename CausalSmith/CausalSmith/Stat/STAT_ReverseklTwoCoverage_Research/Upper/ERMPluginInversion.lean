import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Upper.ERMPluginCore
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Localization.BoundedLinearLocalization.LinearExactShell
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Localization.BoundedLinearLocalization.Adapters

/-!
# Sample-size inversion for the ERM Gibbs plug-in bound

This module converts the finite-sample two-branch learner-risk inequality into
the explicit plug-in sample-complexity bound.
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

lemma log_two_mul_ten_pow_eight_le_thirty :
    Real.log (2 * (10 : ℝ) ^ 8) ≤ 30 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  calc
    2 * (10 : ℝ) ^ 8 ≤ 2 ^ 30 := by norm_num
    _ ≤ (Real.exp 1) ^ 30 :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le _
    _ = Real.exp 30 := by
      rw [← Real.exp_nat_mul]
      norm_num

lemma localizationComplexity_le_of_pluginLog
    (d N : ℕ) (eta eps q : ℝ)
    (hd : 4 ≤ d) (heta : 0 < eta) (heps : 0 < eps)
    (hq : 1 ≤ q)
    (hNlower :
      (10 : ℝ) ^ 8 * q * pluginLogFactor eta eps q ≤ N)
    (hNupper :
      (N : ℝ) ≤ 2 * ((10 : ℝ) ^ 8 * q * pluginLogFactor eta eps q)) :
    localizationComplexity d N ≤
      20 * (d + 2 : ℝ) * pluginLogFactor eta eps q := by
  let L := pluginLogFactor eta eps q
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hthird :
      0 ≤ Real.log (1 + (1 + eta) * q / eps) := by
    apply Real.log_nonneg
    have : 0 ≤ (1 + eta) * q / eps := by positivity
    linarith
  have hL : 2 ≤ L := by
    dsimp [L, pluginLogFactor]
    rw [Real.log_mul (Real.exp_ne_zero 1) hqpos.ne', Real.log_exp]
    linarith
  have hNpos : 0 < (N : ℝ) := by
    have htpos : 0 < (10 : ℝ) ^ 8 * q * L := by positivity
    exact lt_of_lt_of_le htpos hNlower
  have hlogN : Real.log N ≤ 17 * L := by
    calc
      Real.log N ≤
          Real.log (2 * ((10 : ℝ) ^ 8 * q * L)) :=
        Real.strictMonoOn_log.monotoneOn hNpos
          (show 0 < 2 * ((10 : ℝ) ^ 8 * q * L) by
            exact mul_pos (by norm_num)
              (mul_pos (mul_pos (by positivity) hqpos) (by linarith)))
          hNupper
      _ = Real.log (2 * (10 : ℝ) ^ 8) + Real.log q + Real.log L := by
        rw [show 2 * ((10 : ℝ) ^ 8 * q * L) =
          ((2 * (10 : ℝ) ^ 8) * q) * L by ring,
          Real.log_mul (mul_ne_zero (by norm_num) hqpos.ne') (by linarith),
          Real.log_mul (by norm_num : (2 * (10 : ℝ) ^ 8) ≠ 0) hqpos.ne']
      _ ≤ 30 + L + L := by
        gcongr
        · exact log_two_mul_ten_pow_eight_le_thirty
        · dsimp [L, pluginLogFactor]
          rw [Real.log_mul (Real.exp_ne_zero 1) hqpos.ne', Real.log_exp]
          linarith
        · exact (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
      _ ≤ 17 * L := by linarith
  have hrewrite :
      localizationComplexity d N =
        (d : ℝ) + ((d : ℝ) + 2) * Real.log N + Real.log 2 := by
    simp only [localizationComplexity]
    rw [Real.log_mul (Real.exp_ne_zero 1) (Nat.cast_ne_zero.mpr
        (Nat.ne_of_gt (by exact_mod_cast hNpos))),
      Real.log_exp,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (pow_ne_zero 2 (Nat.cast_ne_zero.mpr
          (Nat.ne_of_gt (by exact_mod_cast hNpos)))),
      Real.log_pow]
    ring
  rw [hrewrite]
  have hlog2 : Real.log 2 ≤ L := by
    calc
      Real.log (2 : ℝ) ≤ 1 :=
        by
          have h := Real.log_le_sub_one_of_pos
            (show (0 : ℝ) < 2 by norm_num)
          norm_num at h ⊢
          exact h
      _ ≤ L := le_trans (by norm_num) hL
  have hdL : (d : ℝ) ≤ (d : ℝ) * L := by
    have hd0 : 0 ≤ (d : ℝ) := by positivity
    nlinarith
  calc
    (d : ℝ) + ((d : ℝ) + 2) * Real.log N + Real.log 2 ≤
        (d : ℝ) * L + ((d : ℝ) + 2) * (17 * L) + L := by
      gcongr
    _ ≤ 20 * (d + 2 : ℝ) * L := by
      have hd0 : 0 ≤ (d : ℝ) := by positivity
      nlinarith

lemma plugin_sampleComplexity_bound
    (E : CommonExperiment d 𝒳 𝒜) (P0 : BanditLaw E) (C D eps : ℝ)
    (hshell : ExactShell E P0 C D)
    (heps : 0 < eps) (heps_one : eps < 1)
    (hrisk :
      ∀ n, ∀ hn : 0 < n,
        IsMeasurableLearner E (ermGibbsPluginLearner (n := n) E) ∧
        ∀ P ∈ exactShellSet E C D,
          learnerRisk E P n (ermGibbsPluginLearner (n := n) E) ≤
            min
              (600 * kappa E.eta * D * localizationComplexity d n / n)
              (Real.sqrt 600 * (1 + Real.exp (2 * E.eta)) *
                Real.sqrt (D * localizationComplexity d n / n)) +
            failureProbability n hn / 2 * min 2 (E.eta / 2)) :
    let q := (d : ℝ) * D *
      min (kappa E.eta / eps)
        ((1 + Real.exp (2 * E.eta)) ^ 2 / eps ^ 2)
    2 ≤ (10 : ℝ) ^ 8 * q * pluginLogFactor E.eta eps q →
      sampleComplexity E eps C D heps heps_one ≤
        (↑⌈(10 : ℝ) ^ 8 * q * pluginLogFactor E.eta eps q⌉₊ :
          WithTop ℕ) := by
  dsimp only
  let qFast := (d : ℝ) * D * (kappa E.eta / eps)
  let qSlow := (d : ℝ) * D *
    ((1 + Real.exp (2 * E.eta)) ^ 2 / eps ^ 2)
  let q := (d : ℝ) * D *
    min (kappa E.eta / eps)
      ((1 + Real.exp (2 * E.eta)) ^ 2 / eps ^ 2)
  let L := pluginLogFactor E.eta eps q
  let T := (10 : ℝ) ^ 8 * q * L
  let N : ℕ := ⌈T⌉₊
  intro hT
  have hNreal : T ≤ (N : ℝ) := Nat.le_ceil _
  have hN : 0 < N := by
    have hNr : (0 : ℝ) < (N : ℝ) := by
      exact lt_of_lt_of_le (by linarith [hT]) hNreal
    exact_mod_cast hNr
  have hNone : (1 : WithTop ℕ) ≤ (N : WithTop ℕ) := by
    exact_mod_cast hN
  by_cases hsmall : 2 * E.eta ≤ eps
  · calc
      sampleComplexity E eps C D heps heps_one ≤ (1 : WithTop ℕ) := by
        apply sampleComplexity_le_of_learnerRisk_le E P0 C D eps
          heps heps_one hshell (ermGibbsPluginLearner (n := 1) E)
          (by norm_num) (ermGibbsPluginLearner_measurable (n := 1) E)
        intro P hP
        exact (ermPluginLearnerRisk_le_two_eta E P C D hP 1).trans hsmall
      _ ≤ N := hNone
  · have heta_eps : eps < 2 * E.eta := lt_of_not_ge hsmall
    have hD : 1 ≤ D := (feasible_index_region (E := E)).1 P0 C D hshell |>.1
    have hkappa : E.eta / 2 ≤ kappa E.eta :=
      kappa_half_le E.eta E.eta_pos
    have hqFast : 1 ≤ qFast := by
      dsimp [qFast]
      have hd : (4 : ℝ) ≤ d := by exact_mod_cast E.dim_ge_four
      have hratio : 1 / 4 < kappa E.eta / eps := by
        apply (lt_div_iff₀ heps).2
        nlinarith
      have hdD : (4 : ℝ) ≤ (d : ℝ) * D := by
        calc
          (4 : ℝ) = 4 * 1 := by ring
          _ ≤ (d : ℝ) * D := mul_le_mul hd hD
            (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
      have hfour :
          (4 : ℝ) * (1 / 4) < 4 * (kappa E.eta / eps) :=
        mul_lt_mul_of_pos_left hratio (by norm_num)
      have hprod :
          4 * (kappa E.eta / eps) ≤
            ((d : ℝ) * D) * (kappa E.eta / eps) :=
        mul_le_mul_of_nonneg_right hdD
          (le_trans (by norm_num) hratio.le)
      nlinarith
    have hqSlow : 1 ≤ qSlow := by
      dsimp [qSlow]
      have hd : (4 : ℝ) ≤ d := by exact_mod_cast E.dim_ge_four
      have hexp : 1 ≤ Real.exp (2 * E.eta) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (mul_nonneg (by norm_num) E.eta_pos.le)
      have hepssq : eps ^ 2 < 1 := by nlinarith [sq_pos_of_pos heps]
      have hratio :
          4 < (1 + Real.exp (2 * E.eta)) ^ 2 / eps ^ 2 := by
        apply (lt_div_iff₀ (sq_pos_of_pos heps)).2
        nlinarith [sq_nonneg (Real.exp (2 * E.eta) - 1)]
      have hdD : (4 : ℝ) ≤ (d : ℝ) * D := by
        calc
          (4 : ℝ) = 4 * 1 := by ring
          _ ≤ (d : ℝ) * D := mul_le_mul hd hD
            (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
      have hprod :
          4 * ((1 + Real.exp (2 * E.eta)) ^ 2 / eps ^ 2) ≤
            ((d : ℝ) * D) *
              ((1 + Real.exp (2 * E.eta)) ^ 2 / eps ^ 2) :=
        mul_le_mul_of_nonneg_right hdD (by positivity)
      nlinarith
    have hdDnonneg : 0 ≤ (d : ℝ) * D :=
      mul_nonneg (by positivity) (le_trans zero_le_one hD)
    have hqeq : q = min qFast qSlow := by
      dsimp only [q, qFast, qSlow]
      exact (mul_min_of_nonneg
        (kappa E.eta / eps)
        ((1 + Real.exp (2 * E.eta)) ^ 2 / eps ^ 2)
        hdDnonneg)
    have hq : 1 ≤ q := by rw [hqeq]; exact le_min hqFast hqSlow
    have hL : 2 ≤ L := by
      dsimp [L, pluginLogFactor]
      have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq
      have hthird :
          0 ≤ Real.log (1 + (1 + E.eta) * q / eps) := by
        apply Real.log_nonneg
        have : 0 ≤ (1 + E.eta) * q / eps := by
          exact div_nonneg
            (mul_nonneg (by linarith [E.eta_pos]) (le_trans zero_le_one hq))
            heps.le
        linarith
      rw [Real.log_mul (Real.exp_ne_zero 1)
        (ne_of_gt (lt_of_lt_of_le zero_lt_one hq)), Real.log_exp]
      linarith
    have hTpos : 0 < T := by
      dsimp [T]
      exact mul_pos (mul_pos (by positivity) (lt_of_lt_of_le zero_lt_one hq))
        (lt_of_lt_of_le zero_lt_two hL)
    have hNupper : (N : ℝ) ≤ 2 * T := by
      have hceil := Nat.ceil_lt_add_one (le_of_lt hTpos)
      calc
        (N : ℝ) ≤ T + 1 := hceil.le
        _ ≤ 2 * T := by nlinarith [hT]
    have hloc :
        localizationComplexity d N ≤ 20 * (d + 2 : ℝ) * L := by
      apply localizationComplexity_le_of_pluginLog d N E.eta eps q
        E.dim_ge_four E.eta_pos heps hq
      · simpa [T] using hNreal
      · simpa [T] using hNupper
    have hlocnonneg : 0 ≤ localizationComplexity d N := by
      unfold localizationComplexity
      have hlog1 : 0 ≤ Real.log (Real.exp 1 * N) := by
        apply Real.log_nonneg
        have he : 1 ≤ Real.exp 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by norm_num)
        have hncast : (1 : ℝ) ≤ N := by exact_mod_cast hN
        nlinarith [mul_le_mul he hncast (by norm_num : (0 : ℝ) ≤ 1)
          (Real.exp_pos 1).le]
      have hlog2 : 0 ≤ Real.log (2 * (N : ℝ) ^ 2) := by
        apply Real.log_nonneg
        have hncast : (1 : ℝ) ≤ N := by exact_mod_cast hN
        nlinarith [sq_nonneg ((N : ℝ) - 1)]
      positivity
    have hden : 0 < (N : ℝ) := by exact_mod_cast hN
    have hbase := hrisk N hN
    rcases le_total qFast qSlow with hbranch | hbranch
    · have hqbranch : min qFast qSlow = qFast := min_eq_left hbranch
      have hgood :
          600 * kappa E.eta * D * localizationComplexity d N / N ≤
            eps / 4 := by
        apply (div_le_iff₀ hden).2
        have hcoef : 0 ≤ 600 * kappa E.eta * D := by
          have hk0 : 0 ≤ kappa E.eta := le_trans
            (div_nonneg E.eta_pos.le (by norm_num)) hkappa
          positivity
        calc
          600 * kappa E.eta * D * localizationComplexity d N ≤
              600 * kappa E.eta * D *
                (20 * (d + 2 : ℝ) * L) :=
            mul_le_mul_of_nonneg_left hloc hcoef
          _ ≤ eps / 4 * T := by
            dsimp [T]
            rw [hqeq, hqbranch]
            dsimp [qFast]
            have hd : (4 : ℝ) ≤ d := by exact_mod_cast E.dim_ge_four
            have hL0 : 0 ≤ L := le_trans zero_le_two hL
            field_simp [ne_of_gt heps]
            nlinarith [mul_nonneg (mul_nonneg
              (le_trans (div_nonneg E.eta_pos.le (by norm_num)) hkappa)
              (le_trans zero_le_one hD)) hL0]
          _ ≤ eps / 4 * N :=
            mul_le_mul_of_nonneg_left hNreal
              (div_nonneg heps.le (by norm_num))
      have hfail :
          failureProbability N hN / 2 * min 2 (E.eta / 2) ≤ eps / 4 := by
        rw [failureProbability]
        have hcap : min 2 (E.eta / 2) ≤ kappa E.eta :=
          (min_le_right _ _).trans hkappa
        have hNkap : 4 * kappa E.eta / eps ≤ (N : ℝ) := by
          calc
            4 * kappa E.eta / eps ≤ qFast := by
              dsimp [qFast]
              have hdD : (4 : ℝ) ≤ (d : ℝ) * D := by
                calc
                  (4 : ℝ) = 4 * 1 := by ring
                  _ ≤ (d : ℝ) * D := mul_le_mul
                    (by exact_mod_cast E.dim_ge_four) hD
                    (by norm_num) (by positivity)
              have hr : 0 ≤ kappa E.eta / eps :=
                div_nonneg (le_trans
                  (div_nonneg E.eta_pos.le (by norm_num)) hkappa) heps.le
              convert mul_le_mul_of_nonneg_right hdD hr using 1 <;> ring
            _ ≤ T := by
              dsimp [T]
              rw [hqeq, hqbranch]
              nlinarith [hqFast, hL]
            _ ≤ N := hNreal
        have hNtwo : (2 : ℝ) ≤ N := by
          exact le_trans hT hNreal
        have hsq : 0 < (N : ℝ) ^ 2 := sq_pos_of_pos hden
        rw [div_eq_mul_inv]
        apply (le_trans (mul_le_mul_of_nonneg_left hcap
          (mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (by positivity))))
        calc
          ((N : ℝ) ^ 2)⁻¹ * 2⁻¹ * kappa E.eta ≤
              eps / (8 * N) := by
            have hk : 4 * kappa E.eta ≤ eps * (N : ℝ) :=
              by simpa [mul_comm] using (div_le_iff₀ heps).mp hNkap
            field_simp [ne_of_gt hden]
            nlinarith
          _ ≤ eps / 4 := by
            field_simp
            nlinarith
      apply sampleComplexity_le_of_learnerRisk_le E P0 C D eps
        heps heps_one hshell (ermGibbsPluginLearner (n := N) E)
        hN hbase.1
      intro P hP
      calc
        learnerRisk E P N (ermGibbsPluginLearner (n := N) E) ≤
            min
                (600 * kappa E.eta * D * localizationComplexity d N / N)
                (Real.sqrt 600 * (1 + Real.exp (2 * E.eta)) *
                  Real.sqrt (D * localizationComplexity d N / N)) +
              failureProbability N hN / 2 * min 2 (E.eta / 2) :=
          hbase.2 P hP
        _ ≤ eps / 4 + eps / 4 := add_le_add
          ((min_le_left _ _).trans hgood) hfail
        _ ≤ eps := by linarith
    · have hqbranch : min qFast qSlow = qSlow := min_eq_right hbranch
      let A := 1 + Real.exp (2 * E.eta)
      let X := D * localizationComplexity d N / N
      have hA : 0 < A := by dsimp [A]; positivity
      have hX : 0 ≤ X := by
        dsimp [X]
        positivity
      have hslowSq :
          (Real.sqrt 600 * A * Real.sqrt X) ^ 2 ≤ (eps / 2) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num),
          Real.sq_sqrt hX]
        dsimp [X]
        rw [show
          600 * A ^ 2 * (D * localizationComplexity d N / (N : ℝ)) =
            (600 * A ^ 2 * (D * localizationComplexity d N)) / N by ring]
        apply (div_le_iff₀ hden).2
        calc
          600 * A ^ 2 * (D * localizationComplexity d N) ≤
              600 * A ^ 2 * (D * (20 * (d + 2 : ℝ) * L)) := by
            gcongr
          _ ≤ (eps / 2) ^ 2 * T := by
            dsimp [T]
            rw [hqeq, hqbranch]
            dsimp [qSlow, A]
            have hd : (4 : ℝ) ≤ d := by exact_mod_cast E.dim_ge_four
            have hL0 : 0 ≤ L := le_trans zero_le_two hL
            field_simp [ne_of_gt heps]
            nlinarith [mul_nonneg
              (mul_nonneg (sq_nonneg (1 + Real.exp (2 * E.eta)))
                (le_trans zero_le_one hD)) hL0]
          _ ≤ (eps / 2) ^ 2 * N :=
            mul_le_mul_of_nonneg_left hNreal (sq_nonneg _)
      have hslow :
          Real.sqrt 600 * (1 + Real.exp (2 * E.eta)) *
              Real.sqrt (D * localizationComplexity d N / N) ≤ eps / 2 := by
        change Real.sqrt 600 * A * Real.sqrt X ≤ eps / 2
        have hy : 0 ≤ Real.sqrt 600 * A * Real.sqrt X := by positivity
        have he : 0 ≤ eps / 2 := by positivity
        nlinarith
      have hfail :
          failureProbability N hN / 2 * min 2 (E.eta / 2) ≤ eps / 4 := by
        rw [failureProbability]
        have hcap : min 2 (E.eta / 2) ≤ 2 := min_le_left _ _
        have hNeps : 2 / eps ≤ (N : ℝ) := by
          calc
            2 / eps ≤ qSlow := by
              dsimp [qSlow]
              have hdD : (4 : ℝ) ≤ (d : ℝ) * D := by
                calc
                  (4 : ℝ) = 4 * 1 := by ring
                  _ ≤ (d : ℝ) * D := mul_le_mul
                    (by exact_mod_cast E.dim_ge_four) hD
                    (by norm_num) (by positivity)
              have hexp : 1 ≤ Real.exp (2 * E.eta) := by
                rw [← Real.exp_zero]
                exact Real.exp_le_exp.mpr
                  (mul_nonneg (by norm_num) E.eta_pos.le)
              have hA2 : (4 : ℝ) ≤
                  (1 + Real.exp (2 * E.eta)) ^ 2 := by nlinarith
              have hnum : 2 * eps ≤
                  ((d : ℝ) * D) *
                    (1 + Real.exp (2 * E.eta)) ^ 2 := by
                have hp := mul_le_mul hdD hA2
                  (by norm_num : (0 : ℝ) ≤ 4) (by positivity)
                nlinarith
              apply (div_le_iff₀ heps).2
              rw [show
                ((d : ℝ) * D *
                    ((1 + Real.exp (2 * E.eta)) ^ 2 / eps ^ 2)) * eps =
                  ((d : ℝ) * D *
                    (1 + Real.exp (2 * E.eta)) ^ 2) / eps by
                  field_simp [ne_of_gt heps]
                  <;> ring]
              exact (le_div_iff₀ heps).2 hnum
            _ ≤ T := by
              dsimp [T]
              rw [hqeq, hqbranch]
              have hscale :
                  2 * qSlow ≤ L * qSlow :=
                mul_le_mul_of_nonneg_right hL (le_trans zero_le_one hqSlow)
              nlinarith
            _ ≤ N := hNreal
        have hsq : (2 / eps) ^ 2 ≤ (N : ℝ) ^ 2 :=
          (sq_le_sq₀ (div_nonneg (by norm_num) heps.le)
            (Nat.cast_nonneg N)).2 hNeps
        have hinv :
            ((N : ℝ) ^ 2)⁻¹ ≤ (eps / 2) ^ 2 := by
          calc
            ((N : ℝ) ^ 2)⁻¹ ≤ ((2 / eps) ^ 2)⁻¹ :=
              inv_anti₀ (sq_pos_of_pos (div_pos (by norm_num) heps)) hsq
            _ = (eps / 2) ^ 2 := by
              field_simp [ne_of_gt heps]
        calc
          ((N : ℝ) ^ 2)⁻¹ / 2 * min 2 (E.eta / 2) ≤
              ((N : ℝ) ^ 2)⁻¹ / 2 * 2 := by gcongr
          _ = ((N : ℝ) ^ 2)⁻¹ := by ring
          _ ≤ (eps / 2) ^ 2 := hinv
          _ ≤ eps / 4 := by nlinarith [heps_one]
      apply sampleComplexity_le_of_learnerRisk_le E P0 C D eps
        heps heps_one hshell (ermGibbsPluginLearner (n := N) E)
        hN hbase.1
      intro P hP
      calc
        learnerRisk E P N (ermGibbsPluginLearner (n := N) E) ≤
            min
                (600 * kappa E.eta * D * localizationComplexity d N / N)
                (Real.sqrt 600 * (1 + Real.exp (2 * E.eta)) *
                  Real.sqrt (D * localizationComplexity d N / N)) +
              failureProbability N hN / 2 * min 2 (E.eta / 2) :=
          hbase.2 P hP
        _ ≤ eps / 2 + eps / 4 := add_le_add
          ((min_le_right _ _).trans hslow) hfail
        _ ≤ eps := by linarith

end CausalSmith.Stat.ReverseKLTwoCoverage
