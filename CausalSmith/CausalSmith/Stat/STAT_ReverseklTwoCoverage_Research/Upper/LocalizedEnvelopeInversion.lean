import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Upper.LocalizedEnvelopeRisk
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Upper.LocalizedDefs
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Feasibility.IndexRegion

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory ProbabilityTheory
open LinearExactShellTypeFit
open BoundedLinearLocalizationAdapters

variable {d n : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [LinearOrder 𝒳] [LinearOrder 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]

lemma localized_sampleComplexity_le_of_learnerRisk_le
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

lemma localized_log_constant :
    Real.log (2 * (10 : ℝ) ^ 8) ≤ 30 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  calc
    2 * (10 : ℝ) ^ 8 ≤ 2 ^ 30 := by norm_num
    _ ≤ (Real.exp 1) ^ 30 :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le _
    _ = Real.exp 30 := by
      rw [← Real.exp_nat_mul]
      norm_num

lemma localizedComplexity_le_of_logFactor
    (d N : ℕ) (eta eps q : ℝ)
    (hd : 4 ≤ d) (heta : 0 < eta) (heps : 0 < eps)
    (hq : 1 ≤ q)
    (hNlower :
      (10 : ℝ) ^ 8 * q * localizedLogFactor eta eps q ≤ N)
    (hNupper :
      (N : ℝ) ≤
        2 * ((10 : ℝ) ^ 8 * q * localizedLogFactor eta eps q)) :
    (d : ℝ) * Real.log (Real.exp 1 * N) +
        Real.log (2 * (N : ℝ) ^ 2) ≤
      20 * (d + 2 : ℝ) * localizedLogFactor eta eps q := by
  let L := localizedLogFactor eta eps q
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hthird :
      0 ≤ Real.log (1 + (1 + eta) * q / eps) := by
    apply Real.log_nonneg
    have : 0 ≤ (1 + eta) * q / eps := by positivity
    linarith
  have hL : 2 ≤ L := by
    dsimp [L, localizedLogFactor]
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
          (show 0 < 2 * ((10 : ℝ) ^ 8 * q * L) by positivity)
          hNupper
      _ = Real.log (2 * (10 : ℝ) ^ 8) + Real.log q + Real.log L := by
        rw [show 2 * ((10 : ℝ) ^ 8 * q * L) =
          ((2 * (10 : ℝ) ^ 8) * q) * L by ring,
          Real.log_mul (mul_ne_zero (by norm_num) hqpos.ne') (by linarith),
          Real.log_mul (by norm_num : (2 * (10 : ℝ) ^ 8) ≠ 0) hqpos.ne']
      _ ≤ 30 + L + L := by
        gcongr
        · exact localized_log_constant
        · dsimp [L, localizedLogFactor]
          rw [Real.log_mul (Real.exp_ne_zero 1) hqpos.ne', Real.log_exp]
          linarith
        · exact (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
      _ ≤ 17 * L := by linarith
  have hrewrite :
      (d : ℝ) * Real.log (Real.exp 1 * N) +
          Real.log (2 * (N : ℝ) ^ 2) =
        (d : ℝ) + ((d : ℝ) + 2) * Real.log N + Real.log 2 := by
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
      Real.log (2 : ℝ) ≤ 1 := by
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

lemma lowerEnvelopeRisk_le_localizedRate
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (C D : ℝ)
    (hshell : ExactShell E P C D)
    (hZhao : ZhaoUniformSquareComparison (𝒳 := 𝒳) (𝒜 := 𝒜))
    (hn : 0 < n) :
    learnerRisk E P n
        (predictionPolytopeLearner E 64 (by norm_num) (n := n)).deployed ≤
      600 * localizedRate E.eta D d n + failureProbability n hn := by
  refine (lowerEnvelopeLearnerRisk_le E P C D hshell hZhao hn).trans ?_
  unfold localizedRate
  have hfast :
      300 * E.eta * (d : ℝ) * D *
          (((d : ℝ) * Real.log (Real.exp 1 * n) +
            Real.log (2 * (n : ℝ) ^ 2)) / n) ≤
        600 * (E.eta * (d : ℝ) * D *
          ((d : ℝ) * Real.log (Real.exp 1 * n) +
            Real.log (2 * (n : ℝ) ^ 2)) / n) := by
    have hnonneg :
        0 ≤ E.eta * (d : ℝ) * D *
          ((d : ℝ) * Real.log (Real.exp 1 * n) +
            Real.log (2 * (n : ℝ) ^ 2)) / n := by
      have hD := hshell.featureExactShell.1.le
      have ha : 0 ≤ (d : ℝ) * Real.log (Real.exp 1 * n) +
          Real.log (2 * (n : ℝ) ^ 2) := by
        have hlog1 : 0 ≤ Real.log (Real.exp 1 * (n : ℝ)) := by
          apply Real.log_nonneg
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          have he : 1 ≤ Real.exp 1 := by
            rw [← Real.exp_zero]
            exact Real.exp_le_exp.mpr (by norm_num)
          nlinarith [mul_le_mul he hn1 (by norm_num : (0 : ℝ) ≤ 1)
            (Real.exp_pos 1).le]
        have hlog2 : 0 ≤ Real.log (2 * (n : ℝ) ^ 2) := by
          apply Real.log_nonneg
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          nlinarith [sq_nonneg ((n : ℝ) - 1)]
        positivity
      exact div_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg E.eta_pos.le (Nat.cast_nonneg d))
            hshell.featureExactShell.1.le)
          ha)
        (Nat.cast_nonneg n)
    convert (mul_le_mul_of_nonneg_right (by norm_num : (300 : ℝ) ≤ 600)
      hnonneg) using 1 <;> ring
  have hslow :
      Real.sqrt
          (600 * (d : ℝ) * D *
            (((d : ℝ) * Real.log (Real.exp 1 * n) +
              Real.log (2 * (n : ℝ) ^ 2)) / n)) ≤
        600 * Real.sqrt
          ((d : ℝ) * D *
            ((d : ℝ) * Real.log (Real.exp 1 * n) +
              Real.log (2 * (n : ℝ) ^ 2)) / n) := by
    rw [show 600 * (d : ℝ) * D *
        (((d : ℝ) * Real.log (Real.exp 1 * n) +
          Real.log (2 * (n : ℝ) ^ 2)) / n) =
      600 * ((d : ℝ) * D *
        ((d : ℝ) * Real.log (Real.exp 1 * n) +
          Real.log (2 * (n : ℝ) ^ 2)) / n) by ring,
      Real.sqrt_mul (by norm_num : 0 ≤ (600 : ℝ))]
    have hsqrt : Real.sqrt 600 ≤ 600 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 600 by norm_num),
        Real.sqrt_nonneg 600]
    exact mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)
  change
    min
        (300 * E.eta * (d : ℝ) * D *
          (((d : ℝ) * Real.log (Real.exp 1 * n) +
            Real.log (2 * (n : ℝ) ^ 2)) / n))
        (Real.sqrt
          (600 * (d : ℝ) * D *
            (((d : ℝ) * Real.log (Real.exp 1 * n) +
              Real.log (2 * (n : ℝ) ^ 2)) / n))) +
      failureProbability n hn ≤
    600 *
        min
          (E.eta * (d : ℝ) * D *
            ((d : ℝ) * Real.log (Real.exp 1 * n) +
              Real.log (2 * (n : ℝ) ^ 2)) / n)
          (Real.sqrt
            ((d : ℝ) * D *
              ((d : ℝ) * Real.log (Real.exp 1 * n) +
                Real.log (2 * (n : ℝ) ^ 2)) / n)) +
      failureProbability n hn
  gcongr
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 600)]
  exact min_le_min hfast hslow

lemma lowerEnvelope_sampleComplexity_bound
    (E : CommonExperiment d 𝒳 𝒜) (P0 : BanditLaw E) (C D eps : ℝ)
    (hshell : ExactShell E P0 C D)
    (hZhao : ZhaoUniformSquareComparison (𝒳 := 𝒳) (𝒜 := 𝒜))
    (heps : 0 < eps) (heps_one : eps < 1) :
    let q := (d : ℝ) ^ 2 * D *
      min (E.eta / eps) ((eps ^ 2)⁻¹)
    2 ≤ (10 : ℝ) ^ 8 * q * localizedLogFactor E.eta eps q →
      sampleComplexity E eps C D heps heps_one ≤
        (↑⌈(10 : ℝ) ^ 8 * q * localizedLogFactor E.eta eps q⌉₊ :
          WithTop ℕ) := by
  dsimp only
  let qFast := (d : ℝ) ^ 2 * D * (E.eta / eps)
  let qSlow := (d : ℝ) ^ 2 * D * (eps ^ 2)⁻¹
  let q := (d : ℝ) ^ 2 * D *
    min (E.eta / eps) ((eps ^ 2)⁻¹)
  let L := localizedLogFactor E.eta eps q
  let T := (10 : ℝ) ^ 8 * q * L
  let N : ℕ := ⌈T⌉₊
  intro hT
  have hNreal : T ≤ (N : ℝ) := Nat.le_ceil _
  have hN : 0 < N := by
    have hNr : (0 : ℝ) < (N : ℝ) :=
      lt_of_lt_of_le (by linarith [hT]) hNreal
    exact_mod_cast hNr
  have hNone : (1 : WithTop ℕ) ≤ (N : WithTop ℕ) := by
    exact_mod_cast hN
  by_cases hsmall : E.eta ≤ 2 * eps
  · calc
      sampleComplexity E eps C D heps heps_one ≤ (1 : WithTop ℕ) := by
        apply localized_sampleComplexity_le_of_learnerRisk_le
          E P0 C D eps heps heps_one hshell
          (predictionPolytopeLearner E 64 (by norm_num) (n := 1)).deployed
          (by norm_num)
          (predictionPolytopeLearner_measurable (n := 1) E 64 (by norm_num))
        intro P hP
        exact (lowerEnvelopeLearnerRisk_le_eta_half E P C D hP
          (by norm_num)).trans (by linarith)
      _ ≤ N := hNone
  · have heta_eps : 2 * eps < E.eta := lt_of_not_ge hsmall
    have hD : 1 ≤ D :=
      (feasible_index_region (E := E)).1 P0 C D hshell |>.1
    have hd : (4 : ℝ) ≤ d := by exact_mod_cast E.dim_ge_four
    have hd2D : (16 : ℝ) ≤ (d : ℝ) ^ 2 * D := by
      have hd2 : (16 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
      calc
        (16 : ℝ) = 16 * 1 := by ring
        _ ≤ (d : ℝ) ^ 2 * D :=
          mul_le_mul hd2 hD (by norm_num) (sq_nonneg _)
    have hqFast : 1 ≤ qFast := by
      dsimp [qFast]
      have hratio : 2 < E.eta / eps := (lt_div_iff₀ heps).2 heta_eps
      have hprod := mul_le_mul_of_nonneg_right hd2D
        (by linarith : 0 ≤ E.eta / eps)
      nlinarith
    have hqSlow : 1 ≤ qSlow := by
      dsimp [qSlow]
      have hepssq : eps ^ 2 < 1 := by nlinarith [sq_pos_of_pos heps]
      have hinv : 1 < (eps ^ 2)⁻¹ := by
        rw [one_lt_inv₀ (sq_pos_of_pos heps)]
        exact hepssq
      have hprod := mul_le_mul_of_nonneg_right hd2D
        (by linarith : 0 ≤ (eps ^ 2)⁻¹)
      nlinarith
    have hd2Dnonneg : 0 ≤ (d : ℝ) ^ 2 * D :=
      mul_nonneg (sq_nonneg _) (le_trans zero_le_one hD)
    have hqeq : q = min qFast qSlow := by
      dsimp only [q, qFast, qSlow]
      exact mul_min_of_nonneg (E.eta / eps) ((eps ^ 2)⁻¹) hd2Dnonneg
    have hq : 1 ≤ q := by
      rw [hqeq]
      exact le_min hqFast hqSlow
    have hL : 2 ≤ L := by
      dsimp [L, localizedLogFactor]
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
      positivity
    have hNupper : (N : ℝ) ≤ 2 * T := by
      have hceil := Nat.ceil_lt_add_one (le_of_lt hTpos)
      calc
        (N : ℝ) ≤ T + 1 := hceil.le
        _ ≤ 2 * T := by nlinarith [hT]
    have hloc :
        (d : ℝ) * Real.log (Real.exp 1 * N) +
            Real.log (2 * (N : ℝ) ^ 2) ≤
          20 * (d + 2 : ℝ) * L := by
      apply localizedComplexity_le_of_logFactor d N E.eta eps q
        E.dim_ge_four E.eta_pos heps hq
      · simpa [T] using hNreal
      · simpa [T] using hNupper
    have haNnonneg :
        0 ≤ (d : ℝ) * Real.log (Real.exp 1 * N) +
          Real.log (2 * (N : ℝ) ^ 2) := by
      have hlog1 : 0 ≤ Real.log (Real.exp 1 * (N : ℝ)) := by
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
    rcases le_total qFast qSlow with hbranch | hbranch
    · have hqbranch : min qFast qSlow = qFast := min_eq_left hbranch
      have hgood :
          300 * E.eta * (d : ℝ) * D *
              (((d : ℝ) * Real.log (Real.exp 1 * N) +
                Real.log (2 * (N : ℝ) ^ 2)) / N) ≤ eps / 4 := by
        rw [show
          300 * E.eta * (d : ℝ) * D *
              (((d : ℝ) * Real.log (Real.exp 1 * N) +
                Real.log (2 * (N : ℝ) ^ 2)) / N) =
            (300 * E.eta * (d : ℝ) * D *
              ((d : ℝ) * Real.log (Real.exp 1 * N) +
                Real.log (2 * (N : ℝ) ^ 2))) / N by ring]
        apply (div_le_iff₀ hden).2
        calc
          _ ≤ 300 * E.eta * (d : ℝ) * D *
              (20 * (d + 2 : ℝ) * L) := by
            exact mul_le_mul_of_nonneg_left hloc
              (mul_nonneg
                (mul_nonneg
                  (mul_nonneg (by norm_num) E.eta_pos.le)
                  (Nat.cast_nonneg d))
                (le_trans zero_le_one hD))
          _ ≤ eps / 4 * T := by
            dsimp [T]
            rw [hqeq, hqbranch]
            dsimp [qFast]
            have hL0 : 0 ≤ L := le_trans zero_le_two hL
            field_simp [ne_of_gt heps]
            nlinarith [mul_nonneg
              (mul_nonneg E.eta_pos.le (le_trans zero_le_one hD)) hL0]
          _ ≤ eps / 4 * N :=
            mul_le_mul_of_nonneg_left hNreal
              (div_nonneg heps.le (by norm_num))
      have hfail :
          failureProbability N hN / 2 * min 2 (E.eta / 2) ≤ eps / 4 := by
        rw [failureProbability]
        have hcap : min 2 (E.eta / 2) ≤ E.eta / 2 := min_le_right _ _
        have hNeta : E.eta / eps ≤ (N : ℝ) := by
          calc
            E.eta / eps ≤ qFast := by
              dsimp [qFast]
              have hr : 0 ≤ E.eta / eps := div_nonneg E.eta_pos.le heps.le
              nlinarith [mul_le_mul_of_nonneg_right hd2D hr]
            _ ≤ T := by
              dsimp [T]
              rw [hqeq, hqbranch]
              nlinarith [hqFast, hL]
            _ ≤ N := hNreal
        have hNoneReal : (1 : ℝ) ≤ N := by exact_mod_cast hN
        have hetaN : E.eta ≤ eps * (N : ℝ) := by
          simpa [mul_comm] using (div_le_iff₀ heps).mp hNeta
        have hinvnonneg : 0 ≤ ((N : ℝ) ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
        calc
          ((N : ℝ) ^ 2)⁻¹ / 2 * min 2 (E.eta / 2) ≤
              ((N : ℝ) ^ 2)⁻¹ / 2 * (E.eta / 2) := by gcongr
          _ ≤ eps / 4 := by
            field_simp [ne_of_gt hden]
            nlinarith
      apply localized_sampleComplexity_le_of_learnerRisk_le
        E P0 C D eps heps heps_one hshell
        (predictionPolytopeLearner E 64 (by norm_num) (n := N)).deployed
        hN (predictionPolytopeLearner_measurable (n := N) E 64 (by norm_num))
      intro P hP
      calc
        learnerRisk E P N
            (predictionPolytopeLearner E 64 (by norm_num)
              (n := N)).deployed ≤
            min
              (300 * E.eta * (d : ℝ) * D *
                (((d : ℝ) * Real.log (Real.exp 1 * N) +
                  Real.log (2 * (N : ℝ) ^ 2)) / N))
              (Real.sqrt
                (600 * (d : ℝ) * D *
                  (((d : ℝ) * Real.log (Real.exp 1 * N) +
                    Real.log (2 * (N : ℝ) ^ 2)) / N))) +
              failureProbability N hN / 2 * min 2 (E.eta / 2) :=
          lowerEnvelopeLearnerRisk_le_sharp E P C D hP hZhao hN
        _ ≤ eps / 4 + eps / 4 :=
          add_le_add ((min_le_left _ _).trans hgood) hfail
        _ ≤ eps := by linarith
    · have hqbranch : min qFast qSlow = qSlow := min_eq_right hbranch
      let X := (d : ℝ) * D *
        (((d : ℝ) * Real.log (Real.exp 1 * N) +
          Real.log (2 * (N : ℝ) ^ 2)) / N)
      have hX : 0 ≤ X := by
        dsimp [X]
        positivity
      have hslowSq :
          (Real.sqrt (600 * X)) ^ 2 ≤ (eps / 2) ^ 2 := by
        rw [Real.sq_sqrt (mul_nonneg (by norm_num) hX)]
        dsimp [X]
        rw [show
          600 * ((d : ℝ) * D *
              (((d : ℝ) * Real.log (Real.exp 1 * N) +
                Real.log (2 * (N : ℝ) ^ 2)) / N)) =
            (600 * ((d : ℝ) * D *
              ((d : ℝ) * Real.log (Real.exp 1 * N) +
                Real.log (2 * (N : ℝ) ^ 2)))) / N by ring]
        apply (div_le_iff₀ hden).2
        calc
          600 * ((d : ℝ) * D *
              ((d : ℝ) * Real.log (Real.exp 1 * N) +
                Real.log (2 * (N : ℝ) ^ 2))) ≤
              600 * ((d : ℝ) * D *
                (20 * (d + 2 : ℝ) * L)) := by gcongr
          _ ≤ (eps / 2) ^ 2 * T := by
            dsimp [T]
            rw [hqeq, hqbranch]
            dsimp [qSlow]
            have hL0 : 0 ≤ L := le_trans zero_le_two hL
            field_simp [ne_of_gt heps]
            nlinarith [mul_nonneg (le_trans zero_le_one hD) hL0]
          _ ≤ (eps / 2) ^ 2 * N :=
            mul_le_mul_of_nonneg_left hNreal (sq_nonneg _)
      have hslow :
          Real.sqrt
            (600 * (d : ℝ) * D *
              (((d : ℝ) * Real.log (Real.exp 1 * N) +
                Real.log (2 * (N : ℝ) ^ 2)) / N)) ≤ eps / 2 := by
        dsimp [X] at hslowSq
        rw [show
          600 * (d : ℝ) * D *
              (((d : ℝ) * Real.log (Real.exp 1 * N) +
                Real.log (2 * (N : ℝ) ^ 2)) / N) =
            600 * ((d : ℝ) * D *
              (((d : ℝ) * Real.log (Real.exp 1 * N) +
                Real.log (2 * (N : ℝ) ^ 2)) / N)) by ring]
        nlinarith [Real.sqrt_nonneg
          (600 * ((d : ℝ) * D *
            (((d : ℝ) * Real.log (Real.exp 1 * N) +
              Real.log (2 * (N : ℝ) ^ 2)) / N)))]
      have hfail :
          failureProbability N hN / 2 * min 2 (E.eta / 2) ≤ eps / 4 := by
        rw [failureProbability]
        have hcap : min 2 (E.eta / 2) ≤ 2 := min_le_left _ _
        have hNeps : 2 / eps ≤ (N : ℝ) := by
          calc
            2 / eps ≤ qSlow := by
              dsimp [qSlow]
              apply (div_le_iff₀ heps).2
              rw [show
                ((d : ℝ) ^ 2 * D * (eps ^ 2)⁻¹) * eps =
                  ((d : ℝ) ^ 2 * D) / eps by
                    field_simp [ne_of_gt heps] <;> ring]
              exact (le_div_iff₀ heps).2 (by nlinarith [hd2D])
            _ ≤ T := by
              dsimp [T]
              rw [hqeq, hqbranch]
              nlinarith [hqSlow, hL]
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
      apply localized_sampleComplexity_le_of_learnerRisk_le
        E P0 C D eps heps heps_one hshell
        (predictionPolytopeLearner E 64 (by norm_num) (n := N)).deployed
        hN (predictionPolytopeLearner_measurable (n := N) E 64 (by norm_num))
      intro P hP
      calc
        learnerRisk E P N
            (predictionPolytopeLearner E 64 (by norm_num)
              (n := N)).deployed ≤
            min
              (300 * E.eta * (d : ℝ) * D *
                (((d : ℝ) * Real.log (Real.exp 1 * N) +
                  Real.log (2 * (N : ℝ) ^ 2)) / N))
              (Real.sqrt
                (600 * (d : ℝ) * D *
                  (((d : ℝ) * Real.log (Real.exp 1 * N) +
                    Real.log (2 * (N : ℝ) ^ 2)) / N))) +
              failureProbability N hN / 2 * min 2 (E.eta / 2) :=
          lowerEnvelopeLearnerRisk_le_sharp E P C D hP hZhao hN
        _ ≤ eps / 2 + eps / 4 :=
          add_le_add ((min_le_right _ _).trans hslow) hfail
        _ ≤ eps := by linarith

end CausalSmith.Stat.ReverseKLTwoCoverage
