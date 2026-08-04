import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Upper.ERMPlugin

namespace CausalSmith.Stat.ReverseKLTwoCoverage

variable {d : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [LinearOrder 𝒳] [LinearOrder 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
  (E : CommonExperiment d 𝒳 𝒜)

noncomputable def inversionB : ℝ := min 2 (E.eta / 2) / 2

noncomputable def inversionQ (D : ℝ) : ℝ :=
  max (600 * kappa E.eta * D * (d + 2)) (max (inversionB E) 1)

/-- Real-valued reading of a finite `WithTop ℕ` sample complexity. -/
noncomputable def sampleComplexityReal (eps C D : ℝ) : ℝ :=
  if hε : eps ∈ Set.Ioo (0 : ℝ) 1 then
    sInf {r : ℝ | ∃ n : ℕ, sampleComplexity E eps C D hε.1 hε.2 = n ∧ r = n}
  else 0

-- @node: sampleComplexityReal_eq_nat
lemma sampleComplexityReal_eq_nat
    (eps C D : ℝ) (hε : eps ∈ Set.Ioo (0 : ℝ) 1) (k : ℕ)
    (hk : sampleComplexity E eps C D hε.1 hε.2 = k) :
    sampleComplexityReal E eps C D = k := by
  simp only [sampleComplexityReal, dif_pos hε]
  rw [show {r : ℝ | ∃ n : ℕ,
      sampleComplexity E eps C D hε.1 hε.2 = n ∧ r = n} = {(k : ℝ)} by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨n, hn, rfl⟩
      rw [hk] at hn
      exact_mod_cast (WithTop.coe_eq_coe.mp hn).symm
    · rintro rfl
      exact ⟨k, hk, rfl⟩]
  simp

-- @node: fixedExperimentSampleComplexityBound
lemma fixedExperimentSampleComplexityBound
    (P0 : BanditLaw E) (C D : ℝ) (hshell : ExactShell E P0 C D)
    (hZhao : ZhaoUniformSquareComparison (𝒳 := 𝒳) (𝒜 := 𝒜)) :
    ∀ eps, ∀ hε : eps ∈ Set.Ioo (0 : ℝ) 1,
      sampleComplexity E eps C D hε.1 hε.2 ≤
        (↑⌈8 * inversionQ E D / eps *
          Real.log (8 * Real.exp 1 * inversionQ E D / eps)⌉₊ : WithTop ℕ) := by
  intro eps hε
  have hmodel : (exactShellSet E C D).Nonempty := ⟨P0, hshell⟩
  obtain ⟨K, hK, hplugin⟩ := erm_plugin_upper
  have hplugin' := hplugin d 𝒳 𝒜 E P0 C D hshell hZhao
  let Q := inversionQ E D
  let L := Real.log (8 * Real.exp 1 * Q / eps)
  let N : ℕ := ⌈8 * Q / eps * L⌉₊
  have hQ : 1 ≤ Q := by
    dsimp [Q, inversionQ]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have harg : Real.exp 1 < 8 * Real.exp 1 * Q / eps := by
    have heexp : 0 < Real.exp 1 := Real.exp_pos _
    have heps : 0 < eps := hε.1
    apply (lt_div_iff₀ heps).2
    nlinarith [hε.2]
  have hL : 1 < L := by
    dsimp [L]
    have hlog := Real.strictMonoOn_log (Real.exp_pos _)
      (lt_trans (Real.exp_pos _) harg) harg
    simpa using hlog
  have hNreal : 8 * Q / eps * L ≤ N := Nat.le_ceil _
  have hN : 0 < N := by
    have hbase : 0 < 8 * Q / eps * L :=
      mul_pos (div_pos (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hQ)) hε.1)
        (lt_trans zero_lt_one hL)
    exact_mod_cast (lt_of_lt_of_le hbase hNreal)
  change sampleComplexityPositive E eps C D hε.1 ≤ (N : WithTop ℕ)
  rw [sampleComplexityPositive, if_pos hmodel]
  apply csInf_le
  · exact ⟨1, by
      rintro m ⟨n, hn, rfl, _⟩
      exact_mod_cast hn⟩
  · refine ⟨N, hN, rfl, ?_⟩
    have hNupper : (N : ℝ) ≤ 9 * Q / eps * L := by
      have hceil := Nat.ceil_lt_add_one
        (show 0 ≤ 8 * Q / eps * L from
          (mul_pos (div_pos (mul_pos (by norm_num)
            (lt_of_lt_of_le zero_lt_one hQ)) hε.1)
            (lt_trans zero_lt_one hL)).le)
      have ht : 1 ≤ Q / eps * L := by
        have hQeps : 1 < Q / eps := by
          apply (lt_div_iff₀ hε.1).2
          simpa using (lt_of_lt_of_le hε.2 hQ)
        nlinarith [hL]
      change (N : ℝ) ≤ 9 * Q / eps * L
      calc
        (N : ℝ) ≤ 8 * Q / eps * L + 1 := hceil.le
        _ ≤ 9 * Q / eps * L := by
          rw [show 8 * Q / eps * L = 8 * (Q / eps * L) by ring,
            show 9 * Q / eps * L = 9 * (Q / eps * L) by ring]
          linarith
    have hlogN : Real.log (2 * Real.exp 1 * N) ≤ 3 * L := by
      have hexpL : Real.exp L = 8 * Real.exp 1 * Q / eps := by
        dsimp [L]
        rw [Real.exp_log]
        exact lt_trans (Real.exp_pos _) harg
      have hexpL_pos : 0 < Real.exp L := Real.exp_pos _
      have hLexp : L ≤ Real.exp L := by
        linarith [Real.add_one_le_exp L]
      have hconst : (9 / 4 : ℝ) ≤ Real.exp L := by
        rw [hexpL]
        have he : 1 ≤ Real.exp 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by norm_num)
        have hqeps : 1 < Q / eps :=
          (lt_div_iff₀ hε.1).2 (by simpa using (lt_of_lt_of_le hε.2 hQ))
        calc
          (9 / 4 : ℝ) ≤ 8 := by norm_num
          _ ≤ 8 * Real.exp 1 * (Q / eps) := by nlinarith
          _ = 8 * Real.exp 1 * Q / eps := by ring
      have hargN :
          2 * Real.exp 1 * (N : ℝ) ≤ Real.exp (3 * L) := by
        calc
          2 * Real.exp 1 * (N : ℝ) ≤
              18 * Real.exp 1 * Q / eps * L := by
            have := mul_le_mul_of_nonneg_left hNupper
              (show 0 ≤ 2 * Real.exp 1 by positivity)
            convert this using 1 <;> ring
          _ = (9 / 4) * Real.exp L * L := by rw [hexpL]; ring
          _ ≤ Real.exp L * Real.exp L * Real.exp L := by
            calc
              (9 / 4) * Real.exp L * L ≤
                  Real.exp L * Real.exp L * L :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hconst (Real.exp_pos L).le)
                  (lt_trans zero_lt_one hL).le
              _ ≤ Real.exp L * Real.exp L * Real.exp L :=
                mul_le_mul_of_nonneg_left hLexp
                  (mul_nonneg (Real.exp_pos L).le (Real.exp_pos L).le)
          _ = Real.exp (3 * L) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1 <;> ring
      have hargNpos : 0 < 2 * Real.exp 1 * (N : ℝ) := by positivity
      calc
        Real.log (2 * Real.exp 1 * N) ≤ Real.log (Real.exp (3 * L)) :=
          Real.strictMonoOn_log.monotoneOn hargNpos (Real.exp_pos _) hargN
        _ = 3 * L := Real.log_exp _
    have hlocal :
        localizationComplexity d N ≤ (d + 2 : ℝ) * (3 * L) := by
      have hNrealpos : 0 < (N : ℝ) := by exact_mod_cast hN
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hrewrite :
          localizationComplexity d N =
            (d : ℝ) + ((d : ℝ) + 2) * Real.log N + Real.log 2 := by
        simp only [localizationComplexity]
        rw [Real.log_mul (Real.exp_ne_zero 1) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)),
          Real.log_exp, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
            (pow_ne_zero 2 (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))),
          Real.log_pow]
        ring
      rw [hrewrite]
      calc
        (d : ℝ) + ((d : ℝ) + 2) * Real.log N + Real.log 2 ≤
            ((d : ℝ) + 2) * Real.log (2 * Real.exp 1 * N) := by
          rw [Real.log_mul (by positivity : (2 * Real.exp 1 : ℝ) ≠ 0)
            (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)),
            Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero 1),
            Real.log_exp]
          have hd0 : 0 ≤ (d : ℝ) := by positivity
          nlinarith
        _ ≤ ((d : ℝ) + 2) * (3 * L) :=
          mul_le_mul_of_nonneg_left hlogN (by positivity)
    have hcoef : 600 * kappa E.eta * D * (d + 2) ≤ Q := by
      dsimp [Q, inversionQ]
      exact le_max_left _ _
    have hB : inversionB E ≤ Q := by
      dsimp [Q, inversionQ]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hNlower : 8 * Q / eps * L ≤ (N : ℝ) := hNreal
    have hfast :
        600 * kappa E.eta * D * localizationComplexity d N / N ≤
          3 * eps / 8 := by
      have hden : 0 < (N : ℝ) := by exact_mod_cast hN
      apply (div_le_iff₀ hden).2
      have hqL : 0 < Q * L := mul_pos (lt_of_lt_of_le zero_lt_one hQ)
        (lt_trans zero_lt_one hL)
      calc
        600 * kappa E.eta * D * localizationComplexity d N ≤
            Q * (3 * L) := by
          calc
            600 * kappa E.eta * D * localizationComplexity d N ≤
                (600 * kappa E.eta * D * (d + 2)) * (3 * L) := by
              have hnonneg : 0 ≤ 600 * kappa E.eta * D := by
                have := hshell.featureExactShell.1
                have hkappa : 0 ≤ kappa E.eta := by
                  unfold kappa
                  exact mul_nonneg E.eta_pos.le
                    (MeasureTheory.integral_nonneg_of_ae (by
                      filter_upwards [MeasureTheory.ae_restrict_mem
                        measurableSet_Icc] with t ht
                      exact mul_nonneg ht.1 (Real.exp_pos _).le))
                exact mul_nonneg
                  (mul_nonneg (by positivity) hkappa)
                  hshell.featureExactShell.1.le
              nlinarith [mul_le_mul_of_nonneg_left hlocal hnonneg]
            _ ≤ Q * (3 * L) :=
              mul_le_mul_of_nonneg_right hcoef
                (mul_nonneg (by norm_num) (lt_trans zero_lt_one hL).le)
        _ ≤ 3 * eps / 8 * N := by
          have hepsfactor : 0 ≤ 3 * eps / 8 :=
            div_nonneg (mul_nonneg (by norm_num) hε.1.le) (by norm_num)
          have := mul_le_mul_of_nonneg_left hNlower hepsfactor
          calc
            Q * (3 * L) = 3 * eps / 8 * (8 * Q / eps * L) := by
              field_simp [ne_of_gt hε.1]
            _ ≤ 3 * eps / 8 * N := this
    have hfail :
        failureProbability N hN / 2 * min 2 (E.eta / 2) ≤ eps / 64 := by
      rw [failureProbability]
      have hNlower' : 8 * Q / eps ≤ (N : ℝ) := by
        calc
          8 * Q / eps ≤ 8 * Q / eps * L := by
            have : 0 ≤ 8 * Q / eps :=
              (div_pos (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hQ))
                hε.1).le
            nlinarith
          _ ≤ N := hNlower
      have hsq : (8 * Q / eps) ^ 2 ≤ (N : ℝ) ^ 2 :=
        (sq_le_sq₀
          (div_nonneg (mul_nonneg (by norm_num) (le_trans zero_le_one hQ)) hε.1.le)
          (Nat.cast_nonneg N)).2 hNlower'
      have hBnonneg : 0 ≤ inversionB E := by
        unfold inversionB
        exact div_nonneg
          (le_min (by norm_num) (div_nonneg E.eta_pos.le (by norm_num)))
          (by norm_num)
      have hN2 : 0 < (N : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hN)
      have hqpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
      dsimp [inversionB] at hB hBnonneg ⊢
      rw [div_eq_mul_inv]
      have hinv : ((N : ℝ) ^ 2)⁻¹ ≤ (eps / (8 * Q)) ^ 2 := by
        calc
          ((N : ℝ) ^ 2)⁻¹ = 1 / (N : ℝ) ^ 2 := by rw [one_div]
          _ ≤ 1 / (8 * Q / eps) ^ 2 :=
            one_div_le_one_div_of_le
              (sq_pos_of_pos (div_pos (mul_pos (by norm_num) hqpos) hε.1)) hsq
          _ = (eps / (8 * Q)) ^ 2 := by
            field_simp [ne_of_gt hε.1, ne_of_gt hqpos]
      have hminQ : min 2 (E.eta / 2) / 2 ≤ Q := hB
      calc
        ((N : ℝ) ^ 2)⁻¹ * 2⁻¹ * min 2 (E.eta / 2) =
            ((N : ℝ) ^ 2)⁻¹ * (min 2 (E.eta / 2) / 2) := by ring
        _ ≤ (eps / (8 * Q)) ^ 2 * Q :=
          mul_le_mul hinv hminQ hBnonneg (sq_nonneg _)
        _ ≤ eps / 64 := by
          have hepsQ : eps ≤ Q := le_trans hε.2.le hQ
          have hepssqQ : eps ^ 2 ≤ eps * Q := by
            nlinarith [mul_le_mul_of_nonneg_left hepsQ hε.1.le]
          field_simp [ne_of_gt hqpos]
          nlinarith
    have hlearner :
        ∀ P ∈ exactShellSet E C D,
          learnerRisk E P N (ermGibbsPluginLearner (n := N) E) ≤ eps := by
      intro P hP
      calc
        learnerRisk E P N (ermGibbsPluginLearner (n := N) E) ≤
            min
                (600 * kappa E.eta * D * localizationComplexity d N / N)
                (Real.sqrt 600 * (1 + Real.exp (2 * E.eta)) *
                  Real.sqrt (D * localizationComplexity d N / N)) +
              failureProbability N hN / 2 * min 2 (E.eta / 2) :=
          (hplugin'.1 N hN).2 P hP
        _ ≤ 600 * kappa E.eta * D * localizationComplexity d N / N +
              failureProbability N hN / 2 * min 2 (E.eta / 2) :=
          by
            gcongr
            exact min_le_left _ _
        _ ≤ 3 * eps / 8 + eps / 64 := add_le_add hfast hfail
        _ ≤ eps := by linarith [hε.1]
    unfold minimaxRisk
    by_cases hb : BddBelow
        {r : ℝ | ∃ L : Learner N (𝒳 := 𝒳) (𝒜 := 𝒜),
          IsMeasurableLearner E L ∧
          r = sSup {q : ℝ | ∃ P : BanditLaw E,
            P ∈ exactShellSet E C D ∧ q = learnerRisk E P N L}}
    · calc
        sInf {r : ℝ | ∃ L : Learner N (𝒳 := 𝒳) (𝒜 := 𝒜),
            IsMeasurableLearner E L ∧
            r = sSup {q : ℝ | ∃ P : BanditLaw E,
              P ∈ exactShellSet E C D ∧ q = learnerRisk E P N L}} ≤
            sSup {q : ℝ | ∃ P : BanditLaw E, P ∈ exactShellSet E C D ∧
              q = learnerRisk E P N (ermGibbsPluginLearner (n := N) E)} := by
          apply csInf_le hb
          exact ⟨ermGibbsPluginLearner (n := N) E, (hplugin'.1 N hN).1, rfl⟩
        _ ≤ eps := by
          apply csSup_le
          · exact ⟨learnerRisk E P0 N (ermGibbsPluginLearner (n := N) E),
              P0, hshell, rfl⟩
          · rintro q ⟨P, hP, rfl⟩
            exact hlearner P hP
    · rw [csInf_of_not_bddBelow hb]
      simpa using hε.1.le

end CausalSmith.Stat.ReverseKLTwoCoverage

namespace CausalSmith.Stat.ReverseKLTwoCoverage

variable {d : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [LinearOrder 𝒳] [LinearOrder 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
  (E : CommonExperiment d 𝒳 𝒜)

-- @node: fixedExperimentSampleComplexityLimit
lemma fixedExperimentSampleComplexityLimit
    (P0 : BanditLaw E) (C D : ℝ) (hshell : ExactShell E P0 C D)
    (hbound : ∀ eps, ∀ hε : eps ∈ Set.Ioo (0 : ℝ) 1,
      sampleComplexity E eps C D hε.1 hε.2 ≤
        (↑⌈8 * inversionQ E D / eps *
          Real.log (8 * Real.exp 1 * inversionQ E D / eps)⌉₊ : WithTop ℕ)) :
    Filter.Tendsto
      (fun eps : ℝ => eps ^ 2 / d * sampleComplexityReal E eps C D)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hd : 0 < d := by
    by_contra hd
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    subst d
    have hzero : featureCoverage E P0 = 0 := by
      have hempty :
          {q : ℝ | ∃ v : Fin 0 → ℝ, v ≠ 0 ∧
            q = quadraticForm (targetCovariance E P0) v /
              quadraticForm (loggingCovariance E P0) v} = ∅ := by
        ext q
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨v, hv, hq⟩
        apply hv
        funext i
        exact Fin.elim0 i
      change sSup
          {q : ℝ | ∃ v : Fin 0 → ℝ, v ≠ 0 ∧
            q = quadraticForm (targetCovariance E P0) v /
              quadraticForm (loggingCovariance E P0) v} = 0
      rw [hempty]
      exact Real.sSup_empty
    have hDeq := hshell.featureExactShell.2
    rw [hzero] at hDeq
    linarith [hshell.featureExactShell.1]
  let Q := inversionQ E D
  have hQ : 1 ≤ Q := by
    dsimp [Q, inversionQ]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hlogeps :
      Filter.Tendsto (fun eps : ℝ => eps * Real.log eps)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have ho := (isLittleO_log_rpow_nhdsGT_zero (r := (-1 : ℝ)) (by norm_num))
      |>.tendsto_div_nhds_zero
    apply ho.congr'
    filter_upwards [self_mem_nhdsWithin] with eps heps
    rw [Real.rpow_neg_one, div_inv_eq_mul]
    ring
  have hmain :
      Filter.Tendsto
        (fun eps : ℝ => eps * Real.log (8 * Real.exp 1 * Q / eps))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hlogQ : 0 < 8 * Real.exp 1 * Q := by positivity
    have hconst :
        Filter.Tendsto (fun eps : ℝ => eps * Real.log (8 * Real.exp 1 * Q))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hid : Filter.Tendsto (fun eps : ℝ => eps)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds continuousAt_id
      simpa using
        hid.mul_const (Real.log (8 * Real.exp 1 * Q))
    have heq : (fun eps : ℝ =>
        eps * Real.log (8 * Real.exp 1 * Q) - eps * Real.log eps) =ᶠ[
          nhdsWithin 0 (Set.Ioi 0)]
        (fun eps => eps * Real.log (8 * Real.exp 1 * Q / eps)) := by
      filter_upwards [self_mem_nhdsWithin] with eps heps
      rw [Real.log_div hlogQ.ne' heps.ne']
      ring
    simpa using (hconst.sub hlogeps).congr' heq
  have hupper :
      Filter.Tendsto
        (fun eps : ℝ =>
          eps ^ 2 / d *
            (8 * Q / eps * Real.log (8 * Real.exp 1 * Q / eps) + 1))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hfirst :
        Filter.Tendsto
          (fun eps : ℝ => (8 * Q / d) *
            (eps * Real.log (8 * Real.exp 1 * Q / eps)))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa using hmain.const_mul (8 * Q / d)
    have hsecond :
        Filter.Tendsto (fun eps : ℝ => eps ^ 2 / d)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hid : Filter.Tendsto (fun eps : ℝ => eps)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds continuousAt_id
      simpa using
        (hid.pow 2).div_const (d : ℝ)
    have heq : (fun eps : ℝ => (8 * Q / d) *
        (eps * Real.log (8 * Real.exp 1 * Q / eps)) + eps ^ 2 / d) =ᶠ[
          nhdsWithin 0 (Set.Ioi 0)]
        (fun eps => eps ^ 2 / d *
          (8 * Q / eps * Real.log (8 * Real.exp 1 * Q / eps) + 1)) := by
      filter_upwards [self_mem_nhdsWithin] with eps heps
      have hepspos : 0 < eps := heps
      field_simp [ne_of_gt hepspos, Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)]
    simpa using (hfirst.add hsecond).congr' heq
  apply Filter.Tendsto.squeeze' tendsto_const_nhds hupper
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left]
      with eps heps heps1
    have hε : eps ∈ Set.Ioo (0 : ℝ) 1 := ⟨heps, heps1⟩
    have hfinite : sampleComplexity E eps C D hε.1 hε.2 ≠ ⊤ := by
      intro htop
      have hle := hbound eps hε
      rw [htop] at hle
      exact WithTop.not_top_le_coe _ hle
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfinite
    have hk' : sampleComplexity E eps C D hε.1 hε.2 = k := hk.symm
    rw [sampleComplexityReal_eq_nat E eps C D hε k hk']
    positivity
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left]
      with eps heps heps1
    have hε : eps ∈ Set.Ioo (0 : ℝ) 1 := ⟨heps, heps1⟩
    have hfinite : sampleComplexity E eps C D hε.1 hε.2 ≠ ⊤ := by
      intro htop
      have hle := hbound eps hε
      rw [htop] at hle
      exact WithTop.not_top_le_coe _ hle
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfinite
    have hk' : sampleComplexity E eps C D hε.1 hε.2 = k := hk.symm
    rw [sampleComplexityReal_eq_nat E eps C D hε k hk']
    have hkceil : k ≤
        ⌈8 * Q / eps * Real.log (8 * Real.exp 1 * Q / eps)⌉₊ := by
      have := hbound eps hε
      rw [hk'] at this
      exact WithTop.coe_le_coe.mp this
    have hbase : 0 ≤ 8 * Q / eps *
        Real.log (8 * Real.exp 1 * Q / eps) := by
      have hepspos : 0 < eps := heps
      have harg : 1 < 8 * Real.exp 1 * Q / eps := by
        apply (lt_div_iff₀ hepspos).2
        have hexp : 1 ≤ Real.exp 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by norm_num)
        nlinarith [hQ]
      exact mul_nonneg
        (div_nonneg (mul_nonneg (by norm_num) (le_trans zero_le_one hQ)) hepspos.le)
        (Real.log_nonneg harg.le)
    have hceil :
        (⌈8 * Q / eps * Real.log (8 * Real.exp 1 * Q / eps)⌉₊ : ℝ) ≤
          8 * Q / eps * Real.log (8 * Real.exp 1 * Q / eps) + 1 :=
      (Nat.ceil_lt_add_one hbase).le
    have hfactor : 0 ≤ eps ^ 2 / (d : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left
      ((show (k : ℝ) ≤
          (⌈8 * Q / eps * Real.log (8 * Real.exp 1 * Q / eps)⌉₊ : ℝ) by
            exact_mod_cast hkceil).trans hceil) hfactor

end CausalSmith.Stat.ReverseKLTwoCoverage
