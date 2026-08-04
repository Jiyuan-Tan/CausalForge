import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Helpers.FastBranchInversion

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

variable {d : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [LinearOrder 𝒳] [LinearOrder 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
  (E : CommonExperiment d 𝒳 𝒜)

-- @node: lem:fixed-experiment-fast-branch-inversion
lemma fixed_experiment_fast_branch_inversion
    (P0 : BanditLaw E) (C D : ℝ) (hshell : ExactShell E P0 C D)
    (hZhao : ZhaoUniformSquareComparison (𝒳 := 𝒳) (𝒜 := 𝒜)) :
    (∀ eps, ∀ hε : eps ∈ Set.Ioo (0 : ℝ) 1,
      sampleComplexity E eps C D hε.1 hε.2 ≤
        (↑⌈8 * inversionQ E D / eps *
          Real.log (8 * Real.exp 1 * inversionQ E D / eps)⌉₊ : WithTop ℕ)) ∧
    Filter.Tendsto
      (fun eps : ℝ => eps ^ 2 / d * sampleComplexityReal E eps C D)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hbound :=
    fixedExperimentSampleComplexityBound E P0 C D hshell hZhao
  exact ⟨hbound,
    fixedExperimentSampleComplexityLimit E P0 C D hshell hbound⟩

-- @node: thm:no-shared-feature-slow-branch
theorem no_shared_feature_slow_branch
    (P0 : BanditLaw E) (C D : ℝ) (hshell : ExactShell E P0 C D)
    (hC : 1 < D ∧ D < C ∧ C < Real.exp E.eta)
    (hZhao : ZhaoUniformSquareComparison (𝒳 := 𝒳) (𝒜 := 𝒜)) :
    (∀ eps, ∀ hε : eps ∈ Set.Ioo (0 : ℝ) 1,
      sampleComplexity E eps C D hε.1 hε.2 ≤
        (↑⌈8 * inversionQ E D / eps *
          Real.log (8 * Real.exp 1 * inversionQ E D / eps)⌉₊ : WithTop ℕ)) ∧
    ¬ ∃ c eps0 : ℝ, 0 < c ∧ 0 < eps0 ∧
      ∀ eps, ∀ heps : 0 < eps, ∀ heps_one : eps < 1, eps ≤ eps0 →
        (↑⌈c * (d : ℝ) / eps ^ 2⌉₊ : WithTop ℕ) ≤
          sampleComplexity E eps C D heps heps_one := by
  obtain ⟨hbound, htend⟩ :=
    fixed_experiment_fast_branch_inversion E P0 C D hshell hZhao
  refine ⟨hbound, ?_⟩
  rintro ⟨c, eps0, hc, heps0, hlower⟩
  have hratio : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0),
      eps ^ 2 / d * sampleComplexityReal E eps C D < c :=
    htend.eventually (eventually_lt_nhds hc)
  have hsmall : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0),
      eps < min eps0 1 :=
    (eventually_lt_nhds (lt_min heps0 zero_lt_one)).filter_mono inf_le_left
  have hpos : ∀ᶠ eps : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < eps :=
    self_mem_nhdsWithin
  obtain ⟨eps, hratio_eps, hsmall_eps, heps⟩ :=
    (hratio.and (hsmall.and hpos)).exists
  have heps0' : eps ≤ eps0 := (hsmall_eps.trans_le (min_le_left _ _)).le
  have heps1 : eps < 1 := hsmall_eps.trans_le (min_le_right _ _)
  have hfinite : sampleComplexity E eps C D heps heps1 ≠ ⊤ := by
    intro htop
    have hle := hbound eps ⟨heps, heps1⟩
    rw [htop] at hle
    exact WithTop.not_top_le_coe _ hle
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hk' : sampleComplexity E eps C D heps heps1 = k := hk.symm
  have hreal : sampleComplexityReal E eps C D = k :=
    sampleComplexityReal_eq_nat E eps C D ⟨heps, heps1⟩ k hk'
  have hl := hlower eps heps heps1 heps0'
  have hl_nat : ⌈c * (d : ℝ) / eps ^ 2⌉₊ ≤ k := by
    rw [hk'] at hl
    exact WithTop.coe_le_coe.mp hl
  have hceil : c * (d : ℝ) / eps ^ 2 ≤ k :=
    Nat.le_ceil _ |>.trans (by exact_mod_cast hl_nat)
  rw [hreal] at hratio_eps
  have hdpos : 0 < (d : ℝ) := by
    have : 0 < d := by
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
      linarith [hC.1]
    exact_mod_cast this
  have hepssq : 0 < eps ^ 2 := sq_pos_of_pos heps
  have hc_d_le : c * (d : ℝ) ≤ (k : ℝ) * eps ^ 2 :=
    (div_le_iff₀ hepssq).mp hceil
  have hk_lt : eps ^ 2 * (k : ℝ) < c * (d : ℝ) := by
    apply (div_lt_iff₀ hdpos).mp
    calc
      eps ^ 2 * (k : ℝ) / (d : ℝ) =
          eps ^ 2 / (d : ℝ) * (k : ℝ) := by ring
      _ < c := hratio_eps
  nlinarith

end CausalSmith.Stat.ReverseKLTwoCoverage
