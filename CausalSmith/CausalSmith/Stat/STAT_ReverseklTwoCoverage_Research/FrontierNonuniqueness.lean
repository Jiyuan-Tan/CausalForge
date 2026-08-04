import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Feasibility.IndexRegion
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.InformativeShell
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Upper.CleanTemperature
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.NoSlowBranch

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

variable {d : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [LinearOrder 𝒳] [LinearOrder 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]

/-- Same numerical indices, but sample-complexity-one and informative public
experiments.  The lower constants are chosen before the dimension and are
therefore uniform in `d`, with dependence only on `(C,D,eta)`. -/
def FrontierNonuniqueAt (eta C D : ℝ) : Prop :=
  ∃ c eps0 : ℝ, 0 < c ∧ 0 < eps0 ∧
    ∀ d : ℕ, 4 ≤ d →
      ∃ (mX0 mA0 mX1 mA1 : ℕ)
        (E0 : CommonExperiment d (Fin mX0) (Fin mA0))
        (E1 : CommonExperiment d (Fin mX1) (Fin mA1)),
        E0.eta = eta ∧ E1.eta = eta ∧
        (exactShellSet E0 C D).Nonempty ∧ (exactShellSet E1 C D).Nonempty ∧
        (∀ eps, ∀ heps : 0 < eps,
          sampleComplexityPositive E0 eps C D heps = 1) ∧
        ∀ eps, ∀ heps : 0 < eps, ∀ heps_one : eps < 1, eps ≤ eps0 →
          (↑⌈c * (d : ℝ) * D * eta / eps⌉₊ : WithTop ℕ) ≤
            sampleComplexity E1 eps C D heps heps_one

/-- The stronger zero-risk witness used only by the theorem that explicitly
asserts zero minimax risk at every sample size. -/
def ZeroRiskFrontierNonuniqueAt (eta C D : ℝ) : Prop :=
  ∃ c eps0 : ℝ, 0 < c ∧ 0 < eps0 ∧
    ∀ d : ℕ, 4 ≤ d →
      ∃ (mX0 mA0 mX1 mA1 : ℕ)
        (E0 : CommonExperiment d (Fin mX0) (Fin mA0))
        (E1 : CommonExperiment d (Fin mX1) (Fin mA1)),
        E0.eta = eta ∧ E1.eta = eta ∧
        (exactShellSet E0 C D).Nonempty ∧ (exactShellSet E1 C D).Nonempty ∧
        (∀ n, minimaxRisk E0 n (exactShellSet E0 C D) = 0) ∧
        (∀ eps, ∀ heps : 0 < eps,
          sampleComplexityPositive E0 eps C D heps = 1) ∧
        ∀ eps, ∀ heps : 0 < eps, ∀ heps_one : eps < 1, eps ≤ eps0 →
          (↑⌈c * (d : ℝ) * D * eta / eps⌉₊ : WithTop ℕ) ≤
            sampleComplexity E1 eps C D heps heps_one

-- @node: thm:fixed-design-feasibility-and-frontier-nonuniqueness
theorem fixed_design_feasibility_and_frontier_nonuniqueness
    (E : CommonExperiment d 𝒳 𝒜) (C D : ℝ) :
    ((exactShellSet E C D).Nonempty ↔
      BoundedFeatures E ∧ FixedExperimentFeasibilitySystem E C D) ∧
    (1 < D → D ≤ C → C < Real.exp E.eta →
      ZeroRiskFrontierNonuniqueAt E.eta C D ∧
      ∀ lower : ℝ → WithTop ℕ,
        (∀ (mX mA : ℕ) (E' : CommonExperiment d (Fin mX) (Fin mA)),
          E'.eta = E.eta → (exactShellSet E' C D).Nonempty →
          ∀ eps, ∀ heps : 0 < eps,
            lower eps ≤ sampleComplexityPositive E' eps C D heps) →
        ∀ eps, 0 < eps → lower eps ≤ 1) := by
  constructor
  · exact (fixed_experiment_shell_certificate E C D).1
  · intro hD hDC hC
    constructor
    · rcases informative_fast_shell_all_indices E.eta C D E.eta_pos hD hDC hC with
        ⟨c, eps0, hc, heps0, hinformative⟩
      refine ⟨c, eps0, hc, heps0, ?_⟩
      intro d' hd'
      rcases zero_risk_nontrivial_shell d' hd' E.eta C D E.eta_pos hD hDC hC with
        ⟨mX0, mA0, E0, hE0eta, hE0shell, _hpolicy, hE0risk, hE0sample⟩
      rcases hinformative d' hd' with
        ⟨mX1, mA1, E1, hE1eta, hE1shell, hE1sample⟩
      exact ⟨mX0, mA0, mX1, mA1, E0, E1,
        hE0eta, hE1eta, hE0shell, hE1shell, hE0risk, hE0sample, hE1sample⟩
    · intro lower hlower eps heps
      rcases zero_risk_nontrivial_shell d E.dim_ge_four E.eta C D
          E.eta_pos hD hDC hC with
        ⟨mX, mA, E0, hE0eta, hE0shell, _hpolicy, _hrisk, hsample⟩
      exact (hlower mX mA E0 hE0eta hE0shell eps heps).trans_eq
        (hsample eps heps)

-- @node: thm:fixed-design-index-insufficiency
theorem fixed_design_index_insufficiency
    (E : CommonExperiment d 𝒳 𝒜) (C D : ℝ)
    (hZhao : ZhaoUniformSquareComparison (𝒳 := 𝒳) (𝒜 := 𝒜))
    (hMaximum : MeasurableMaximumTheorem) :
    (1 < D → D ≤ C → C < Real.exp E.eta →
      ((exactShellSet E C D).Nonempty ↔
        BoundedFeatures E ∧ FixedExperimentFeasibilitySystem E C D)) ∧
    ((exactShellSet E C D).Nonempty →
      (∀ n, 0 < n → IsMeasurableLearner E (stabilizedLearner (n := n) E)) ∧
      ∀ eps, ∀ heps : eps ∈ Set.Ioo (0 : ℝ) 1,
      (E.eta ≤ 2 * eps →
        sampleComplexity E eps C D heps.1 heps.2 = 1) ∧
      (2 * eps < E.eta →
        let n0 := ⌈(10 : ℝ) ^ 8 * cleanQ d D E.eta eps *
          cleanLogFactor d D E.eta eps⌉₊
        (∀ P ∈ exactShellSet E C D,
          learnerRisk E P n0 (stabilizedLearner (n := n0) E) ≤ eps) ∧
        sampleComplexity E eps C D heps.1 heps.2 ≤ n0)) ∧
    ((exactShellSet E 1 1).Nonempty →
      ∀ eps, ∀ heps : 0 < eps,
        sampleComplexityPositive E eps 1 1 heps = 1) ∧
    (1 < D → D ≤ C → C < Real.exp E.eta →
      FrontierNonuniqueAt E.eta C D) ∧
    ((exactShellSet E C D).Nonempty → Filter.Tendsto
      (fun eps : ℝ => eps ^ 2 / d * sampleComplexityReal E eps C D)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro _hD _hDC _hC
    exact (fixed_experiment_shell_certificate E C D).1
  · intro hnonempty
    rcases hnonempty with ⟨P0, hP0⟩
    have hclean :=
      clean_temperature_feature_upper E P0 C D hP0 hZhao hMaximum
    refine ⟨?_, hclean.2⟩
    intro n hn
    exact (hclean.1 n hn).1
  · intro hnonempty eps heps
    exact (zero_risk_boundary E hnonempty eps heps).2
  · intro hD hDC hC
    rcases
        (fixed_design_feasibility_and_frontier_nonuniqueness E C D).2
          hD hDC hC |>.1 with
      ⟨c, eps0, hc, heps0, hfrontier⟩
    refine ⟨c, eps0, hc, heps0, ?_⟩
    intro d' hd'
    rcases hfrontier d' hd' with
      ⟨mX0, mA0, mX1, mA1, E0, E1, hE0eta, hE1eta,
        hE0shell, hE1shell, _hE0risk, hE0sample, hE1sample⟩
    exact ⟨mX0, mA0, mX1, mA1, E0, E1, hE0eta, hE1eta,
      hE0shell, hE1shell, hE0sample, hE1sample⟩
  · intro hnonempty
    rcases hnonempty with ⟨P0, hP0⟩
    exact (fixed_experiment_fast_branch_inversion E P0 C D hP0 hZhao).2

-- @node: thm:full-feasible-frontier-answer
theorem full_feasible_frontier_answer
    (E : CommonExperiment d 𝒳 𝒜) (C D : ℝ)
    (hZhao : ZhaoUniformSquareComparison (𝒳 := 𝒳) (𝒜 := 𝒜))
    (hMaximum : MeasurableMaximumTheorem) :
    ((exactShellSet E C D).Nonempty ↔
      BoundedFeatures E ∧ FixedExperimentFeasibilitySystem E C D) ∧
    ((exactShellSet E 1 1).Nonempty →
      ∀ eps, ∀ heps : 0 < eps,
        sampleComplexityPositive E eps 1 1 heps = 1) ∧
    ((exactShellSet E C D).Nonempty →
      (∀ n, 0 < n → IsMeasurableLearner E (stabilizedLearner (n := n) E)) ∧
      ∀ eps, ∀ heps : eps ∈ Set.Ioo (0 : ℝ) 1,
        (E.eta ≤ 2 * eps →
          sampleComplexity E eps C D heps.1 heps.2 = 1) ∧
        (2 * eps < E.eta →
          let n0 := ⌈(10 : ℝ) ^ 8 * cleanQ d D E.eta eps *
            cleanLogFactor d D E.eta eps⌉₊
          (∀ P ∈ exactShellSet E C D,
            learnerRisk E P n0 (stabilizedLearner (n := n0) E) ≤ eps) ∧
          sampleComplexity E eps C D heps.1 heps.2 ≤ n0)) ∧
    (1 < D → D ≤ C → C < Real.exp E.eta →
      FrontierNonuniqueAt E.eta C D) ∧
    ((exactShellSet E C D).Nonempty → Filter.Tendsto
      (fun eps : ℝ => eps ^ 2 / d * sampleComplexityReal E eps C D)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) := by
  have hindex :=
    fixed_design_index_insufficiency E C D hZhao hMaximum
  have hcertificate :=
    (fixed_experiment_shell_certificate E C D).1
  exact ⟨hcertificate, hindex.2.2.1, hindex.2.1,
    hindex.2.2.2.1, hindex.2.2.2.2⟩

end CausalSmith.Stat.ReverseKLTwoCoverage
