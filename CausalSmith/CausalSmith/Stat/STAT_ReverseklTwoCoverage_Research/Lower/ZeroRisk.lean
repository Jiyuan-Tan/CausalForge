import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.ZeroRisk.CommonPolicy
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.ZeroRisk.Minimax

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

theorem zero_risk_nontrivial_shell_proof
    (d : ℕ) (hd : 4 ≤ d) (eta C D : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C) (hC : C < Real.exp eta) :
    ∃ (mX mA : ℕ)
      (E : CommonExperiment d (Fin mX) (Fin mA)),
      E.eta = eta ∧
      (exactShellSet E C D).Nonempty ∧
      (∃ piDagger : Policy (Fin mX) (Fin mA),
        IsPolicy piDagger ∧
        ∀ P ∈ exactShellSet E C D, gibbsPolicy E P = piDagger) ∧
      (∀ n, minimaxRisk E n (exactShellSet E C D) = 0) ∧
      ∀ eps, ∀ heps : 0 < eps,
        sampleComplexityPositive E eps C D heps = 1 := by
  have hC1 : 1 < C := lt_of_lt_of_le hD hDC
  by_cases hEq : D = C
  · subst D
    let E := zeroRiskCoreExperiment d hd eta C heta hC1 hC
    have hmodel : (exactShellSet E C C).Nonempty := by
      rcases zeroRiskCore_exactShell d hd eta C heta hC1 hC with ⟨P, hP⟩
      exact ⟨P, hP⟩
    let piDagger : Policy (Fin d) (Fin 2) :=
      zeroRiskDaggerPolicy E (⟨0, by omega⟩ : Fin d)
    have hpi : IsPolicy piDagger :=
      gibbsFromPotential_isPolicy E
        (zeroRiskDaggerPotential (⟨0, by omega⟩ : Fin d))
    have hsupp : PolicySupportedOn piDagger E.reference := by
      intro x a href
      simp [piDagger, zeroRiskDaggerPolicy, gibbsFromPotential, href]
    have hcommon :
        ∀ P ∈ exactShellSet E C C, gibbsPolicy E P = piDagger := by
      exact zeroRiskCore_common_gibbs d hd eta C C heta hC1 hC
    have hrisk :=
      common_gibbs_minimaxRisk_zero E C C piDagger hpi hsupp hmodel hcommon
    refine ⟨d, 2, E, rfl, hmodel, ⟨piDagger, hpi, hcommon⟩,
      hrisk, ?_⟩
    intro eps heps
    exact zero_minimax_sampleComplexityPositive_one
      E C C hmodel hrisk eps heps
  · have hlt : D < C := lt_of_le_of_ne hDC hEq
    let E := zeroRiskAnchorExperiment d hd eta C heta hC1 hC
    have hmodel : (exactShellSet E C D).Nonempty := by
      rcases zeroRiskAnchor_exactShell
          d hd eta C D heta hC1 hD hlt hC with ⟨P, hP⟩
      exact ⟨P, hP⟩
    let piDagger : Policy (Fin (d + 1)) (Fin 2) :=
      zeroRiskDaggerPolicy E (⟨0, by omega⟩ : Fin d).succ
    have hpi : IsPolicy piDagger :=
      gibbsFromPotential_isPolicy E
        (zeroRiskDaggerPotential (⟨0, by omega⟩ : Fin d).succ)
    have hsupp : PolicySupportedOn piDagger E.reference := by
      intro x a href
      simp [piDagger, zeroRiskDaggerPolicy, gibbsFromPotential, href]
    have hcommon :
        ∀ P ∈ exactShellSet E C D, gibbsPolicy E P = piDagger := by
      exact zeroRiskAnchor_common_gibbs d hd eta C D heta hC1 hC
    have hrisk :=
      common_gibbs_minimaxRisk_zero E C D piDagger hpi hsupp hmodel hcommon
    refine ⟨d + 1, 2, E, rfl, hmodel, ⟨piDagger, hpi, hcommon⟩,
      hrisk, ?_⟩
    intro eps heps
    exact zero_minimax_sampleComplexityPositive_one
      E C D hmodel hrisk eps heps


end

end CausalSmith.Stat.ReverseKLTwoCoverage

