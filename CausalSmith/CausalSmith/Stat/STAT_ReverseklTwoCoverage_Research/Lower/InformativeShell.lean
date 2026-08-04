import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Basic
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Gibbs.RegretIdentity
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.ZeroRisk
import Causalean.Stat.Minimax.Assouad
import Causalean.Stat.Minimax.Pinsker
import Causalean.Stat.Minimax.Mixture
import Causalean.Stat.Minimax.TotalVariation
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.Informative.Calibration

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

-- @node: prop:informative-fast-shell-all-indices
theorem informative_fast_shell_all_indices
    (eta C D : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C) (hC : C < Real.exp eta) :
    ∃ c eps0 : ℝ, 0 < c ∧ 0 < eps0 ∧
      ∀ d : ℕ, 4 ≤ d →
        ∃ (mX mA : ℕ)
          (E : CommonExperiment d (Fin mX) (Fin mA)),
          E.eta = eta ∧
          (exactShellSet E C D).Nonempty ∧
        ∀ eps, ∀ heps : 0 < eps, ∀ heps_one : eps < 1, eps ≤ eps0 →
          (↑⌈c * (d : ℝ) * D * eta / eps⌉₊ : WithTop ℕ) ≤
            sampleComplexity E eps C D heps heps_one := by
  let c := informativeLowerConstant eta D
  let eps0 := informativeAccuracyCap eta C D
  have hDexp : D < Real.exp eta := lt_of_le_of_lt hDC hC
  have hc : 0 < c := informativeLowerConstant_pos heta hD hDexp
  have heps0 : 0 < eps0 :=
    informativeAccuracyCap_pos heta hD hDC hC
  refine ⟨c, eps0, hc, heps0, ?_⟩
  intro d hd
  let E := informativeExperiment d hd eta C D heta
    (lt_of_lt_of_le hD hDC) hC
  have hcap : 0 ≤ informativeGammaCap eta D :=
    (informativeGammaCap_pos heta hD hDexp).le
  let v0 : Fin (d - 1) → Bool := fun _ => false
  let P0 : BanditLaw E :=
    informativeLaw d hd eta C D 0 heta hD hDC hC v0 (le_refl 0) hcap
  have hP0 : P0 ∈ exactShellSet E C D := by
    exact informativeLaw_exactShell d hd eta C D 0 heta hD hDC hC
      v0 (le_refl 0) hcap
  have hmodel : (exactShellSet E C D).Nonempty := ⟨P0, hP0⟩
  refine ⟨d + 1, 2, E, rfl, hmodel, ?_⟩
  intro eps heps heps_one heps_le
  change
    (↑⌈c * (d : ℝ) * D * eta / eps⌉₊ : WithTop ℕ) ≤
      sampleComplexityPositive E eps C D heps
  rw [sampleComplexityPositive, if_pos hmodel]
  apply le_sInf
  intro m hm
  rcases hm with ⟨n, hn_one, rfl, hrisk⟩
  have hnat :
      ⌈c * (d : ℝ) * D * eta / eps⌉₊ ≤ n := by
    by_contra hnot
    have hnlt :
        n < ⌈informativeLowerConstant eta D * (d : ℝ) * D * eta / eps⌉₊ := by
      simpa [c] using Nat.lt_of_not_ge hnot
    let gamma := informativeGammaFor d eta C D eps
    have hgamma0 : 0 ≤ gamma :=
      informativeGammaFor_nonneg d eta C D eps
    have hgamma : gamma ≤ informativeGammaCap eta D := by
      exact informativeGammaFor_le_cap hd heta hD hDC hC heps
        (by simpa [eps0] using heps_le)
    have hbudget :
        (n : ℝ) *
          (4 * gamma ^ 2 / informativeTotal d eta C D *
            (1 / informativeBeta eta D +
              1 / (1 - informativeBeta eta D))) ≤ 1 := by
      exact informative_budget_of_lt_ceil hd heta hD hDC hC heps hnlt
    have hlower := informative_minimaxRisk_lower hd eta C D gamma heta hD hDC
      hC hgamma0 hgamma hbudget
    have heq :
        eta⁻¹ * (1 / informativeTotal d eta C D) *
              ((eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2) *
              ((d - 1 : ℕ) : ℝ) / 8 =
            2 * eps := by
      exact informative_rawLower_eq_two_eps hd heta hD hDC hC heps
    rw [heq] at hlower
    nlinarith
  exact_mod_cast hnat

-- @node: prop:zero-risk-nontrivial-shell
theorem zero_risk_nontrivial_shell
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
  exact zero_risk_nontrivial_shell_proof d hd eta C D
    heta hD hDC hC

end CausalSmith.Stat.ReverseKLTwoCoverage
