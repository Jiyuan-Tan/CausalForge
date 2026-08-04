import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.SameShellLower.Inversion

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

noncomputable section

theorem same_shell_lower_disposable_proof :
    ∀ eta C D : ℝ, 0 < eta → 1 < D → D ≤ C →
      C < Real.exp eta → 2 * D - 1 < Real.exp eta →
      ∃ eps1 c : ℝ, 0 < eps1 ∧ 0 < c ∧
        ∀ d : ℕ, 4 ≤ d →
          ∃ (mX mA : ℕ) (E : CommonExperiment d (Fin mX) (Fin mA)),
            E.eta = eta ∧
            0 < hardScale D eta ∧
            eps1 ≤ hardAccuracyRange C D eta ∧
            ∃ (plus minus zero : Fin mA) (xC xA xZ : Fin mX)
              (xHard : Fin (hardCoordinateCount d) → Fin mX)
              (e0 z : Fin d → ℝ)
              (u w : Fin (hardCoordinateCount d) → Fin d → ℝ),
              ∀ eps, ∀ heps : 0 < eps, ∀ heps_one : eps < 1, eps ≤ eps1 →
                ∃ family :
                    (Fin (hardCoordinateCount d) → Bool) → BanditLaw E,
                  (explicitHardFamily E C D eps plus minus zero xC xA xZ
                    xHard e0 z u w family).Nonempty ∧
                  explicitHardFamily E C D eps plus minus zero xC xA xZ
                    xHard e0 z u w family ⊆ exactShellSet E C D ∧
                  (↑⌈c * (d : ℝ) * D * eta / eps⌉₊ : WithTop ℕ) ≤
                    sampleComplexity E eps C D heps heps_one := by
  intro eta C D heta hD hDC hCexp hDexp
  obtain ⟨eps1, g, heps1, hg, hgM, hepsRange, hscaleGood⟩ :=
    exists_hardStrongEpsScale (C := C) heta hD hDexp
  let c := hardLowerConstant D eta
  have hc : 0 < c := hardLowerConstant_pos heta hD hDexp
  refine ⟨eps1, c, heps1, hc, ?_⟩
  intro d hd
  let E := hardExperiment d hd eta C D heta hD hDC hCexp
  refine ⟨hardContextCard d C D, 3, E, rfl,
    hardScale_pos heta hD hDexp, hepsRange,
    hardPlus, hardMinus, hardZero,
    hardContextEquiv d C D hardContextCalibration,
    hardContextEquiv d C D hardContextAnchor,
    hardContextEquiv d C D hardContextResidual,
    (fun j => hardContextEquiv d C D (hardContextHard j)),
    hardBasisE0 hd, hardBasisZ hd, hardBasisU hd, hardBasisW hd, ?_⟩
  intro eps heps heps_one hepsle
  let gamma := hardPerturbation eps eta
  obtain ⟨hgamma, hgammag, hepsSmall, hgammaLog, hden,
    hgammaBetaHalf, hgammaOneHalf, hbLo, hbHi⟩ :=
    hscaleGood eps heps hepsle
  have hgammaBeta : gamma ≤ hardBeta D eta gamma :=
    hgammaBetaHalf.trans (by linarith)
  have hgammaOne : gamma ≤ 1 - hardBeta D eta gamma :=
    hgammaOneHalf.trans (by linarith)
  have hbeta0 := hardBeta_zero_pos heta hD
  have hbeta1zero := hardBeta_zero_lt_one heta hDexp hD
  have hbeta : 0 < hardBeta D eta gamma :=
    (half_pos hbeta0).trans_le hbLo
  have hbeta1 : hardBeta D eta gamma < 1 := by
    have : (1 + hardBeta D eta 0) / 2 < 1 := by linarith
    exact hbHi.trans_lt this
  have hpert : gamma ≤
      min (hardScale D eta)
        (min (1 / 4)
          (min (hardBeta D eta gamma)
            (1 - hardBeta D eta gamma))) := by
    apply le_min
    · exact hgammag.trans (hgM.trans (min_le_left _ _))
    apply le_min
    · exact hgammag.trans (hgM.trans (min_le_right _ _))
    exact le_min hgammaBeta hgammaOne
  let family :
      (Fin (hardCoordinateCount d) → Bool) → BanditLaw E :=
    fun v => hardLaw hd eta C D gamma heta hD hDC hCexp v
      hgamma.le hgammaBeta hgammaOne
  have hfamilyInj : Function.Injective family := by
    simpa [family, E] using
      hardLaw_family_injective hd heta hD hDC hCexp hgamma
        hgammaBeta hgammaOne
  have hblue : ∀ v, HardFamilyBlueprint E (family v) C D eps v
      hardPlus hardMinus hardZero
      (hardContextEquiv d C D hardContextCalibration)
      (hardContextEquiv d C D hardContextAnchor)
      (hardContextEquiv d C D hardContextResidual)
      (fun j => hardContextEquiv d C D (hardContextHard j))
      (hardBasisE0 hd) (hardBasisZ hd) (hardBasisU hd)
      (hardBasisW hd) := by
    intro v
    simpa [family, E] using
      hard_blueprint hd heta hD hDC hCexp hDexp heps
        (hepsle.trans hepsRange)
        (gamma := gamma) rfl hgamma.le hden hgammaBeta hgammaOne
        hpert v
  have hnonempty :
      (explicitHardFamily E C D eps hardPlus hardMinus hardZero
        (hardContextEquiv d C D hardContextCalibration)
        (hardContextEquiv d C D hardContextAnchor)
        (hardContextEquiv d C D hardContextResidual)
        (fun j => hardContextEquiv d C D (hardContextHard j))
        (hardBasisE0 hd) (hardBasisZ hd) (hardBasisU hd)
        (hardBasisW hd) family).Nonempty := by
    let v0 : Fin (hardCoordinateCount d) → Bool := fun _ => false
    refine ⟨family v0, hfamilyInj, hblue, v0, rfl⟩
  have hsubset :
      explicitHardFamily E C D eps hardPlus hardMinus hardZero
        (hardContextEquiv d C D hardContextCalibration)
        (hardContextEquiv d C D hardContextAnchor)
        (hardContextEquiv d C D hardContextResidual)
        (fun j => hardContextEquiv d C D (hardContextHard j))
        (hardBasisE0 hd) (hardBasisZ hd) (hardBasisU hd)
        (hardBasisW hd) family ⊆ exactShellSet E C D := by
    rintro P ⟨_, _, v, rfl⟩
    simpa [family, E] using
      hard_exactShell hd heta hD hDC hCexp hgamma.le hden
        hgammaBeta hgammaOne v
  refine ⟨family, hnonempty, hsubset, ?_⟩
  have hmodel : (exactShellSet E C D).Nonempty := by
    rcases hnonempty with ⟨P, hP⟩
    exact ⟨P, hsubset hP⟩
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
        n < ⌈hardLowerConstant D eta * (d : ℝ) * D * eta / eps⌉₊ := by
      simpa [c] using Nat.lt_of_not_ge hnot
    have hgammaSq : gamma ^ 2 ≤ 256 * eps / eta := by
      simpa [gamma] using hardPerturbation_sq_le heta heps hepsSmall
    have hbudget :
        (n : ℝ) * hardNeighborChiBound d eta C D gamma ≤
          Real.log (17 / 16) :=
      hard_budget_of_lt_ceil hd heta hD hDC hCexp hDexp heps
        hgammaSq hbLo hbHi hnlt
    have hlower := hard_minimaxRisk_lower hd eta C D gamma
      heta hD hDC hCexp hgamma hbeta hbeta1 hgammaBetaHalf
      hgammaOneHalf hden hpert hbudget
    have hraw :
        eps <
          eta⁻¹ *
            ((hardCoordinateCount d : ℝ)⁻¹ / hardTotal d C D eta) *
            ((((1 / 4 : ℝ) - hardGibbsLow eta gamma) / 2) ^ 2 / 2) *
            (hardCoordinateCount d : ℝ) * 7 / 16 := by
      simpa [gamma] using
        hard_rawLower_gt_eps hd heta hD hDC hCexp heps hgammaLog
    exact (not_lt_of_ge hrisk) (hraw.trans_le hlower)
  exact_mod_cast hnat

end

end CausalSmith.Stat.ReverseKLTwoCoverage
