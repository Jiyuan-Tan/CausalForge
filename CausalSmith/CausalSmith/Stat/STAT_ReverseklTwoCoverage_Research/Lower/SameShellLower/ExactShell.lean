import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.SameShellLower.Kernel

set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

noncomputable section

theorem hard_exactShell {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (hgamma : 0 ≤ gamma)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma))
    (hgammaBeta : gamma ≤ hardBeta D eta gamma)
    (hgammaOne : gamma ≤ 1 - hardBeta D eta gamma)
    (v : Fin (hardCoordinateCount d) → Bool) :
    ExactShell
      (hardExperiment d hd eta C D heta hD hDC hCexp)
      (hardLaw hd eta C D gamma heta hD hDC hCexp v
        hgamma hgammaBeta hgammaOne)
      C D := by
  let j0 : Fin (hardCoordinateCount d) :=
    ⟨0, hardCoordinateCount_pos hd⟩
  have ha0 : 0 <
      (hardExperiment d hd eta C D heta hD hDC hCexp).reference
        (hardContextEquiv d C D hardContextCalibration) hardPlus := by
    simpa [hardExperiment, hardContextCalibration,
      hardReferenceOnContext, hardPlus] using
      hardQ_pos heta hD hDC hCexp
  have hunorm :
      dotProduct (hardHighVector hd v j0) (hardHighVector hd v j0) = 1 :=
    hardHighVector_norm hd v j0
  simpa only [hardLaw] using
    ibBernoulliLaw_exactShell_of_certificate
      (hardExperiment d hd eta C D heta hD hDC hCexp) C D
      (hardTheta hd D eta gamma v)
      (hardRho (d := d) (C := C) (D := D) (eta := eta))
      (hardContextEquiv d C D hardContextCalibration) hardPlus
      (hardHighVector hd v j0)
      (hard_boundedFeatures hd heta hD hDC hCexp)
      ha0
      (hard_linear_bounds hd v hgamma hgammaBeta hgammaOne)
      (hardRho_pos hd heta hD hDC hCexp)
      (hardRho_sum hd heta hD hDC hCexp)
      (hard_logging_posDef hd heta hD hDC hCexp)
      (hard_certificate_bound hd heta hD hDC hCexp hgamma hden
        hgammaBeta v)
      (hard_certificate_eq hd heta hD hDC hCexp v)
      (hard_gap_posSemidef hd heta hD hDC hCexp hgamma hden
        hgammaBeta v)
      (hard_gap_kernel hd heta hD hDC hCexp hgamma hden
        hgammaBeta v j0)
      hunorm

end

end CausalSmith.Stat.ReverseKLTwoCoverage
