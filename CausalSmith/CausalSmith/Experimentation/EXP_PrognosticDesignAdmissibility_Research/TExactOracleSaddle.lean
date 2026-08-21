/- Exact balanced-cut-hull oracle saddle and design implementation. -/
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.Helpers.SimplexMinimax
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.Helpers.FourUnit
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.TConeLiftDual
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.TExactDesignRisk
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.TBalancedCovarianceRealizability

namespace CausalSmith.Experimentation.PrognosticDesignAdmissibility

open Causalean.Experimentation.DesignBased

/-- Worst SATE MSE over all fixed populations whose centered mean lies in the shell. -/
noncomputable def designShellRisk (n : ℕ) (D : FiniteDesign (Assignment n))
    (rho M : ℝ) (S : Submodule ℝ (EVec n)) : ℝ :=
  sSup {r | ∃ (Y : Fin n → Bool → Assignment n → ℝ)
      (yr : Fin n → Assignment n → ℝ),
    FixedPotentialOutcomes Y ∧ ConsistencyNoInterference Y yr ∧
    centeredOutcomeMean Y ∈ qualityShell rho M S ∧
    r = D.E (fun z => (diffInMeans yr z - sate Y) ^ 2)}

/-- The complete saddle identity, epigraph form, and implementable risk converse. -/
def ExactOracleSaddleStatement (n : ℕ) (S : Submodule ℝ (EVec n)) (M : ℝ) : Prop :=
  ∀ rho ∈ Set.Icc (0 : ℝ) 1,
    oracleValue n rho S =
        sInf {v | ∃ A ∈ covarianceHull n,
          v = sSup {w | ∃ X ∈ liftedAdversary rho S, w = (A * X).trace}} ∧
    oracleValue n rho S =
        sSup {v | ∃ X ∈ liftedAdversary rho S,
          v = sInf {w | ∃ z, IsBalanced z ∧ w = quadraticForm X (signVector z)}} ∧
    oracleValue n rho S =
        sSup {t | ∃ X ∈ liftedAdversary rho S,
          ∀ z, IsBalanced z → t ≤ quadraticForm X (signVector z)} ∧
    (∃ Dstar ∈ balancedDesignSpace n,
      designShellRisk n Dstar rho M S = oracleRisk n rho M S) ∧
    (∀ D ∈ balancedDesignSpace n,
      oracleRisk n rho M S ≤ designShellRisk n D rho M S)

-- @node: thm:exact-oracle-saddle
/-- The exact full-hull saddle program has sign-pair weights defining an attaining
balanced design, and every balanced design obeys the matching SATE-risk converse. -/
theorem exact_oracle_saddle
    (n : ℕ) (hn : 4 ≤ n) (hpar : Even n)
    (S : Submodule ℝ (EVec n)) (hSH : S ≤ centeredSubspace n)
    (hp0 : 1 ≤ Module.finrank ℝ S)
    (M : ℝ) (hM : 0 < M) :
    ExactOracleSaddleStatement n S M := by
  sorry

end CausalSmith.Experimentation.PrognosticDesignAdmissibility
