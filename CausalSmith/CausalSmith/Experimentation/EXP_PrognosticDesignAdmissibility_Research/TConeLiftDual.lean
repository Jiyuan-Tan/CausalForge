/- Rank-one exact lift and compactified scalar dual. -/
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.Helpers.ExtremePoints
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.Helpers.Separation
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.Helpers.Spectral
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.Helpers.Compactness

namespace CausalSmith.Experimentation.PrognosticDesignAdmissibility

/-- Full rank-one lift, scalar dual, and endpoint-attainment assertion. -/
def ConeLiftDualStatement (n : ℕ) (S : Submodule ℝ (EVec n)) : Prop :=
  ∀ A ∈ covarianceHull n, ∀ rho ∈ Set.Icc (0 : ℝ) 1,
    shellLoss A rho S =
        sSup {v | ∃ X ∈ liftedAdversary rho S, v = (A * X).trace} ∧
    shellLoss A rho S =
        sInf {v | ∃ eta ≥ 0,
          v = lambdaMaxOn (A + eta • projMatrix S) (centeredSubspace n) - eta * rho ^ 2} ∧
    (∃ u : EVec n, u ∈ centeredSubspace n ∧ ‖u‖ = 1 ∧
      rho ^ 2 ≤ ‖(S.orthogonalProjection u : EVec n)‖ ^ 2 ∧
      vectorOuter u ∈ liftedAdversary rho S ∧
      (A * vectorOuter u).trace = shellLoss A rho S) ∧
    shellLoss A rho S = compactifiedDual n A S (rho ^ 2) ∧
    (rho < 1 → ∃ eta ≥ 0,
      shellLoss A rho S = spectralRegretHandle n A S (rho ^ 2) eta) ∧
    (rho = 1 →
      (∃ eta ≥ 0, shellLoss A rho S = spectralRegretHandle n A S 1 eta) ∨
      shellLoss A rho S = compressedLambdaMax A S)

-- @node: thm:cone-lift-dual
/-- The nonconvex shell has an exact rank-one lifted formulation and scalar dual;
finite multipliers attain below perfect quality, while the perfect-quality endpoint
may occur only at the compactified point. -/
theorem cone_lift_dual
    (n : ℕ) (hn : 4 ≤ n) (hpar : Even n)
    (S : Submodule ℝ (EVec n)) (hSH : S ≤ centeredSubspace n)
    (hp0 : 1 ≤ Module.finrank ℝ S) :
    ConeLiftDualStatement n S := by
  sorry -- BLOCKER: needs-substrate(rank-one extreme points of the PSD trace-one score slice)

end CausalSmith.Experimentation.PrognosticDesignAdmissibility
