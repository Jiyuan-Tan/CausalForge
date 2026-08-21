/- Endpoint reductions and explicit four-unit checks. -/
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.Helpers.FourUnit
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.TAdmissibilityFrontier
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.TPairSpaceExactFrontier

namespace CausalSmith.Experimentation.PrognosticDesignAdmissibility

/-- First-coordinate direction, defined uniformly even for the empty index type. -/
def firstDirection (n : ℕ) : EVec n := WithLp.toLp 2 (fun i => if i.val = 0 then 1 else 0)

/-- Singleton-versus-rest score line. -/
noncomputable def centeredFirstDirection (n : ℕ) : EVec n :=
  (centeredSubspace n).orthogonalProjection (firstDirection n)

noncomputable def outlierScoreSpace (n : ℕ) : Submodule ℝ (EVec n) :=
  Submodule.span ℝ {centeredFirstDirection n}

/-- Normalized singleton-versus-rest basis. -/
noncomputable def outlierUnit (n : ℕ) : EVec n :=
  ‖centeredFirstDirection n‖⁻¹ • centeredFirstDirection n

/-- Intermediate four-unit basis and score line. -/
noncomputable def middleUnit4 : EVec 4 :=
  WithLp.toLp 2 ![(1 : ℝ) / Real.sqrt 6, 1 / Real.sqrt 6, 0, -2 / Real.sqrt 6]

noncomputable def middleScoreSpace4 : Submodule ℝ (EVec 4) := Submodule.span ℝ {middleUnit4}

/-- All endpoint, worked-example, branch-attainment, and eight-unit checks. -/
noncomputable def EndpointReductionsStatement
    (n : ℕ) (hn : 4 ≤ n) (hpar : Even n) (M : ℝ) : Prop :=
  (∀ rho ∈ Set.Icc (0 : ℝ) 1,
    oracleValue n rho (centeredSubspace n) = cnConst n) ∧
  centeredSubspace n ∉ admissibleFamily n M ∧
  (∀ z, IsBalanced z → quadraticForm (vectorOuter (signVector z)) (outlierUnit n) = cnConst n) ∧
  (∀ rho ∈ Set.Icc (0 : ℝ) 1,
    oracleValue n rho (outlierScoreSpace n) = cnConst n) ∧
  kappaInvariant n (outlierScoreSpace n) = cnConst n ∧
  gammaInvariant n (outlierScoreSpace n) = 1 ∧
  outlierScoreSpace n ∉ admissibleFamily n M ∧
  kappaInvariant 4 middleScoreSpace4 = 2 / 3 ∧
  gammaInvariant 4 middleScoreSpace4 = 8 / 9 ∧
  criticalQuality 4 M middleScoreSpace4 = 2 * Real.sqrt 2 / 3 ∧
  middleScoreSpace4 ∈ admissibleFamily 4 M ∧
  designCovariance pairDesign4 = covPair4 ∧
  (∀ rho ∈ Set.Icc (0 : ℝ) 1,
    oracleValue 4 rho scoreSpace4 = min (4 / 3) (2 * (1 - rho ^ 2))) ∧
  kappaInvariant 4 scoreSpace4 = 0 ∧
  gammaInvariant 4 scoreSpace4 = 1 / 3 ∧
  criticalQuality 4 M scoreSpace4 = 1 / Real.sqrt 3 ∧
  (∀ rho ∈ Set.Icc (0 : ℝ) (1 / Real.sqrt 3),
    shellLoss (crdCovariance 4) rho scoreSpace4 = 4 / 3) ∧
  (∀ rho ∈ Set.Icc (1 / Real.sqrt 3) 1,
    shellLoss covPair4 rho scoreSpace4 = 2 * (1 - rho ^ 2)) ∧
  kappaInvariant n (pairScoreSpace n hn hpar) = 0 ∧
  pairScoreSpace n hn hpar ∈ admissibleFamily n M ∧
  oracleRisk 8 1 1 (pairScoreSpace 8 (by decide) (by decide)) = 0 ∧
  crdRisk 8 1 = 4 / 7

-- @node: prop:endpoint-reductions
/-- Full-space and singleton scores are design-useless, while the intermediate and
equal-leverage four-unit spaces have the stated exact thresholds and branch formulas;
the eight-unit perfect-quality pair check is exact. -/
theorem endpoint_reductions
    (n : ℕ) (hn : 4 ≤ n) (hpar : Even n) (M : ℝ) (hM : 0 < M) :
    EndpointReductionsStatement n hn hpar M := by
  sorry

end CausalSmith.Experimentation.PrognosticDesignAdmissibility
