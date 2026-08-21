/- Exact admissibility and leverage-profile threshold frontier. -/
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.Helpers.AffineHull
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.Helpers.GramDiagonal
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.Helpers.LeverageProfile
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.TExactOracleSaddle

namespace CausalSmith.Experimentation.PrognosticDesignAdmissibility

/-- Score leverage at a unit. -/
noncomputable def leverage (S : Submodule ℝ (EVec n)) (i : Fin n) : ℝ := projMatrix S i i

/-- The one-dimensional leverage feasibility condition defining `U`. -/
noncomputable def LeverageFeasible (n : ℕ) (S : Submodule ℝ (EVec n)) (t : ℝ) : Prop :=
  let p : ℝ := Module.finrank ℝ S
  let d : Fin n → ℝ := fun i => ((n - 1 : ℕ) : ℝ) / n * t - leverage S i
  t ∈ Set.Icc (p / (n - 1)) 1 ∧
    (∀ i, 0 ≤ d i) ∧
    ∀ i, 2 * Real.sqrt (d i) ≤ ∑ j, Real.sqrt (d j)

/-- The leverage-only frontier `U(diag P_S)`. -/
noncomputable def leverageFrontier (n : ℕ) (S : Submodule ℝ (EVec n)) : ℝ :=
  sInf {t | LeverageFeasible n S t}

/-- Matrices with the centeredness and diagonal required by the leverage reduction. -/
def leverageMatrixClass (n : ℕ) (S : Submodule ℝ (EVec n)) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  {K | K.transpose = K ∧ K.mulVec (fun _ => 1) = 0 ∧ ∀ i, K i i = leverage S i}

noncomputable def equalProfile4 : Fin 4 → ℝ := ![(1 : ℝ) / 4, 1 / 4, 1 / 4, 1 / 4]
noncomputable def middleProfile4 : Fin 4 → ℝ := ![(1 : ℝ) / 6, 1 / 6, 0, 2 / 3]
noncomputable def outlierProfile4 : Fin 4 → ℝ := ![(3 : ℝ) / 4, 1 / 12, 1 / 12, 1 / 12]

/-- The finite simplex of weights on balanced assignments. -/
def balancedAssignmentSimplex (n : ℕ) : Set (Assignment n → ℝ) :=
  {a | (∀ z, 0 ≤ a z) ∧ (∀ z, ¬IsBalanced z → a z = 0) ∧ ∑ z, a z = 1}

/-- Covariance obtained from a finite balanced-assignment weight vector. -/
noncomputable def assignmentMixtureCovariance (a : Assignment n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∑ z, a z • signOuter z

/-- Finite semidefinite epigraph computing `κ(S)` by assignment enumeration. -/
noncomputable def kappaFiniteSDPValue
    (n : ℕ) (S : Submodule ℝ (EVec n)) : ℝ :=
  sInf {t | ∃ a ∈ balancedAssignmentSimplex n,
    (t • projMatrix S -
      projMatrix S * assignmentMixtureCovariance a * projMatrix S).PosSemidef}

/-- Full arbitrary-subspace admissibility, leverage characterization, sharp bounds,
equality case, and the three four-unit test profiles. -/
noncomputable def AdmissibilityFrontierStatement
    (n : ℕ) (S : Submodule ℝ (EVec n)) (M : ℝ) : Prop :=
  let p : ℝ := Module.finrank ℝ S
  (S ∈ admissibleFamily n M ↔ kappaInvariant n S < cnConst n) ∧
  (kappaInvariant n S < cnConst n ↔ gammaInvariant n S < 1) ∧
  (S ∈ admissibleFamily n M →
    criticalQuality n M S = Real.sqrt (gammaInvariant n S)) ∧
  (S ∉ admissibleFamily n M → criticalQuality n M S = 1) ∧
  gammaInvariant n S =
      sInf {t | ∃ K ∈ leverageMatrixClass n S,
        t = lambdaMaxOn K (centeredSubspace n)} ∧
  gammaInvariant n S = leverageFrontier n S ∧
  kappaInvariant n S = kappaFiniteSDPValue n S ∧
  (∀ epsilon > 0, ∃ D ∈ balancedDesignSpace n,
    compressedLambdaMax (designCovariance D) S < kappaInvariant n S + epsilon) ∧
  (n : ℝ) / (n - 1) * sSup (Set.range (leverage S)) ≤ gammaInvariant n S ∧
  p / (n - 1) ≤ gammaInvariant n S ∧
  (gammaInvariant n S = p / (n - 1) ↔
    ∀ i, leverage S i = p / n) ∧
  criticalQuality n M S ^ 2 ≥ p / (n - 1) ∧
  (∀ rho ∈ Set.Icc (0 : ℝ) 1,
    oracleRisk n rho M S < crdRisk n M →
      gammaInvariant n S < rho ^ 2 ∧
      (n : ℝ) / (n - 1) * sSup (Set.range (leverage S)) ≤ gammaInvariant n S ∧
      p / (n - 1) ≤ gammaInvariant n S) ∧
  (∀ T : Submodule ℝ (EVec 4), T ≤ centeredSubspace 4 → Module.finrank ℝ T = 1 →
    (∀ i, leverage T i = equalProfile4 i) → gammaInvariant 4 T = 1 / 3) ∧
  (∀ T : Submodule ℝ (EVec 4), T ≤ centeredSubspace 4 → Module.finrank ℝ T = 1 →
    (∀ i, leverage T i = middleProfile4 i) → gammaInvariant 4 T = 8 / 9) ∧
  (∀ T : Submodule ℝ (EVec 4), T ≤ centeredSubspace 4 → Module.finrank ℝ T = 1 →
    (∀ i, leverage T i = outlierProfile4 i) → gammaInvariant 4 T = 1)

-- @node: thm:admissibility-frontier
/-- Admissibility is equivalent to both spectral inequalities; the critical squared
quality is exactly the one-dimensional leverage-profile feasibility value, with the
sharp leverage/dimension bounds and equality characterization. -/
theorem admissibility_frontier
    (n : ℕ) (hn : 4 ≤ n) (hpar : Even n)
    (S : Submodule ℝ (EVec n)) (hSH : S ≤ centeredSubspace n)
    (hp0 : 1 ≤ Module.finrank ℝ S) (hp1 : Module.finrank ℝ S ≤ n - 1)
    (M : ℝ) (hM : 0 < M) :
    AdmissibilityFrontierStatement n S M := by
  sorry

end CausalSmith.Experimentation.PrognosticDesignAdmissibility
