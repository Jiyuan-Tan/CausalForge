/- Exact matched-pair oracle and unknown-quality regret corollary. -/
import Causalean.Experimentation.MatchedPairDesign.MatchedPair
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.TPairSpaceExactFrontier
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.TBalancedCovarianceRealizability

namespace CausalSmith.Experimentation.PrognosticDesignAdmissibility

/-- Matched-pair mixing weight. -/
noncomputable def pairMixWeight (n : ℕ) : ℝ := (n - 2 : ℕ) / (2 * (n - 1 : ℕ))

/-- Covariance of the CRD/within-pair mixture. -/
noncomputable def pairMixCovariance
    (n : ℕ) (hn : 4 ≤ n) (hpar : Even n) : Matrix (Fin n) (Fin n) ℝ :=
  pairMixWeight n • crdCovariance n +
    (1 - pairMixWeight n) • (2 • (projHMat n - projMatrix (pairScoreSpace n hn hpar)))

/-- Representatives of the three balanced sign-pairs at `n = 4`; coordinate zero
is the pair omitted by independent within-pair orientations. -/
def fourPairRepresentative : Fin 3 → Assignment 4
  | 0 => ![true, true, false, false]
  | 1 => ![true, false, true, false]
  | 2 => ![true, false, false, true]

/-- Covariance represented by weights on the three four-unit sign-pairs. -/
noncomputable def fourPairWeightedCovariance (w : Fin 3 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  ∑ j, w j • signOuter (fourPairRepresentative j)

/-- The three assignments above are exactly one representative per balanced
four-unit sign-pair. -/
def FourPairRepresentativeProperty : Prop :=
  (∀ j, IsBalanced (fourPairRepresentative j)) ∧
  (∀ j k, fourPairRepresentative j = fourPairRepresentative k ∨
      fourPairRepresentative j = (fun i => !fourPairRepresentative k i) → j = k) ∧
  ∀ z, IsBalanced z → ∃ j,
    z = fourPairRepresentative j ∨ z = (fun i => !fourPairRepresentative j i)

/-- Complete matched-pair corollary, including both binding endpoint regrets and the
explicit four-unit sign-pair weights. -/
noncomputable def ExactPairSpaceRegretStatement
    (n : ℕ) (hn : 4 ≤ n) (hpar : Even n) (M : ℝ) : Prop :=
  let SP := pairScoreSpace n hn hpar
  let Amix := pairMixCovariance n hn hpar
  let optimum : ℝ := (n : ℝ) * (n - 2 : ℕ) / (2 * (n - 1 : ℕ) ^ 2)
  (∃ k, n = 2 * k) ∧
  (∀ rho ∈ Set.Icc (0 : ℝ) 1,
    oracleValue n rho SP = min (cnConst n) (2 * (1 - rho ^ 2))) ∧
  kappaInvariant n SP = 0 ∧
  gammaInvariant n SP = pairMixWeight n ∧
  criticalQuality n M SP = Real.sqrt (pairMixWeight n) ∧
  Amix ∈ covarianceHull n ∧
  sInf {r | ∃ A ∈ covarianceHull n, r = regretGap n A SP} = optimum ∧
  minimaxRegret n SP M = 2 * M * (n - 2 : ℕ) / (n - 1 : ℕ) ^ 2 ∧
  regretGap n Amix SP = optimum ∧
  shellLoss Amix 0 SP - oracleValue n 0 SP = optimum ∧
  shellLoss Amix 1 SP - oracleValue n 1 SP = optimum ∧
  pairMixWeight 4 = 1 / 3 ∧
  FourPairRepresentativeProperty ∧
  (∃ w : Fin 3 → ℝ,
    w = ![(1 : ℝ) / 9, 4 / 9, 4 / 9] ∧
    (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧
    w 0 = 1 / 9 ∧ pairDesign4.p (fourPairRepresentative 0) = 0 ∧
    fourPairWeightedCovariance w = pairMixCovariance 4 (by decide) (by decide) ∧
    ∃ D ∈ balancedDesignSpace 4,
      designCovariance D = fourPairWeightedCovariance w) ∧
  regretGap 4 (pairMixCovariance 4 (by decide) (by decide)) scoreSpace4 = 4 / 9 ∧
  shellLoss (pairMixCovariance 4 (by decide) (by decide)) 0 scoreSpace4 -
      oracleValue 4 0 scoreSpace4 = 4 / 9 ∧
  shellLoss (pairMixCovariance 4 (by decide) (by decide)) 1 scoreSpace4 -
      oracleValue 4 1 scoreSpace4 = 4 / 9 ∧
  sInf {r | ∃ A ∈ covarianceHull 4, r = regretGap 4 A scoreSpace4} = 4 / 9 ∧
  minimaxRegret 4 scoreSpace4 M = 4 * M / 9

-- @node: thm:exact-pair-space-regret
/-- Matched pairs have the exact two-branch oracle frontier and the displayed
quality-agnostic CRD/pair mixture, exact regret, and four-unit weights. -/
theorem exact_pair_space_regret
    (n : ℕ) (hn : 4 ≤ n) (hpar : Even n) (M : ℝ) (hM : 0 < M) :
    ExactPairSpaceRegretStatement n hn hpar M := by
  sorry

end CausalSmith.Experimentation.PrognosticDesignAdmissibility
