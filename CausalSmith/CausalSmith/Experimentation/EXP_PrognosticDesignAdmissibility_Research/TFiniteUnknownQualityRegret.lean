/- Exact finite robust-SDP representation for unknown score quality. -/
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.Helpers.RegretRepresentation
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.TAdmissibilityFrontier
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.TExactOracleSaddle
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.TBalancedCovarianceRealizability

namespace CausalSmith.Experimentation.PrognosticDesignAdmissibility

open Causalean.Experimentation.DesignBased

/-- Number of balanced sign-pairs. -/
def signPairCount (n : ℕ) : ℕ := Nat.choose n (n / 2) / 2

/-- Probability simplex on `m` atoms. -/
def finiteSimplex (m : ℕ) : Set (Fin m → ℝ) :=
  {a | (∀ j, 0 ≤ a j) ∧ ∑ j, a j = 1}

/-- A list containing exactly one representative from every balanced sign-pair. -/
def SignPairRepresentatives {m n : ℕ} (rep : Fin m → Assignment n) : Prop :=
  (∀ j, IsBalanced (rep j)) ∧
  (∀ j k, rep j = rep k ∨ rep j = (fun i => !rep k i) → j = k) ∧
  ∀ z, IsBalanced z → ∃ j, z = rep j ∨ z = (fun i => !rep j i)

/-- `QH` has orthonormal columns spanning exactly the centered hyperplane. -/
def CenteredOrthonormalBasis
    (n : ℕ) (QH : Matrix (Fin n) (Fin (n - 1)) ℝ) : Prop :=
  QH.transpose * QH = 1 ∧ QH * QH.transpose = projHMat n

/-- Covariance represented by simplex weights on sign-pair representatives. -/
noncomputable def weightedCovariance {m n : ℕ} (rep : Fin m → Assignment n)
    (a : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ j, a j • signOuter (rep j)

/-- Exact finite robust semidefinite objective from the paper. -/
noncomputable def finiteRobustRegretValue {m n : ℕ}
    (rep : Fin m → Assignment n) (QH : Matrix (Fin n) (Fin (n - 1)) ℝ)
    (S : Submodule ℝ (EVec n)) : ℝ :=
  sInf {v | ∃ a ∈ finiteSimplex m,
    v = sSup {r | ∃ (u : EVec n) (b : Fin m → ℝ) (eta ell : ℝ),
      u ∈ centeredSubspace n ∧ ‖u‖ = 1 ∧ b ∈ finiteSimplex m ∧ 0 ≤ eta ∧
      (ell • (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ) -
        QH.transpose * (weightedCovariance rep b + eta • projMatrix S) * QH).PosSemidef ∧
      r = quadraticForm (weightedCovariance rep a) u +
        eta * ‖(S.orthogonalProjection u : EVec n)‖ ^ 2 - ell}}

/-- The finite program, outer attainment, universal bracket, equality family, and
the exact design-level quality-agnostic regret assertion. -/
noncomputable def FiniteUnknownQualityRegretStatement
    (n : ℕ) (S : Submodule ℝ (EVec n)) (M : ℝ) : Prop :=
  let p : ℝ := Module.finrank ℝ S
  (∀ (rep : Fin (signPairCount n) → Assignment n),
    SignPairRepresentatives rep →
    ∀ (QH : Matrix (Fin n) (Fin (n - 1)) ℝ),
    CenteredOrthonormalBasis n QH →
    minimaxRegret n S M * n / (4 * M) = finiteRobustRegretValue rep QH S ∧
    ∃ a ∈ finiteSimplex (signPairCount n),
      finiteRobustRegretValue rep QH S =
        sSup {r | ∃ (u : EVec n) (b : Fin (signPairCount n) → ℝ) (eta ell : ℝ),
          u ∈ centeredSubspace n ∧ ‖u‖ = 1 ∧
          b ∈ finiteSimplex (signPairCount n) ∧ 0 ≤ eta ∧
          (ell • (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ) -
            QH.transpose * (weightedCovariance rep b + eta • projMatrix S) * QH).PosSemidef ∧
          r = quadraticForm (weightedCovariance rep a) u +
            eta * ‖(S.orthogonalProjection u : EVec n)‖ ^ 2 - ell}) ∧
  p / (n - 1) * (cnConst n - kappaInvariant n S) ≤
    minimaxRegret n S M * n / (4 * M) ∧
  minimaxRegret n S M * n / (4 * M) ≤ cnConst n - kappaInvariant n S ∧
  crdCovariance n ∈ covarianceHull n ∧
  regretGap n (crdCovariance n) S = cnConst n - kappaInvariant n S ∧
  (kappaInvariant n S = cnConst n → minimaxRegret n S M = 0) ∧
  (∀ (B m : ℕ) (hB : 2 ≤ B) (P : Fin n → Fin B), ∀ hP : Function.Surjective P,
    0 < m → Even m → n = B * m →
    (∀ j, blockSize P j = m) →
    minimaxRegret n (partitionScoreSpace P hB hP) M * n / (4 * M) =
      ((B - 1 : ℕ) : ℝ) / (n - 1) *
        (cnConst n - kappaInvariant n (partitionScoreSpace P hB hP))) ∧
  (∃ Dreg ∈ balancedDesignSpace n, -- @realizes d_reg(quality-agnostic attaining design)
    sSup {r | ∃ rho ∈ Set.Icc (0 : ℝ) 1,
      r = designShellRisk n Dreg rho M S - oracleRisk n rho M S} = minimaxRegret n S M) ∧
  (∀ D ∈ balancedDesignSpace n,
    minimaxRegret n S M ≤ sSup {r | ∃ rho ∈ Set.Icc (0 : ℝ) 1,
      r = designShellRisk n D rho M S - oracleRisk n rho M S})

-- @node: thm:finite-unknown-quality-regret
/-- Unknown-quality regret has the exact finite robust-SDP value closure, an attained
outer minimum, the universal sharp bracket, and an implementable balanced design
with a matching converse over all single designs chosen without knowing quality. -/
theorem finite_unknown_quality_regret
    (n : ℕ) (hn : 4 ≤ n) (hpar : Even n)
    (S : Submodule ℝ (EVec n)) (hSH : S ≤ centeredSubspace n)
    (hp0 : 1 ≤ Module.finrank ℝ S)
    (M : ℝ) (hM : 0 < M) :
    FiniteUnknownQualityRegretStatement n S M := by
  sorry

end CausalSmith.Experimentation.PrognosticDesignAdmissibility
