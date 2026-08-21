/- Exact partition-orbit reduction and block closed forms. -/
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.Helpers.OrbitReduction
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.Helpers.BlockSpectrum
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.Helpers.HomogeneousBlocks
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.TAdmissibilityFrontier

namespace CausalSmith.Experimentation.PrognosticDesignAdmissibility

/-- The parity floor for a block-sum coordinate. -/
def parityFloor (m : ℕ) : ℝ := if Even m then 0 else 1

/-- Exact finite orbit reduction for an arbitrary genuine partition, including
attainment by a reduced moment matrix and an actual balanced design. -/
noncomputable def PartitionOrbitReduction {B n : ℕ} (P : Fin n → Fin B)
    (hB : 2 ≤ B) (hP : Function.Surjective P) : Prop :=
  ∀ rho ∈ Set.Icc (0 : ℝ) 1,
    oracleValue n rho (partitionScoreSpace P hB hP) =
      sInf {q | ∃ G, ∃ hG : G ∈ blockSumPolytope P,
        q = shellLoss (orbitCovariance P hB hP G hG)
          rho (partitionScoreSpace P hB hP)} ∧
    (∃ G, ∃ hG : G ∈ blockSumPolytope P,
      oracleValue n rho (partitionScoreSpace P hB hP) =
        shellLoss (orbitCovariance P hB hP G hG) rho (partitionScoreSpace P hB hP) ∧
      ∃ D ∈ balancedDesignSpace n,
        designCovariance D = orbitCovariance P hB hP G hG) ∧
    (∀ G, ∀ hG : G ∈ blockSumPolytope P,
      orbitCovariance P hB hP G hG ∈ covarianceHull n ∧
      ∃ D ∈ balancedDesignSpace n,
        designCovariance D = orbitCovariance P hB hP G hG) ∧
    (∀ A ∈ covarianceHull n, ∃ G, ∃ hG : G ∈ blockSumPolytope P,
      shellLoss (orbitCovariance P hB hP G hG)
          rho (partitionScoreSpace P hB hP) ≤
        shellLoss A rho (partitionScoreSpace P hB hP))

/-- Unequal two-block oracle, threshold, and regret formulas, including the forced
singleton-block case and an attaining CRD/parity-endpoint mixture. -/
noncomputable def UnequalTwoBlockFrontier (n : ℕ) (P : Fin n → Fin 2)
    (hP : Function.Surjective P) (M : ℝ) : Prop :=
  let hB : 2 ≤ 2 := by decide
  let SP := partitionScoreSpace P hB hP
  let m := min (blockSize P 0) (blockSize P 1)
  let ell := max (blockSize P 0) (blockSize P 1)
  let e := parityFloor m
  let kappa2 : ℝ := (n : ℝ) * e / ((m : ℝ) * ell)
  let b0 : ℝ := ((m : ℝ) ^ 2 - e) / ((m : ℝ) * (m - 1))
  let s0 : ℝ := (ell : ℝ) / ((m : ℝ) * (n - 1))
  let qc : ℝ := (m : ℝ) * ell / (n - 1)
  let optimum := s0 * (cnConst n - kappa2)
  {q : ℝ | ∃ G ∈ blockSumPolytope P, q = G 0 0} = Set.Icc e ((m : ℝ) ^ 2) ∧
  (m = 1 →
    (∀ rho ∈ Set.Icc (0 : ℝ) 1,
      oracleValue n rho SP = cnConst n) ∧
    kappaInvariant n SP = cnConst n ∧
    gammaInvariant n SP = 1 ∧
    criticalQuality n M SP = 1 ∧
    minimaxRegret n SP M = 0) ∧
  (1 < m → m < ell →
    (Even (blockSize P 0) ↔ Even (blockSize P 1)) ∧
    (∀ rho ∈ Set.Icc (0 : ℝ) 1,
      oracleValue n rho SP =
        min (cnConst n) ((1 - rho ^ 2) * b0 + rho ^ 2 * kappa2)) ∧
    kappaInvariant n SP = kappa2 ∧
    gammaInvariant n SP = s0 ∧
    criticalQuality n M SP = Real.sqrt s0 ∧
    sInf {r | ∃ A ∈ covarianceHull n,
      r = regretGap n A SP} = optimum ∧
    minimaxRegret n SP M = (4 * M / n) * optimum ∧
    ∃ Gcrd, ∃ hGcrd : Gcrd ∈ blockSumPolytope P,
      Gcrd 0 0 = qc ∧ orbitCovariance P hB hP Gcrd hGcrd = crdCovariance n ∧
      (∀ rho ∈ Set.Icc (0 : ℝ) 1,
        shellLoss (orbitCovariance P hB hP Gcrd hGcrd) rho SP = cnConst n) ∧
      (∃ Dcrd ∈ balancedDesignSpace n,
        designCovariance Dcrd = orbitCovariance P hB hP Gcrd hGcrd) ∧
    ∃ rEnd ∈ blockSumLattice P,
    ∃ Gend, ∃ hGend : Gend ∈ blockSumPolytope P,
      Gend = blockSumOuter rEnd ∧ (rEnd 0 : ℝ) ^ 2 = e ∧ Gend 0 0 = e ∧
      (∀ rho ∈ Set.Icc (0 : ℝ) 1,
        shellLoss (orbitCovariance P hB hP Gend hGend) rho SP =
          (1 - rho ^ 2) * b0 + rho ^ 2 * kappa2) ∧
      (∃ Dend ∈ balancedDesignSpace n,
        designCovariance Dend = orbitCovariance P hB hP Gend hGend) ∧
    ∃ Greg, ∃ hGreg : Greg ∈ blockSumPolytope P,
      Greg = (1 - s0) • Gend + s0 • Gcrd ∧
      Greg 0 0 = (1 - s0) * e + s0 * qc ∧
      orbitCovariance P hB hP Greg hGreg =
        s0 • crdCovariance n + (1 - s0) • orbitCovariance P hB hP Gend hGend ∧
      regretGap n (orbitCovariance P hB hP Greg hGreg) SP = optimum ∧
      shellLoss (orbitCovariance P hB hP Greg hGreg) 0 SP - oracleValue n 0 SP = optimum ∧
      shellLoss (orbitCovariance P hB hP Greg hGreg) 1 SP - oracleValue n 1 SP = optimum ∧
      ∀ A ∈ covarianceHull n, optimum ≤
        max (shellLoss A 0 SP - oracleValue n 0 SP)
          (shellLoss A 1 SP - oracleValue n 1 SP))

/-- Closed forms for every homogeneous even-block partition. -/
noncomputable def HomogeneousEvenBlockFrontier {B n : ℕ}
    (P : Fin n → Fin B) (hB : 2 ≤ B) (hP : Function.Surjective P) (M : ℝ) : Prop :=
  ∀ m, 0 < m → Even m → n = B * m → (∀ j, blockSize P j = m) →
    let SP := partitionScoreSpace P hB hP
    let p : ℝ := B - 1
    let h : ℝ := n - B
    let delta : ℝ := n / h
    let beta : ℝ := p / (n - 1)
    (∀ rho ∈ Set.Icc (0 : ℝ) 1,
      oracleValue n rho SP =
        min (cnConst n) (delta * (1 - rho ^ 2))) ∧
    kappaInvariant n SP = 0 ∧
    gammaInvariant n SP = beta ∧
    criticalQuality n M SP = Real.sqrt beta ∧
    sInf {r | ∃ A ∈ covarianceHull n,
      r = regretGap n A SP} = (n : ℝ) * p / (n - 1) ^ 2 ∧
    minimaxRegret n SP M = 4 * M * p / (n - 1) ^ 2 ∧
    ∃ Awithin ∈ covarianceHull n,
      Awithin = delta • (projHMat n - projMatrix SP) ∧
      (∃ Dwithin ∈ balancedDesignSpace n, designCovariance Dwithin = Awithin) ∧
      let Amix := beta • crdCovariance n + (1 - beta) • Awithin
      Amix ∈ covarianceHull n ∧
      regretGap n Amix SP = (n : ℝ) * p / (n - 1) ^ 2 ∧
      shellLoss Amix 0 SP - oracleValue n 0 SP = (n : ℝ) * p / (n - 1) ^ 2 ∧
      shellLoss Amix 1 SP - oracleValue n 1 SP = (n : ℝ) * p / (n - 1) ^ 2

/-- Full partition theorem, including parity classification and all claimed closed
forms while leaving general unequal partitions at the exact finite polytope program. -/
noncomputable def PairSpaceExactFrontierStatement {B n : ℕ}
    (P : Fin n → Fin B) (hB : 2 ≤ B) (hP : Function.Surjective P)
    (hn : 4 ≤ n) (hpar : Even n) (M : ℝ) : Prop :=
  PartitionOrbitReduction P hB hP ∧
  (kappaInvariant n (partitionScoreSpace P hB hP) = 0 ↔ ∀ j, Even (blockSize P j)) ∧
  (∀ hB2 : B = 2, UnequalTwoBlockFrontier n (hB2 ▸ P) (by cases hB2; exact hP) M) ∧
  HomogeneousEvenBlockFrontier P hB hP M ∧
  (∀ rho ∈ Set.Icc (0 : ℝ) 1,
    oracleValue n rho (pairScoreSpace n hn hpar) = min (cnConst n) (2 * (1 - rho ^ 2))) ∧
  kappaInvariant n (pairScoreSpace n hn hpar) = 0 ∧
  gammaInvariant n (pairScoreSpace n hn hpar) = (n - 2 : ℕ) / (2 * (n - 1 : ℕ)) ∧
  criticalQuality n M (pairScoreSpace n hn hpar) =
    Real.sqrt ((n - 2 : ℕ) / (2 * (n - 1 : ℕ)))

-- @node: lem:pair-space-exact-frontier
/-- Within-block orbit averaging is exact for every partition; parity characterizes
zero perfect-quality loss, with the stated unequal-two-block, homogeneous-even-block,
and matched-pair oracle and regret formulas. -/
lemma pair_space_exact_frontier
    (n B : ℕ) (hn : 4 ≤ n) (hpar : Even n) (hB : 2 ≤ B)
    (P : Fin n → Fin B) (hP : Function.Surjective P)
    (M : ℝ) (hM : 0 < M) :
    PairSpaceExactFrontierStatement P hB hP hn hpar M := by
  sorry

end CausalSmith.Experimentation.PrognosticDesignAdmissibility
