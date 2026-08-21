/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Prognostic-score design admissibility: shared definitions

This cold Stage-2 scaffold formalizes the finite-design and Euclidean worlds used by
the paper.  The sampling layer reuses `FiniteDesign`; the covariance hull and score
geometry are paper-local Mathlib constructions.

## Substrate survey

* `Causalean.Experimentation.DesignBased.DesignCore` and `PotentialOutcome` are reused
  for finite PMFs, finite-sum moments, and exposure-based consistency.
* HT and complete-randomization results are bypass-justified because their carriers
  describe one inverse-propensity or fixed-count design, whereas this paper ranges
  over every mean-zero law on balanced Boolean assignments.
* Causalean's finite `DesignFamily` optimality layer is bypass-justified because the
  present design variable ranges over the continuum-valued covariance convex hull.
* The superpopulation `Causalean.PO` layer is bypass-justified: assignment is the only
  random object here.
* Matrix spectrahedra, convex hulls, projectors, and Rayleigh suprema are implemented
  over Mathlib; the substrate survey found no Causalean elliptope or restricted-top-
  eigenvalue primitive.
-/

import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Causalean.Experimentation.DesignBased.DesignCore
import Causalean.Experimentation.DesignBased.PotentialOutcome
import Causalean.Experimentation.DesignBased.Risk

namespace CausalSmith.Experimentation.PrognosticDesignAdmissibility

open Causalean.Experimentation.DesignBased
open scoped BigOperators Matrix

abbrev Assignment (n : ℕ) := Fin n → Bool
abbrev EVec (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-! ## Shared environments -/

-- @env: S1
-- @env: S2
variable {n : ℕ} (hn : 4 ≤ n) (hpar : Even n)
-- @realizes n(carrier ℕ; constrained by 4 ≤ n and Even n)

/-- Convert a Boolean assignment to its `±1` sign vector.
@realizes z(random balanced assignment carrier `Fin n → Bool`)
@realizes treatment_label(Boolean treatment label; true=treatment, false=control) -/
def signOf (z : Assignment n) : Fin n → ℝ := fun i => if z i then 1 else -1

/-- Sign vector as an element of Euclidean space. -/
def signVector (z : Assignment n) : EVec n := WithLp.toLp 2 (signOf z)

/-- The all-ones vector.
@realizes one_n(all-ones vector in ℝ^n) -/
def onesVec (n : ℕ) : EVec n := WithLp.toLp 2 (fun _ => 1)

/-- The identity matrix.
@realizes I_n(identity matrix in ℝ^(n×n)) -/
def identityMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := 1

/-- Euclidean basis vector. -/
def basisVec (j : Fin n) : EVec n := WithLp.toLp 2 (fun i => if i = j then 1 else 0)

/-- Matrix action on Euclidean vectors. -/
noncomputable def matrixAction (A : Matrix (Fin n) (Fin n) ℝ) (x : EVec n) : EVec n :=
  WithLp.toLp 2 (A.mulVec x)

/-- Euclidean quadratic form `xᵀAx`. -/
noncomputable def quadraticForm (A : Matrix (Fin n) (Fin n) ℝ) (x : EVec n) : ℝ :=
  ∑ i, x i * (A.mulVec x) i

/-- Rank-one outer product of a Euclidean vector. -/
def vectorOuter (x : EVec n) : Matrix (Fin n) (Fin n) ℝ := fun i j => x i * x j

/-- The centered hyperplane `H_n = {x : ∑ i, x i = 0}`.
@realizes H_n(centered subspace orthogonal to one_n) -/
def centeredSubspace (n : ℕ) : Submodule ℝ (EVec n) where
  carrier := {x | ∑ i, x i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change ∑ i, x i = 0 at hx
    change ∑ i, y i = 0 at hy
    change ∑ i, (x + y) i = 0
    simp [Finset.sum_add_distrib, hx, hy]
  smul_mem' := by
    intro c x hx
    change ∑ i, x i = 0 at hx
    change ∑ i, (c • x) i = 0
    rw [show (∑ i, (c • x) i) = c * ∑ i, x i by simp [Finset.mul_sum]]
    simp [hx]

/-- Matrix of the orthogonal projector onto a subspace.
@realizes P_S(orthogonal projector onto score subspace S)
@realizes S(carrier: real linear subspace of H_n; containment threaded in statements) -/
noncomputable def projMatrix (S : Submodule ℝ (EVec n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (S.orthogonalProjection (basisVec j) : EVec n) i

/-- The centering projector `P_H`.
@realizes P_H(orthogonal projector onto H_n) -/
noncomputable def projHMat (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  projMatrix (centeredSubspace n)

/-! ## Assumption atoms and finite-population quantities -/

-- @node: ass:fixed-potential-outcomes
/-- Potential outcomes do not vary with the assignment law. -/
def FixedPotentialOutcomes
    (Y : Fin n → Bool → Assignment n → ℝ) : Prop :=
  ∀ i a z z', Y i a z = Y i a z'

/-- The fixed potential-outcome array extracted at a canonical assignment.
@realizes y_i_a(fixed real potential outcome y_i(a)) -/
def fixedOutcome (Y : Fin n → Bool → Assignment n → ℝ) : Fin n → Bool → ℝ :=
  fun i a => Y i a (fun _ => false)

-- @node: ass:consistency-no-interference
/-- Consistency and no interference for the assignment-indexed potential-outcome
array.  Together with `FixedPotentialOutcomes`, this derives Causalean's
`ProperlySpecified` predicate for `fixedOutcome`.
@realizes Y_i_obs(observed real response depends only on own treatment) -/
def ConsistencyNoInterference
    (Y : Fin n → Bool → Assignment n → ℝ)
    (yr : Fin n → Assignment n → ℝ) : Prop :=
  ∀ i z, yr i z = fixedOutcome Y i (z i)

/-- The sample average treatment effect.
@realizes tau_n(n⁻¹ sum of y_i(1)-y_i(0)) -/
noncomputable def sate (Y : Fin n → Bool → Assignment n → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, (fixedOutcome Y i true - fixedOutcome Y i false)

/-- The balanced difference-in-means estimator.
@realizes hat_tau_d(2n⁻¹ sum z_i Y_i_obs) -/
noncomputable def diffInMeans (yr : Fin n → Assignment n → ℝ) (z : Assignment n) : ℝ :=
  2 * (n : ℝ)⁻¹ * ∑ i, signOf z i * yr i z

/-- Centered average-potential-outcome vector.
@realizes mu(P_H applied to m_i=(y_i(1)+y_i(0))/2) -/
noncomputable def centeredOutcomeMean
    (Y : Fin n → Bool → Assignment n → ℝ) : EVec n :=
  (centeredSubspace n).orthogonalProjection
    (WithLp.toLp 2 (fun i => (fixedOutcome Y i true + fixedOutcome Y i false) / 2))

/-! ## Balanced design and covariance hull -/

/-- Exact treatment-control balance.
@realizes Z_n(set of ±1 assignments whose coordinate sum is zero) -/
def IsBalanced (z : Assignment n) : Prop := ∑ i, signOf z i = 0

/-- The finite balanced assignment set. -/
def balancedAssignments (n : ℕ) : Set (Assignment n) := {z | IsBalanced z}

-- @node: def:balanced-design-space
/-- The class `D_n` of PMFs supported on balanced assignments and having zero
coordinate means.
@realizes Delta_Z_n(probability simplex carried by FiniteDesign with balanced support)
@realizes d(assignment distribution selected before outcomes)
@realizes D_n(balanced, mean-zero design class) -/
def balancedDesignSpace (n : ℕ) : Set (FiniteDesign (Assignment n)) :=
  {D | (∀ z, D.p z ≠ 0 → IsBalanced z) ∧ ∀ i, D.E (fun z => signOf z i) = 0}

/-- Outer product of a sign vector. -/
def signOuter (z : Assignment n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => signOf z i * signOf z j

/-- Covariance/second moment induced by a design.
@realizes A_d(E_d[zzᵀ], equal to covariance on D_n) -/
noncomputable def designCovariance (D : FiniteDesign (Assignment n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => D.E (fun z => signOf z i * signOf z j)

-- @node: def:covariance-hull
/-- Exact convex hull of balanced sign outer products.
@realizes C_n(convex hull of zzᵀ for z in Z_n) -/
def covarianceHull (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  convexHull ℝ (signOuter '' balancedAssignments n)

/-! ## Score quality, lifted adversary, and oracle risk -/

/-- Realized score quality `‖P_S μ‖/‖μ‖`.
@realizes rho_mu(norm ratio in [0,1] for nonzero mu in H_n) -/
noncomputable def realizedQuality (S : Submodule ℝ (EVec n))
    (_hSH : S ≤ centeredSubspace n) (mu : EVec n)
    (_hmuH : mu ∈ centeredSubspace n) (_hmu0 : mu ≠ 0) : ℝ :=
  ‖(S.orthogonalProjection mu : EVec n)‖ / ‖mu‖

-- @node: def:realized-score-quality
/-- A paper-domain quality lower bound: `rho` is in `[0,1]`, `S` is centered,
and the specified nonzero centered outcome vector has realized quality at least `rho`. -/
def RealizedQualityAtLeast (S : Submodule ℝ (EVec n)) (mu : EVec n) (rho : ℝ) : Prop :=
  ∃ hSH : S ≤ centeredSubspace n, ∃ hmuH : mu ∈ centeredSubspace n, ∃ hmu0 : mu ≠ 0,
    rho ∈ Set.Icc (0 : ℝ) 1 ∧ realizedQuality S hSH mu hmuH hmu0 ≥ rho

-- @node: def:score-quality-shell
/-- The nonconvex score-quality shell.
@realizes rho(free quality lower bound; range [0,1] threaded in statements)
@realizes M(positive energy scale; positivity threaded in statements)
@realizes Y_rho_M_S(centered spherical shell with score-energy lower bound) -/
def qualityShell (rho M : ℝ) (S : Submodule ℝ (EVec n)) : Set (EVec n) :=
  {mu | rho ∈ Set.Icc (0 : ℝ) 1 ∧ -- @realizes rho(range [0,1])
    0 < M ∧ -- @realizes M(strictly positive outcome-energy scale)
    mu ∈ centeredSubspace n ∧ ‖mu‖ ^ 2 = n * M ∧
    rho ^ 2 * ‖mu‖ ^ 2 ≤ ‖(S.orthogonalProjection mu : EVec n)‖ ^ 2}

-- @node: def:lifted-adversary
/-- Rank-free lifted score-quality spectrahedron.
@realizes X_rho_S(PSD, centered, trace-one spectrahedron with score trace at least rho²) -/
def liftedAdversary (rho : ℝ) (S : Submodule ℝ (EVec n)) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  {X | X.PosSemidef ∧ X = projHMat n * X * projHMat n ∧ X.trace = 1 ∧
    rho ^ 2 ≤ (projMatrix S * X).trace}

/-- Restricted Rayleigh supremum. -/
noncomputable def lambdaMaxOn (A : Matrix (Fin n) (Fin n) ℝ)
    (L : Submodule ℝ (EVec n)) : ℝ :=
  sSup {r | ∃ u : EVec n, u ∈ L ∧ ‖u‖ = 1 ∧ r = quadraticForm A u}

/-- Worst normalized quadratic loss on the quality shell.
@realizes q_rho(maximum Rayleigh loss over centered unit vectors satisfying score quality) -/
noncomputable def shellLoss (A : Matrix (Fin n) (Fin n) ℝ) (rho : ℝ)
    (S : Submodule ℝ (EVec n)) : ℝ :=
  sSup {r | ∃ u : EVec n, u ∈ centeredSubspace n ∧ ‖u‖ = 1 ∧
    rho ^ 2 ≤ ‖(S.orthogonalProjection u : EVec n)‖ ^ 2 ∧ r = quadraticForm A u}

/-- The normalized oracle minimax value.
@realizes v_star(minimum of q_rho over C_n) -/
noncomputable def oracleValue (n : ℕ) (rho : ℝ) (S : Submodule ℝ (EVec n)) : ℝ :=
  sInf {q | ∃ A ∈ covarianceHull n, q = shellLoss A rho S}

-- @node: def:oracle-risk
/-- Exact SATE minimax risk.
@realizes V_star((4M/n) times v_star) -/
noncomputable def oracleRisk (n : ℕ) (rho M : ℝ) (S : Submodule ℝ (EVec n)) : ℝ :=
  (4 * M / n) * oracleValue n rho S

/-- Complete-randomization benchmark risk.
@realizes V_CRD(4M/(n-1)) -/
noncomputable def crdRisk (n : ℕ) (M : ℝ) : ℝ := 4 * M / (n - 1)

/-- Complete-randomization spectral constant.
@realizes c_n(n/(n-1), with range >1 from ambient n constraints) -/
noncomputable def cnConst (n : ℕ) : ℝ := n / (n - 1)

/-- Complete-randomization covariance.
@realizes A_CRD(c_n P_H, a member of C_n by later theorem) -/
noncomputable def crdCovariance (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  cnConst n • projHMat n

/-! ## Admissibility and regret -/

/-- Compressed top eigenvalue. -/
noncomputable def compressedLambdaMax (A : Matrix (Fin n) (Fin n) ℝ)
    (S : Submodule ℝ (EVec n)) : ℝ :=
  lambdaMaxOn (projMatrix S * A * projMatrix S) S

/-- Perfect-quality compressed spectral value.
@realizes kappa_S(minimum compressed top eigenvalue over C_n) -/
noncomputable def kappaInvariant (n : ℕ) (S : Submodule ℝ (EVec n)) : ℝ :=
  sInf {t | ∃ A ∈ covarianceHull n, t = compressedLambdaMax A S}

/-- Critical squared-quality slope invariant.
@realizes gamma_S(infimum positive-multiplier slope relative to c_n) -/
noncomputable def gammaInvariant (n : ℕ) (S : Submodule ℝ (EVec n)) : ℝ :=
  sInf {t | ∃ A ∈ covarianceHull n, ∃ eta > 0,
    t = (lambdaMaxOn (A + eta • projMatrix S) (centeredSubspace n) - cnConst n) / eta}

-- @node: def:admissibility-invariants
/-- The paired admissibility invariants `(κ(S), γ(S))` from the paper. -/
noncomputable def admissibilityInvariants (n : ℕ) (S : Submodule ℝ (EVec n)) : ℝ × ℝ :=
  (kappaInvariant n S, gammaInvariant n S)

/-- Admissible score subspaces.
@realizes A_n(subspaces of H_n improving on CRD for some rho<1) -/
noncomputable def admissibleFamily (n : ℕ) (M : ℝ) : Set (Submodule ℝ (EVec n)) :=
  {S | S ≤ centeredSubspace n ∧ ∃ rho ∈ Set.Ico (0 : ℝ) 1,
    oracleRisk n rho M S < crdRisk n M}

/-- Critical score quality, with value one when the improving set is empty.
@realizes rho_star_S(infimum improving rho in [0,1], defaulting to 1) -/
noncomputable def criticalQuality (n : ℕ) (M : ℝ) (S : Submodule ℝ (EVec n)) : ℝ :=
  sInf ({rho | rho ∈ Set.Icc (0 : ℝ) 1 ∧ oracleRisk n rho M S < crdRisk n M} ∪ {1})

/-- Normalized additive oracle regret.
@realizes Delta_reg(sup over rho in [0,1] of q_rho(A)-v_star(rho)) -/
noncomputable def regretGap (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (S : Submodule ℝ (EVec n)) : ℝ :=
  sSup {r | ∃ rho ∈ Set.Icc (0 : ℝ) 1, r = shellLoss A rho S - oracleValue n rho S}

-- @node: def:regret-object
/-- Finite-population minimax additive regret.
@realizes R_star((4M/n) times the minimum regret gap over C_n) -/
noncomputable def minimaxRegret (n : ℕ) (S : Submodule ℝ (EVec n)) (M : ℝ) : ℝ :=
  (4 * M / n) * sInf {r | ∃ A ∈ covarianceHull n, r = regretGap n A S}

/-- Finite-multiplier spectral regret handle. -/
noncomputable def spectralRegretHandle (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (S : Submodule ℝ (EVec n)) (s eta : ℝ) : ℝ :=
  lambdaMaxOn (A + eta • projMatrix S) (centeredSubspace n) - eta * s

/-- Value closure adding the perfect-quality infinite-multiplier endpoint. -/
noncomputable def compactifiedDual (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (S : Submodule ℝ (EVec n)) (s : ℝ) : ℝ :=
  if s = 1 then
    min (sInf {v | ∃ eta ≥ 0, v = spectralRegretHandle n A S s eta})
      (compressedLambdaMax A S)
  else sInf {v | ∃ eta ≥ 0, v = spectralRegretHandle n A S s eta}

/-- Balanced-cut-hull support oracle used by the finite active-face formulation. -/
noncomputable def balancedCutSupportOracle (n : ℕ)
    (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf {v | ∃ z, IsBalanced z ∧ v = quadraticForm X (signVector z)}

/-- The exact finite-multiplier regret epigraph.  Membership records `A ∈ C_n`,
uses `s = rho²` for `rho ∈ [0,1]`, and evaluates the scalar dual through its
`h = (1+eta)⁻¹ = 0` boundary closure. -/
def spectralRegretEpigraph (n : ℕ) (S : Submodule ℝ (EVec n)) :
    Set (Matrix (Fin n) (Fin n) ℝ × ℝ) :=
  {At | At.1 ∈ covarianceHull n ∧
    ∀ rho ∈ Set.Icc (0 : ℝ) 1,
      compactifiedDual n At.1 S (rho ^ 2) - oracleValue n rho S ≤ At.2}

-- @node: def:regret-handle
/-- The compactified regret-epigraph value, scaled to the paper's `R*(n,S)` units.
The finite balanced-cut support oracle above supplies the active-simplex algebraic
handle; no finite optimizer in the multiplier is asserted at perfect quality. -/
noncomputable def compactifiedRegretProgram
    (n : ℕ) (S : Submodule ℝ (EVec n)) (M : ℝ) : ℝ :=
  (4 * M / n) * sInf {t | ∃ A, (A, t) ∈ spectralRegretEpigraph n S}

/-! ## Partition score spaces -/

/-- Centered block-constant score subspace for a labelled partition.
@realizes S_partition(block-constant linear subspace of H_n) -/
def partitionScoreSpace {B : ℕ} (P : Fin n → Fin B)
    (_hB : 2 ≤ B) (_hP : Function.Surjective P) : Submodule ℝ (EVec n) where
  carrier := {x | x ∈ centeredSubspace n ∧ ∀ i i', P i = P i' → x i = x i'}
  zero_mem' := by simp [centeredSubspace]
  add_mem' := by
    intro x y hx hy
    constructor
    · exact (centeredSubspace n).add_mem hx.1 hy.1
    · intro i i' hii
      simp [hx.2 i i' hii, hy.2 i i' hii]
  smul_mem' := by
    intro c x hx
    constructor
    · exact (centeredSubspace n).smul_mem c hx.1
    · intro i i' hii
      simp [hx.2 i i' hii]

/-- Equal-block score space induced by the canonical quotient labelling.
@realizes S_B(homogeneous equal-block specialization) -/
def homogeneousBlockScoreSpace {B : ℕ} (P : Fin n → Fin B)
    (hB : 2 ≤ B) (hP : Function.Surjective P) (m : ℕ)
    (_hm : 0 < m) (_hmeven : Even m)
    (_hsize : ∀ j, (Finset.univ.filter fun i => P i = j).card = m) :
    Submodule ℝ (EVec n) :=
  partitionScoreSpace P hB hP

/-- Matched-pair block-constant centered subspace.
@realizes S_pair(pair partition: coordinates with equal quotient by two) -/
def pairScoreSpace (n : ℕ) (_hn : 4 ≤ n) (_hpar : Even n) : Submodule ℝ (EVec n) where
  carrier := {x | x ∈ centeredSubspace n ∧
    ∀ i i' : Fin n, i.val / 2 = i'.val / 2 → x i = x i'}
  zero_mem' := by simp [centeredSubspace]
  add_mem' := by
    intro x y hx hy
    constructor
    · exact (centeredSubspace n).add_mem hx.1 hy.1
    · intro i i' hii
      simp [hx.2 i i' hii, hy.2 i i' hii]
  smul_mem' := by
    intro c x hx
    constructor
    · exact (centeredSubspace n).smul_mem c hx.1
    · intro i i' hii
      simp [hx.2 i i' hii]

-- @node: def:pair-score-space
/-- The paper's three linked partition geometries: a genuine partition with at least
two nonempty blocks, its homogeneous equal-positive-even-block specialization, and
the canonical matched-pair specialization for even `n ≥ 4`. -/
def partitionScoreGeometry {B : ℕ} (P : Fin n → Fin B)
    (hB : 2 ≤ B) (hP : Function.Surjective P)
    {Bh : ℕ} (Ph : Fin n → Fin Bh) (hBh : 2 ≤ Bh) (hPh : Function.Surjective Ph)
    (m : ℕ) (hm : 0 < m) (hmeven : Even m) (_hnBhm : n = Bh * m)
    (hsize : ∀ j, (Finset.univ.filter fun i => Ph i = j).card = m)
    (hn : 4 ≤ n) (hpar : Even n) :
    Submodule ℝ (EVec n) × Submodule ℝ (EVec n) × Submodule ℝ (EVec n) :=
  (partitionScoreSpace P hB hP,
    homogeneousBlockScoreSpace Ph hBh hPh m hm hmeven hsize,
    pairScoreSpace n hn hpar)

/-! ## Four-unit worked construction -/

/-- Four explicit balanced assignments used by the pair design. -/
def pairAssignments4 : Fin 4 → Assignment 4
  | 0 => ![true, false, true, false]
  | 1 => ![false, true, false, true]
  | 2 => ![true, false, false, true]
  | 3 => ![false, true, true, false]

/-- Four-unit score vector.
@realizes u_4((1,1,-1,-1)/2) -/
noncomputable def u4 : EVec 4 := WithLp.toLp 2 ![(1 : ℝ) / 2, 1 / 2, -1 / 2, -1 / 2]

/-- Four-unit score line.
@realizes S_4(span of u_4, the n=4 pair-score instance) -/
noncomputable def scoreSpace4 : Submodule ℝ (EVec 4) := Submodule.span ℝ {u4}

/-- Uniform law on the four stated balanced assignments.
@realizes d_pair_4(probability 1/4 on each of the two sign-pairs) -/
noncomputable def pairDesign4 : FiniteDesign (Assignment 4) where
  p := fun z => ∑ k : Fin 4, if z = pairAssignments4 k then (1 : ℝ) / 4 else 0
  p_nonneg := by
    intro z
    exact Finset.sum_nonneg (fun k _ => by split_ifs <;> norm_num)
  p_sum := by
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq']

/-- Covariance of the four-unit pair design.
@realizes A_pair_4(explicit two-pair covariance matrix) -/
def covPair4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(1 : ℝ), -1, 0, 0;
     -1, 1, 0, 0;
     0, 0, 1, -1;
     0, 0, -1, 1]

-- @node: def:four-unit-score-mixture
/-- The complete four-unit construction, including its score vector and line, the
four-point design law, and the asserted design-covariance identity. -/
noncomputable def FourUnitScoreMixture : Prop :=
  scoreSpace4 = Submodule.span ℝ {u4} ∧
    designCovariance pairDesign4 = covPair4 ∧
    pairDesign4 ∈ balancedDesignSpace 4

/-! ## Partition orbit construction -/

/-- Cardinality of a labelled block. -/
def blockSize {B : ℕ} (P : Fin n → Fin B) (j : Fin B) : ℕ :=
  (Finset.univ.filter fun i => P i = j).card

/-- Feasible integer block-sum lattice. -/
def blockSumLattice {B : ℕ} (P : Fin n → Fin B) : Set (Fin B → ℤ) :=
  {r | (∀ j, |r j| ≤ blockSize P j ∧ (r j - blockSize P j) % 2 = 0) ∧ ∑ j, r j = 0}

/-- Outer product of integer block sums, cast to reals. -/
def blockSumOuter {B : ℕ} (r : Fin B → ℤ) : Matrix (Fin B) (Fin B) ℝ :=
  fun j k => (r j : ℝ) * (r k : ℝ)

/-- Block-sum second-moment polytope.
@realizes G_Pi(convex hull of rrᵀ over the feasible parity lattice) -/
def blockSumPolytope {B : ℕ} (P : Fin n → Fin B) :
    Set (Matrix (Fin B) (Fin B) ℝ) :=
  convexHull ℝ (blockSumOuter '' blockSumLattice P)

/-- Embedded within-block centering projector. -/
noncomputable def blockProjector {B : ℕ} (P : Fin n → Fin B) (j : Fin B) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i k => if P i = j ∧ P k = j then
    (if i = k then 1 else 0) - (blockSize P j : ℝ)⁻¹ else 0

-- @node: def:partition-orbit-covariance
/-- Orbit-symmetrized covariance candidate from a block-sum moment matrix.
@realizes A_Pi_G(WD⁻¹GD⁻¹Wᵀ plus embedded within-block projectors) -/
noncomputable def orbitCovariance {B : ℕ} (P : Fin n → Fin B)
    (_hB : 2 ≤ B) (_hP : Function.Surjective P)
    (G : Matrix (Fin B) (Fin B) ℝ) (_hG : G ∈ blockSumPolytope P) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i k =>
    G (P i) (P k) / ((blockSize P (P i) : ℝ) * blockSize P (P k)) +
      ∑ j, if 1 < blockSize P j then
        (((blockSize P j : ℝ) ^ 2 - G j j) /
          ((blockSize P j : ℝ) * (blockSize P j - 1))) * blockProjector P j i k
      else 0

/-! ## Source-matched cited gate -/

/-- `R` is the positive-semidefinite square root of `K`. -/
def IsPSDSquareRoot (K R : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  R.PosSemidef ∧ R * R = K

/-- The ellipsoidal conditional-mean class `M_K = {K u : uᵀ K u ≤ C}`. -/
noncomputable def kallusEllipsoidalClass
    (K : Matrix (Fin n) (Fin n) ℝ) (C : ℝ) : Set (EVec n) :=
  {mu | ∃ u : EVec n, mu = matrixAction K u ∧ quadraticForm K u ≤ C}

/-- Symmetric balanced mixed designs in the cited paper's feasible class. -/
def kallusFeasibleDesigns (n : ℕ) : Set (FiniteDesign (Assignment n)) :=
  {D | (∀ z, D.p z ≠ 0 → IsBalanced z) ∧
    ∀ z, D.p z = D.p (fun i => !z i)}

/-- Worst-case quadratic design variance on the cited ellipsoidal class. -/
noncomputable def kallusWorstVariance (D : FiniteDesign (Assignment n))
    (K : Matrix (Fin n) (Fin n) ℝ) (C : ℝ) : ℝ :=
  sSup {v | ∃ mu ∈ kallusEllipsoidalClass K C,
    v = quadraticForm (designCovariance D) mu}

-- @node: lem:kallus-mixed-strategy-eigenvalue-framework
/-- Kallus (2021), Section 5, pp. 407--408: for the ellipsoidal class
`M_K = {Ku : uᵀKu ≤ C}`, worst-case variance is `C` times the top eigenvalue of
`K¹ᵇ² Q K¹ᵇ²`, and the randomized MSOD minimizes this criterion over its
feasible mixed-design class.  Source handle: `Kallus2021Randomization`,
doi:10.1111/rssb.12412. -/
def KallusMixedStrategyEigenvalueFramework
    (K : Matrix (Fin n) (Fin n) ℝ) (C : ℝ) : Prop :=
  K.PosSemidef ∧ 0 ≤ C →
    (∀ D ∈ kallusFeasibleDesigns n, ∀ R, IsPSDSquareRoot K R →
      kallusWorstVariance D K C =
        C * lambdaMaxOn (R * designCovariance D * R) ⊤) ∧
    ∃ Dopt ∈ kallusFeasibleDesigns n, ∀ D ∈ kallusFeasibleDesigns n,
      kallusWorstVariance Dopt K C ≤ kallusWorstVariance D K C

end CausalSmith.Experimentation.PrognosticDesignAdmissibility
