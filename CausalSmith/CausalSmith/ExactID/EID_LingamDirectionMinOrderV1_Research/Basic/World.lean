/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Minimal cumulant order for causal-direction recovery in bivariate LvLiNGAM: shared core

Stage-2 scaffold for `eid_lingam_direction_min_order_v1`
(specialization `truncated_cumulant_minimality`).

This file carries the two environment S-blocks (the observational
linear-non-Gaussian source-mixing law world and the complexified structural
parameter world), the modeling-assumption atoms, and the two LvLiNGAM class
structures.  The cumulant coordinates, admissible swaps, and assembled crux
lemma live in the focused modules imported by the `Basic` compatibility barrel.

## Causalean substrate survey (bypass-justified)

| Submodule | Decision | Reason |
| --- | --- | --- |
| `Causalean.PO.*`, `Causalean.SCM.Do.*`, `Causalean.Graph.SWIG`, `SWIGGraph` | bypass-justified | potential-outcome / graph identification abstraction; this world is a linear-non-Gaussian source-mixing law with joint-cumulant coordinates, a strictly different abstraction (`local_search 'cumulant' → []`). |
| `Causalean.Discovery.LiNGAM.Kurtosis.cross_fourth_cumulant_eq_sum` | surveyed-and-rejected | fixed single-order (fourth / kurtosis) cross-cumulant identity; cannot express the all-order overcomplete truncation `T_L`. |
| `Mathlib.Probability.{Independence, Distributions.Gaussian}`, `MeasureTheory`, `Finpartition`, `MvPolynomial`, `Equiv.Perm` | reuse | source independence, non-Gaussianity, moment/cumulant plumbing, Zariski closure, source relabeling. |

No new typeclasses are introduced.
-/

import Causalean.Stat.Nonparametric.MomentProblems.Cumulant
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Complex.Basic
import Mathlib.GroupTheory.Perm.Basic

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

/-! ## Cumulant coordinates (re-imported from Causalean)

The Gaussian-law predicate and the joint / univariate cumulants are general moment-problem
objects; they were promoted to `Causalean.Stat.MomentProblems` and are re-exported here under the
run's namespace so the run's statements read unchanged. -/

export Causalean.Stat.MomentProblems (IsGaussianLaw jointCumulant sourceCumulant)

/-! ## Environment S1 — observational bivariate LvLiNGAM data world

Centered independent non-Gaussian latent sources on a common probability space,
observed through a real pair `(X, Y)`; `P` is the pushforward law on `ℝ²`. -/

-- @env: S1
variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Dimension bookkeeping symbols -/

/-- Number of independent sources `n = m + 2`.
@realizes n(n = m+2 sources) -/
def numSources (m : ℕ) : ℕ := m + 2

/-- Candidate sufficient truncation order `K = 2m + 2`.
@realizes K(K = 2m+2) -/
def candidateOrder (m : ℕ) : ℕ := 2 * m + 2

/-- One-order-lower truncation `K₋ = 2m + 1`.
@realizes K_-(K₋ = 2m+1) -/
def lowerOrder (m : ℕ) : ℕ := 2 * m + 1

/-- Observable cumulant-coordinate dimension `q_L = L(L+3)/2 - 2`.
@realizes q_L,p_L(q_L = L(L+3)/2 - 2) -/
def qDim (L : ℕ) : ℕ := L * (L + 3) / 2 - 2

/-- Structural-parameter dimension `p_L = (m+2)L - 1`.
@realizes q_L,p_L(p_L = (m+2)L - 1) -/
def pDim (m L : ℕ) : ℕ := (m + 2) * L - 1

/-- Space of the structural-complexity index `m ∈ {1, 2, …}`: at least one latent
confounder.  Every statement in this development is stated for `m` with this
well-formedness clause.
@realizes m(m ≥ 1, i.e. m ∈ {1,2,…}) -/
def ValidComplexity (m : ℕ) : Prop := 1 ≤ m

/-- Space of the truncation endpoint `L ∈ {2, …, K}` with `K = 2m + 2`: the order
variable ranges over the retained cumulant orders.
@realizes L(2 ≤ L ≤ 2m + 2) -/
def ValidOrder (m L : ℕ) : Prop := 2 ≤ L ∧ L ≤ 2 * m + 2

/-! ## Environment S2 — complexified structural-parameter / cumulant-coordinate world

`bypass-justified`: no Causalean world models complexified algebraic parameter
spaces, Zariski loci, or polynomial cumulant maps.  A structural parameter
`θ = (γ, ρ, c)` (or `η = (δ, σ, d)`) is a scalar direct slope, an `m`-family of
latent slopes, and a source-cumulant weight family; the observable cumulant
vector `t` is coordinatized by `(r, a)`. -/

-- @env: S2
/-- Structural parameter space `Θ^b_{m,L} = R^{m+1} × R^{n(L-1)}`.  The three
components are the direct slope, the `m` latent-loading slopes, and the
source-cumulant weight family `(j, r) ↦ c_{jr}`.
@realizes Theta^right_{m,L},Theta^left_{m,L},theta,eta(coordinates (γ/δ, ρ/σ, c/d))
@realizes gamma(component `.1`)  @realizes rho_i(component `.2.1`)
@realizes delta(component `.1`)  @realizes sigma_i(component `.2.1`)
@realizes c_{jr},d_{jr}(component `.2.2 j r`) -/
abbrev ParamSpace (R : Type*) (m : ℕ) : Type _ :=
  R × (Fin m → R) × (Fin (m + 2) → ℕ → R)

/-- Observable truncated-cumulant coordinate vector `t ∈ R^{q_L}`, indexed by
`(r, a)` with `2 ≤ r ≤ L`, `0 ≤ a ≤ r`.
@realizes T_L(P),t(coordinate family (r,a) ↦ t_{r,a})
@realizes kappa_{r,a}(P)(coordinate (r,a)) -/
abbrev CumVec (R : Type*) : Type _ := ℕ → ℕ → R

/-- Forward source direction family `u_j ∈ R²`:
`u₀ = (1, γ)`, `u_j = (1, ρ_j)` for `1 ≤ j ≤ m`, `u_{m+1} = (0, 1)`.
@realizes u_j(u₀=(1,γ), u_j=(1,ρ_j), u_{m+1}=(0,1)) -/
def forwardLoading {R : Type*} [CommRing R] (m : ℕ) (γ : R) (ρ : Fin m → R) :
    Fin (m + 2) → R × R :=
  fun j =>
    if _ : j.val = 0 then (1, γ)
    else if _ : j.val = m + 1 then (0, 1)
    else (1, ρ ⟨j.val - 1, by have := j.isLt; omega⟩)

/-- Reverse source direction family `v_j ∈ R²`:
`v₀ = (1, 0)`, `v_j = (σ_j, 1)` for `1 ≤ j ≤ m`, `v_{m+1} = (δ, 1)`.
@realizes v_j(v₀=(1,0), v_j=(σ_j,1), v_{m+1}=(δ,1)) -/
def reverseLoading {R : Type*} [CommRing R] (m : ℕ) (δ : R) (σ : Fin m → R) :
    Fin (m + 2) → R × R :=
  fun j =>
    if _ : j.val = 0 then (1, 0)
    else if _ : j.val = m + 1 then (δ, 1)
    else (σ ⟨j.val - 1, by have := j.isLt; omega⟩, 1)

/-! ## Modeling-assumption atoms -/

/-- Mutual independence of the `m + 2` sources.
@realizes S_j(source family S : Fin (m+2) → Ω → ℝ) -/
-- @node: ass:independent-sources
def IndependentSources (μ : Measure Ω) {m : ℕ} (S : Fin (m + 2) → Ω → ℝ) : Prop :=
  iIndepFun S μ

/-- Finite `K`-th absolute moment `E|S_j|^K < ∞` for every source. -/
-- @node: ass:finite-cumulants
def FiniteCumulants (μ : Measure Ω) {m : ℕ} (S : Fin (m + 2) → Ω → ℝ) (K : ℕ) : Prop :=
  ∀ j, MemLp (S j) (K : ℝ≥0∞) μ

/-- Every source law is non-Gaussian. -/
-- @node: ass:source-nongaussianity
def SourceNonGaussian (μ : Measure Ω) {m : ℕ} (S : Fin (m + 2) → Ω → ℝ) : Prop :=
  ∀ j, ¬ IsGaussianLaw (μ.map (S j))

/-- Forward linear source-mixing structural equation `(X, Y)ᵀ = Σ_j u_j S_j`.
@realizes X(X = Σ_j u_{j1} S_j)  @realizes Y(Y = Σ_j u_{j2} S_j) -/
-- @node: ass:forward-axis-model
def ForwardAxisModel (X Y : Ω → ℝ) {m : ℕ} (S : Fin (m + 2) → Ω → ℝ)
    (γ : ℝ) (ρ : Fin m → ℝ) : Prop :=
  (∀ ω, X ω = ∑ j, (forwardLoading m γ ρ j).1 * S j ω) ∧
  (∀ ω, Y ω = ∑ j, (forwardLoading m γ ρ j).2 * S j ω)

/-- Reverse linear source-mixing structural equation `(X, Y)ᵀ = Σ_j v_j S_j`. -/
-- @node: ass:reverse-axis-model
def ReverseAxisModel (X Y : Ω → ℝ) {m : ℕ} (S : Fin (m + 2) → Ω → ℝ)
    (δ : ℝ) (σ : Fin m → ℝ) : Prop :=
  (∀ ω, X ω = ∑ j, (reverseLoading m δ σ j).1 * S j ω) ∧
  (∀ ω, Y ω = ∑ j, (reverseLoading m δ σ j).2 * S j ω)

/-- Distinct forward loading directions `|{γ, ρ_i}| = m + 1`. -/
-- @node: ass:forward-noncollinearity
def ForwardNonCollinear {m : ℕ} (γ : ℝ) (ρ : Fin m → ℝ) : Prop :=
  Function.Injective (Fin.cons γ ρ : Fin (m + 1) → ℝ)

/-- Distinct reverse loading directions `|{δ, σ_i}| = m + 1`. -/
-- @node: ass:reverse-noncollinearity
def ReverseNonCollinear {m : ℕ} (δ : ℝ) (σ : Fin m → ℝ) : Prop :=
  Function.Injective (Fin.cons δ σ : Fin (m + 1) → ℝ)

/-- Nonzero forward direct edge `γ ≠ 0`.
@realizes gamma(γ ≠ 0) -/
-- @node: ass:forward-nonzero-edge
def ForwardNonzeroEdge (γ : ℝ) : Prop := γ ≠ 0

/-- Nonzero reverse direct edge `δ ≠ 0`.
@realizes delta(δ ≠ 0) -/
-- @node: ass:reverse-nonzero-edge
def ReverseNonzeroEdge (δ : ℝ) : Prop := δ ≠ 0

/-! ## LvLiNGAM class structures -/

/-- Forward bivariate LvLiNGAM class membership of an observational law
`P ∈ Laws(ℝ²)`: there **exist** a probability space `(Ω, μ)`, centered independent
non-Gaussian sources `S` with finite moments through `K = 2m + 2`, an observed
pair `(X, Y)`, and forward loadings `(γ, ρ)` realizing all six forward modeling
assumptions, such that `P` is the pushforward law of `(X, Y)` under `μ`.  This is
the existential *class* of laws (not a witness bundle for fixed data): the
witnesses are quantified, the sources are centered, and `P` is pinned as the
pushforward law. -/
-- @node: def:forward-lvlingam-class
def ForwardLvLiNGAM (P : Measure (ℝ × ℝ)) (m : ℕ) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (S : Fin (m + 2) → Ω → ℝ) (X Y : Ω → ℝ) (γ : ℝ) (ρ : Fin m → ℝ),
    IsProbabilityMeasure μ ∧
    IndependentSources μ S ∧
    FiniteCumulants μ S (2 * m + 2) ∧
    SourceNonGaussian μ S ∧
    (∀ j, ∫ ω, S j ω ∂μ = 0) ∧
    ForwardAxisModel X Y S γ ρ ∧
    ForwardNonCollinear γ ρ ∧
    ForwardNonzeroEdge γ ∧
    P = μ.map (fun ω => (X ω, Y ω))

/-- Reverse bivariate LvLiNGAM class membership of an observational law
`P ∈ Laws(ℝ²)`, reverse-parameterized: existential centered independent
non-Gaussian sources and reverse loadings `(δ, σ)` whose pushforward law is `P`. -/
-- @node: def:reverse-lvlingam-class
def ReverseLvLiNGAM (P : Measure (ℝ × ℝ)) (m : ℕ) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (S : Fin (m + 2) → Ω → ℝ) (X Y : Ω → ℝ) (δ : ℝ) (σ : Fin m → ℝ),
    IsProbabilityMeasure μ ∧
    IndependentSources μ S ∧
    FiniteCumulants μ S (2 * m + 2) ∧
    SourceNonGaussian μ S ∧
    (∀ j, ∫ ω, S j ω ∂μ = 0) ∧
    ReverseAxisModel X Y S δ σ ∧
    ReverseNonCollinear δ σ ∧
    ReverseNonzeroEdge δ ∧
    P = μ.map (fun ω => (X ω, Y ω))

/-- A forward LvLiNGAM representation of an observational law by a specified
parameter consists of centered independent non-Gaussian sources whose stated
loadings and cumulants generate that law.

The forward axis model uses exactly the slopes carried by `θ`, and every source
cumulant from order two through `K` is exactly the corresponding weight carried
by `θ`.  This is strictly stronger than `ForwardLvLiNGAM P m`, whose loadings
and sources are existentially quantified independently of a specified parameter. -/
def ForwardLvLiNGAMRep (P : Measure (ℝ × ℝ)) (m K : ℕ) (θ : ParamSpace ℝ m) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (S : Fin (m + 2) → Ω → ℝ) (X Y : Ω → ℝ),
    IsProbabilityMeasure μ ∧
    IndependentSources μ S ∧
    FiniteCumulants μ S (2 * m + 2) ∧
    SourceNonGaussian μ S ∧
    (∀ j, ∫ ω, S j ω ∂μ = 0) ∧
    ForwardAxisModel X Y S θ.1 θ.2.1 ∧
    ForwardNonCollinear θ.1 θ.2.1 ∧
    ForwardNonzeroEdge θ.1 ∧
    (∀ (j : Fin (m + 2)) (r : ℕ), 2 ≤ r → r ≤ K →
      sourceCumulant μ (S j) r = θ.2.2 j r) ∧
    P = μ.map (fun ω => (X ω, Y ω))

/-- A reverse LvLiNGAM representation of an observational law by a specified
parameter consists of centered independent non-Gaussian sources whose stated
loadings and cumulants generate that law.

The reverse axis model uses exactly the slopes carried by `η`, and every source
cumulant from order two through `K` is exactly the corresponding weight carried
by `η`.  This is strictly stronger than `ReverseLvLiNGAM P m`, whose loadings
and sources are existentially quantified independently of a specified parameter. -/
def ReverseLvLiNGAMRep (P : Measure (ℝ × ℝ)) (m K : ℕ) (η : ParamSpace ℝ m) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (S : Fin (m + 2) → Ω → ℝ) (X Y : Ω → ℝ),
    IsProbabilityMeasure μ ∧
    IndependentSources μ S ∧
    FiniteCumulants μ S (2 * m + 2) ∧
    SourceNonGaussian μ S ∧
    (∀ j, ∫ ω, S j ω ∂μ = 0) ∧
    ReverseAxisModel X Y S η.1 η.2.1 ∧
    ReverseNonCollinear η.1 η.2.1 ∧
    ReverseNonzeroEdge η.1 ∧
    (∀ (j : Fin (m + 2)) (r : ℕ), 2 ≤ r → r ≤ K →
      sourceCumulant μ (S j) r = η.2.2 j r) ∧
    P = μ.map (fun ω => (X ω, Y ω))

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
