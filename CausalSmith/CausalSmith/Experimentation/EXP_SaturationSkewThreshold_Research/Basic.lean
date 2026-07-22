/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Saturation-design skew threshold (quartic moment program): shared core

Stage-2 scaffold for `exp_saturation_skew_threshold` (v1).

This file carries the shared environment S-blocks (the Borel-law moment-program
world S1, the finite saturation-vector world S2, and the design-based PO carrier
for S3), the assumption-atom `def`s, and the construction `def`s. Each emitted
declaration carries its own `@node` tag.

## Causalean substrate survey

| Submodule | Decision | Reason |
| --- | --- | --- |
| `Causalean.Experimentation.DesignBased.*` (FiniteDesign/E/Var/compound) | bypass-justified | finite-sum randomization layer, NOT a Borel-measure moment-program world; the law world S1 is built over Mathlib `ProbabilityMeasure`. |
| `Causalean.Experimentation.DesignBased.PotentialOutcome` (ProperlySpecified) | bypass-justified | isolated-interference PO interface is at unit/assignment level; the bridge's cluster-level isolated/anonymous restrictions are stated as threaded `Prop`s over a generic outcome carrier. |

No new typeclasses or cluster-scale structures are introduced; the design PO
world S3 is carried as a plain outcome function with threaded `Prop` hypotheses.
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Topology.Order.Compact

namespace CausalSmith.Experimentation.SaturationSkew

open MeasureTheory
open scoped BigOperators

/-! ## Environment S1 — Borel saturation-law moment-program world

A saturation law `ν` is a Borel probability measure on `ℝ` supported on `[0,1]`
(the `SupportedOn01` predicate); moments and the quartic functional are integrals
of bounded polynomials, and weak convergence is the ambient `ProbabilityMeasure`
weak topology. -/

-- @env: S1
/-- A saturation law: a Borel probability measure on `ℝ`.
@realizes nu(carrier ProbabilityMeasure ℝ; supported on [0,1] via SupportedOn01) -/
abbrev Law := ProbabilityMeasure ℝ

/-- Dirac law `δ_x`.
@realizes delta_x([0,1]→P([0,1]) point mass) -/
noncomputable def diracLaw (x : ℝ) : Law := ⟨Measure.dirac x, inferInstance⟩

/-- Support constraint `supp ν ⊆ [0,1]`, the `P([0,1])` part of admissibility.
@realizes nu(supp ⊆ Icc 0 1) -/
def SupportedOn01 (ν : Law) : Prop := (ν : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0

/-- `ν` is carried by at most `n` atoms: some `Finset` of cardinality `≤ n` has
full mass. -/
def cardSupportLe (n : ℕ) (ν : Law) : Prop :=
  ∃ s : Finset ℝ, s.card ≤ n ∧ (ν : Measure ℝ) ((↑s : Set ℝ)ᶜ) = 0

-- @node: def:centering-map
/-- Centered share map `T_pbar(u) = u - pbar`.
@realizes T_pbar(centeredShare = u - pbar) -/
def centeredShare (pbar u : ℝ) : ℝ := u - pbar

-- @node: def:centered-support-domain
/-- Centered support domain `D_pbar = [-pbar, 1 - pbar]`.
@realizes D_pbar(Icc (-pbar) (1-pbar)) -/
def centeredSupportDomain (pbar : ℝ) : Set ℝ := Set.Icc (-pbar) (1 - pbar)

-- @node: def:centered-moments
/-- Centered saturation moment `m_r(ν) = ∫ (u - pbar)^r dν`, for `r ∈ {2,3,4}`.
@realizes m_r(ν)(∫ (u-pbar)^r dν) -/
noncomputable def centeredMoment (pbar : ℝ) (r : ℕ) (ν : Law) : ℝ :=
  ∫ u, (u - pbar) ^ r ∂(ν : Measure ℝ)

-- @node: def:admissible-law-class
/-- Admissible saturation laws `N(pbar) = {ν ∈ P([0,1]) : ∫ u dν = pbar}`.
Realized as the bare set-membership predicate (the core construction is exactly
the mean constraint over `P([0,1])`); the interior budget `0 < pbar < 1` is the
threaded `BudgetInterior` atom, kept OUT of this class so the boundary lemmas
(`pbar ∈ {0,1}`) range over the same predicate. (Plan sync-back: class → `def`.)
@realizes N(pbar)(SupportedOn01 ∧ mean = pbar) -/
def IsAdmissible (pbar : ℝ) (ν : Law) : Prop :=
  SupportedOn01 ν ∧ ∫ u, u ∂(ν : Measure ℝ) = pbar -- @realizes nu(∫ u dν = pbar)

/-- Pushforward of a law by the centering map `T_pbar(u) = u - pbar`. -/
noncomputable def centeredPush (pbar : ℝ) (ν : Law) : Law :=
  ν.map (f := fun u => u - pbar) (by fun_prop)

/-- Pushforward of a centered law back by `d ↦ pbar + d`. -/
noncomputable def decenterPush (pbar : ℝ) (μ : Law) : Law :=
  μ.map (f := fun d => pbar + d) (by fun_prop)

-- @node: def:fixed-second-moment-slice
/-- Second-moment slice `N_s(pbar,s) = {ν ∈ N(pbar) : m_2(ν) = s}`.
@realizes N_s(pbar,s)(IsAdmissible ∧ centeredMoment 2 = s) -/
def secondMomentSlice (pbar s : ℝ) : Set Law :=
  {ν | IsAdmissible pbar ν ∧ centeredMoment pbar 2 ν = s}

-- @node: def:variance-functional
/-- Quartic variance functional
`V(ν) = V_0 + V_1 m_2 + V_3 m_3 + V_4 (m_4 - m_2^2)`.
@realizes V(nu)(V0 + V1 m2 + V3 m3 + V4 (m4 - m2^2)) -/
noncomputable def varianceFunctional (V0 V1 V3 V4 pbar : ℝ) (ν : Law) : ℝ :=
  V0 + V1 * centeredMoment pbar 2 ν + V3 * centeredMoment pbar 3 ν
    + V4 * (centeredMoment pbar 4 ν - (centeredMoment pbar 2 ν) ^ 2)

/-- `ν ∈ argmin_{N(pbar)} V`: admissible and pointwise-minimal in `V`. -/
def IsMinimizer (V0 V1 V3 V4 pbar : ℝ) (ν : Law) : Prop :=
  IsAdmissible pbar ν ∧
    ∀ η, IsAdmissible pbar η →
      varianceFunctional V0 V1 V3 V4 pbar ν ≤ varianceFunctional V0 V1 V3 V4 pbar η

-- @node: def:profile-value
/-- Profiled inner value
`F(s) = inf_{ν ∈ N_s(pbar,s)} ∫ (V_1 d^2 + V_3 d^3 + V_4 d^4) dν`, `d = u - pbar`.
@realizes F(s)(iInf over slice of the centered quartic integrand) -/
noncomputable def profileValue (V1 V3 V4 pbar s : ℝ) : ℝ :=
  ⨅ ν : secondMomentSlice pbar s,
    ∫ u, (V1 * (u - pbar) ^ 2 + V3 * (u - pbar) ^ 3 + V4 * (u - pbar) ^ 4)
      ∂((ν : Law) : Measure ℝ)

-- @node: def:quartic-dual-residual
/-- Quartic dual residual `Q_{a,b,c}(d) = V_1 d^2 + V_3 d^3 + V_4 d^4 - a - b d - c d^2`.
@realizes Q_{a,b,c}(d)(V1 d² + V3 d³ + V4 d⁴ - a - b d - c d²) -/
def quarticDualResidual (V1 V3 V4 a b c d : ℝ) : ℝ :=
  V1 * d ^ 2 + V3 * d ^ 3 + V4 * d ^ 4 - a - b * d - c * d ^ 2

-- @node: def:outer-certificate
/-- Outer (profiled) certificate `H(s) = V_0 + F(s) - V_4 s^2` (primary form).
@realizes H(s)(V0 + F(s) - V4 s²) -/
noncomputable def outerCertificate (V0 V1 V3 V4 pbar s : ℝ) : ℝ :=
  V0 + profileValue V1 V3 V4 pbar s - V4 * s ^ 2

/-- Sufficient affine lower line `G^{lin}_{a,c}(s) = V_0 + a + c s - V_4 s^2`.
@realizes G_{a,c}(s)(V0 + a + c s - V4 s²) -/
def outerAffine (V0 V4 a c s : ℝ) : ℝ := V0 + a + c * s - V4 * s ^ 2

/-! ## Environment S2 — finite saturation-vector / empirical-law world -/

/-- `x` is a `1/m`-grid point in `{0, 1/m, …, 1}`. -/
def gridPoint (m : ℕ) (x : ℝ) : Prop := ∃ k : ℕ, k ≤ m ∧ x = (k : ℝ) / m

-- @node: def:implementable-vector-class
/-- Implementable saturation vectors
`Π_{M,m}(pbar) = {π ∈ {0,1/m,…,1}^M : M⁻¹ ∑ π_j = pbar}`.
Realized as the bare predicate (the core construction is exactly the grid + mean
set-builder); the design atoms `EqualClusterSize` and `BudgetInterior` are
threaded separately by the consuming statements. (Plan sync-back: class → `def`.)
@realizes Pi_{M,m}(pbar)(grid membership ∧ mean = pbar) -/
def IsImplementable (M m : ℕ) (pbar : ℝ) (π : Fin M → ℝ) : Prop :=
  (∀ j, gridPoint m (π j)) ∧ (M : ℝ)⁻¹ * ∑ j, π j = pbar -- @realizes Pi_{M,m}(pbar)(M⁻¹ ∑ π = pbar)

/-- Uniform probability law on `Fin M` (used to build empirical laws). -/
noncomputable def unifFin (M : ℕ) [NeZero M] : ProbabilityMeasure (Fin M) :=
  ⟨(PMF.uniformOfFintype (Fin M)).toMeasure, inferInstance⟩

-- @node: def:empirical-law
/-- Empirical law `L_M(π) = M⁻¹ ∑_j δ_{π_j}` (pushforward of the uniform law on
`Fin M` by `π`; junk `δ_0` at `M = 0`).
@realizes L_M(pi)(M⁻¹ ∑ δ_{π_j}) -/
noncomputable def empiricalLaw (M : ℕ) (π : Fin M → ℝ) : Law :=
  if h : 0 < M then
    haveI : NeZero M := ⟨h.ne'⟩
    (unifFin M).map (f := π) (measurable_from_top).aemeasurable
  else diracLaw 0

-- @node: def:grid-split-rounding
/-- Grid-split rounding handle (`def:grid-split-rounding`), built from the atomic
data of a `K`-atomic law `ν = ∑_ℓ w_ℓ δ_{u_ℓ}` (weights `w`, support `u`) into a
finite saturation vector `π_rd ∈ ℝ^M`, in the three stages of the note's
construction. The realization is the paper's grid-**split** handle — adjacent-grid
splitting with mixing weights and (multi-coordinate) balancing — **not** a
floor-snap with a one-coordinate correction:

* Stage 1 (mass-round, largest-remainder): cluster `j` is allocated to the atom `ℓ`
  whose cumulative-mass band `(cum (ℓ-1), cum ℓ]` contains the quantile `(j+1)/M`,
  i.e. the rounded cluster counts `n_ℓ ≈ M w_ℓ`; `target j = u_ℓ` is the allocated
  atom value;
* Stage 2 (adjacent-grid split with mixing weights): each atom value `u_ℓ` is
  replaced by the **two adjacent** grid points `⌊m·u_ℓ⌋/m` and `⌈m·u_ℓ⌉/m` rather
  than a single floor-snap; the per-cluster choice is the error-feedback split that
  sends a `frac(m·u_ℓ)` mixing-weight share of the atom's clusters to the upper
  point — cluster `j` takes the upper point iff the cumulative fractional mass
  `∑_{j'≤j} frac(m·target j')` crosses an integer at `j` — so each atom's mean
  contribution `n_ℓ·u_ℓ` is preserved up to the `1/m` grid step;
* Stage 3 (mean-balancing): the integer grid-unit deficit
  `D = round(N·pbar) − ∑_j unit_j` is spread as single `±1/m` unit steps across the
  first `|D|` clusters (not dumped on one coordinate), enforcing the budget
  `M⁻¹ ∑_j π_j = pbar` exactly when `N·pbar ∈ ℤ`. (The `O(M⁻¹+m⁻¹)` coupling cost is
  the quantitative content of `lem:finite-atomic-grid-split-rounding`.)
@realizes pi_rd([0,1]^M grid vector via adjacent-grid split + mixing weights + balancing) -/
noncomputable def gridSplitRounding (M m : ℕ) (pbar : ℝ) {K : ℕ} (w u : Fin K → ℝ) :
    Fin M → ℝ :=
  -- Stage 1 (mass-round, largest-remainder): cumulative masses; allocate cluster `j`
  -- to the atom `ℓ` whose band `(cum (ℓ-1), cum ℓ]` contains `(j+1)/M`; `target j = u_ℓ`.
  let cum : Fin K → ℝ := fun ℓ => ∑ ℓ' ∈ Finset.univ.filter (· ≤ ℓ), w ℓ'
  let target : Fin M → ℝ := fun j =>
    if h : ∃ ℓ : Fin K, ((j : ℝ) + 1) / M ≤ cum ℓ then u h.choose else pbar
  -- Stage 2 (adjacent-grid split with mixing weights): the lower/upper adjacent grid
  -- units of `target j` are `⌊m·target j⌋` and `⌈m·target j⌉`; cluster `j` takes the
  -- UPPER unit iff the cumulative fractional mass crosses an integer at `j` (the
  -- error-feedback split realizing the `frac(m·target j)` mixing weight per atom).
  let frac : Fin M → ℝ := fun j => (m : ℝ) * target j - (⌊(m : ℝ) * target j⌋ : ℝ)
  let fracCum : Fin M → ℝ := fun j =>
    ∑ j' ∈ Finset.univ.filter (fun j' : Fin M => (j' : ℕ) ≤ (j : ℕ)), frac j'
  let fracPrev : Fin M → ℝ := fun j => fracCum j - frac j
  let unit : Fin M → ℤ := fun j =>
    if ⌊fracCum j⌋ > ⌊fracPrev j⌋ then ⌈(m : ℝ) * target j⌉ else ⌊(m : ℝ) * target j⌋
  -- Stage 3 (mean-balancing): spread the integer grid-unit deficit `D` as single `±1`
  -- unit steps across the first `|D|` clusters until `∑_j unit_j = round(N·pbar)`.
  let T : ℤ := ∑ j', unit j'
  let D : ℤ := round ((M : ℝ) * (m : ℝ) * pbar) - T
  let step : Fin M → ℤ := fun j =>
    if 0 ≤ D then (if (j : ℕ) < D.toNat then (1 : ℤ) else 0)
    else (if (j : ℕ) < (-D).toNat then (-1 : ℤ) else 0)
  fun j => ((unit j + step j : ℤ) : ℝ) / (m : ℝ)

/-! ## Environment S3 — design-based two-stage saturation PO carrier

The finite-population PO world is carried by a plain outcome function
`Y_{ji}(z)` of the full assignment `z`; the isolated / anonymous-share modeling
restrictions are threaded `Prop`s, and the homogeneous linear-share working model
exposes the affine `(own treatment, centered share)` surface. -/

/-- Cluster `j` treated share under assignment profile `z`. -/
noncomputable def clusterShare {M m : ℕ} (z : Fin M → Fin m → Bool) (j : Fin M) : ℝ :=
  (m : ℝ)⁻¹ * ∑ i, (if z j i then (1 : ℝ) else 0)

/-! ## Assumption atoms (threaded `Prop`s; never discharged) -/

-- @node: ass:equal-cluster-size
/-- A1 equal cluster size: `M` clusters of common size `m`, `N = M m`. -/
def EqualClusterSize (M m N : ℕ) : Prop := N = M * m

-- @node: ass:budget-interior
/-- A2 interior treatment budget `0 < pbar < 1`. -/
def BudgetInterior (pbar : ℝ) : Prop := 0 < pbar ∧ pbar < 1

-- @node: ass:isolated-partial-interference
/-- A3 isolated partial interference: the outcome of unit `(j,i)` depends only on
the within-cluster assignments `z j ·`. -/
def IsolatedPartialInterference {M m : ℕ}
    (Y : Fin M → Fin m → (Fin M → Fin m → Bool) → ℝ) : Prop :=
  ∀ (j : Fin M) (i : Fin m) (z z' : Fin M → Fin m → Bool),
    (∀ i', z j i' = z' j i') → Y j i z = Y j i z'

-- @node: ass:anonymous-share-specialization
/-- A4 anonymous-share specialization: within a cluster, the outcome depends on
the assignment only through the cluster treated share and the unit's own
treatment. -/
def AnonymousShareSpecialization {M m : ℕ}
    (Y : Fin M → Fin m → (Fin M → Fin m → Bool) → ℝ) : Prop :=
  ∀ (j : Fin M) (i : Fin m) (z z' : Fin M → Fin m → Bool),
    clusterShare z j = clusterShare z' j → z j i = z' j i → Y j i z = Y j i z'

-- @node: ass:homogeneous-linear-share-working-model
/-- A5 homogeneous linear-share working model: for each own treatment state the
outcome surface is affine in the centered share `d = u - pbar`, with
cluster-common coefficients `(β₀,β₁,γ₀,γ₁)`. -/
def HomogeneousLinearShareWorkingModel {M m : ℕ} (pbar : ℝ)
    (Y : Fin M → Fin m → (Fin M → Fin m → Bool) → ℝ) : Prop :=
  ∃ β0 β1 γ0 γ1 : ℝ, ∀ (j : Fin M) (i : Fin m) (z : Fin M → Fin m → Bool),
    Y j i z =
      (if z j i then β1 + γ1 * (clusterShare z j - pbar)
        else β0 + γ0 * (clusterShare z j - pbar))

-- @node: ass:cai-leading-expansion-domain
/-- A6 Cai leading-expansion domain (full Cai–Pouget-Abadie–Airoldi (2022) Thm 9
regularity regime over the design sequence `Yseq`): not only `M, m → ∞`, but also
(i) the linear-interference potential-outcome parameters are **uniformly bounded**
along the sequence (`∃ B, |Yseq n j i z| ≤ B`), and (ii) the **regularity** of Cai
Thm 9 holds in the homogeneous / block-fixed isolated-cluster specialization, i.e.
each design in the sequence is isolated, anonymous-share, and homogeneous
linear-in-share. -/
def CaiLeadingExpansionDomain (pbar : ℝ) (Mseq mseq : ℕ → ℕ)
    (Yseq : (n : ℕ) →
      Fin (Mseq n) → Fin (mseq n) → (Fin (Mseq n) → Fin (mseq n) → Bool) → ℝ) : Prop :=
  Filter.Tendsto (fun n => (Mseq n : ℝ)) Filter.atTop Filter.atTop ∧
    Filter.Tendsto (fun n => (mseq n : ℝ)) Filter.atTop Filter.atTop ∧
    -- bounded parameters: uniform bound on the linear-interference outcomes
    (∃ B : ℝ, ∀ (n : ℕ) (j : Fin (Mseq n)) (i : Fin (mseq n))
        (z : Fin (Mseq n) → Fin (mseq n) → Bool), |Yseq n j i z| ≤ B) ∧
    -- regularity in the homogeneous/block-fixed isolated-cluster specialization
    (∀ n, IsolatedPartialInterference (Yseq n) ∧
        AnonymousShareSpecialization (Yseq n) ∧
        HomogeneousLinearShareWorkingModel pbar (Yseq n))

/-! ## Open-ended residual -/

-- @node: oeq:full-branch-optimizer-map
/-- OPEN-ENDED QUESTION (`oeq:full-branch-optimizer-map`). The atlas-compression
residual, stated as a `Prop` (NOT proved): existence of a parameter-uniform,
human-readable semialgebraic optimizer atlas over the coefficient space
`Θ = {(pbar,V_1,V_3,V_4) : 0 ≤ pbar ≤ 1}` — a finite family of semialgebraic
cells and closed-form optimizer/value maps that agree, on each cell, with the
global minimizer of the quartic program. Excluded from the theorem manifest; no
theorem depends on it. -/
def FullBranchOptimizerAtlasOpen : Prop :=
  ∃ (K : ℕ) (cell : Fin K → Set (ℝ × ℝ × ℝ × ℝ))
    (atlasLaw : Fin K → ℝ × ℝ × ℝ × ℝ → Law),
    (∀ θ : ℝ × ℝ × ℝ × ℝ, 0 ≤ θ.1 → θ.1 ≤ 1 → ∃ k, θ ∈ cell k) ∧
    ∀ (k : Fin K) (θ : ℝ × ℝ × ℝ × ℝ), θ ∈ cell k → 0 ≤ θ.1 → θ.1 ≤ 1 →
      IsMinimizer 0 θ.2.1 θ.2.2.1 θ.2.2.2 θ.1 (atlasLaw k θ)

end CausalSmith.Experimentation.SaturationSkew
