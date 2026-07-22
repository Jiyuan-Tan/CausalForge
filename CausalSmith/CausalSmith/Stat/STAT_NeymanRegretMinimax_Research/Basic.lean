/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sharp minimax Neyman-regret rate for adaptive two-arm experiments: shared core

Stage-2 scaffold for `stat_neyman_regret_minimax`.

This file carries the shared environment S-blocks (S1 superpopulation law world,
S2 adaptive-experiment world), the assumption-atom `def`s, the model-class
structures (`MInt`, `MTan`, `MBand`), the algorithm class `AdaptiveAlgorithm`,
the sequential joint-law construction `jointLaw`, and the Neyman-allocation /
regret construction `def`s.  Every declaration carries its own `-- @node:` tag.

## Causalean substrate survey

| Submodule | Decision | Reason |
| --- | --- | --- |
| `Causalean.Stat.IIDSample` (`Causalean.Stat.Sample`) | reuse | S1 i.i.d. superpopulation sampling atom `SuperpopulationIID` wraps a `Nonempty (IIDSample Ω (ℝ×ℝ) μ nu)`. |
| `Causalean.Experimentation.DesignBased.neymanFraction` | reuse | `oracleAllocation nu = neymanFraction (m₁²) (m₀²)` (a one-line derived wrapper, `= m₁/(m₀+m₁)`). |
| `Causalean.Mathlib.Probability.bernoulliLaw` | reuse | conditional randomization `A_t ~ Bernoulli(π_t)` inside `stepKernel`. |
| `Causalean.Experimentation.Sequential.AdaptiveExperiment` | bypass-justified (SYNC-BACK) | its world is an abstract `(Ω, ℱ)` with an adapted `[0,1]` propensity process and NO measure, so it cannot host the concrete sequential joint-law kernel composition the regret integral requires; `AdaptiveAlgorithm` is realized as a concrete history-measurable strict-interior strategy instead. |

No new typeclasses are introduced.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Causalean.Stat.Sample
import Causalean.Mathlib.Probability.BernoulliMeasure
import Causalean.Experimentation.DesignBased.Optimality.Neyman

namespace CausalSmith.Stat.NeymanRegretMinimax

open MeasureTheory
open scoped BigOperators Topology

/-! ## Environment S1 — superpopulation bounded-outcome potential-outcome law -/

-- @env: S1
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Observed per-round record `(π_t, A_t, Y_t) ∈ (0,1) × {0,1} × [0,1]`.  The
assignment `A_t ∈ {0,1}` is encoded at the value level by `A_t : ℝ` supported on
`{0,1}` (via `bernoulliLaw`), and the ranges `(0,1)` / `[0,1]` are carried at the
law level (`PredictableDesign`, `BoundedOutcomes`) rather than by subtypes.
@realizes A_t(record coord 2 ∈ {0,1}) @realizes pi_t(record coord 1)
@realizes Y_t(record coord 3) -/
abbrev NeymanRecord : Type := ℝ × ℝ × ℝ

/-- Arm marginal law `nu_a` of the superpopulation PO law `nu` on `[0,1]²`:
`nu_0` is the law of `Y(0)` (first coordinate), `nu_1` that of `Y(1)` (second).
@realizes nu_0, nu_1(carrier; nu_0 = marginal fst (Y(0)), nu_1 = marginal snd (Y(1))) -/
noncomputable def armMarginal (nu : Measure (ℝ × ℝ)) (a : Fin 2) : Measure ℝ :=
  if a = 0 then nu.map Prod.fst else nu.map Prod.snd

-- @node: def:arm-tangent-strengths
/-- Arm-wise tangent strength `r_{a,nu} = inf_{b₀,b₁} ∫ (y² − b₀ − b₁y)² dnu_a`,
the squared `L²(nu_a)` residual of `y²` on `span{1, y}`.  (SYNC-BACK: relocated
from `Helpers/ScoreProgram` to `Basic` so the assumption atoms
`ArmTangentNondegeneracy` / `TangentBand` can reference it.)
@realizes r_{0,nu}, r_{1,nu}(carrier; inf_b ∫(y²−b₀−b₁y)² dnu_a; lower band TangentBand) -/
noncomputable def armTangentStrength (nu : Measure (ℝ × ℝ)) (a : Fin 2) : ℝ :=
  ⨅ b : ℝ × ℝ, ∫ y, (y ^ 2 - b.1 - b.2 * y) ^ 2 ∂(armMarginal nu a)

/-- Arm-wise root second moment `m_a = (∫ y² dnu_a)^{1/2}`.
@realizes m_0, m_1(carrier; m_a = (∫ y² dnu_a)^{1/2}; (0,1] via InteriorSecondMoments+Bounded) -/
noncomputable def rootSecondMoment (nu : Measure (ℝ × ℝ)) (a : Fin 2) : ℝ :=
  Real.sqrt (∫ y, y ^ 2 ∂(armMarginal nu a))

-- @node: ass:bounded-outcomes
/-- Bounded-outcome restriction `supp(nu) ⊆ [0,1]²`.  This is the predicate pinning
the RANGE of the potential outcomes (both coords `∈ [0,1]`) — and, through the
observed-outcome map `Y = A·Y(1)+(1−A)·Y(0)` in `stepKernel`, the observed outcome
`Y_t ∈ [0,1]` as well.
@realizes nu(supp ⊆ [0,1]² : a.e. both coords in Icc 0 1)
@realizes nu_0, nu_1(support ⊆ [0,1]: arm marginals inherit supp ⊆ Icc 0 1; pins `laws on [0,1]`)
@realizes Y_t(0), Y_t(1)(both coords p.1, p.2 ∈ Icc 0 1, a.e. nu)
@realizes Y_t(observed Y = A·Y(1)+(1−A)·Y(0) ∈ Icc 0 1 via this bound)
@realizes m_0, m_1(upper m_a ≤ 1 of (0,1]: y∈[0,1] a.e. ∧ mass 1 via MInt.isLaw ⟹ ∫y²≤1) -/
def BoundedOutcomes (nu : Measure (ℝ × ℝ)) : Prop :=
  ∀ᵐ p ∂nu, p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1

-- @node: ass:superpopulation-iid
/-- I.i.d. superpopulation sampling: `((Y_t(0), Y_t(1)))_t` are i.i.d. with common
law `nu`, realized by a `Causalean.Stat.IIDSample` on the ambient space `(Ω, μ)`
with value space `ℝ × ℝ` and marginal `nu`.
@realizes Y_t(0), Y_t(1)(i.i.d. draws Z t) @realizes nu(common law of IIDSample) -/
def SuperpopulationIID (μ : Measure Ω) (nu : Measure (ℝ × ℝ)) : Prop :=
  Nonempty (Causalean.Stat.IIDSample Ω (ℝ × ℝ) μ nu)

-- @node: ass:interior-second-moments
/-- Interior positivity of the arm-wise root second moments: `m_a > 0`.  This is the
predicate pinning the LOWER end of `m_a`'s space `(0,1]` (the upper bound `m_a ≤ 1`
is carried by `BoundedOutcomes`); together with the carrier `rootSecondMoment` they
realize the `m_a ∈ (0,1]` cluster.

It is ALSO the standing range clause of the `pi_nu_star` cluster: because
`oracleAllocation nu = neymanFraction (m₁²) (m₀²)` and
`neymanFraction_mem_Ioo (hA : 0 < m₁²) (hB : 0 < m₀²) : 0 < neymanFraction .. < 1`,
the positivity `0 < m_a` (both arms) is exactly what pins the oracle Neyman
allocation into its space `(0,1)`.  This predicate is a member field of
`MInt`/`MTan`/`MBand` (`interiorMoments`), so `pi_nu_star ∈ (0,1)` holds as a
standing property everywhere a model-class law is in scope.
@realizes m_0, m_1(lower end 0 < m_a of (0,1] for both arms via 0 < rootSecondMoment)
@realizes pi_nu_star(range (0,1): 0 < m_a both arms ⟹ 0 < oracleAllocation < 1
  by neymanFraction_mem_Ioo; standing via MInt/MTan/MBand.interiorMoments) -/
def InteriorSecondMoments (nu : Measure (ℝ × ℝ)) : Prop :=
  ∀ a : Fin 2, 0 < rootSecondMoment nu a

-- @node: ass:arm-tangent-nondegeneracy
/-- Arm tangent nondegeneracy: `inf_{b₀,b₁} ∫ (y² − b₀ − b₁y)² dnu_a > 0` for both
arms (`y²` not a.s. affine in `y`; strong identification). -/
def ArmTangentNondegeneracy (nu : Measure (ℝ × ℝ)) : Prop :=
  ∀ a : Fin 2, 0 < armTangentStrength nu a

-- @node: ass:interior-band
/-- Compact interior moment/overlap band `underline_m ≤ m_a ≤ overline_m`.  The
radii `um, om` are named class constants controlling only the frontier constant.
The carrier of each radius is the corresponding `ℝ` parameter here; their range in
the space `(0,1]²` (`0 < um ≤ om ≤ 1`) is pinned STRUCTURALLY by the constraining
`MBand` well-formedness fields `umPos`/`umLeOm`/`omLeOne` (the canonical realization
of the constants' space), and redundantly by the band theorems' `hum`/`humom`/`hom`
hypotheses.  This band-membership predicate itself only encodes `um ≤ m_a ≤ om`
(matching `ass:interior-band` verbatim), so it stays clean of the constant-range clauses.
@realizes underline_m(carrier um : ℝ; band radius m_a ≥ um; space (0,1] via MBand.umPos/umLeOm)
@realizes overline_m(carrier om : ℝ; band radius m_a ≤ om; space (0,1] via MBand.omLeOne/umLeOm)
@realizes underline_m, overline_m(joint carriers (um, om) : ℝ²; band radii um ≤ m_a ≤ om;
  joint space (0,1]² via conjunction MBand.umPos ∧ umLeOm ∧ omLeOne = 0 < um ≤ om ≤ 1)
@realizes m_0, m_1(band range um ≤ m_a ≤ om, both arms; pins m_a in the interior band) -/
def InteriorBand (um om : ℝ) (nu : Measure (ℝ × ℝ)) : Prop :=
  ∀ a : Fin 2, um ≤ rootSecondMoment nu a ∧ rootSecondMoment nu a ≤ om

-- @node: ass:tangent-band
/-- Uniform tangent-strength lower bound `underline_r ≤ r_{a,nu}`.  The radius
`ur` is a named class constant controlling only the frontier constant.  Its
carrier is the `ℝ` parameter here; its range in `(0,∞)` is pinned at the
class-frontier site (`global_log_rate`'s `0 < ur`).
@realizes underline_r(carrier ur : ℝ; tangent-strength lower band radius, r_{a,nu} ≥ ur both arms)
@realizes r_{0,nu}, r_{1,nu}(band-context lower bound ur ≤ r_{a,nu} for both arms) -/
def TangentBand (ur : ℝ) (nu : Measure (ℝ × ℝ)) : Prop :=
  ∀ a : Fin 2, ur ≤ armTangentStrength nu a

-- @node: def:model-class
/-- Interior bounded-outcome model class `M_int`: a well-formed law (`nu` a
probability measure) with bounded outcomes and positive arm-wise root second
moments.  The `isLaw` field pins the total mass to `1`, which is what makes the
root second moment's upper end `m_a ≤ 1` (its space `(0,1]`) hold under
`BoundedOutcomes` (`y² ≤ 1` a.e. and mass `1` give `∫ y² ≤ 1`). -/
structure MInt (nu : Measure (ℝ × ℝ)) : Prop where
  -- @realizes nu(law: probability measure on [0,1]²)
  -- @realizes nu_0, nu_1(law: armMarginal nu a are probability measures on [0,1], maps of law nu)
  -- @realizes m_0, m_1(upper end m_a ≤ 1 of (0,1] for both arms needs total mass 1)
  isLaw : IsProbabilityMeasure nu
  bounded : BoundedOutcomes nu
  interiorMoments : InteriorSecondMoments nu

-- @node: def:tangent-model-class
/-- Tangent-regular model class `M_tan = M_int + ArmTangentNondegeneracy`; the
world every local-converse lemma is stated over. -/
structure MTan (nu : Measure (ℝ × ℝ)) : Prop extends MInt nu where
  tangent : ArmTangentNondegeneracy nu

-- @node: def:regular-band-class
/-- Compact tangent-regular band class `M(underline_m, overline_m, underline_r)
= M_tan + InteriorBand + TangentBand`; the world of the global minimax converse.
The radii well-formedness fields `umPos`/`umLeOm`/`omLeOne` pin the interior-band
constants into their space `(0,1]²` (`0 < um ≤ om ≤ 1`, hence both
`underline_m, overline_m ∈ (0,1]`): membership in the band class thus enforces the
constants' space, making `MBand` the CONSTRAINING-PREDICATE realization of that space
(the theorem-site `hum`/`humom`/`hom` hypotheses are then only a redundant restatement,
not the sole carrier). -/
structure MBand (um om ur : ℝ) (nu : Measure (ℝ × ℝ)) : Prop extends MTan nu where
  -- @realizes underline_m, overline_m(joint (0,1]²: umPos ∧ umLeOm ∧ omLeOne = 0<um≤om≤1)
  umPos : 0 < um  -- @realizes underline_m(space (0,1]: lower end 0 < um)
  umLeOm : um ≤ om  -- @realizes underline_m(um≤1 via um≤om≤1) @realizes overline_m(0<om via 0<um)
  omLeOne : om ≤ 1  -- @realizes overline_m(space (0,1]: upper end om ≤ 1)
  band : InteriorBand um om nu
  tangentBand : TangentBand ur nu

/-! ## Environment S2 — adaptive sequential two-arm experiment -/

-- @node: ass:predictable-design
/-- Predictable (non-anticipating) strict-interior design: `π_t` is a measurable
function of the observed history `H_{t-1} = (π_s, A_s, Y_s)_{s<t}` and valued in
the open interval `(0,1)`.  (The `H_{t-1}`-measurability is the core atom; the
strict `(0,1)` interior is the plan's D0 refinement, matching `π_t`'s space.)
@realizes pi_t(history-measurable, valued in Ioo 0 1) -/
def PredictableDesign (policy : ∀ t : ℕ, (Fin t → NeymanRecord) → ℝ) : Prop :=
  (∀ t, Measurable (policy t)) ∧ ∀ t h, policy t h ∈ Set.Ioo (0 : ℝ) 1

-- @env: S2
-- @node: def:algorithm-class
/-- Adaptive algorithm class `A_T`: a predictable strict-interior allocation
strategy, i.e. a history-measurable propensity `policy t : (Fin t → record) → ℝ`
valued in `(0,1)`.  (SYNC-BACK: realized as a concrete strategy rather than an
`AdaptiveExperiment` extension, since that world carries no measure — see the
substrate survey.  The `ass:bernoulli-randomization` member is realized by the
`jointLaw` construction and carried by the separate `BernoulliRandomization`
atom, not as a structure field, since it is a functional of `nu`.)
@realizes Alg(predictable propensity strategy) -/
structure AdaptiveAlgorithm where
  -- @realizes t(round index t : ℕ; per-round allocation over {1,...,T}, history Fin t → record)
  policy : ∀ t : ℕ, (Fin t → NeymanRecord) → ℝ
  predictable : PredictableDesign policy

/-- One-round transition kernel of the sequential experiment: draw the PO pair
`(Y(0), Y(1)) ~ nu`, draw the assignment `A ~ Bernoulli(π)`, and emit the record
`(π, A, Y)` with the observed outcome `Y = A·Y(1) + (1−A)·Y(0)`.  Helper for
`jointLaw`.  (The observed outcome `Y_t` is realized by the third record coordinate
below; its `[0,1]` range is carried by `BoundedOutcomes nu` on the PO pair `yo`.) -/
noncomputable def stepKernel (nu : Measure (ℝ × ℝ)) (π : ℝ) : Measure NeymanRecord :=
  nu.bind (fun yo =>
    (Causalean.Mathlib.Probability.bernoulliLaw π).bind (fun a =>
      -- @realizes Y_t(observed outcome A·Y(1)+(1−A)·Y(0); range [0,1] via BoundedOutcomes)
      Measure.dirac (π, a, if a = 1 then yo.2 else yo.1)))

/-- Sequential path law over horizon `T`, built by iterated kernel composition of
`stepKernel` with the predictable propensity read off the growing history.  Helper
for `jointLaw`. -/
noncomputable def pathLaw (nu : Measure (ℝ × ℝ))
    (pol : ∀ t : ℕ, (Fin t → NeymanRecord) → ℝ) :
    (T : ℕ) → Measure (Fin T → NeymanRecord)
  | 0 => Measure.dirac Fin.elim0
  | (T + 1) =>
    (pathLaw nu pol T).bind (fun hist =>
      (stepKernel nu (pol T hist)).map (Fin.snoc hist))

-- @node: def:joint-law
/-- Sequential joint law `P_{nu,Alg}` on `((0,1) × {0,1} × [0,1])^T`: the law of
the observed records `(π_t, A_t, Y_t)_{t<T}` generated by the i.i.d. `nu` draws,
the strict-interior predictable propensity, and the Bernoulli assignment.
@realizes P_{nu,Alg}(law on record^T) -/
noncomputable def jointLaw (nu : Measure (ℝ × ℝ)) (Alg : AdaptiveAlgorithm) (T : ℕ) :
    Measure (Fin T → NeymanRecord) :=
  pathLaw nu Alg.policy T

-- @node: ass:bernoulli-randomization
/-- Adaptive Bernoulli randomization `A_t | H_{t-1} ~ Bernoulli(π_t)`: the
assignment marginal of every round's transition kernel is `bernoulliLaw (π_t)`.
(Realized by the `jointLaw` construction; kept as a threaded modeling atom.)
@realizes A_t(Bernoulli(π_t) conditional on H_{t-1}) -/
def BernoulliRandomization (nu : Measure (ℝ × ℝ)) (Alg : AdaptiveAlgorithm) : Prop :=
  ∀ (t : ℕ) (hist : Fin t → NeymanRecord),
    (stepKernel nu (Alg.policy t hist)).map (fun r => r.2.1)
      = Causalean.Mathlib.Probability.bernoulliLaw (Alg.policy t hist)

/-! ## Neyman-allocation and regret constructions -/

-- @node: def:oracle-allocation
/-- Oracle Neyman allocation `π_nu* = m₁/(m₀+m₁)`, reusing
`neymanFraction (m₁²) (m₀²) = √(m₁²)/(√(m₁²)+√(m₀²)) = m₁/(m₀+m₁)` for `m_a ≥ 0`.

This is the CARRIER of the `pi_nu_star` cluster; its space `(0,1)` is not pinned by
the formula alone (at `m₁ = 0` it is `0`, at `m₀ = 0` it is `1`) but by the
accompanying standing range clause `InteriorSecondMoments` (`0 < m_a`, both arms),
which through `neymanFraction_mem_Ioo` forces `0 < oracleAllocation nu < 1`.  That
positivity is a member field of every model class (`MInt`/`MTan`/`MBand`), so the
range `(0,1)` holds standingly wherever a model-class law is in scope.
@realizes pi_nu_star(carrier neymanFraction (m₁²)(m₀²); range (0,1) pinned by the
  standing InteriorSecondMoments clause via neymanFraction_mem_Ioo) -/
noncomputable def oracleAllocation (nu : Measure (ℝ × ℝ)) : ℝ :=
  Causalean.Experimentation.DesignBased.neymanFraction
    (rootSecondMoment nu 1 ^ 2) (rootSecondMoment nu 0 ^ 2)

-- @node: def:variance-objective
/-- Neyman variance objective `V_nu(π) = m₁²/π + m₀²/(1−π)`.
@realizes V_nu(m₁²/π + m₀²/(1−π)) -/
noncomputable def varianceObjective (nu : Measure (ℝ × ℝ)) (π : ℝ) : ℝ :=
  rootSecondMoment nu 1 ^ 2 / π + rootSecondMoment nu 0 ^ 2 / (1 - π)

-- @node: def:neyman-gap
/-- Per-round Neyman loss gap `g_nu(π) = V_nu(π) − V_nu(π_nu*)`.
@realizes g_nu(V_nu π − V_nu π_nu*) -/
noncomputable def neymanGap (nu : Measure (ℝ × ℝ)) (π : ℝ) : ℝ :=
  varianceObjective nu π - varianceObjective nu (oracleAllocation nu)

-- @node: def:cumulative-regret
/-- Cumulative Neyman regret `𝔯_T(Alg,nu) = ∫ [Σ_{t<T} g_nu(π_t)] dP_{nu,Alg}`,
the headline functional.
@realizes mathfrak_R_T(Alg,nu)(∫ Σ g_nu(π_t) dP_{nu,Alg}) -/
noncomputable def cumulativeNeymanRegret
    (Alg : AdaptiveAlgorithm) (nu : Measure (ℝ × ℝ)) (T : ℕ) : ℝ :=
  -- @realizes t(round index summed over {1,...,T}, realized as Fin T)
  -- @realizes T(horizon T : ℕ; number of adaptive rounds)
  ∫ path, ∑ t : Fin T, neymanGap nu ((path t).1) ∂(jointLaw nu Alg T)

-- @node: def:oracle-sensitivity
/-- Oracle-allocation sensitivity `π̇_nu(u) = (u₁ m₀/m₁ − u₀ m₁/m₀)/(2(m₀+m₁)²)`.
@realizes dot_pi_nu(u)(local oracle-allocation derivative) -/
noncomputable def oracleSensitivity (nu : Measure (ℝ × ℝ)) (u : ℝ × ℝ) : ℝ :=
  (u.2 * rootSecondMoment nu 0 / rootSecondMoment nu 1
      - u.1 * rootSecondMoment nu 1 / rootSecondMoment nu 0)
    / (2 * (rootSecondMoment nu 0 + rootSecondMoment nu 1) ^ 2)

-- @node: def:loss-curvature
/-- Loss curvature `H_nu = (m₀+m₁)⁴/(m₀ m₁)`, the quadratic curvature of `g_nu`
at `π_nu*`.
@realizes H_nu((m₀+m₁)⁴/(m₀ m₁)) -/
noncomputable def lossCurvature (nu : Measure (ℝ × ℝ)) : ℝ :=
  (rootSecondMoment nu 0 + rootSecondMoment nu 1) ^ 4
    / (rootSecondMoment nu 0 * rootSecondMoment nu 1)

end CausalSmith.Stat.NeymanRegretMinimax
