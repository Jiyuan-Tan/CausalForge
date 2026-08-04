/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Reverse-KL exact-shell contextual bandits: shared core

Stage-2 scaffold for `stat_reversekl_two_coverage`.

## Causalean substrate survey

| Submodule | Decision | Reason |
| --- | --- | --- |
| `Causalean.Stat.Sample.PiTransport` | reuse | supplies the `Measure.pi` i.i.d.-sample interface used by `productLaw`. |
| `Causalean.Stat.Minimax.MinimaxRisk` | bypass-justified | its public results concern scalar estimation loss, whereas this paper minimizes expected regularized policy regret. |
| `Causalean.PO`, `Causalean.SCM`, `Causalean.Estimation` | bypass-justified | their causal-identification worlds do not model a fixed finite public contextual-bandit experiment. |
| `Causalean.Stat.Concentration.Covering.CoveringNumber` | reuse target | the learner and localization files use its finite-net abstraction. |

The one-observation law below is a genuine measure on `(X,A,Y)`.  The public
experiment contains no context law: `contextMass P` is derived from `P`.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Causalean.Stat.Sample.PiTransport
import Causalean.Stat.Minimax.MinimaxRisk

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal Topology

/-! ## Environment S1: public experiment and one-observation laws -/

-- @env: S1
variable {d n : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
  -- @realizes \mathcal X(discrete/Borel measurable finite context support)
  -- @realizes \mathcal A(discrete/Borel measurable finite action support)

/-- One logged observation `Z=(X,A,Y)`. -/
structure BanditObservation (𝒳 𝒜 : Type*) where
  context : 𝒳 -- @realizes X(carrier 𝒳)
  action : 𝒜 -- @realizes A(carrier 𝒜)
  reward : ℝ -- @realizes Y(carrier ℝ; a.s. range [0,1] in BanditLaw.reward_mem)

instance instMeasurableSpaceBanditObservation
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒜] :
    MeasurableSpace (BanditObservation 𝒳 𝒜) :=
  MeasurableSpace.comap
    (fun z : BanditObservation 𝒳 𝒜 => (z.context, z.action, z.reward)) inferInstance

/-- A stochastic policy represented by its finite action probabilities. -/
abbrev Policy (𝒳 𝒜 : Type*) := 𝒳 → 𝒜 → ℝ

/-- Row-wise probability-simplex constraints. -/
def IsPolicy [Fintype 𝒜] (π : Policy 𝒳 𝒜) : Prop :=
  (∀ x a, 0 ≤ π x a) ∧ ∀ x, ∑ a, π x a = 1

/-- Data carried by the public experiment. -/
structure CommonExperimentData (d : ℕ) (𝒳 𝒜 : Type*)
    [Fintype 𝒳] [Fintype 𝒜] where
  feature : 𝒳 → 𝒜 → Fin d → ℝ
    -- @realizes \phi(carrier 𝒳×𝒜→ℝ^d)
  reference : Policy 𝒳 𝒜
    -- @realizes \pi_{\mathrm{ref}}(carrier 𝒳→Δ(𝒜); simplex pinned by reference_isPolicy)
  eta : ℝ -- @realizes \eta(carrier ℝ; positive via eta_pos)
  reference_isPolicy : IsPolicy reference
    -- @realizes \pi_{\mathrm{ref}}(range Δ(𝒜): nonnegative rows summing to one)
  eta_pos : 0 < eta -- @realizes \eta(range ℝ_{>0})
  dim_ge_four : 4 ≤ d -- @realizes d(range {4,5,...})

-- @node: def:common-experiment
/-- The fixed public design `𝔈=(𝒳,𝒜,φ,π_ref,η)`.  The context law is
intentionally absent. -/
def CommonExperiment (d : ℕ) (𝒳 𝒜 : Type*)
    [Fintype 𝒳] [Fintype 𝒜]
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
    [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜] : Type _ :=
  CommonExperimentData d 𝒳 𝒜
  -- @realizes \mathfrak E(tuple (𝒳,𝒜,φ,π_ref,η), excluding law-specific ρ)
  -- @realizes \mathcal X(carrier type 𝒳; finiteness via FiniteContexts)
  -- @realizes \mathcal A(carrier type 𝒜; finiteness via FiniteActions)
  -- @realizes S(carrier 𝒳×𝒜)

variable {E : CommonExperiment d 𝒳 𝒜}

/-- A bounded contextual-bandit one-observation law with its linear coefficient. -/
structure BanditLaw (E : CommonExperiment d 𝒳 𝒜) where
  dataMeasure : Measure (BanditObservation 𝒳 𝒜)
    -- @realizes P(one-observation law on S×[0,1])
  isProbability : IsProbabilityMeasure dataMeasure
  reward_mem : ∀ᵐ z ∂dataMeasure, z.reward ∈ Set.Icc (0 : ℝ) 1
    -- @realizes Y(a.s. range [0,1])
  theta : Fin d → ℝ -- @realizes \theta(carrier ℝ^d)

/-- Context marginal mass derived from the law. -/
noncomputable def contextMass (P : BanditLaw E) (x : 𝒳) : ℝ :=
  (P.dataMeasure {z | z.context = x}).toReal
  -- @realizes \rho(context distribution Δ(𝒳), derived from P)

/-- Context-action cell mass derived from the one-observation law. -/
noncomputable def cellMass (P : BanditLaw E) (x : 𝒳) (a : 𝒜) : ℝ :=
  (P.dataMeasure {z | z.context = x ∧ z.action = a}).toReal

/-- Conditional reward mean on a positive-mass cell.  Its value on a null cell
is immaterial; the conditional-mean conjunct of `LinearRealizability` only
constrains active cells, while its range conjunct constrains `linearReward`
globally. -/
noncomputable def rewardMean (P : BanditLaw E) (x : 𝒳) (a : 𝒜) : ℝ :=
  (∫ z in {z | z.context = x ∧ z.action = a}, z.reward ∂P.dataMeasure) /
    cellMass P x a
  -- @realizes r_\theta(carrier S→[0,1]; formula tied by LinearRealizability)

/-- Linear prediction generated by the public features and the law coefficient. -/
def linearReward (P : BanditLaw E) (x : 𝒳) (a : 𝒜) : ℝ :=
  ∑ i, E.feature x a i * P.theta i
  -- @realizes r_\theta(formula rθ(x,a)=φ(x,a)ᵀθ)

/-- Gibbs normalizer at a context. -/
noncomputable def gibbsNormalizer (E : CommonExperiment d 𝒳 𝒜)
    (P : BanditLaw E) (x : 𝒳) : ℝ :=
  ∑ a, E.reference x a * Real.exp (E.eta * linearReward P x a)

/-- Population Gibbs optimum. -/
noncomputable def gibbsPolicy (E : CommonExperiment d 𝒳 𝒜)
    (P : BanditLaw E) : Policy 𝒳 𝒜 :=
  fun x a =>
    E.reference x a * Real.exp (E.eta * linearReward P x a) /
      gibbsNormalizer E P x
  -- @realizes \pi_P^\star(Gibbs formula πref·exp(ηrθ)/normalizer)

/-- Finite-action KL on the finite-value domain `PolicySupportedOn π q`.
Outside that domain the paper's KL is extended-real valued; no theorem or
admissible learner may interpret this real-valued representative there. -/
noncomputable def policyKL (π q : Policy 𝒳 𝒜) (x : 𝒳) : ℝ :=
  ∑ a, if π x a = 0 then 0 else π x a * Real.log (π x a / q x a)

/-- A policy is supported on a reference policy when it assigns zero mass to
every action to which the reference assigns zero mass. -/
def PolicySupportedOn (π q : Policy 𝒳 𝒜) : Prop :=
  ∀ x a, q x a = 0 → π x a = 0

/-- Contextwise version of reference support, used by the public repair. -/
def PolicySupportedAt (π q : Policy 𝒳 𝒜) (x : 𝒳) : Prop :=
  ∀ a, q x a = 0 → π x a = 0

/-- Public contextwise support repair.  A supported row is retained verbatim;
an offending row is replaced by the public reference row. -/
noncomputable def supportRepair (E : CommonExperiment d 𝒳 𝒜)
    (π : Policy 𝒳 𝒜) : Policy 𝒳 𝒜 := by
  classical
  exact fun x =>
    if PolicySupportedAt π E.reference x then π x else E.reference x

/-- Reverse-KL-regularized population welfare on reference-supported policies.
`IsMeasurableLearner` below restricts the minimax class to this finite-value
domain, which is equivalent to excluding the paper's infinite-regret policies. -/
noncomputable def regularizedWelfare (E : CommonExperiment d 𝒳 𝒜)
    (P : BanditLaw E) (π : Policy 𝒳 𝒜) : ℝ :=
  (∑ x, contextMass P x * ∑ a, π x a * linearReward P x a) -
    E.eta⁻¹ * ∑ x, contextMass P x * policyKL π E.reference x
  -- @realizes J_{\eta,P}(finite real restriction on reference-supported policies)

/-- The paper's extended reverse-KL welfare on the full policy simplex.
Policies leaving reference support at a positive-context-mass row have value
`-∞`; on the supported domain this embeds the real-valued restriction above. -/
noncomputable def extendedRegularizedWelfare
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E)
    (π : Policy 𝒳 𝒜) : WithBot ℝ := by
  classical
  exact if ∃ x, 0 < contextMass P x ∧ ¬ PolicySupportedAt π E.reference x
    then ⊥
    else ↑(regularizedWelfare E P π)
  -- @realizes J_{\eta,P}(extended codomain ℝ∪{-∞}; off-support value -∞)

/-- Logging feature covariance. -/
noncomputable def loggingCovariance (E : CommonExperiment d 𝒳 𝒜)
    (P : BanditLaw E) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j =>
    ∑ x, contextMass P x *
      ∑ a, E.reference x a * (E.feature x a i * E.feature x a j)
  -- @realizes \Lambda_{\mathrm{ref}}(E_{ρ,πref}[φφᵀ])

/-- Target/Gibbs feature covariance. -/
noncomputable def targetCovariance (E : CommonExperiment d 𝒳 𝒜)
    (P : BanditLaw E) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j =>
    ∑ x, contextMass P x *
      ∑ a, gibbsPolicy E P x a * (E.feature x a i * E.feature x a j)
  -- @realizes \Lambda_P^\star(E_{ρ,π*}[φφᵀ])

/-- Quadratic form of a real matrix. -/
def quadraticForm (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * M i j * v j

/-- Largest generalized Rayleigh quotient.  Under positive-definite logging
geometry this is the largest eigenvalue of the whitened target covariance. -/
noncomputable def maxGeneralizedEigenvalue
    (L T : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  sSup {q : ℝ | ∃ v : Fin d → ℝ, v ≠ 0 ∧
    q = quadraticForm T v / quadraticForm L v}

/-- Pointwise target-to-reference coverage. -/
noncomputable def pointwiseCoverage (E : CommonExperiment d 𝒳 𝒜)
    (P : BanditLaw E) : ℝ :=
  sSup {c : ℝ | ∃ x a, 0 < contextMass P x ∧ 0 < E.reference x a ∧
    c = gibbsPolicy E P x a / E.reference x a}
  -- @realizes C_P(ess sup on finite active support of π*/πref)

/-- Feature coverage. -/
noncomputable def featureCoverage (E : CommonExperiment d 𝒳 𝒜)
    (P : BanditLaw E) : ℝ :=
  maxGeneralizedEigenvalue (loggingCovariance E P) (targetCovariance E P)
  -- @realizes D_P(λmax(Λref^{-1/2}Λ*Λref^{-1/2}) via generalized Rayleigh quotient)

/-- Trace-type feature coverage. -/
noncomputable def traceCoverage (E : CommonExperiment d 𝒳 𝒜)
    (P : BanditLaw E) : ℝ :=
  ∑ i, ∑ j, (loggingCovariance E P)⁻¹ i j * targetCovariance E P j i
  -- @realizes D_{2,P}(tr(Λref⁻¹Λ*))

/-! ## Assumption atoms -/

-- @node: ass:finite-contexts
def FiniteContexts (𝒳 : Type*) : Prop := Nonempty (Fintype 𝒳)
  -- @realizes \mathcal X(finite context support)

-- @node: ass:finite-actions
def FiniteActions (𝒜 : Type*) : Prop := Nonempty (Fintype 𝒜)
  -- @realizes \mathcal A(finite action support)

-- @node: ass:bounded-features
def BoundedFeatures (E : CommonExperiment d 𝒳 𝒜) : Prop :=
  ∀ x a, Real.sqrt (∑ i, (E.feature x a i) ^ 2) ≤ 1
  -- @realizes \phi(sup_{(x,a)∈S} ‖φ(x,a)‖₂ ≤ 1)

-- @node: ass:linear-realizability
def LinearRealizability (E : CommonExperiment d 𝒳 𝒜)
    (P : BanditLaw E) : Prop :=
  (∀ x a, linearReward P x a ∈ Set.Icc (0 : ℝ) 1) ∧
    -- @realizes r_\theta(global function S→[0,1])
    ∀ x a, 0 < cellMass P x a →
      rewardMean P x a = linearReward P x a
      -- @realizes r_\theta(E_P[Y|X=x,A=a]=φ(x,a)ᵀθ on positive-mass cells)

-- @node: ass:reference-logging
def ReferenceLogging (E : CommonExperiment d 𝒳 𝒜)
    (P : BanditLaw E) : Prop :=
  ∀ x a, cellMass P x a = contextMass P x * E.reference x a
  -- @realizes \rho(arbitrary active context support; zero mass is permitted off support)
  -- @realizes \pi_{\mathrm{ref}}(logging factorization on every active context)

-- @node: ass:nonsingular-logging-geometry
def NonsingularLoggingGeometry (E : CommonExperiment d 𝒳 𝒜)
    (P : BanditLaw E) : Prop :=
  Matrix.PosDef (loggingCovariance E P)
  -- @realizes \Lambda_{\mathrm{ref}}(positive definite)

-- @node: ass:pointwise-exact-shell
def PointwiseExactShell (E : CommonExperiment d 𝒳 𝒜)
    (P : BanditLaw E) (C : ℝ) : Prop := -- @realizes C(carrier ℝ)
  1 ≤ C ∧ -- @realizes C(shell index range [1,∞))
    pointwiseCoverage E P = C
    -- @realizes C_P(exact equality C_P=C)

-- @node: ass:feature-exact-shell
def FeatureExactShell (E : CommonExperiment d 𝒳 𝒜)
    (P : BanditLaw E) (D : ℝ) : Prop :=
  0 < D ∧ featureCoverage E P = D
  -- @realizes D(shell index range (0,∞) inherited from D_P)
  -- @realizes D_P(exact equality D_P=D)

-- @node: def:exact-shell
/-- Membership in the exact linear reverse-KL shell for the fixed public
experiment. -/
structure ExactShell (E : CommonExperiment d 𝒳 𝒜)
    (P : BanditLaw E) (C D : ℝ) : Prop where
  finiteContexts : FiniteContexts 𝒳
  finiteActions : FiniteActions 𝒜
  boundedFeatures : BoundedFeatures E
  linearRealizability : LinearRealizability E P
  referenceLogging : ReferenceLogging E P
  nonsingularLoggingGeometry : NonsingularLoggingGeometry E P
  pointwiseExactShell : PointwiseExactShell E P C
  featureExactShell : FeatureExactShell E P D
  -- @realizes \mathcal M_{\mathfrak E}(d,C,D,\eta)(laws P satisfying all eight member atoms)
  -- @realizes \mathcal M(d,C,D,\eta)(fixed-experiment abbreviation)

/-! ## Environment S2: learner class, minimax risk, and sample complexity -/

-- @env: S2
variable (E : CommonExperiment d 𝒳 𝒜)

/-- `n` observations supplied to a learner. -/
abbrev LoggedSample (n : ℕ) (𝒳 𝒜 : Type*) :=
  Fin n → BanditObservation 𝒳 𝒜
  -- @realizes Z_i(carrier coordinate (X_i,A_i,Y_i); boundedness via BoundedLoggedSample)
  -- @realizes \mathcal D_n(product carrier; boundedness via productLaw_bounded_sample)

/-- Every coordinate of a logged sample lies in `S × [0,1]`. -/
def BoundedLoggedSample (sample : LoggedSample n 𝒳 𝒜) : Prop :=
  ∀ i, (sample i).reward ∈ Set.Icc (0 : ℝ) 1
  -- @realizes Z_i(each coordinate belongs to S×[0,1])
  -- @realizes \mathcal D_n(sample belongs to (S×[0,1])^n)

/-- Product law of the i.i.d. logged sample. -/
noncomputable def productLaw (P : BanditLaw E) (n : ℕ) :
    Measure (LoggedSample n 𝒳 𝒜) := by
  letI : IsProbabilityMeasure P.dataMeasure := P.isProbability
  exact Measure.pi (fun _ : Fin n => P.dataMeasure)
  -- @realizes P^{\otimes n}(n-fold product observation law)

/-- The product sample is almost surely supported on bounded bandit observations. -/
lemma productLaw_bounded_sample (P : BanditLaw E) (n : ℕ) :
    ∀ᵐ sample ∂productLaw E P n, BoundedLoggedSample sample := by
  letI : IsProbabilityMeasure P.dataMeasure := P.isProbability
  simp only [BoundedLoggedSample]
  refine ae_all_iff.mpr (fun i ↦ ?_)
  exact (measurePreserving_eval (fun _ : Fin n ↦ P.dataMeasure) i).quasiMeasurePreserving
    |>.ae P.reward_mem
  -- @realizes Z_i(P^n-a.s. coordinate range S×[0,1])
  -- @realizes \mathcal D_n(P^n-a.s. range (S×[0,1])^n)

/-- A policy learner whose mathematical domain is the bounded sample space
`(S × [0,1])ⁿ`. -/
abbrev Learner (n : ℕ) :=
  (sample : LoggedSample n 𝒳 𝒜) → BoundedLoggedSample sample → Policy 𝒳 𝒜

/-- Totalization used only to integrate a bounded-domain learner against the
raw product carrier.  The fallback is irrelevant almost surely. -/
noncomputable def learnerPolicyOnSample
    (L : Learner n (𝒳 := 𝒳) (𝒜 := 𝒜))
    (sample : LoggedSample n 𝒳 𝒜) : Policy 𝒳 𝒜 := by
  classical
  exact if h : BoundedLoggedSample sample then L sample h else E.reference

/-- Coordinatewise measurable simplex-valued maps from bounded samples whose
outputs lie in the finite-KL domain. Policies outside reference support have
infinite regret in the paper's extended-real convention and therefore cannot
improve the minimax infimum. -/
def IsMeasurableLearner
    (L : Learner n (𝒳 := 𝒳) (𝒜 := 𝒜)) : Prop :=
  (∀ x a, Measurable (fun sample => learnerPolicyOnSample E L sample x a)) ∧
    ∀ sample hs,
      IsPolicy (L sample hs) ∧ PolicySupportedOn (L sample hs) E.reference
  -- @realizes \mathcal L_n(\mathfrak E)(measurable maps into the
  -- finite-objective reference-supported part of Δ(𝒜)^𝒳)

/-- The corresponding measurable full-simplex decision class, before the
public support repair is applied. -/
def IsMeasurableFullLearner
    (L : Learner n (𝒳 := 𝒳) (𝒜 := 𝒜)) : Prop :=
  (∀ x a, Measurable (fun sample => learnerPolicyOnSample E L sample x a)) ∧
    ∀ sample hs, IsPolicy (L sample hs)

/-- Apply the public support repair to every output of a learner. -/
noncomputable def supportRepairLearner
    (L : Learner n (𝒳 := 𝒳) (𝒜 := 𝒜)) :
    Learner n (𝒳 := 𝒳) (𝒜 := 𝒜) :=
  fun sample hs => supportRepair E (L sample hs)

/-- On the standing finite discrete supports, support repair is Borel
measurable and maps the full-simplex class into the finite-objective class. -/
-- @node: supportRepairLearner_mem
lemma supportRepairLearner_mem
    (L : Learner n (𝒳 := 𝒳) (𝒜 := 𝒜))
    (hL : IsMeasurableFullLearner E L) :
    IsMeasurableLearner E (supportRepairLearner E L) := by
  classical
  constructor
  · intro x a
    have hsupp_meas : MeasurableSet
        {sample : LoggedSample n 𝒳 𝒜 |
          PolicySupportedAt (learnerPolicyOnSample E L sample) E.reference x} := by
      simp only [PolicySupportedAt]
      rw [show {sample : LoggedSample n 𝒳 𝒜 |
          ∀ b, E.reference x b = 0 →
            learnerPolicyOnSample E L sample x b = 0} =
          ⋂ b : 𝒜, {sample |
            E.reference x b = 0 →
              learnerPolicyOnSample E L sample x b = 0} by
        ext sample
        simp]
      refine MeasurableSet.iInter fun (b : 𝒜) ↦ ?_
      by_cases href : E.reference x b = 0
      · simp only [href, true_implies]
        simpa only [Set.preimage, Set.mem_singleton_iff] using
          hL.1 x b (MeasurableSet.singleton 0)
      · simp [href]
    rw [show (fun sample =>
        learnerPolicyOnSample E (supportRepairLearner E L) sample x a) =
        fun sample => if PolicySupportedAt (learnerPolicyOnSample E L sample)
            E.reference x
          then learnerPolicyOnSample E L sample x a
          else E.reference x a by
      funext sample
      by_cases hsample : BoundedLoggedSample sample
      · by_cases hsupp : PolicySupportedAt (L sample hsample) E.reference x
        · simp [learnerPolicyOnSample, supportRepairLearner, hsample,
            supportRepair, hsupp]
        · simp [learnerPolicyOnSample, supportRepairLearner, hsample,
            supportRepair, hsupp]
      · have hrefsupp : PolicySupportedAt E.reference E.reference x := by
          intro b hb
          exact hb
        simp [learnerPolicyOnSample, supportRepairLearner, hsample,
          supportRepair, hrefsupp]
    ]
    exact Measurable.ite hsupp_meas (hL.1 x a) measurable_const
  · intro sample hs
    have hpol := hL.2 sample hs
    constructor
    · constructor
      · intro x a
        simp only [supportRepairLearner, supportRepair]
        split_ifs
        · exact hpol.1 x a
        · exact E.reference_isPolicy.1 x a
      · intro x
        simp only [supportRepairLearner, supportRepair]
        split_ifs
        · exact hpol.2 x
        · exact E.reference_isPolicy.2 x
    · intro x a href
      simp only [supportRepairLearner, supportRepair]
      split_ifs with hsupp
      · exact hsupp a href
      · exact href

/-- Expected regularized regret of a fixed learner under one law. -/
noncomputable def learnerRisk (P : BanditLaw E) (n : ℕ)
    (L : Learner n (𝒳 := 𝒳) (𝒜 := 𝒜)) : ℝ :=
  ∫ sample,
    (regularizedWelfare E P (gibbsPolicy E P) -
      regularizedWelfare E P (learnerPolicyOnSample E L sample)) ∂productLaw E P n

/-- A positive-mass context at which a policy leaves reference support. -/
def HasActiveSupportViolation (P : BanditLaw E) (π : Policy 𝒳 𝒜) : Prop :=
  ∃ x, 0 < contextMass P x ∧ ¬ PolicySupportedAt π E.reference x

/-- Extended reverse-KL regret.  An active support violation has value
`+∞`; otherwise this is the finite reference-supported regret. -/
noncomputable def extendedRegret (P : BanditLaw E) (π : Policy 𝒳 𝒜) : ℝ≥0∞ :=
  by
    classical
    exact if HasActiveSupportViolation E P π then ⊤
      else ENNReal.ofReal
        (regularizedWelfare E P (gibbsPolicy E P) -
          regularizedWelfare E P π)

/-- The public repair never increases extended reverse-KL regret. -/
lemma supportRepair_extendedRegret_le
    (P : BanditLaw E) (π : Policy 𝒳 𝒜) :
    extendedRegret E P (supportRepair E π) ≤ extendedRegret E P π := by
  classical
  by_cases hviol : HasActiveSupportViolation E P π
  · simp [extendedRegret, hviol]
  have hrepaired_no : ¬ HasActiveSupportViolation E P (supportRepair E π) := by
    rintro ⟨x, hx, hbad⟩
    apply hbad
    intro a href
    simp only [supportRepair]
    split_ifs with hsupp
    · exact hsupp a href
    · exact href
  have hrow (x : 𝒳) (hx : 0 < contextMass P x) :
      supportRepair E π x = π x := by
    simp only [supportRepair]
    rw [if_pos]
    intro a href
    by_contra hne
    exact hviol ⟨x, hx, fun hsupp ↦ hne (hsupp a href)⟩
  have hwelfare :
      regularizedWelfare E P (supportRepair E π) =
        regularizedWelfare E P π := by
    simp only [regularizedWelfare]
    congr 1
    · apply Finset.sum_congr rfl
      intro x _
      by_cases hx : contextMass P x = 0
      · simp [hx]
      · rw [hrow x (lt_of_le_of_ne
          (by exact ENNReal.toReal_nonneg) (Ne.symm hx))]
    · congr 1
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : contextMass P x = 0
      · simp [hx]
      · simp only [policyKL]
        rw [hrow x (lt_of_le_of_ne
          (by exact ENNReal.toReal_nonneg) (Ne.symm hx))]
  simp [extendedRegret, hviol, hrepaired_no, hwelfare]

/-- Full-simplex risk, with the loss interpreted in `[0,+∞]`. -/
noncomputable def fullSimplexLearnerRisk (P : BanditLaw E) (n : ℕ)
    (L : Learner n (𝒳 := 𝒳) (𝒜 := 𝒜)) : ℝ≥0∞ :=
  ∫⁻ sample, extendedRegret E P (learnerPolicyOnSample E L sample) ∂productLaw E P n

-- @node: def:minimax-risk
/-- Infimum over all measurable simplex-valued learners of worst-law expected
regularized regret. -/
noncomputable def minimaxRisk (n : ℕ) (model : Set (BanditLaw E)) : ℝ :=
  sInf {r : ℝ | ∃ L : Learner n (𝒳 := 𝒳) (𝒜 := 𝒜), IsMeasurableLearner E L ∧
    r = sSup {q : ℝ | ∃ P : BanditLaw E, P ∈ model ∧ q = learnerRisk E P n L}}
  -- @realizes \mathfrak R_{n,\mathfrak E}(inf_L sup_P E_{P^n}[J(π*)-J(L)])
  -- @realizes \mathfrak R_n(fixed-experiment abbreviation)

/-- The same minimax problem over every measurable full-simplex learner,
retaining the paper's extended reverse-KL loss. -/
noncomputable def fullSimplexMinimaxRisk
    (n : ℕ) (model : Set (BanditLaw E)) : ℝ≥0∞ :=
  sInf {r : ℝ≥0∞ |
    ∃ L : Learner n (𝒳 := 𝒳) (𝒜 := 𝒜),
      IsMeasurableFullLearner E L ∧
      r = sSup {q : ℝ≥0∞ |
        ∃ P : BanditLaw E, P ∈ model ∧
          q = fullSimplexLearnerRisk E P n L}}

/-- Public support repair proves that the supported real-valued formulation
and the full-simplex extended formulation have the same minimax value. -/
lemma minimaxRisk_eq_fullSimplex
    (n : ℕ) (model : Set (BanditLaw E)) (hmodel : model.Nonempty) :
    0 ≤ minimaxRisk E n model ∧
      ENNReal.ofReal (minimaxRisk E n model) =
        fullSimplexMinimaxRisk E n model := by
  sorry

/-- The exact shell as a set of laws. -/
def exactShellSet (C D : ℝ) : Set (BanditLaw E) :=
  {P | ExactShell E P C D}

/-- The same infimum formula on the all-positive accuracy domain used by the
paper's boundary and experiment-uniform ceiling clauses. -/
noncomputable def sampleComplexityPositive (ε C D : ℝ)
    (_hε : 0 < ε) : WithTop ℕ :=
  by
    classical
    exact if (exactShellSet E C D).Nonempty then
      sInf {m : WithTop ℕ | ∃ n : ℕ, 1 ≤ n ∧ m = n ∧
        minimaxRisk E n (exactShellSet E C D) ≤ ε}
    else ⊤
  -- @realizes \epsilon(all-positive extension for boundary and uniform-ceiling clauses)

-- @node: def:sample-complexity
/-- First sample size whose exact-shell minimax risk is at most `ε`, with
`sInf ∅ = ⊤`, on the declared accuracy space `0 < ε < 1`. -/
noncomputable def sampleComplexity (ε C D : ℝ)
    (_hε : 0 < ε) (_hε_one : ε < 1) : WithTop ℕ :=
  sampleComplexityPositive E ε C D _hε
  -- @realizes N^\star_{\mathfrak E}(inf{n≥1 : R_{n,E}(M_E)≤ε}, empty inf = ∞)
  -- @realizes N^\star(fixed-experiment abbreviation)
  -- @realizes \epsilon(domain 0<ε<1, carried by both proof-bearing arguments)
  -- @realizes n(sample-size carrier ℕ)

end CausalSmith.Stat.ReverseKLTwoCoverage
