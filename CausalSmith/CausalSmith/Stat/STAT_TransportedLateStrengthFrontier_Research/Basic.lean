/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Transported LATE strength frontier: shared model

This file gives the explicit two-population coordinate law, its observed source
experiment, the sixteen named modeling assumptions, the two model classes, and
the deterministic geometry and finite-cell slices used by the paper.

The potential-outcome layer deliberately bypasses the regime-indexed
`Causalean.PO` world: that API has no population indicator or transport law.
`Causalean.PO.ID.Exact.LATE` is imported as the analogous identification chain.
The two independent finite product samples reuse `Causalean.Stat.Sample` and
`Causalean.Stat.Sample.PiTransport`.
-/

import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.UniformOn
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Causalean.Stat.Sample
import Causalean.Stat.Sample.PiTransport
import Causalean.PO.ID.Exact.LATE

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

/-! ## Explicit full-data and observed-data worlds -/

/-- Full-data coordinate `(S,X,D(0),D(1),Y(0),Y(1))`. -/
abbrev FullData (𝒳 : Type*) := Bool × 𝒳 × Bool × Bool × ℝ × ℝ

/-- Source observation `(X,Z,D,Y)`. -/
abbrev SourceObs (𝒳 : Type*) := 𝒳 × Bool × Bool × ℝ

/-- The assigned source overlay `(full data,Z)`. -/
abbrev AssignedFullData (𝒳 : Type*) := FullData 𝒳 × Bool

/-- Returns the indicator for whether a full-data unit belongs to the source population. -/
def fullS {𝒳 : Type*} (o : FullData 𝒳) : Bool := o.1
/-- Returns a full-data unit's covariate value. -/
def fullX {𝒳 : Type*} (o : FullData 𝒳) : 𝒳 := o.2.1
/-- Returns a unit's potential treatment receipt under instrument value zero. -/
def fullD0 {𝒳 : Type*} (o : FullData 𝒳) : Bool := o.2.2.1
/-- Returns a unit's potential treatment receipt under instrument value one. -/
def fullD1 {𝒳 : Type*} (o : FullData 𝒳) : Bool := o.2.2.2.1
/-- Returns a unit's potential outcome under treatment receipt zero. -/
def fullY0 {𝒳 : Type*} (o : FullData 𝒳) : ℝ := o.2.2.2.2.1
/-- Returns a unit's potential outcome under treatment receipt one. -/
def fullY1 {𝒳 : Type*} (o : FullData 𝒳) : ℝ := o.2.2.2.2.2

/-- Converts a binary indicator to its real-valued zero-one representation. -/
def boolReal (b : Bool) : ℝ := if b then 1 else 0

/-- Returns the treatment receipt a unit would have under the specified instrument assignment. -/
def potentialReceipt {𝒳 : Type*} (o : FullData 𝒳) (z : Bool) : Bool :=
  if z then fullD1 o else fullD0 o

/-- Returns the outcome a unit would have under the specified treatment receipt. -/
def potentialOutcome {𝒳 : Type*} (o : FullData 𝒳) (d : Bool) : ℝ :=
  if d then fullY1 o else fullY0 o

/-- An array law contains only primitive laws and conditional-mean versions.
The assumption atoms below pin every version to its law by integral identities. -/
structure TransportedArray (𝒳 : Type*) [MeasurableSpace 𝒳] where
  fullLaw : ℕ → Measure (FullData 𝒳)
    -- @realizes P_n^F(full-data law carrier; probability/support via FullDataSupport)
    -- @realizes P(triangular array primitive)
  assignedSourceLaw : ℕ → Measure (AssignedFullData 𝒳)
    -- @realizes P_S(source assigned-full-data carrier)
  propensity : ℕ → 𝒳 → ℝ
    -- @realizes e(carrier 𝒳→ℝ; range pinned by InstrumentOverlap)
  propensity_measurable : ∀ n, Measurable (propensity n)
  assignmentOutcome : ℕ → Bool → FullData 𝒳 → ℝ
    -- @realizes Y^Z(z)(assignment-potential-outcome carrier; pinned by IVExclusion)
  assignmentOutcome_measurable : ∀ n z, Measurable (assignmentOutcome n z)
  assignmentContrast : ℕ → Bool → 𝒳 → ℝ
  assignmentContrast_measurable : ∀ n s, Measurable (assignmentContrast n s)
  receiptContrast : ℕ → Bool → 𝒳 → ℝ
  receiptContrast_measurable : ∀ n s, Measurable (receiptContrast n s)

-- @env: S1
variable {𝒳 : Type*} [MeasurableSpace 𝒳]
  -- @realizes \mathcal X(measurable covariate space)
variable (n : ℕ)
  -- @realizes n(asymptotic index in Nat)
variable (P : TransportedArray 𝒳)
  -- @realizes P(array of full-data laws and propensity)

/-- Population-conditioned full-data law. -/
noncomputable def populationLaw (P : TransportedArray 𝒳) (n : ℕ) (s : Bool) :
    Measure (FullData 𝒳) :=
  ProbabilityTheory.cond (P.fullLaw n) {o | fullS o = s}
  -- @realizes S(Bool population indicator; true=source, false=target)

/-- The covariate marginal in population `s`. -/
noncomputable def populationXLaw (P : TransportedArray 𝒳) (n : ℕ) (s : Bool) :
    Measure 𝒳 :=
  (populationLaw P n s).map fullX
  -- @realizes X(covariate carrier 𝒳 under the contextual population)

/-- Target covariate law. -/
noncomputable def targetXLaw (P : TransportedArray 𝒳) (n : ℕ) : Measure 𝒳 :=
  populationXLaw P n false
  -- @realizes P_T(X-marginal conditional on S=false)

/-- Assignment potential outcome `Y(D(z))`. -/
def derivedAssignmentOutcome (o : FullData 𝒳) (z : Bool) : ℝ :=
  potentialOutcome o (potentialReceipt o z)
  -- @realizes Y^Z(z)(Y(D(z)))

/-- The observed source record derived from assigned full data. -/
def observeSource (q : AssignedFullData 𝒳) : SourceObs 𝒳 :=
  (fullX q.1, q.2, potentialReceipt q.1 q.2,
    potentialOutcome q.1 (potentialReceipt q.1 q.2))
  -- @realizes O_i^S((X_i,Z_i,D_i,Y_i))
  -- @realizes Z(Bool encouragement coordinate)
  -- @realizes D(Bool observed receipt D(Z))
  -- @realizes Y(real observed outcome Y(D))

/-- Observed source law induced by the assigned full-data overlay. -/
noncomputable def sourceObsLaw (P : TransportedArray 𝒳) (n : ℕ) :
    Measure (SourceObs 𝒳) :=
  (P.assignedSourceLaw n).map observeSource
  -- @realizes P_S(law of (X,Z,D,Y))

/-- Source covariate marginal. -/
noncomputable def sourceXLaw (P : TransportedArray 𝒳) (n : ℕ) : Measure 𝒳 :=
  (sourceObsLaw P n).map (fun o => o.1)
  -- @realizes P_S^X(X-marginal of P_S)

/-- Inverse-propensity score multiplier. -/
noncomputable def instrumentScore (P : TransportedArray 𝒳) (n : ℕ)
    (o : SourceObs 𝒳) : ℝ :=
  (if o.2.1 then 1 / P.propensity n o.1 else
    -1 / (1 - P.propensity n o.1))

/-- A measurable version of the observed source outcome ITT is characterized
by its integrals over every measurable covariate set. -/
def OutcomeContrastRepresentation (P : TransportedArray 𝒳) (n : ℕ)
    (f : 𝒳 → ℝ) : Prop :=
  Measurable f ∧
    ∀ A, MeasurableSet A →
      ∫ o in {o | o.1 ∈ A},
          instrumentScore P n o * o.2.2.2 ∂sourceObsLaw P n =
        ∫ x in A, f x ∂sourceXLaw P n

/-- The source outcome ITT is the canonical observed-law representative,
rather than an independently supplied model coordinate. -/
noncomputable def TransportedArray.deltaY (P : TransportedArray 𝒳)
    (n : ℕ) : 𝒳 → ℝ :=
  P.assignmentContrast n true
  -- @realizes \Delta_Y(observed conditional outcome contrast)

/-- The source conditional outcome contrast is measurable as a function of covariates. -/
lemma TransportedArray.deltaY_measurable (P : TransportedArray 𝒳) (n : ℕ) :
    Measurable (P.deltaY n) :=
  P.assignmentContrast_measurable n true

/-- A measurable version of the observed source receipt ITT is characterized
by its integrals over every measurable covariate set. -/
def ReceiptContrastRepresentation (P : TransportedArray 𝒳) (n : ℕ)
    (f : 𝒳 → ℝ) : Prop :=
  Measurable f ∧
    ∀ A, MeasurableSet A →
      ∫ o in {o | o.1 ∈ A},
          instrumentScore P n o * boolReal o.2.2.1 ∂sourceObsLaw P n =
        ∫ x in A, f x ∂sourceXLaw P n

/-- The source receipt ITT is the canonical observed-law representative,
rather than an independently supplied model coordinate. -/
noncomputable def TransportedArray.deltaD (P : TransportedArray 𝒳)
    (n : ℕ) : 𝒳 → ℝ :=
  P.receiptContrast n true
  -- @realizes \Delta_D(observed conditional receipt contrast)

/-- The source conditional treatment-receipt contrast is measurable as a function of covariates. -/
lemma TransportedArray.deltaD_measurable (P : TransportedArray 𝒳) (n : ℕ) :
    Measurable (P.deltaD n) :=
  P.receiptContrast_measurable n true

/-- Radon--Nikodym transport weight, real-valued by `ENNReal.toReal`. -/
noncomputable def transportWeight (P : TransportedArray 𝒳) (n : ℕ) : 𝒳 → ℝ :=
  fun x => ((targetXLaw P n).rnDeriv (sourceXLaw P n) x).toReal
  -- @realizes w(dP_T/dP_S^X; carrier 𝒳→[0,∞))

/-- Kish dispersion. -/
noncomputable def kishDispersion (P : TransportedArray 𝒳) (n : ℕ) : ℝ :=
  ∫ x, (transportWeight P n x) ^ 2 ∂sourceXLaw P n
  -- @realizes \kappa_n(E_S[w(X)^2]; lower range derived by TransportedFunctionalRanges)

/-- Transported source outcome contrast. -/
noncomputable def transportedOutcomeITT (P : TransportedArray 𝒳) (n : ℕ) : ℝ :=
  ∫ x, transportWeight P n x * P.deltaY n x ∂sourceXLaw P n
  -- @realizes \mu_{Y,n}(E_S[w Δ_Y]; range derived by TransportedFunctionalRanges)

/-- Target complier probability under the target population. -/
noncomputable def targetComplierShare (P : TransportedArray 𝒳) (n : ℕ) : ℝ :=
  (populationLaw P n false {o | fullD1 o = true ∧ fullD0 o = false}).toReal

/-- The paper's transported first stage is the source-law moment of the
transport weight times the identified conditional receipt contrast. -/
noncomputable def transportedFirstStage (P : TransportedArray 𝒳) (n : ℕ) : ℝ :=
  ∫ x, transportWeight P n x * P.deltaD n x ∂sourceXLaw P n
  -- @realizes \mu_n(E_S[w(X) Δ_D(X)])

/-- Effective identification strength. -/
noncomputable def effectiveStrength (P : TransportedArray 𝒳) (n : ℕ) : ℝ :=
  (n : ℝ) * (transportedFirstStage P n) ^ 2 / kishDispersion P n
  -- @realizes t_n(n μ_n^2/κ_n; positivity derived by TransportedFunctionalRanges)

/-- A positive effective-strength threshold excludes the zero sample index. -/
lemma index_pos_of_pos_le_effectiveStrength (P : TransportedArray 𝒳)
    {n : ℕ} {t0 : ℝ} (ht0 : 0 < t0)
    (hstrength : t0 ≤ effectiveStrength P n) : 0 < n := by
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  simp [effectiveStrength] at hstrength
  exact (not_lt_of_ge hstrength) ht0

/-- Forced parameter range. -/
def parameterSpace : Set ℝ := Set.Icc (-1 : ℝ) 1
  -- @realizes \Theta([-1,1])

/-- Target complier average causal effect, with Lean's total division convention. -/
noncomputable def targetCACE (P : TransportedArray 𝒳) (n : ℕ) : ℝ :=
  (∫ o, (fullY1 o - fullY0 o) *
      (if fullD1 o = true ∧ fullD0 o = false then 1 else 0)
      ∂populationLaw P n false) / targetComplierShare P n
  -- @realizes \theta_T(E[Y(1)-Y(0) | D(1)>D(0), S=0])

/-! ## Two-sample world -/

-- @env: S2
variable (N : ℕ → ℕ)
  -- @realizes N_n(target sample-size sequence)
variable (c epsilon : ℝ)
  -- @realizes c(positive target/source sample-size limit)
  -- @realizes \varepsilon(overlap constant; range pinned by InstrumentOverlap)

/-- Index-`n` source sample. -/
abbrev SourceSample (𝒳 : Type*) (n : ℕ) := Fin n → SourceObs 𝒳

/-- Index-`n` target covariate sample. -/
abbrev TargetSample (𝒳 : Type*) (N : ℕ) := Fin N → 𝒳

/-- Product sample carrier. -/
abbrev TwoSample (𝒳 : Type*) (n N : ℕ) :=
  SourceSample 𝒳 n × TargetSample 𝒳 N
  -- @realizes X_j^T(target covariate coordinate)

/-- The independent source/target finite-product sampling law. -/
noncomputable def twoSampleLaw (P : TransportedArray 𝒳) (N : ℕ → ℕ) (n : ℕ) :
    Measure (TwoSample 𝒳 n (N n)) :=
  (Measure.pi (fun _ : Fin n => sourceObsLaw P n)).prod
    (Measure.pi (fun _ : Fin (N n) => targetXLaw P n))
  -- @realizes O_i^S(i.i.d. source coordinates)
  -- @realizes X_j^T(i.i.d. target coordinates, independent by Measure.prod)

/-! ## Named modeling assumptions -/

-- @node: ass:full-data-support
/-- Full-data probability law and bounded potential outcomes. -/
def FullDataSupport (P : TransportedArray 𝒳) (n : ℕ) : Prop :=
  IsProbabilityMeasure (P.fullLaw n) ∧ -- @realizes P_n^F(probability measure)
    ∀ᵐ o : FullData 𝒳 ∂P.fullLaw n,
      fullY0 o ∈ Set.Icc (0 : ℝ) 1 ∧ -- @realizes Y(d)(Y(0)∈[0,1])
                                         -- @realizes Y^Z(z)(bounded support inherited from Y(0),Y(1))
      fullY1 o ∈ Set.Icc (0 : ℝ) 1   -- @realizes Y(d)(Y(1)∈[0,1])
                                         -- @realizes Y^Z(z)(bounded support inherited from Y(0),Y(1))

-- @node: ass:population-presence
/-- Both populations have strictly positive full-data mass. -/
def PopulationPresence (P : TransportedArray 𝒳) (n : ℕ) : Prop :=
  ∀ s : Bool, 0 < (P.fullLaw n {o | fullS o = s}).toReal
  -- @realizes S(P_n^F(S=s)>0 for both Bool values)
  -- @realizes Y^Z(z)(both population fibers have positive mass)

-- @node: ass:two-sample-array
/-- The two sample factors are probability laws and `N_n/n → c`. -/
def TwoSampleArray (P : TransportedArray 𝒳) (N : ℕ → ℕ) (c : ℝ) : Prop :=
  0 < c ∧ -- @realizes c(c∈(0,∞))
    (∀ n, IsProbabilityMeasure (sourceObsLaw P n)) ∧
    (∀ n, IsProbabilityMeasure (targetXLaw P n)) ∧
    Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 c)
    -- @realizes N_n(N_n/n→c)
    -- @realizes c(limit of N_n/n)

-- @node: ass:instrument-overlap
/-- Instrument propensity is in `[ε,1-ε]` source-almost surely. -/
def InstrumentOverlap (P : TransportedArray 𝒳) (n : ℕ) (epsilon : ℝ) : Prop :=
  0 < epsilon ∧ epsilon < 1 / 2 ∧
    ∀ᵐ x ∂sourceXLaw P n,
      epsilon ≤ P.propensity n x ∧
      P.propensity n x ≤ 1 - epsilon
      -- @realizes e(propensity range [ε,1-ε])
      -- @realizes \varepsilon(0<ε<1/2)

-- @node: ass:source-observation
/-- The paper's source assignment and consistency assumption.  The assigned
overlay is a genuine probability law with the source-population full-data
marginal; mapping it through `observeSource` enforces `D=D(Z)` and `Y=Y(D)`,
while the last clause pins the assignment propensity. -/
def SourceAssignmentConsistency (P : TransportedArray 𝒳) (n : ℕ) : Prop :=
  IsProbabilityMeasure (P.assignedSourceLaw n) ∧
    (P.assignedSourceLaw n).map Prod.fst = populationLaw P n true ∧
    (∀ A, MeasurableSet A →
      (sourceObsLaw P n {o | o.1 ∈ A ∧ o.2.1 = true}).toReal =
        ∫ x in A, P.propensity n x ∂sourceXLaw P n)
    -- @realizes P_S(genuine source probability induced from P_n^F | S=true)
    -- @realizes e(P_S(Z=1|X)=e(X))

/-- Well-definedness and auxiliary-representation facts carried by the complete
model.  These pin its observed law and contrast fields to the paper-defined
objects; `SourceAssignmentConsistency` is the paper assumption itself. -/
def SourceObservation (P : TransportedArray 𝒳) (n : ℕ) : Prop :=
  IsProbabilityMeasure (P.assignedSourceLaw n) ∧
    IsProbabilityMeasure (sourceObsLaw P n) ∧ -- @realizes P_S(probability measure)
    (∀ᵐ o ∂sourceObsLaw P n,
      o.2.2.2 ∈ Set.Icc (0 : ℝ) 1) ∧ -- @realizes Y(observed Y∈[0,1])
      -- @realizes O_i^S(observed-Y coordinate lies in [0,1])
    (P.assignedSourceLaw n).map Prod.fst = populationLaw P n true ∧
    (∀ A, MeasurableSet A →
      (sourceObsLaw P n {o | o.1 ∈ A ∧ o.2.1 = true}).toReal =
        ∫ x in A, P.propensity n x ∂sourceXLaw P n) ∧
      -- @realizes e(P_S(Z=1|X)=e(X))
    (∀ A, MeasurableSet A →
      ∫ o in {o | o.1 ∈ A},
          instrumentScore P n o * o.2.2.2 ∂sourceObsLaw P n =
        ∫ x in A, P.deltaY n x ∂sourceXLaw P n) ∧
    (∀ᵐ x ∂sourceXLaw P n,
      P.deltaY n x ∈ Set.Icc (-1 : ℝ) 1) ∧
      -- @realizes \Delta_Y(observed conditional outcome ITT in [-1,1])
    (∀ A, MeasurableSet A →
      ∫ o in {o | o.1 ∈ A},
          instrumentScore P n o * boolReal o.2.2.1 ∂sourceObsLaw P n =
        ∫ x in A, P.deltaD n x ∂sourceXLaw P n) ∧
    (∀ᵐ x ∂sourceXLaw P n,
      P.deltaD n x ∈ Set.Icc (0 : ℝ) 1)
      -- @realizes \Delta_D(observed conditional receipt ITT in [0,1])
    -- @realizes P(source assignment and observed-data law)

-- @node: ass:iv-randomization
/-- Conditional randomization: the assigned-full-data law factors with
Bernoulli propensity given the source full-data law. -/
def IVRandomization (P : TransportedArray 𝒳) (n : ℕ) : Prop :=
  ∀ (A : Set (FullData 𝒳)), MeasurableSet A → ∀ z : Bool,
    (P.assignedSourceLaw n {q | q.1 ∈ A ∧ q.2 = z}).toReal =
      ∫ o in A, (if z then P.propensity n (fullX o)
        else 1 - P.propensity n (fullX o)) ∂populationLaw P n true
    -- @realizes Z(Z ⟂ (Y(0),Y(1),D(0),D(1)) | (X,S=1))

-- @node: ass:iv-exclusion
/-- Exclusion pins the assignment potential outcome to `Y(D(z))` in both
populations. -/
def IVExclusion (P : TransportedArray 𝒳) (n : ℕ) : Prop :=
  ∀ s z : Bool, P.assignmentOutcome n z =ᵐ[populationLaw P n s]
    fun o => derivedAssignmentOutcome o z
    -- @realizes Y^Z(z)(equals Y(D(z)) in both populations)

-- @node: ass:iv-monotonicity
/-- No defiers in either population. -/
def IVMonotonicity (P : TransportedArray 𝒳) (n : ℕ) : Prop :=
  ∀ s : Bool, ∀ᵐ o ∂populationLaw P n s,
    boolReal (fullD0 o) ≤ boolReal (fullD1 o)
    -- @realizes D(z)(D(1)≥D(0) in each population)

-- @node: ass:outcome-transport
/-- Conditional assignment-outcome contrasts are pinned to each population law
and agree target-almost everywhere. -/
def OutcomeTransport (P : TransportedArray 𝒳) (n : ℕ) : Prop :=
  (∀ s : Bool, ∀ A, MeasurableSet A →
    ∫ o in {o | fullX o ∈ A},
        (P.assignmentOutcome n true o - P.assignmentOutcome n false o)
        ∂populationLaw P n s =
      ∫ x in A, P.assignmentContrast n s x ∂populationXLaw P n s) ∧
  P.assignmentContrast n false =ᵐ[targetXLaw P n]
    P.assignmentContrast n true

-- @node: ass:receipt-transport
/-- Integrated first-stage transport, with population conditional receipt
contrasts pinned by integral identities. -/
def ReceiptTransport (P : TransportedArray 𝒳) (n : ℕ) : Prop :=
  (∀ s : Bool, ∀ A, MeasurableSet A →
    ∫ o in {o | fullX o ∈ A},
        (boolReal (fullD1 o) - boolReal (fullD0 o))
        ∂populationLaw P n s =
      ∫ x in A, P.receiptContrast n s x ∂populationXLaw P n s) ∧
  (∫ x, P.receiptContrast n false x ∂targetXLaw P n) =
    ∫ x, P.receiptContrast n true x ∂targetXLaw P n

-- @node: ass:target-complier-positivity
/-- The target complier share is positive. -/
def TargetComplierPositivity (P : TransportedArray 𝒳) (n : ℕ) : Prop :=
  0 < targetComplierShare P n
  -- @realizes \mu_n(complier-share positivity input to the derived range)

-- @node: ass:transport-domination
/-- Target covariate law is absolutely continuous with respect to source. -/
def TransportDomination (P : TransportedArray 𝒳) (n : ℕ) : Prop :=
  targetXLaw P n ≪ sourceXLaw P n

-- @node: ass:weight-envelope
/-- The transport density ratio is capped by `2 k_n`. -/
def WeightEnvelope (P : TransportedArray 𝒳) (k : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ᵐ x ∂sourceXLaw P n,
    0 ≤ transportWeight P n x ∧ transportWeight P n x ≤ 2 * (k n : ℝ)
    -- @realizes w(0≤w≤2k_n)
    -- @realizes k_n(weight-envelope sequence)

-- @node: ass:weight-second-moment
/-- Kish dispersion is at most the envelope. -/
def WeightSecondMoment (P : TransportedArray 𝒳) (k : ℕ → ℕ) (n : ℕ) : Prop :=
  kishDispersion P n ≤ (k n : ℝ)
  -- @realizes \kappa_n(κ_n≤k_n)

-- @node: ass:degrading-array
/-- The overlap envelope diverges sub-root-`n` while the first stage vanishes. -/
def DegradingArray (P : TransportedArray 𝒳) (k : ℕ → ℕ) : Prop :=
  Tendsto (fun n => (k n : ℝ)) atTop atTop ∧
    Tendsto (fun n => (k n : ℝ) / Real.sqrt n) atTop (𝓝 0) ∧
    Tendsto
      (fun n => ∫ x, transportWeight P n x * P.deltaD n x
        ∂sourceXLaw P n)
      atTop (𝓝 0)
    -- @realizes k_n(k_n→∞ and k_n=o(√n))
    -- @realizes \mu_n(μ_n→0)

/-- The uniform probability law on a row's injected finite covariate carrier.
Equality with this measure is the carrier-exhaustion clause: the experiment is
definitionally a pushforward of the discrete `Fin m` experiment, even though
all rows share one arbitrary ambient measurable carrier. -/
noncomputable def finiteUniformCellLaw {m : ℕ} (cell : Fin m ↪ 𝒳) : Measure 𝒳 :=
  ∑ i : Fin m, (m : ENNReal)⁻¹ • Measure.dirac (cell i)

-- @node: ass:finite-cell-source
/-- At index `n`, `cell` realizes the paper's literal finite covariate
experiment inside the common ambient carrier.  The source law is exactly the
uniform pushforward from `Fin (k n)`; hence the injected image exhausts the
row-law carrier and every ambient point outside it is null. -/
def FiniteCellSource (P : TransportedArray 𝒳) (k : ℕ → ℕ) (n : ℕ) : Prop :=
  0 < k n ∧
  IsProbabilityMeasure (sourceXLaw P n) ∧
  ∃ cell : Fin (k n) ↪ 𝒳,
    (∀ i, MeasurableSet {cell i}) ∧
    sourceXLaw P n (Set.range cell) = 1 ∧
    (∀ i, (sourceXLaw P n {cell i}).toReal = (k n : ℝ)⁻¹) ∧
    sourceXLaw P n = finiteUniformCellLaw cell ∧
    (∀ᵐ x ∂sourceXLaw P n, P.propensity n x = 1 / 2)
    -- @realizes \mathcal X(row law is exactly the uniform pushforward of
    --   discrete Fin k_n; injected measurable atoms exhaust its carrier)
    -- @realizes P_S^X(uniform source-cell law)
    -- @realizes e(e=1/2 source-a.s.)

/-! ## Main and finite-cell classes -/

-- @node: def:model-class
/-- Main transported-IV model class at index `n`. -/
structure TransportedIVClass (P : TransportedArray 𝒳) (N k : ℕ → ℕ)
    (c epsilon : ℝ) (n : ℕ) : Prop where
  fullDataSupport : FullDataSupport P n
  populationPresence : PopulationPresence P n
  twoSampleArray : TwoSampleArray P N c
  instrumentOverlap : InstrumentOverlap P n epsilon
  sourceObservation : SourceAssignmentConsistency P n
  ivRandomization : IVRandomization P n
  ivExclusion : IVExclusion P n
  ivMonotonicity : IVMonotonicity P n
  outcomeTransport : OutcomeTransport P n
  receiptTransport : ReceiptTransport P n
  targetComplierPositivity : TargetComplierPositivity P n
  transportDomination : TransportDomination P n
  weightEnvelope : WeightEnvelope P k n
  weightSecondMoment : WeightSecondMoment P k n
  degradingArray : DegradingArray P k
  -- @realizes \mathcal P_n(main model membership at index n)

/-- Derived-facing view of the complete model's observed-law well-definedness
and auxiliary-field pinning facts. -/
def SourceObservationFacts (P : TransportedArray 𝒳) (n : ℕ) : Prop :=
  IsProbabilityMeasure (P.assignedSourceLaw n) ∧
    IsProbabilityMeasure (sourceObsLaw P n) ∧ -- @realizes P_S(probability measure)
    (∀ᵐ o ∂sourceObsLaw P n,
      o.2.2.2 ∈ Set.Icc (0 : ℝ) 1) ∧ -- @realizes Y(observed Y∈[0,1])
      -- @realizes O_i^S(observed-Y coordinate lies in [0,1])
    (P.assignedSourceLaw n).map Prod.fst = populationLaw P n true ∧
    (∀ A, MeasurableSet A →
      (sourceObsLaw P n {o | o.1 ∈ A ∧ o.2.1 = true}).toReal =
        ∫ x in A, P.propensity n x ∂sourceXLaw P n) ∧
    (∀ A, MeasurableSet A →
      ∫ o in {o | o.1 ∈ A},
          instrumentScore P n o * o.2.2.2 ∂sourceObsLaw P n =
        ∫ x in A, P.deltaY n x ∂sourceXLaw P n) ∧
    (∀ᵐ x ∂sourceXLaw P n,
      P.deltaY n x ∈ Set.Icc (-1 : ℝ) 1) ∧
      -- @realizes \Delta_Y(observed conditional outcome ITT in [-1,1])
    (∀ A, MeasurableSet A →
      ∫ o in {o | o.1 ∈ A},
          instrumentScore P n o * boolReal o.2.2.1 ∂sourceObsLaw P n =
        ∫ x in A, P.deltaD n x ∂sourceXLaw P n) ∧
    (∀ᵐ x ∂sourceXLaw P n,
      P.deltaD n x ∈ Set.Icc (0 : ℝ) 1)
      -- @realizes \Delta_D(observed conditional receipt ITT in [0,1])

/-- The probability, boundedness, and identified-contrast consequences of the
complete transported-IV model assumptions. -/
lemma sourceObservationFacts_of_class
    (P : TransportedArray 𝒳) (N k : ℕ → ℕ) (c epsilon : ℝ) (n : ℕ)
    (hP : TransportedIVClass P N k c epsilon n) :
    SourceObservationFacts P n := by
  have hObserve :
      Measurable (observeSource : AssignedFullData 𝒳 → SourceObs 𝒳) := by
    have hx : Measurable fun q : AssignedFullData 𝒳 => q.1.2.1 := by
      fun_prop
    have hz : Measurable fun q : AssignedFullData 𝒳 => q.2 := by
      fun_prop
    have hd : Measurable fun q : AssignedFullData 𝒳 =>
        if q.2 then q.1.2.2.2.1 else q.1.2.2.1 := by
      exact Measurable.ite
        (hz (MeasurableSet.singleton true)) (by fun_prop) (by fun_prop)
    have hy : Measurable fun q : AssignedFullData 𝒳 =>
        if (if q.2 then q.1.2.2.2.1 else q.1.2.2.1)
          then q.1.2.2.2.2.2 else q.1.2.2.2.2.1 := by
      exact Measurable.ite
        (hd (MeasurableSet.singleton true)) (by fun_prop) (by fun_prop)
    exact hx.prodMk (hz.prodMk (hd.prodMk hy))
  have hFullX : Measurable (fullX : FullData 𝒳 → 𝒳) := by
    unfold fullX
    fun_prop
  have hSourceX :
      sourceXLaw P n = populationXLaw P n true := by
    rw [sourceXLaw, sourceObsLaw, Measure.map_map measurable_fst hObserve]
    rw [populationXLaw, ← hP.sourceObservation.2.1]
    rw [Measure.map_map hFullX measurable_fst]
    congr 1
  have hAssigned : IsProbabilityMeasure (P.assignedSourceLaw n) :=
    hP.sourceObservation.1
  have hObserved : IsProbabilityMeasure (sourceObsLaw P n) :=
    hP.twoSampleArray.2.1 n
  letI : IsProbabilityMeasure (P.assignedSourceLaw n) := hAssigned
  letI : IsProbabilityMeasure (sourceObsLaw P n) := hObserved
  letI : IsProbabilityMeasure (sourceXLaw P n) := by
    unfold sourceXLaw
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hPopulation : IsProbabilityMeasure (populationLaw P n true) := by
    rw [← hP.sourceObservation.2.1]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure (populationLaw P n true) := hPopulation
  have hSupportSource : ∀ᵐ o ∂populationLaw P n true,
      fullY0 o ∈ Set.Icc (0 : ℝ) 1 ∧
        fullY1 o ∈ Set.Icc (0 : ℝ) 1 :=
    ProbabilityTheory.cond_absolutelyContinuous.ae_le hP.fullDataSupport.2
  have hAssignedSupport : ∀ᵐ q ∂P.assignedSourceLaw n,
      fullY0 q.1 ∈ Set.Icc (0 : ℝ) 1 ∧
        fullY1 q.1 ∈ Set.Icc (0 : ℝ) 1 := by
    have hs : ∀ᵐ o ∂(P.assignedSourceLaw n).map Prod.fst,
        fullY0 o ∈ Set.Icc (0 : ℝ) 1 ∧
          fullY1 o ∈ Set.Icc (0 : ℝ) 1 := by
      rw [hP.sourceObservation.2.1]
      exact hSupportSource
    exact ae_of_ae_map measurable_fst.aemeasurable hs
  have hObservedBound : ∀ᵐ o ∂sourceObsLaw P n,
      o.2.2.2 ∈ Set.Icc (0 : ℝ) 1 := by
    unfold sourceObsLaw
    apply (ae_map_iff hObserve.aemeasurable
      ((show Measurable fun o : SourceObs 𝒳 => o.2.2.2 by
        fun_prop) measurableSet_Icc)).2
    filter_upwards [hAssignedSupport] with q hq
    rcases q with ⟨o, z⟩
    cases z <;> cases hd0 : fullD0 o <;> cases hd1 : fullD1 o <;>
      simp [observeSource, potentialOutcome, potentialReceipt, hd0, hd1]
        at hq ⊢ <;> tauto
  have hOverlapObs : ∀ᵐ o ∂sourceObsLaw P n,
      epsilon ≤ P.propensity n o.1 ∧
        P.propensity n o.1 ≤ 1 - epsilon := by
    have hx := hP.instrumentOverlap.2.2
    unfold sourceXLaw at hx
    exact ae_of_ae_map measurable_fst.aemeasurable hx
  have hScoreMeasurable : Measurable (instrumentScore P n) := by
    have hz : Measurable fun o : SourceObs 𝒳 => o.2.1 := by
      fun_prop
    have he : Measurable fun o : SourceObs 𝒳 => P.propensity n o.1 :=
      (P.propensity_measurable n).comp measurable_fst
    unfold instrumentScore
    exact Measurable.ite (hz (MeasurableSet.singleton true))
      (measurable_const.div he)
      (measurable_const.neg.div (measurable_const.sub he))
  have hScoreBound : ∀ᵐ o ∂sourceObsLaw P n,
      |instrumentScore P n o| ≤ 1 / epsilon := by
    filter_upwards [hOverlapObs] with o ho
    rcases o with ⟨x, z, d, y⟩
    cases z
    · simp only [instrumentScore, Bool.false_eq_true, ↓reduceIte, abs_neg,
        abs_div, abs_one]
      rw [abs_of_pos (sub_pos.mpr (lt_of_le_of_lt ho.2
        (by linarith [hP.instrumentOverlap.1])))]
      exact one_div_le_one_div_of_le hP.instrumentOverlap.1
        (by linarith [ho.2])
    · simp only [instrumentScore, ↓reduceIte, abs_div, abs_one]
      rw [abs_of_pos
        (lt_of_lt_of_le hP.instrumentOverlap.1 ho.1)]
      exact one_div_le_one_div_of_le hP.instrumentOverlap.1 ho.1
  have hScoreIntegrable
      (G : SourceObs 𝒳 → ℝ) (hGmeas : Measurable G)
      (hGbound : ∀ᵐ o ∂sourceObsLaw P n, |G o| ≤ 1) :
      Integrable (fun o => instrumentScore P n o * G o)
        (sourceObsLaw P n) := by
    refine Integrable.of_bound
      ((hScoreMeasurable.mul hGmeas).aestronglyMeasurable)
      (1 / epsilon) ?_
    filter_upwards [hScoreBound, hGbound] with o hs hG
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |instrumentScore P n o| * |G o| ≤ (1 / epsilon) * 1 :=
        mul_le_mul hs hG (abs_nonneg _)
          (one_div_nonneg.mpr hP.instrumentOverlap.1.le)
      _ = 1 / epsilon := mul_one _
  have hOutcomeScoreIntegrable :
      Integrable (fun o => instrumentScore P n o * o.2.2.2)
        (sourceObsLaw P n) := by
    apply hScoreIntegrable (fun o => o.2.2.2) (by fun_prop)
    filter_upwards [hObservedBound] with o ho
    rw [abs_of_nonneg ho.1]
    exact ho.2
  have hReceiptMeasurable :
      Measurable (fun o : SourceObs 𝒳 => boolReal o.2.2.1) := by
    unfold boolReal
    have hd : Measurable fun o : SourceObs 𝒳 => o.2.2.1 := by
      fun_prop
    exact Measurable.ite (hd (MeasurableSet.singleton true))
      measurable_const measurable_const
  have hReceiptScoreIntegrable :
      Integrable (fun o => instrumentScore P n o * boolReal o.2.2.1)
        (sourceObsLaw P n) := by
    apply hScoreIntegrable _ hReceiptMeasurable
    filter_upwards with o
    cases o.2.2.1 <;> simp [boolReal]
  have hSlice (z : Bool) :
      ((P.assignedSourceLaw n).restrict {q | q.2 = z}).map Prod.fst =
        (populationLaw P n true).withDensity (fun o =>
          ENNReal.ofReal
            (if z then P.propensity n (fullX o)
              else 1 - P.propensity n (fullX o))) := by
    let μ := populationLaw P n true
    let ν := ((P.assignedSourceLaw n).restrict {q | q.2 = z}).map Prod.fst
    let w : FullData 𝒳 → ℝ := fun o =>
      if z then P.propensity n (fullX o)
        else 1 - P.propensity n (fullX o)
    have hwmeas : Measurable w := by
      have hecomp : Measurable fun o : FullData 𝒳 =>
          P.propensity n (fullX o) :=
        (P.propensity_measurable n).comp hFullX
      cases z
      · simpa [w] using measurable_const.sub hecomp
      · simpa [w] using hecomp
    have hoverlapPop : ∀ᵐ o ∂μ,
        epsilon ≤ P.propensity n (fullX o) ∧
          P.propensity n (fullX o) ≤ 1 - epsilon := by
      have hx := hP.instrumentOverlap.2.2
      rw [hSourceX] at hx
      exact ae_of_ae_map hFullX.aemeasurable hx
    have hw0 : ∀ᵐ o ∂μ, 0 ≤ w o := by
      filter_upwards [hoverlapPop] with o ho
      unfold w
      cases z
      · simp
        linarith [hP.instrumentOverlap.1]
      · simpa using
          (le_trans hP.instrumentOverlap.1.le ho.1)
    have hwle : ∀ᵐ o ∂μ, w o ≤ 1 := by
      filter_upwards [hoverlapPop] with o ho
      unfold w
      cases z
      · simp
        linarith [ho.1, hP.instrumentOverlap.1]
      · simpa using
          ho.2.trans (sub_le_self 1 hP.instrumentOverlap.1.le)
    have hwint : Integrable w μ := by
      refine Integrable.of_bound hwmeas.aestronglyMeasurable 1 ?_
      filter_upwards [hw0, hwle] with o h0 h1
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact h1
    ext A hA
    rw [withDensity_apply _ hA]
    rw [← ofReal_integral_eq_lintegral_ofReal hwint.integrableOn
      ((ae_restrict_iff' hA).2
        (Filter.Eventually.mono hw0 fun _ hx _ => hx))]
    rw [← ENNReal.ofReal_toReal (measure_ne_top ν A)]
    congr 1
    rw [Measure.map_apply measurable_fst hA]
    rw [Measure.restrict_apply (hA.preimage measurable_fst)]
    rw [show Prod.fst ⁻¹' A ∩ {q | q.2 = z} =
        {q | q.1 ∈ A ∧ q.2 = z} by
      ext q
      simp]
    simpa [μ, ν, w] using hP.ivRandomization A hA z
  have hIPW
      (F0 F1 : FullData 𝒳 → ℝ)
      (hF0 : Measurable F0) (hF1 : Measurable F1)
      (hF0int : Integrable F0 (populationLaw P n true))
      (hF1int : Integrable F1 (populationLaw P n true))
      (hInt : Integrable (fun q : AssignedFullData 𝒳 =>
        if q.2 then
          (1 / P.propensity n (fullX q.1)) * F1 q.1
        else
          (-1 / (1 - P.propensity n (fullX q.1))) * F0 q.1)
        (P.assignedSourceLaw n))
      (A : Set 𝒳) (hA : MeasurableSet A) :
      (∫ q in {q | fullX q.1 ∈ A},
        (if q.2 then
          (1 / P.propensity n (fullX q.1)) * F1 q.1
        else
          (-1 / (1 - P.propensity n (fullX q.1))) * F0 q.1)
        ∂P.assignedSourceLaw n) =
        ∫ o in {o | fullX o ∈ A}, (F1 o - F0 o)
          ∂populationLaw P n true := by
    let μ := populationLaw P n true
    let e : FullData 𝒳 → ℝ := fun o => P.propensity n (fullX o)
    let S : Set (AssignedFullData 𝒳) := {q | fullX q.1 ∈ A}
    let E : Set (AssignedFullData 𝒳) := {q | q.2 = true}
    let W : AssignedFullData 𝒳 → ℝ := fun q =>
      if q.2 then (1 / e q.1) * F1 q.1
        else (-1 / (1 - e q.1)) * F0 q.1
    have hS : MeasurableSet S :=
      hA.preimage (hFullX.comp measurable_fst)
    have hE : MeasurableSet E :=
      measurable_snd (MeasurableSet.singleton true)
    have hsplit := integral_add_compl
      (μ := (P.assignedSourceLaw n).restrict S) hE hInt.integrableOn
    have hemeas : Measurable e :=
      (P.propensity_measurable n).comp hFullX
    have hoverlapPop : ∀ᵐ o ∂μ,
        epsilon ≤ e o ∧ e o ≤ 1 - epsilon := by
      have hx := hP.instrumentOverlap.2.2
      rw [hSourceX] at hx
      exact ae_of_ae_map hFullX.aemeasurable hx
    have htrue :
        (∫ q in S ∩ E, W q ∂P.assignedSourceLaw n) =
          ∫ o in {o | fullX o ∈ A}, F1 o ∂μ := by
      have hmap :
          (∫ o in {o | fullX o ∈ A}, (1 / e o) * F1 o
              ∂(((P.assignedSourceLaw n).restrict E).map Prod.fst)) =
            ∫ q in S ∩ E, W q ∂P.assignedSourceLaw n := by
        calc
          _ = ∫ q in Prod.fst ⁻¹' {o | fullX o ∈ A},
                (1 / e q.1) * F1 q.1
                ∂(P.assignedSourceLaw n).restrict E :=
            setIntegral_map (μ := (P.assignedSourceLaw n).restrict E)
              (hA.preimage hFullX)
              ((measurable_const.div hemeas).mul hF1).aestronglyMeasurable
              measurable_fst.aemeasurable
          _ = _ := by
            change (∫ q, (1 / e q.1) * F1 q.1
              ∂((P.assignedSourceLaw n).restrict E).restrict
                (Prod.fst ⁻¹' {o | fullX o ∈ A})) =
                  ∫ q in S ∩ E, W q ∂P.assignedSourceLaw n
            rw [Measure.restrict_restrict' hE]
            apply integral_congr_ae
            filter_upwards [ae_restrict_mem (hS.inter hE)] with q hq
            have hqtrue : q.2 = true := hq.2
            simp [W, hqtrue]
      rw [← hmap, hSlice true]
      change (∫ o in {o | fullX o ∈ A}, (1 / e o) * F1 o
        ∂μ.withDensity (fun o => ENNReal.ofReal (e o))) =
          ∫ o in {o | fullX o ∈ A}, F1 o ∂μ
      calc
        _ = ∫ o in {o | fullX o ∈ A},
            (ENNReal.ofReal (e o)).toReal • ((1 / e o) * F1 o) ∂μ :=
          setIntegral_withDensity_eq_setIntegral_toReal_smul
            (ENNReal.measurable_ofReal.comp hemeas)
            (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
            (fun o => (1 / e o) * F1 o) (hA.preimage hFullX)
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_of_ae hoverlapPop] with o ho
          have hepos : 0 < e o :=
            lt_of_lt_of_le hP.instrumentOverlap.1 ho.1
          simp [ENNReal.toReal_ofReal hepos.le, smul_eq_mul, hepos.ne']
    have hfalse :
        (∫ q in S ∩ Eᶜ, W q ∂P.assignedSourceLaw n) =
          ∫ o in {o | fullX o ∈ A}, -F0 o ∂μ := by
      have hmap :
          (∫ o in {o | fullX o ∈ A}, (-1 / (1 - e o)) * F0 o
              ∂(((P.assignedSourceLaw n).restrict {q | q.2 = false}).map
                Prod.fst)) =
            ∫ q in S ∩ Eᶜ, W q ∂P.assignedSourceLaw n := by
        calc
          _ = ∫ q in Prod.fst ⁻¹' {o | fullX o ∈ A},
                (-1 / (1 - e q.1)) * F0 q.1
                ∂(P.assignedSourceLaw n).restrict {q | q.2 = false} :=
            setIntegral_map
              (μ := (P.assignedSourceLaw n).restrict {q | q.2 = false})
              (hA.preimage hFullX)
              ((measurable_const.neg.div (measurable_const.sub hemeas)).mul
                hF0).aestronglyMeasurable
              measurable_fst.aemeasurable
          _ = _ := by
            have hEf : {q : AssignedFullData 𝒳 | q.2 = false} = Eᶜ := by
              ext q
              cases q.2 <;> simp [E]
            rw [hEf]
            change (∫ q, (-1 / (1 - e q.1)) * F0 q.1
              ∂((P.assignedSourceLaw n).restrict Eᶜ).restrict
                (Prod.fst ⁻¹' {o | fullX o ∈ A})) =
                  ∫ q in S ∩ Eᶜ, W q ∂P.assignedSourceLaw n
            rw [Measure.restrict_restrict' hE.compl]
            apply integral_congr_ae
            filter_upwards [ae_restrict_mem (hS.inter hE.compl)] with q hq
            have hqfalse : q.2 = false := by
              cases hqz : q.2
              · rfl
              · exfalso
                exact hq.2 (by simp [E, hqz])
            simp [W, hqfalse]
      rw [← hmap, hSlice false]
      change (∫ o in {o | fullX o ∈ A}, (-1 / (1 - e o)) * F0 o
        ∂μ.withDensity (fun o => ENNReal.ofReal (1 - e o))) =
          ∫ o in {o | fullX o ∈ A}, -F0 o ∂μ
      calc
        _ = ∫ o in {o | fullX o ∈ A},
            (ENNReal.ofReal (1 - e o)).toReal •
              ((-1 / (1 - e o)) * F0 o) ∂μ :=
          setIntegral_withDensity_eq_setIntegral_toReal_smul
            (ENNReal.measurable_ofReal.comp (measurable_const.sub hemeas))
            (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
            (fun o => (-1 / (1 - e o)) * F0 o) (hA.preimage hFullX)
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_of_ae hoverlapPop] with o ho
          have hden : 0 < 1 - e o := by
            linarith [ho.2, hP.instrumentOverlap.1]
          rw [ENNReal.toReal_ofReal hden.le]
          simp only [smul_eq_mul]
          field_simp [hden.ne']
    have hsplitW :
        (∫ q in S ∩ E, W q ∂P.assignedSourceLaw n) +
          (∫ q in S ∩ Eᶜ, W q ∂P.assignedSourceLaw n) =
            ∫ q in S, W q ∂P.assignedSourceLaw n := by
      rw [Measure.restrict_restrict hE,
        Measure.restrict_restrict hE.compl] at hsplit
      simpa [S, E, W, e, Set.inter_comm] using hsplit
    change (∫ q in S, W q ∂P.assignedSourceLaw n) =
      ∫ o in {o | fullX o ∈ A}, F1 o - F0 o ∂μ
    rw [← hsplitW, htrue, hfalse]
    calc
      (∫ o in {o | fullX o ∈ A}, F1 o ∂μ) +
          ∫ o in {o | fullX o ∈ A}, -F0 o ∂μ =
          ∫ o in {o | fullX o ∈ A}, F1 o + -F0 o ∂μ := by
        simpa only [Pi.neg_apply] using
          (integral_add hF1int.integrableOn hF0int.neg.integrableOn).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with o
        ring
  have hDerivedMeas (z : Bool) :
      Measurable (fun o : FullData 𝒳 => derivedAssignmentOutcome o z) := by
    have hd : Measurable fun o : FullData 𝒳 => potentialReceipt o z := by
      cases z
      · simpa [potentialReceipt] using
          (show Measurable (fullD0 : FullData 𝒳 → Bool) by
            unfold fullD0
            fun_prop)
      · simpa [potentialReceipt] using
          (show Measurable (fullD1 : FullData 𝒳 → Bool) by
            unfold fullD1
            fun_prop)
    unfold derivedAssignmentOutcome potentialOutcome
    have hy0 : Measurable (fullY0 : FullData 𝒳 → ℝ) := by
      unfold fullY0
      fun_prop
    have hy1 : Measurable (fullY1 : FullData 𝒳 → ℝ) := by
      unfold fullY1
      fun_prop
    exact Measurable.ite (hd (MeasurableSet.singleton true)) hy1 hy0
  have hDerivedBound (z : Bool) :
      ∀ᵐ o ∂populationLaw P n true,
        |derivedAssignmentOutcome o z| ≤ 1 := by
    filter_upwards [hSupportSource] with o ho
    unfold derivedAssignmentOutcome potentialOutcome potentialReceipt
    cases z <;> cases fullD0 o <;> cases fullD1 o <;>
      simp [abs_of_nonneg ho.1.1, abs_of_nonneg ho.2.1,
        ho.1.2, ho.2.2]
  have hF0int :
      Integrable (fun o : FullData 𝒳 => derivedAssignmentOutcome o false)
        (populationLaw P n true) :=
    Integrable.of_bound (hDerivedMeas false).aestronglyMeasurable 1
      (hDerivedBound false)
  have hF1int :
      Integrable (fun o : FullData 𝒳 => derivedAssignmentOutcome o true)
        (populationLaw P n true) :=
    Integrable.of_bound (hDerivedMeas true).aestronglyMeasurable 1
      (hDerivedBound true)
  have hOutcomeIdentity :
      ∀ A, MeasurableSet A →
        ∫ o in {o | o.1 ∈ A},
            instrumentScore P n o * o.2.2.2 ∂sourceObsLaw P n =
          ∫ x in A, P.deltaY n x ∂sourceXLaw P n := by
    intro A hA
    have hpull :
        Integrable (fun q : AssignedFullData 𝒳 =>
          instrumentScore P n (observeSource q) * (observeSource q).2.2.2)
          (P.assignedSourceLaw n) := by
      unfold sourceObsLaw at hOutcomeScoreIntegrable
      exact hOutcomeScoreIntegrable.comp_measurable hObserve
    have hWint :
        Integrable (fun q : AssignedFullData 𝒳 =>
          if q.2 then
            (1 / P.propensity n (fullX q.1)) *
              derivedAssignmentOutcome q.1 true
          else
            (-1 / (1 - P.propensity n (fullX q.1))) *
              derivedAssignmentOutcome q.1 false)
          (P.assignedSourceLaw n) := by
      apply hpull.congr
      filter_upwards with q
      cases hz : q.2 <;>
        cases hd0 : fullD0 q.1 <;> cases hd1 : fullD1 q.1 <;>
          simp [observeSource, instrumentScore, derivedAssignmentOutcome,
            potentialOutcome, potentialReceipt, hz, hd0, hd1]
    calc
      _ = ∫ q in {q | fullX q.1 ∈ A},
          (if q.2 then
            (1 / P.propensity n (fullX q.1)) *
              derivedAssignmentOutcome q.1 true
          else
            (-1 / (1 - P.propensity n (fullX q.1))) *
              derivedAssignmentOutcome q.1 false)
            ∂P.assignedSourceLaw n := by
        unfold sourceObsLaw
        calc
          _ = ∫ q in observeSource ⁻¹' {o | o.1 ∈ A},
              instrumentScore P n (observeSource q) *
                (observeSource q).2.2.2 ∂P.assignedSourceLaw n :=
            setIntegral_map (μ := P.assignedSourceLaw n)
              (hA.preimage measurable_fst)
              (hScoreMeasurable.mul (by fun_prop)).aestronglyMeasurable
              hObserve.aemeasurable
          _ = _ := by
            apply integral_congr_ae
            filter_upwards with q
            cases hz : q.2 <;>
              cases hd0 : fullD0 q.1 <;> cases hd1 : fullD1 q.1 <;>
                simp [observeSource, instrumentScore,
                  derivedAssignmentOutcome, potentialOutcome,
                  potentialReceipt, fullX, hz, hd0, hd1]
      _ = ∫ o in {o | fullX o ∈ A},
          (derivedAssignmentOutcome o true -
            derivedAssignmentOutcome o false) ∂populationLaw P n true :=
        hIPW _ _ (hDerivedMeas false) (hDerivedMeas true)
          hF0int hF1int hWint A hA
      _ = ∫ o in {o | fullX o ∈ A},
          (P.assignmentOutcome n true o -
            P.assignmentOutcome n false o) ∂populationLaw P n true := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae (hP.ivExclusion true true),
          ae_restrict_of_ae (hP.ivExclusion true false)] with o h1 h0
        rw [h1, h0]
      _ = ∫ x in A, P.assignmentContrast n true x
          ∂sourceXLaw P n := by
        rw [hSourceX]
        simpa using hP.outcomeTransport.1 true A hA
      _ = _ := rfl
  have hD0meas :
      Measurable (fun o : FullData 𝒳 => boolReal (fullD0 o)) := by
    unfold boolReal
    have hd : Measurable (fullD0 : FullData 𝒳 → Bool) := by
      unfold fullD0
      fun_prop
    exact Measurable.ite (hd (MeasurableSet.singleton true))
      measurable_const measurable_const
  have hD1meas :
      Measurable (fun o : FullData 𝒳 => boolReal (fullD1 o)) := by
    unfold boolReal
    have hd : Measurable (fullD1 : FullData 𝒳 → Bool) := by
      unfold fullD1
      fun_prop
    exact Measurable.ite (hd (MeasurableSet.singleton true))
      measurable_const measurable_const
  have hD0int :
      Integrable (fun o : FullData 𝒳 => boolReal (fullD0 o))
        (populationLaw P n true) := by
    refine Integrable.of_bound hD0meas.aestronglyMeasurable 1 ?_
    filter_upwards with o
    cases fullD0 o <;> simp [boolReal]
  have hD1int :
      Integrable (fun o : FullData 𝒳 => boolReal (fullD1 o))
        (populationLaw P n true) := by
    refine Integrable.of_bound hD1meas.aestronglyMeasurable 1 ?_
    filter_upwards with o
    cases fullD1 o <;> simp [boolReal]
  have hReceiptIdentity :
      ∀ A, MeasurableSet A →
        ∫ o in {o | o.1 ∈ A},
            instrumentScore P n o * boolReal o.2.2.1
              ∂sourceObsLaw P n =
          ∫ x in A, P.deltaD n x ∂sourceXLaw P n := by
    intro A hA
    have hpull :
        Integrable (fun q : AssignedFullData 𝒳 =>
          instrumentScore P n (observeSource q) *
            boolReal (observeSource q).2.2.1)
          (P.assignedSourceLaw n) := by
      unfold sourceObsLaw at hReceiptScoreIntegrable
      exact hReceiptScoreIntegrable.comp_measurable hObserve
    have hWint :
        Integrable (fun q : AssignedFullData 𝒳 =>
          if q.2 then
            (1 / P.propensity n (fullX q.1)) * boolReal (fullD1 q.1)
          else
            (-1 / (1 - P.propensity n (fullX q.1))) *
              boolReal (fullD0 q.1))
          (P.assignedSourceLaw n) := by
      apply hpull.congr
      filter_upwards with q
      cases hz : q.2 <;>
        cases hd0 : fullD0 q.1 <;> cases hd1 : fullD1 q.1 <;>
          simp [observeSource, instrumentScore, potentialReceipt, boolReal,
            hz, hd0, hd1]
    calc
      _ = ∫ q in {q | fullX q.1 ∈ A},
          (if q.2 then
            (1 / P.propensity n (fullX q.1)) * boolReal (fullD1 q.1)
          else
            (-1 / (1 - P.propensity n (fullX q.1))) *
              boolReal (fullD0 q.1)) ∂P.assignedSourceLaw n := by
        unfold sourceObsLaw
        calc
          _ = ∫ q in observeSource ⁻¹' {o | o.1 ∈ A},
              instrumentScore P n (observeSource q) *
                boolReal (observeSource q).2.2.1
                ∂P.assignedSourceLaw n :=
            setIntegral_map (μ := P.assignedSourceLaw n)
              (hA.preimage measurable_fst)
              (hScoreMeasurable.mul hReceiptMeasurable).aestronglyMeasurable
              hObserve.aemeasurable
          _ = _ := by
            apply integral_congr_ae
            filter_upwards with q
            cases hz : q.2 <;>
              cases hd0 : fullD0 q.1 <;> cases hd1 : fullD1 q.1 <;>
                simp [observeSource, instrumentScore, potentialReceipt,
                  boolReal, fullX, hz, hd0, hd1]
      _ = ∫ o in {o | fullX o ∈ A},
          (boolReal (fullD1 o) - boolReal (fullD0 o))
            ∂populationLaw P n true :=
        hIPW _ _ hD0meas hD1meas hD0int hD1int hWint A hA
      _ = ∫ x in A, P.receiptContrast n true x
          ∂sourceXLaw P n := by
        rw [hSourceX]
        simpa using hP.receiptTransport.1 true A hA
      _ = _ := rfl
  have hAbsBound
      (mu : Measure 𝒳) [IsFiniteMeasure mu]
      (f : 𝒳 → ℝ) (hf : Measurable f)
      (hdom : ∀ A, MeasurableSet A →
        |∫ x in A, f x ∂mu| ≤ (mu A).toReal) :
      ∀ᵐ x ∂mu, |f x| ≤ 1 := by
    have hupper : ∀ q : ℝ, 1 < q → ∀ᵐ x ∂mu, f x ≤ q := by
      intro q hq
      have hslice : ∀ m : ℕ,
          ∀ᵐ x ∂mu, ¬(q < f x ∧ f x ≤ (m : ℝ)) := by
        intro m
        let A : Set 𝒳 := {x | q < f x ∧ f x ≤ (m : ℝ)}
        have hA : MeasurableSet A :=
          (measurableSet_Ioi.preimage hf).inter
            (measurableSet_Iic.preimage hf)
        have hfin : mu A < ∞ := measure_lt_top mu A
        have hfA : IntegrableOn f A mu := by
          apply IntegrableOn.of_bound hfin hf.aestronglyMeasurable.restrict
            (m : ℝ)
          filter_upwards [self_mem_ae_restrict hA] with x hxA
          rw [Real.norm_eq_abs,
            abs_of_pos (lt_trans (by linarith) hxA.1)]
          exact hxA.2
        have hconst : IntegrableOn (fun _ : 𝒳 => q) A mu :=
          integrableOn_const hfin.ne
        have hlower :
            q * (mu A).toReal ≤ ∫ x in A, f x ∂mu := by
          calc
            q * (mu A).toReal = ∫ _ in A, q ∂mu := by
              rw [setIntegral_const]
              simp [Measure.real]
              ring
            _ ≤ ∫ x in A, f x ∂mu :=
              integral_mono_ae hconst hfA
                (ae_restrict_iff' hA |>.2 <| by
                  filter_upwards with x hx
                  exact hx.1.le)
        have hupperInt :
            (∫ x in A, f x ∂mu) ≤ (mu A).toReal :=
          (le_abs_self _).trans (hdom A hA)
        have hzeroReal : (mu A).toReal = 0 := by
          have hnonneg : 0 ≤ (mu A).toReal := ENNReal.toReal_nonneg
          nlinarith
        have hzero : mu A = 0 := by
          rw [ENNReal.toReal_eq_zero_iff] at hzeroReal
          exact hzeroReal.resolve_right hfin.ne
        rw [ae_iff]
        simpa [A] using hzero
      rw [← ae_all_iff] at hslice
      filter_upwards [hslice] with x hx
      by_contra hqx
      have hqfx : q < f x := lt_of_not_ge hqx
      obtain ⟨m, hm⟩ := exists_nat_ge (f x)
      exact hx m ⟨hqfx, hm⟩
    have hlower : ∀ q : ℝ, 1 < q → ∀ᵐ x ∂mu, -q ≤ f x := by
      intro q hq
      have hslice : ∀ m : ℕ,
          ∀ᵐ x ∂mu, ¬(-(m : ℝ) ≤ f x ∧ f x < -q) := by
        intro m
        let A : Set 𝒳 := {x | -(m : ℝ) ≤ f x ∧ f x < -q}
        have hA : MeasurableSet A :=
          (measurableSet_Ici.preimage hf).inter
            (measurableSet_Iio.preimage hf)
        have hfin : mu A < ∞ := measure_lt_top mu A
        have hfA : IntegrableOn f A mu := by
          apply IntegrableOn.of_bound hfin hf.aestronglyMeasurable.restrict
            (m : ℝ)
          filter_upwards [self_mem_ae_restrict hA] with x hxA
          rw [Real.norm_eq_abs,
            abs_of_neg (lt_trans hxA.2
              (neg_lt_zero.mpr (by linarith)))]
          linarith [hxA.1]
        have hconst : IntegrableOn (fun _ : 𝒳 => -q) A mu :=
          integrableOn_const hfin.ne
        have hupperSlice :
            (∫ x in A, f x ∂mu) ≤ -q * (mu A).toReal := by
          calc
            (∫ x in A, f x ∂mu) ≤ ∫ _ in A, -q ∂mu :=
              integral_mono_ae hfA hconst
                (ae_restrict_iff' hA |>.2 <| by
                  filter_upwards with x hx
                  exact hx.2.le)
            _ = -q * (mu A).toReal := by
              rw [setIntegral_const]
              simp [Measure.real]
              ring
        have hlowerInt :
            -(mu A).toReal ≤ ∫ x in A, f x ∂mu := by
          have := hdom A hA
          linarith [neg_abs_le (∫ x in A, f x ∂mu)]
        have hzeroReal : (mu A).toReal = 0 := by
          have hnonneg : 0 ≤ (mu A).toReal := ENNReal.toReal_nonneg
          nlinarith
        have hzero : mu A = 0 := by
          rw [ENNReal.toReal_eq_zero_iff] at hzeroReal
          exact hzeroReal.resolve_right hfin.ne
        rw [ae_iff]
        simpa [A] using hzero
      rw [← ae_all_iff] at hslice
      filter_upwards [hslice] with x hx
      by_contra hqx
      have hfxq : f x < -q := lt_of_not_ge hqx
      obtain ⟨m, hm⟩ := exists_nat_ge (-f x)
      exact hx m ⟨by linarith, hfxq⟩
    have hupperOne : ∀ᵐ x ∂mu, f x ≤ 1 := by
      have hq := fun j : ℕ => hupper
        (1 + 1 / ((j + 1 : ℕ) : ℝ)) (by
          have : 0 < 1 / ((j + 1 : ℕ) : ℝ) := by positivity
          linarith)
      rw [← ae_all_iff] at hq
      filter_upwards [hq] with x hx
      by_contra hx1
      have hpos : 0 < f x - 1 := sub_pos.mpr (lt_of_not_ge hx1)
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt hpos
      have hxj := hx j
      norm_num [Nat.cast_add, Nat.cast_one] at hxj
      have hj' : ((j : ℝ) + 1)⁻¹ < f x - 1 := by
        simpa [one_div] using hj
      linarith
    have hlowerOne : ∀ᵐ x ∂mu, -1 ≤ f x := by
      have hq := fun j : ℕ => hlower
        (1 + 1 / ((j + 1 : ℕ) : ℝ)) (by
          have : 0 < 1 / ((j + 1 : ℕ) : ℝ) := by positivity
          linarith)
      rw [← ae_all_iff] at hq
      filter_upwards [hq] with x hx
      by_contra hx1
      have hlt : f x < -1 := lt_of_not_ge hx1
      have hpos : 0 < -f x - 1 := by linarith
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt hpos
      have hxj := hx j
      norm_num [Nat.cast_add, Nat.cast_one] at hxj
      have hj' : ((j : ℝ) + 1)⁻¹ < -f x - 1 := by
        simpa [one_div] using hj
      linarith
    filter_upwards [hupperOne, hlowerOne] with x hxU hxL
    exact abs_le.mpr ⟨by linarith, hxU⟩
  have hAssignmentBound :
      ∀ᵐ o ∂populationLaw P n true,
        |P.assignmentOutcome n true o -
          P.assignmentOutcome n false o| ≤ 1 := by
    filter_upwards [hSupportSource,
      hP.ivExclusion true true, hP.ivExclusion true false]
      with o ho htrue hfalse
    rw [htrue, hfalse]
    unfold derivedAssignmentOutcome potentialOutcome potentialReceipt
    cases fullD0 o <;> cases fullD1 o <;>
      simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals
      rw [abs_le]
      constructor <;> linarith [ho.1.1, ho.1.2, ho.2.1, ho.2.2]
  have hReceiptBound :
      ∀ᵐ o ∂populationLaw P n true,
        |boolReal (fullD1 o) - boolReal (fullD0 o)| ≤ 1 := by
    filter_upwards with o
    cases fullD0 o <;> cases fullD1 o <;> norm_num [boolReal]
  have hAssignmentDom : ∀ A, MeasurableSet A →
      |∫ x in A, P.assignmentContrast n true x
          ∂sourceXLaw P n| ≤ (sourceXLaw P n A).toReal := by
    intro A hA
    rw [hSourceX]
    rw [← hP.outcomeTransport.1 true A hA]
    have hbound := norm_setIntegral_le_of_norm_le_const_ae'
      (f := fun o : FullData 𝒳 =>
        P.assignmentOutcome n true o -
          P.assignmentOutcome n false o)
      (s := {o | fullX o ∈ A}) (C := 1)
      (measure_lt_top (populationLaw P n true) _) (by
        filter_upwards [hAssignmentBound] with o ho
        intro _
        simpa [Real.norm_eq_abs] using ho)
    rw [one_mul] at hbound
    rw [populationXLaw, Measure.map_apply hFullX hA]
    simpa [Real.norm_eq_abs] using hbound
  have hReceiptDom : ∀ A, MeasurableSet A →
      |∫ x in A, P.receiptContrast n true x
          ∂sourceXLaw P n| ≤ (sourceXLaw P n A).toReal := by
    intro A hA
    rw [hSourceX]
    rw [← hP.receiptTransport.1 true A hA]
    have hbound := norm_setIntegral_le_of_norm_le_const_ae'
      (f := fun o : FullData 𝒳 =>
        boolReal (fullD1 o) - boolReal (fullD0 o))
      (s := {o | fullX o ∈ A}) (C := 1)
      (measure_lt_top (populationLaw P n true) _) (by
        filter_upwards [hReceiptBound] with o ho
        intro _
        simpa [Real.norm_eq_abs] using ho)
    rw [one_mul] at hbound
    rw [populationXLaw, Measure.map_apply hFullX hA]
    simpa [Real.norm_eq_abs] using hbound
  have hDeltaYBound :
      ∀ᵐ x ∂sourceXLaw P n, P.deltaY n x ∈ Set.Icc (-1 : ℝ) 1 := by
    have hAE := hAbsBound (sourceXLaw P n)
      (P.assignmentContrast n true)
      (P.assignmentContrast_measurable n true) hAssignmentDom
    filter_upwards [hAE] with x hx
    simpa [TransportedArray.deltaY] using (abs_le.mp hx)
  have hDeltaDAbs :
      ∀ᵐ x ∂sourceXLaw P n,
        |P.receiptContrast n true x| ≤ 1 :=
    hAbsBound (sourceXLaw P n) (P.receiptContrast n true)
      (P.receiptContrast_measurable n true) hReceiptDom
  have hDeltaDInt :
      Integrable (P.receiptContrast n true) (sourceXLaw P n) :=
    Integrable.of_bound
      (P.receiptContrast_measurable n true).aestronglyMeasurable 1
      (by simpa [Real.norm_eq_abs] using hDeltaDAbs)
  have hDeltaDNonneg :
      ∀ᵐ x ∂sourceXLaw P n, 0 ≤ P.receiptContrast n true x := by
    apply ae_nonneg_of_forall_setIntegral_nonneg hDeltaDInt
    intro A hA hAfin
    rw [hSourceX]
    rw [← hP.receiptTransport.1 true A hA]
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_of_ae (hP.ivMonotonicity true)] with o ho
    exact sub_nonneg.mpr ho
  have hDeltaDBound :
      ∀ᵐ x ∂sourceXLaw P n, P.deltaD n x ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hDeltaDNonneg, hDeltaDAbs] with x h0 h1
    rw [TransportedArray.deltaD]
    exact ⟨h0, (abs_le.mp h1).2⟩
  exact ⟨hAssigned, hObserved, hObservedBound,
    hP.sourceObservation.2.1, hP.sourceObservation.2.2,
    hOutcomeIdentity, hDeltaYBound, hReceiptIdentity, hDeltaDBound⟩

/-- Complete model membership entails the paper's source assignment atom. -/
lemma sourceAssignmentConsistency_of_class
    (P : TransportedArray 𝒳) (N k : ℕ → ℕ) (c epsilon : ℝ) (n : ℕ)
    (hP : TransportedIVClass P N k c epsilon n) :
    SourceAssignmentConsistency P n := by
  exact hP.sourceObservation

/-- A covariate-indexed contrast representation remains valid after
multiplication by an integrable measurable covariate weight. -/
lemma weighted_observed_contrast_eq
    (P : TransportedArray 𝒳) (n : ℕ)
    (F : SourceObs 𝒳 → ℝ) (d w : 𝒳 → ℝ)
    (hprob : IsProbabilityMeasure (sourceObsLaw P n))
    (hF : Integrable F (sourceObsLaw P n))
    (hd : Integrable d (sourceXLaw P n))
    (hdmeas : Measurable d)
    (hw : Measurable w)
    (hWF : Integrable (fun o => w o.1 * F o) (sourceObsLaw P n))
    (hwd : Integrable (fun x => w x * d x) (sourceXLaw P n))
    (hset : ∀ A, MeasurableSet A →
      ∫ o in {o | o.1 ∈ A}, F o ∂sourceObsLaw P n =
        ∫ x in A, d x ∂sourceXLaw P n) :
    (∫ o, w o.1 * F o ∂sourceObsLaw P n) =
      ∫ x, w x * d x ∂sourceXLaw P n := by
  let m0 : MeasurableSpace (SourceObs 𝒳) := inferInstance
  let mX : MeasurableSpace (SourceObs 𝒳) :=
    MeasurableSpace.comap (fun o => o.1)
      (inferInstance : MeasurableSpace 𝒳)
  letI : MeasurableSpace (SourceObs 𝒳) := m0
  letI : IsProbabilityMeasure (sourceObsLaw P n) := hprob
  have hfst :
      @Measurable (SourceObs 𝒳) 𝒳 m0 inferInstance (fun o => o.1) :=
    measurable_fst
  have hm : mX ≤ m0 := hfst.comap_le
  have hfstM :
      @Measurable (SourceObs 𝒳) 𝒳 mX inferInstance (fun o => o.1) := by
    intro A hA
    exact MeasurableSpace.measurableSet_comap.mpr ⟨A, hA, rfl⟩
  have hdcomp : Integrable (fun o => d o.1) (sourceObsLaw P n) := by
    have hdmap : Integrable d
        (Measure.map (fun o : SourceObs 𝒳 => o.1) (sourceObsLaw P n)) := by
      simpa [sourceXLaw] using hd
    simpa [Function.comp_def] using
      (integrable_map_measure hdmap.1 hfst.aemeasurable).mp hdmap
  have hcond : (fun o => d o.1) =ᵐ[sourceObsLaw P n]
      (sourceObsLaw P n)[F | mX] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq
      (μ := sourceObsLaw P n) (f := F) (g := fun o => d o.1)
      hm hF ?_ ?_ ?_
    · intro s hs _hfin
      exact hdcomp.integrableOn
    · intro s hs _hfin
      rcases MeasurableSpace.measurableSet_comap.mp hs with
        ⟨A, hA, rfl⟩
      calc
        (∫ x in (fun o : SourceObs 𝒳 => o.1) ⁻¹' A,
            d x.1 ∂sourceObsLaw P n) =
            ∫ x in A, d x ∂sourceXLaw P n := by
          rw [sourceXLaw]
          exact (setIntegral_map hA hd.1 hfst.aemeasurable).symm
        _ = ∫ x in (fun o : SourceObs 𝒳 => o.1) ⁻¹' A,
            F x ∂sourceObsLaw P n := (hset A hA).symm
    · exact (hdmeas.comp hfstM).aestronglyMeasurable
  have hwM : @StronglyMeasurable (SourceObs 𝒳) ℝ _ mX
      (fun o => w o.1) :=
    (hw.comp hfstM).stronglyMeasurable
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (m := mX) (μ := sourceObsLaw P n) hwM hWF hF
  have hpull' :
      (sourceObsLaw P n)[(fun o => w o.1 * F o) | mX] =ᵐ[
        sourceObsLaw P n]
          fun o => w o.1 * (sourceObsLaw P n)[F | mX] o := by
    simpa only [Pi.mul_apply] using hpull
  calc
    (∫ o, w o.1 * F o ∂sourceObsLaw P n) =
        ∫ o, (sourceObsLaw P n)[(fun o => w o.1 * F o) | mX] o
          ∂sourceObsLaw P n := (integral_condExp hm).symm
    _ = ∫ o, w o.1 * d o.1 ∂sourceObsLaw P n := by
      apply integral_congr_ae
      filter_upwards [hpull', hcond] with o hp hc
      rw [hp, ← hc]
    _ = ∫ x, w x * d x ∂sourceXLaw P n := by
      rw [sourceXLaw]
      exact (integral_map measurable_fst.aemeasurable hwd.1).symm

/-- The named transported first stage unfolds to the paper's weighted
conditional receipt-contrast moment. -/
lemma transportedFirstStage_eq_weighted_deltaD
    (P : TransportedArray 𝒳) (k : ℕ → ℕ) (epsilon : ℝ) (n : ℕ)
    (hFacts : SourceObservationFacts P n)
    (hOverlap : InstrumentOverlap P n epsilon)
    (hEnvelope : WeightEnvelope P k n) :
    transportedFirstStage P n =
      ∫ x, transportWeight P n x * P.deltaD n x ∂sourceXLaw P n := by
  rfl

/-- The paper-declared ranges of the four scalar functionals.  This predicate
does not add a model assumption: the companion lemma below derives it from
membership in the transported-IV class. -/
def TransportedFunctionalRanges (P : TransportedArray 𝒳) (n : ℕ) : Prop :=
  transportedOutcomeITT P n ∈ Set.Icc (-1 : ℝ) 1 ∧
    -- @realizes \mu_{Y,n}(transported outcome ITT lies in [-1,1])
  transportedFirstStage P n ∈ Set.Ioc (0 : ℝ) 1 ∧
    -- @realizes \mu_n(transported first stage lies in (0,1])
  1 ≤ kishDispersion P n ∧
    -- @realizes \kappa_n(Kish dispersion lies in [1,∞))
  (0 < n → 0 < effectiveStrength P n)
    -- @realizes t_n(effective strength is positive on the paper domain n>0)

/-- Every transported-IV class member satisfies the scalar ranges declared in
the paper.  In particular these bounds are consequences of normalization,
bounded contrasts, complier positivity, and the defining identities rather
than additional hypotheses. -/
-- @realizes \mu_{Y,n}(range derived for every transported-IV class member)
-- @realizes \mu_n(range derived for every transported-IV class member)
-- @realizes \kappa_n(lower bound derived for every transported-IV class member)
-- @realizes t_n(positivity derived on the paper domain n>0)
lemma transportedFunctionalRanges_of_class
    (P : TransportedArray 𝒳) (N k : ℕ → ℕ) (c epsilon : ℝ) (n : ℕ)
    (hP : TransportedIVClass P N k c epsilon n) :
    TransportedFunctionalRanges P n := by
  have hSourceFacts :=
    sourceObservationFacts_of_class P N k c epsilon n hP
  have hTwo := hP.twoSampleArray
  have hOverlap := hP.instrumentOverlap
  have hRandom := hP.ivRandomization
  have hMono := hP.ivMonotonicity
  have hOutcome := hP.outcomeTransport
  have hReceipt := hP.receiptTransport
  have hPositive := hP.targetComplierPositivity
  have hDom := hP.transportDomination
  have hEnvelope := hP.weightEnvelope
  have hSecond := hP.weightSecondMoment
  letI : IsProbabilityMeasure (sourceObsLaw P n) := hTwo.2.1 n
  letI : IsProbabilityMeasure (sourceXLaw P n) := by
    unfold sourceXLaw
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure (targetXLaw P n) := hTwo.2.2.1 n
  have hWeightMeas : Measurable (transportWeight P n) :=
    (Measure.measurable_rnDeriv
      (targetXLaw P n) (sourceXLaw P n)).ennreal_toReal
  have hWeightMem : MemLp (transportWeight P n) 2 (sourceXLaw P n) := by
    refine MemLp.of_bound hWeightMeas.aestronglyMeasurable
      (2 * (k n : ℝ)) ?_
    filter_upwards [hEnvelope] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2
  have hWeightMean :
      (∫ x, transportWeight P n x ∂sourceXLaw P n) = 1 := by
    have hchange := integral_rnDeriv_smul
      (μ := targetXLaw P n) (ν := sourceXLaw P n)
      (f := fun _ => (1 : ℝ)) hDom
    simpa [transportWeight] using hchange
  have hKish : 1 ≤ kishDispersion P n := by
    have hv := variance_nonneg (transportWeight P n) (sourceXLaw P n)
    rw [variance_eq_sub hWeightMem, hWeightMean] at hv
    norm_num at hv ⊢
    simpa [kishDispersion] using hv
  have hDeltaYSource :
      ∀ᵐ x ∂sourceXLaw P n, P.deltaY n x ∈ Set.Icc (-1 : ℝ) 1 :=
    hSourceFacts.2.2.2.2.2.2.1
  have hDeltaDSource :
      ∀ᵐ x ∂sourceXLaw P n, P.deltaD n x ∈ Set.Icc (0 : ℝ) 1 :=
    hSourceFacts.2.2.2.2.2.2.2.2
  have hDeltaYTarget :
      ∀ᵐ x ∂targetXLaw P n, P.deltaY n x ∈ Set.Icc (-1 : ℝ) 1 :=
    hDom.ae_le hDeltaYSource
  have hDeltaDTarget :
      ∀ᵐ x ∂targetXLaw P n, P.deltaD n x ∈ Set.Icc (0 : ℝ) 1 :=
    hDom.ae_le hDeltaDSource
  have hYInt : Integrable (P.deltaY n) (targetXLaw P n) := by
    refine Integrable.of_bound
      (P.deltaY_measurable n).aestronglyMeasurable 1 ?_
    filter_upwards [hDeltaYTarget] with x hx
    rw [Real.norm_eq_abs]
    exact (abs_le).2 hx
  have hDInt : Integrable (P.deltaD n) (targetXLaw P n) := by
    refine Integrable.of_bound
      (P.deltaD_measurable n).aestronglyMeasurable 1 ?_
    filter_upwards [hDeltaDTarget] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2
  have hOutcomeChange :
      transportedOutcomeITT P n =
        ∫ x, P.deltaY n x ∂targetXLaw P n := by
    unfold transportedOutcomeITT transportWeight
    simpa only [smul_eq_mul] using
      (integral_rnDeriv_smul
        (μ := targetXLaw P n) (ν := sourceXLaw P n)
        (f := P.deltaY n) hDom)
  have hOutcomeRange :
      transportedOutcomeITT P n ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [hOutcomeChange]
    constructor
    · have hconst : Integrable (fun _ : 𝒳 => (-1 : ℝ)) (targetXLaw P n) :=
        integrable_const _
      simpa using integral_mono_ae hconst hYInt (hDeltaYTarget.mono fun x hx => hx.1)
    · have hconst : Integrable (fun _ : 𝒳 => (1 : ℝ)) (targetXLaw P n) :=
        integrable_const _
      simpa using integral_mono_ae hYInt hconst (hDeltaYTarget.mono fun x hx => hx.2)
  clear hOutcomeRange hOutcomeChange hYInt
    hDeltaYTarget hDeltaYSource hKish hWeightMean hWeightMem hWeightMeas hDInt
  have hMeasObserve :
      Measurable (observeSource : AssignedFullData 𝒳 → SourceObs 𝒳) := by
    have hx : Measurable fun q : AssignedFullData 𝒳 => q.1.2.1 := by fun_prop
    have hz : Measurable fun q : AssignedFullData 𝒳 => q.2 := by fun_prop
    have hd : Measurable fun q : AssignedFullData 𝒳 =>
        if q.2 then q.1.2.2.2.1 else q.1.2.2.1 := by
      exact Measurable.ite
        (hz (MeasurableSet.singleton true)) (by fun_prop) (by fun_prop)
    have hy : Measurable fun q : AssignedFullData 𝒳 =>
        if (if q.2 then q.1.2.2.2.1 else q.1.2.2.1)
          then q.1.2.2.2.2.2 else q.1.2.2.2.2.1 := by
      exact Measurable.ite
        (hd (MeasurableSet.singleton true)) (by fun_prop) (by fun_prop)
    exact hx.prodMk (hz.prodMk (hd.prodMk hy))
  have hSourceX :
      sourceXLaw P n = populationXLaw P n true := by
    have hFullX : Measurable (fullX : FullData 𝒳 → 𝒳) := by
      unfold fullX
      fun_prop
    rw [sourceXLaw, sourceObsLaw, Measure.map_map measurable_fst hMeasObserve]
    rw [populationXLaw, ← hSourceFacts.2.2.2.1]
    rw [Measure.map_map hFullX measurable_fst]
    congr 1
  have hSlice : ∀ z : Bool,
      ((P.assignedSourceLaw n).restrict {q | q.2 = z}).map Prod.fst =
        (populationLaw P n true).withDensity (fun o =>
          ENNReal.ofReal
            (if z then P.propensity n (fullX o)
              else 1 - P.propensity n (fullX o))) := by
    intro z
    let μ := populationLaw P n true
    let ν := ((P.assignedSourceLaw n).restrict {q | q.2 = z}).map Prod.fst
    let w : FullData 𝒳 → ℝ := fun o =>
      if z then P.propensity n (fullX o)
        else 1 - P.propensity n (fullX o)
    have hFullX : Measurable (fullX : FullData 𝒳 → 𝒳) := by
      unfold fullX
      fun_prop
    have hwmeas : Measurable w := by
      have hecomp : Measurable fun o : FullData 𝒳 =>
          P.propensity n (fullX o) :=
        (P.propensity_measurable n).comp hFullX
      cases z
      · simpa [w] using measurable_const.sub hecomp
      · simpa [w] using hecomp
    have hoverlapPop : ∀ᵐ o ∂μ,
        epsilon ≤ P.propensity n (fullX o) ∧
          P.propensity n (fullX o) ≤ 1 - epsilon := by
      have hx := hOverlap.2.2
      rw [hSourceX] at hx
      exact ae_of_ae_map hFullX.aemeasurable hx
    have hw0 : ∀ᵐ o ∂μ, 0 ≤ w o := by
      filter_upwards [hoverlapPop] with o ho
      unfold w
      cases z
      · simp
        linarith [hOverlap.1]
      · simpa using (le_trans hOverlap.1.le ho.1)
    have hwle : ∀ᵐ o ∂μ, w o ≤ 1 := by
      filter_upwards [hoverlapPop] with o ho
      unfold w
      cases z
      · simp
        linarith [ho.1, hOverlap.1]
      · simpa using ho.2.trans (sub_le_self 1 hOverlap.1.le)
    letI : IsProbabilityMeasure (P.assignedSourceLaw n) := hSourceFacts.1
    letI : IsProbabilityMeasure μ := by
      unfold μ
      rw [← hSourceFacts.2.2.2.1]
      exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    have hwint : Integrable w μ := by
      refine Integrable.of_bound hwmeas.aestronglyMeasurable 1 ?_
      filter_upwards [hw0, hwle] with o h0 h1
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact h1
    ext A hA
    rw [Measure.map_apply measurable_fst hA]
    rw [Measure.restrict_apply (hA.preimage measurable_fst)]
    rw [show Prod.fst ⁻¹' A ∩ {q | q.2 = z} =
        {q | q.1 ∈ A ∧ q.2 = z} by
      ext q
      simp]
    rw [withDensity_apply _ hA]
    rw [← ofReal_integral_eq_lintegral_ofReal hwint.integrableOn
      ((ae_restrict_iff' hA).2
        (Filter.Eventually.mono hw0 fun _ hx _ => hx))]
    rw [← hRandom A hA z, ENNReal.ofReal_toReal
      (measure_ne_top (P.assignedSourceLaw n) _)]
  have hFullXMeas : Measurable (fullX : FullData 𝒳 → 𝒳) := by
    unfold fullX
    fun_prop
  have hD0Meas : Measurable fun o : FullData 𝒳 => boolReal (fullD0 o) := by
    unfold boolReal
    have hd : Measurable (fullD0 : FullData 𝒳 → Bool) := by
      unfold fullD0
      fun_prop
    exact Measurable.ite
      (hd (MeasurableSet.singleton true))
      measurable_const measurable_const
  have hD1Meas : Measurable fun o : FullData 𝒳 => boolReal (fullD1 o) := by
    unfold boolReal
    have hd : Measurable (fullD1 : FullData 𝒳 → Bool) := by
      unfold fullD1
      fun_prop
    exact Measurable.ite
      (hd (MeasurableSet.singleton true))
      measurable_const measurable_const
  have hOverlapObs : ∀ᵐ o ∂sourceObsLaw P n,
      epsilon ≤ P.propensity n o.1 ∧
        P.propensity n o.1 ≤ 1 - epsilon := by
    have hx := hOverlap.2.2
    unfold sourceXLaw at hx
    exact ae_of_ae_map measurable_fst.aemeasurable hx
  have hScoreMeas : Measurable (instrumentScore P n) := by
    unfold instrumentScore
    exact Measurable.ite
      ((by fun_prop : Measurable fun o : SourceObs 𝒳 => o.2.1)
        (MeasurableSet.singleton true))
      (measurable_const.div ((P.propensity_measurable n).comp measurable_fst))
      (measurable_const.neg.div
        (measurable_const.sub ((P.propensity_measurable n).comp measurable_fst)))
  have hScoreBound : ∀ᵐ o ∂sourceObsLaw P n,
      |instrumentScore P n o| ≤ 1 / epsilon := by
    filter_upwards [hOverlapObs] with o ho
    rcases o with ⟨x, z, d, y⟩
    cases z
    · simp only [instrumentScore, Bool.false_eq_true, ↓reduceIte, abs_neg,
        abs_div, abs_one]
      rw [abs_of_pos (sub_pos.mpr (lt_of_le_of_lt ho.2
        (by linarith [hOverlap.1])))]
      exact one_div_le_one_div_of_le hOverlap.1 (by linarith [ho.2])
    · simp only [instrumentScore, ↓reduceIte, abs_div, abs_one]
      rw [abs_of_pos (lt_of_lt_of_le hOverlap.1 ho.1)]
      exact one_div_le_one_div_of_le hOverlap.1 ho.1
  have hReceiptScoreInt :
      Integrable (fun o =>
        instrumentScore P n o * boolReal o.2.2.1) (sourceObsLaw P n) := by
    refine Integrable.of_bound
      ((hScoreMeas.mul
        (Measurable.ite
          ((by fun_prop : Measurable fun o : SourceObs 𝒳 => o.2.2.1)
            (MeasurableSet.singleton true))
          measurable_const measurable_const)).aestronglyMeasurable)
      (1 / epsilon) ?_
    filter_upwards [hScoreBound] with o hs
    rw [Real.norm_eq_abs, abs_mul]
    cases o.2.2.1
    · simp only [boolReal, Bool.false_eq_true, ↓reduceIte, abs_zero, mul_zero]
      exact (one_div_pos.mpr hOverlap.1).le
    · simpa [boolReal] using hs
  have hD0Int :
      Integrable (fun o : FullData 𝒳 => boolReal (fullD0 o))
        (populationLaw P n true) := by
    letI : IsProbabilityMeasure (P.assignedSourceLaw n) := hSourceFacts.1
    letI : IsProbabilityMeasure (populationLaw P n true) := by
      rw [← hSourceFacts.2.2.2.1]
      exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    refine Integrable.of_bound hD0Meas.aestronglyMeasurable 1 ?_
    filter_upwards with o
    cases fullD0 o <;> simp [boolReal]
  have hD1Int :
      Integrable (fun o : FullData 𝒳 => boolReal (fullD1 o))
        (populationLaw P n true) := by
    letI : IsProbabilityMeasure (P.assignedSourceLaw n) := hSourceFacts.1
    letI : IsProbabilityMeasure (populationLaw P n true) := by
      rw [← hSourceFacts.2.2.2.1]
      exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    refine Integrable.of_bound hD1Meas.aestronglyMeasurable 1 ?_
    filter_upwards with o
    cases fullD1 o <;> simp [boolReal]
  have hIPW : ∀ (A : Set 𝒳), MeasurableSet A →
      (∫ q in {q | fullX q.1 ∈ A},
        (if q.2 then
          (1 / P.propensity n (fullX q.1)) * boolReal (fullD1 q.1)
        else
          (-1 / (1 - P.propensity n (fullX q.1))) *
            boolReal (fullD0 q.1)) ∂P.assignedSourceLaw n) =
        ∫ o in {o | fullX o ∈ A},
          (boolReal (fullD1 o) - boolReal (fullD0 o))
          ∂populationLaw P n true := by
    intro A hA
    let μ := populationLaw P n true
    let e : FullData 𝒳 → ℝ := fun o => P.propensity n (fullX o)
    let S : Set (AssignedFullData 𝒳) := {q | fullX q.1 ∈ A}
    let E : Set (AssignedFullData 𝒳) := {q | q.2 = true}
    let W : AssignedFullData 𝒳 → ℝ := fun q =>
      if q.2 then (1 / e q.1) * boolReal (fullD1 q.1)
      else (-1 / (1 - e q.1)) * boolReal (fullD0 q.1)
    have hS : MeasurableSet S :=
      hA.preimage (hFullXMeas.comp measurable_fst)
    have hE : MeasurableSet E :=
      measurable_snd (MeasurableSet.singleton true)
    have hemeas : Measurable e :=
      (P.propensity_measurable n).comp hFullXMeas
    have hWInt : Integrable W (P.assignedSourceLaw n) := by
      have hpull :
          Integrable (fun q : AssignedFullData 𝒳 =>
            instrumentScore P n (observeSource q) *
              boolReal (observeSource q).2.2.1)
            (P.assignedSourceLaw n) := by
        unfold sourceObsLaw at hReceiptScoreInt
        exact hReceiptScoreInt.comp_measurable hMeasObserve
      apply hpull.congr
      filter_upwards with q
      cases hz : q.2 <;>
        cases hd0 : fullD0 q.1 <;> cases hd1 : fullD1 q.1 <;>
          simp [W, e, observeSource, instrumentScore, potentialReceipt,
            boolReal, hz, hd0, hd1]
    have hsplit := integral_add_compl
      (μ := (P.assignedSourceLaw n).restrict S) hE hWInt.integrableOn
    have hoverlapPop : ∀ᵐ o ∂μ,
        epsilon ≤ e o ∧ e o ≤ 1 - epsilon := by
      have hx := hOverlap.2.2
      rw [hSourceX] at hx
      exact ae_of_ae_map hFullXMeas.aemeasurable hx
    have htrue :
        (∫ q in S ∩ E, W q ∂P.assignedSourceLaw n) =
          ∫ o in {o | fullX o ∈ A}, boolReal (fullD1 o) ∂μ := by
      have hmap :
          (∫ o in {o | fullX o ∈ A}, (1 / e o) * boolReal (fullD1 o)
              ∂(((P.assignedSourceLaw n).restrict E).map Prod.fst)) =
            ∫ q in S ∩ E, W q ∂P.assignedSourceLaw n := by
        calc
          _ = ∫ q in Prod.fst ⁻¹' {o | fullX o ∈ A},
                (1 / e q.1) * boolReal (fullD1 q.1)
                ∂(P.assignedSourceLaw n).restrict E :=
            setIntegral_map (μ := (P.assignedSourceLaw n).restrict E)
              (hA.preimage hFullXMeas)
              ((measurable_const.div hemeas).mul hD1Meas).aestronglyMeasurable
              measurable_fst.aemeasurable
          _ = _ := by
            rw [Measure.restrict_restrict' hE]
            apply integral_congr_ae
            filter_upwards [ae_restrict_mem (hS.inter hE)] with q hq
            have hqtrue : q.2 = true := hq.2
            simp [W, hqtrue]
      rw [← hmap, hSlice true]
      change (∫ o in {o | fullX o ∈ A},
        (1 / e o) * boolReal (fullD1 o)
          ∂μ.withDensity (fun o => ENNReal.ofReal (e o))) = _
      calc
        _ = ∫ o in {o | fullX o ∈ A},
            (ENNReal.ofReal (e o)).toReal •
              ((1 / e o) * boolReal (fullD1 o)) ∂μ :=
          setIntegral_withDensity_eq_setIntegral_toReal_smul
            (ENNReal.measurable_ofReal.comp hemeas)
            (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
            _ (hA.preimage hFullXMeas)
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_of_ae hoverlapPop] with o ho
          have hepos : 0 < e o := lt_of_lt_of_le hOverlap.1 ho.1
          simp [ENNReal.toReal_ofReal hepos.le, smul_eq_mul, hepos.ne']
    have hfalse :
        (∫ q in S ∩ Eᶜ, W q ∂P.assignedSourceLaw n) =
          ∫ o in {o | fullX o ∈ A}, -boolReal (fullD0 o) ∂μ := by
      have hEf : {q : AssignedFullData 𝒳 | q.2 = false} = Eᶜ := by
        ext q
        cases q.2 <;> simp [E]
      have hmap :
          (∫ o in {o | fullX o ∈ A},
              (-1 / (1 - e o)) * boolReal (fullD0 o)
              ∂(((P.assignedSourceLaw n).restrict {q | q.2 = false}).map
                Prod.fst)) =
            ∫ q in S ∩ Eᶜ, W q ∂P.assignedSourceLaw n := by
        calc
          _ = ∫ q in Prod.fst ⁻¹' {o | fullX o ∈ A},
                (-1 / (1 - e q.1)) * boolReal (fullD0 q.1)
                ∂(P.assignedSourceLaw n).restrict {q | q.2 = false} :=
            setIntegral_map
              (μ := (P.assignedSourceLaw n).restrict {q | q.2 = false})
              (hA.preimage hFullXMeas)
              ((measurable_const.neg.div
                (measurable_const.sub hemeas)).mul hD0Meas).aestronglyMeasurable
              measurable_fst.aemeasurable
          _ = _ := by
            rw [hEf, Measure.restrict_restrict' hE.compl]
            apply integral_congr_ae
            filter_upwards [ae_restrict_mem (hS.inter hE.compl)] with q hq
            have hqfalse : q.2 = false := by
              cases hqz : q.2
              · rfl
              · exact False.elim (hq.2 (by simp [E, hqz]))
            simp [W, hqfalse]
      rw [← hmap, hSlice false]
      change (∫ o in {o | fullX o ∈ A},
        (-1 / (1 - e o)) * boolReal (fullD0 o)
          ∂μ.withDensity (fun o => ENNReal.ofReal (1 - e o))) = _
      calc
        _ = ∫ o in {o | fullX o ∈ A},
            (ENNReal.ofReal (1 - e o)).toReal •
              ((-1 / (1 - e o)) * boolReal (fullD0 o)) ∂μ :=
          setIntegral_withDensity_eq_setIntegral_toReal_smul
            (ENNReal.measurable_ofReal.comp (measurable_const.sub hemeas))
            (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
            _ (hA.preimage hFullXMeas)
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_of_ae hoverlapPop] with o ho
          have hden : 0 < 1 - e o := by linarith [ho.2, hOverlap.1]
          rw [ENNReal.toReal_ofReal hden.le]
          simp only [smul_eq_mul]
          field_simp [hden.ne']
    have hsplitW :
        (∫ q in S ∩ E, W q ∂P.assignedSourceLaw n) +
          (∫ q in S ∩ Eᶜ, W q ∂P.assignedSourceLaw n) =
            ∫ q in S, W q ∂P.assignedSourceLaw n := by
      rw [Measure.restrict_restrict hE,
        Measure.restrict_restrict hE.compl] at hsplit
      simpa [S, E, W, e, Set.inter_comm] using hsplit
    change (∫ q in S, W q ∂P.assignedSourceLaw n) =
      ∫ o in {o | fullX o ∈ A},
        boolReal (fullD1 o) - boolReal (fullD0 o) ∂μ
    rw [← hsplitW, htrue, hfalse]
    calc
      (∫ o in {o | fullX o ∈ A}, boolReal (fullD1 o) ∂μ) +
          ∫ o in {o | fullX o ∈ A}, -boolReal (fullD0 o) ∂μ =
          ∫ o in {o | fullX o ∈ A},
            boolReal (fullD1 o) + -boolReal (fullD0 o) ∂μ := by
        simpa only [Pi.neg_apply] using
          (integral_add hD1Int.integrableOn hD0Int.neg.integrableOn).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with o
        ring
  have hDeltaDMoment : ∀ A, MeasurableSet A →
      (∫ x in A, P.deltaD n x ∂sourceXLaw P n) =
        ∫ x in A, P.receiptContrast n true x ∂sourceXLaw P n := by
    intro A hA
    have hpull :
        Integrable (fun q : AssignedFullData 𝒳 =>
          instrumentScore P n (observeSource q) *
            boolReal (observeSource q).2.2.1)
          (P.assignedSourceLaw n) := by
      unfold sourceObsLaw at hReceiptScoreInt
      exact hReceiptScoreInt.comp_measurable hMeasObserve
    calc
      (∫ x in A, P.deltaD n x ∂sourceXLaw P n) =
          ∫ o in {o | o.1 ∈ A},
            instrumentScore P n o * boolReal o.2.2.1
              ∂sourceObsLaw P n :=
        (hSourceFacts.2.2.2.2.2.2.2.1 A hA).symm
      _ = ∫ q in {q | fullX q.1 ∈ A},
          (if q.2 then
            (1 / P.propensity n (fullX q.1)) * boolReal (fullD1 q.1)
          else
            (-1 / (1 - P.propensity n (fullX q.1))) *
              boolReal (fullD0 q.1)) ∂P.assignedSourceLaw n := by
        unfold sourceObsLaw
        calc
          _ = ∫ q in observeSource ⁻¹' {o | o.1 ∈ A},
              instrumentScore P n (observeSource q) *
                boolReal (observeSource q).2.2.1
                ∂P.assignedSourceLaw n :=
            setIntegral_map (μ := P.assignedSourceLaw n)
              (hA.preimage measurable_fst)
              (hScoreMeas.mul
                (Measurable.ite
                  ((by fun_prop :
                    Measurable fun o : SourceObs 𝒳 => o.2.2.1)
                    (MeasurableSet.singleton true))
                  measurable_const measurable_const)).aestronglyMeasurable
              hMeasObserve.aemeasurable
          _ = _ := by
            apply integral_congr_ae
            filter_upwards with q
            cases hz : q.2 <;>
              cases hd0 : fullD0 q.1 <;> cases hd1 : fullD1 q.1 <;>
                simp [observeSource, instrumentScore, potentialReceipt,
                  boolReal, fullX, hz, hd0, hd1]
      _ = ∫ o in {o | fullX o ∈ A},
          (boolReal (fullD1 o) - boolReal (fullD0 o))
            ∂populationLaw P n true := hIPW A hA
      _ = ∫ x in A, P.receiptContrast n true x ∂sourceXLaw P n := by
        rw [hSourceX]
        simpa using hReceipt.1 true A hA
  have hDeltaDReceiptSource :
      P.deltaD n =ᵐ[sourceXLaw P n] P.receiptContrast n true := by
    let E : ℕ → Set 𝒳 := fun m =>
      {x | |P.receiptContrast n true x| ≤ (m : ℝ)}
    have hEmeas : ∀ m, MeasurableSet (E m) := by
      intro m
      exact
        ((P.receiptContrast_measurable n true).norm
          measurableSet_Iic)
    have heq : ∀ m, P.deltaD n =ᵐ[(sourceXLaw P n).restrict (E m)]
        P.receiptContrast n true := by
      intro m
      have hdi : Integrable (P.deltaD n)
          ((sourceXLaw P n).restrict (E m)) := by
        exact (Integrable.of_bound
          (P.deltaD_measurable n).aestronglyMeasurable 1
          (hDeltaDSource.mono fun x hx => by
            rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
            exact hx.2)).integrableOn
      have hri : Integrable (P.receiptContrast n true)
          ((sourceXLaw P n).restrict (E m)) := by
        refine Integrable.of_bound
          (P.receiptContrast_measurable n true).aestronglyMeasurable m ?_
        filter_upwards [ae_restrict_mem (hEmeas m)] with x hx
        simpa [Real.norm_eq_abs, E] using hx
      refine Integrable.ae_eq_of_forall_setIntegral_eq
        (P.deltaD n) (P.receiptContrast n true) hdi hri ?_
      intro A hA hAfin
      simpa [Measure.restrict_restrict hA, Set.inter_comm] using
        hDeltaDMoment (A ∩ E m) (hA.inter (hEmeas m))
    have hall : ∀ᵐ x ∂sourceXLaw P n, ∀ m,
        x ∈ E m → P.deltaD n x = P.receiptContrast n true x := by
      apply ae_all_iff.mpr
      intro m
      exact (ae_restrict_iff' (hEmeas m)).mp (heq m)
    filter_upwards [hall] with x hx
    obtain ⟨m, hm⟩ := exists_nat_ge |P.receiptContrast n true x|
    exact hx m hm
  have hDeltaDReceiptTarget :
      P.deltaD n =ᵐ[targetXLaw P n] P.receiptContrast n true :=
    hDom.ae_le hDeltaDReceiptSource
  have hFirstChange :
      transportedFirstStage P n =
        ∫ x, P.deltaD n x ∂targetXLaw P n := by
    have hWeightMeasurable : Measurable (transportWeight P n) :=
      (Measure.measurable_rnDeriv
        (targetXLaw P n) (sourceXLaw P n)).ennreal_toReal
    have hWeightBoundObs : ∀ᵐ o ∂sourceObsLaw P n,
        0 ≤ transportWeight P n o.1 ∧
          transportWeight P n o.1 ≤ 2 * (k n : ℝ) := by
      have hx := hEnvelope
      unfold sourceXLaw at hx
      exact ae_of_ae_map measurable_fst.aemeasurable hx
    have hWeightedScoreIntegrable :
        Integrable (fun o => transportWeight P n o.1 *
          (instrumentScore P n o * boolReal o.2.2.1))
          (sourceObsLaw P n) := by
      refine Integrable.of_bound
        (((hWeightMeasurable.comp measurable_fst).mul
          (hScoreMeas.mul (by
            unfold boolReal
            have hd : Measurable fun o : SourceObs 𝒳 => o.2.2.1 := by
              fun_prop
            exact Measurable.ite (hd (MeasurableSet.singleton true))
              measurable_const measurable_const))).aestronglyMeasurable)
        ((2 * (k n : ℝ)) * (1 / epsilon)) ?_
      filter_upwards [hWeightBoundObs, hScoreBound] with o hw hs
      have hbool : |boolReal o.2.2.1| ≤ 1 := by
        cases o.2.2.1 <;> simp [boolReal]
      have hscoreReceipt :
          |instrumentScore P n o * boolReal o.2.2.1| ≤ 1 / epsilon := by
        rw [abs_mul]
        calc
          |instrumentScore P n o| * |boolReal o.2.2.1| ≤
              (1 / epsilon) * 1 :=
            mul_le_mul hs hbool (abs_nonneg _)
              (one_div_nonneg.mpr hOverlap.1.le)
          _ = 1 / epsilon := mul_one _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw.1]
      exact mul_le_mul hw.2 hscoreReceipt (abs_nonneg _)
        (mul_nonneg (by positivity) (Nat.cast_nonneg _))
    have hDeltaDIntegrable :
        Integrable (P.deltaD n) (sourceXLaw P n) := by
      refine Integrable.of_bound
        (P.deltaD_measurable n).aestronglyMeasurable 1 ?_
      filter_upwards [hDeltaDSource] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact hx.2
    have hWeightedDeltaDIntegrable :
        Integrable (fun x => transportWeight P n x * P.deltaD n x)
          (sourceXLaw P n) := by
      refine Integrable.of_bound
        ((hWeightMeasurable.mul (P.deltaD_measurable n)).aestronglyMeasurable)
        (2 * (k n : ℝ)) ?_
      filter_upwards [hEnvelope, hDeltaDSource] with x hw hd
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw.1,
        abs_of_nonneg hd.1]
      calc
        transportWeight P n x * P.deltaD n x ≤
            (2 * (k n : ℝ)) * 1 :=
          mul_le_mul hw.2 hd.2 hd.1
            (mul_nonneg (by positivity) (Nat.cast_nonneg _))
        _ = 2 * (k n : ℝ) := mul_one _
    calc
      transportedFirstStage P n =
          ∫ x, transportWeight P n x * P.deltaD n x
            ∂sourceXLaw P n := by
        rfl
      _ = ∫ x, P.deltaD n x ∂targetXLaw P n := by
        unfold transportWeight
        simpa only [smul_eq_mul] using
          (integral_rnDeriv_smul
            (μ := targetXLaw P n) (ν := sourceXLaw P n)
            (f := P.deltaD n) hDom)
  have hFirstEq :
      transportedFirstStage P n = targetComplierShare P n := by
    rw [hFirstChange]
    calc
      (∫ x, P.deltaD n x ∂targetXLaw P n) =
          ∫ x, P.receiptContrast n true x ∂targetXLaw P n :=
        integral_congr_ae hDeltaDReceiptTarget
      _ = ∫ x, P.receiptContrast n false x ∂targetXLaw P n :=
        hReceipt.2.symm
      _ = ∫ o, (boolReal (fullD1 o) - boolReal (fullD0 o))
            ∂populationLaw P n false := by
        simpa using (hReceipt.1 false Set.univ MeasurableSet.univ).symm
      _ = ∫ o, (if fullD1 o = true ∧ fullD0 o = false
            then (1 : ℝ) else 0) ∂populationLaw P n false := by
        apply integral_congr_ae
        filter_upwards [hMono false] with o ho
        cases h0 : fullD0 o <;> cases h1 : fullD1 o <;>
          simp [boolReal, h0, h1] at ho ⊢ <;> norm_num at ho
      _ = targetComplierShare P n := by
        unfold targetComplierShare
        have hC : MeasurableSet
            {o : FullData 𝒳 | fullD1 o = true ∧ fullD0 o = false} := by
          exact
            ((by
              unfold fullD1
              fun_prop : Measurable (fullD1 : FullData 𝒳 → Bool))
                (MeasurableSet.singleton true)).inter
            ((by
              unfold fullD0
              fun_prop : Measurable (fullD0 : FullData 𝒳 → Bool))
                (MeasurableSet.singleton false))
        simpa [Set.indicator, Measure.real] using
          (integral_indicator_const
            (μ := populationLaw P n false) (1 : ℝ) hC)
  have hFirstPos : 0 < transportedFirstStage P n := by
    rw [hFirstEq]
    exact hPositive
  have hFirstUpper : transportedFirstStage P n ≤ 1 := by
    rw [hFirstChange]
    have hDInt : Integrable (P.deltaD n) (targetXLaw P n) := by
      refine Integrable.of_bound
        (P.deltaD_measurable n).aestronglyMeasurable 1 ?_
      filter_upwards [hDeltaDTarget] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact hx.2
    have hconst : Integrable (fun _ : 𝒳 => (1 : ℝ)) (targetXLaw P n) :=
      integrable_const _
    simpa using integral_mono_ae hDInt hconst (hDeltaDTarget.mono fun x hx => hx.2)
  have hDeltaYSource :
      ∀ᵐ x ∂sourceXLaw P n, P.deltaY n x ∈ Set.Icc (-1 : ℝ) 1 :=
    hSourceFacts.2.2.2.2.2.2.1
  have hDeltaYTarget :
      ∀ᵐ x ∂targetXLaw P n, P.deltaY n x ∈ Set.Icc (-1 : ℝ) 1 :=
    hDom.ae_le hDeltaYSource
  have hYInt : Integrable (P.deltaY n) (targetXLaw P n) := by
    refine Integrable.of_bound
      (P.deltaY_measurable n).aestronglyMeasurable 1 ?_
    filter_upwards [hDeltaYTarget] with x hx
    rw [Real.norm_eq_abs]
    exact (abs_le).2 hx
  have hOutcomeChange :
      transportedOutcomeITT P n =
        ∫ x, P.deltaY n x ∂targetXLaw P n := by
    unfold transportedOutcomeITT transportWeight
    simpa only [smul_eq_mul] using
      (integral_rnDeriv_smul
        (μ := targetXLaw P n) (ν := sourceXLaw P n)
        (f := P.deltaY n) hDom)
  have hOutcomeRange :
      transportedOutcomeITT P n ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [hOutcomeChange]
    constructor
    · have hconst : Integrable (fun _ : 𝒳 => (-1 : ℝ)) (targetXLaw P n) :=
        integrable_const _
      simpa using integral_mono_ae hconst hYInt
        (hDeltaYTarget.mono fun x hx => hx.1)
    · have hconst : Integrable (fun _ : 𝒳 => (1 : ℝ)) (targetXLaw P n) :=
        integrable_const _
      simpa using integral_mono_ae hYInt hconst
        (hDeltaYTarget.mono fun x hx => hx.2)
  have hWeightMeas : Measurable (transportWeight P n) :=
    (Measure.measurable_rnDeriv
      (targetXLaw P n) (sourceXLaw P n)).ennreal_toReal
  have hWeightMem : MemLp (transportWeight P n) 2 (sourceXLaw P n) := by
    refine MemLp.of_bound hWeightMeas.aestronglyMeasurable
      (2 * (k n : ℝ)) ?_
    filter_upwards [hEnvelope] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2
  have hWeightMean :
      (∫ x, transportWeight P n x ∂sourceXLaw P n) = 1 := by
    have hchange := integral_rnDeriv_smul
      (μ := targetXLaw P n) (ν := sourceXLaw P n)
      (f := fun _ => (1 : ℝ)) hDom
    simpa [transportWeight] using hchange
  have hKish : 1 ≤ kishDispersion P n := by
    have hv := variance_nonneg (transportWeight P n) (sourceXLaw P n)
    rw [variance_eq_sub hWeightMem, hWeightMean] at hv
    norm_num at hv ⊢
    simpa [kishDispersion] using hv
  refine ⟨hOutcomeRange, ⟨hFirstPos, hFirstUpper⟩, hKish, ?_⟩
  intro hn
  unfold effectiveStrength
  positivity

-- @node: def:finite-cell-class
/-- Uniform finite-cell subclass, flattened to the sixteen core members.
Its `finiteCellSource` field carries the exact finite pushforward-law
exhaustion condition, rather than merely requiring full mass on some subset. -/
structure FiniteCellClass (P : TransportedArray 𝒳) (N k : ℕ → ℕ)
    (c epsilon : ℝ) (n : ℕ) : Prop where
  fullDataSupport : FullDataSupport P n
  populationPresence : PopulationPresence P n
  twoSampleArray : TwoSampleArray P N c
  instrumentOverlap : InstrumentOverlap P n epsilon
  sourceObservation : SourceAssignmentConsistency P n
  ivRandomization : IVRandomization P n
  ivExclusion : IVExclusion P n
  ivMonotonicity : IVMonotonicity P n
  outcomeTransport : OutcomeTransport P n
  receiptTransport : ReceiptTransport P n
  targetComplierPositivity : TargetComplierPositivity P n
  transportDomination : TransportDomination P n
  weightEnvelope : WeightEnvelope P k n
  weightSecondMoment : WeightSecondMoment P k n
  degradingArray : DegradingArray P k
  finiteCellSource : FiniteCellSource P k n
  -- @realizes \mathcal N_n(uniform finite-cell subclass)

/-- Forget the finite-cell restriction. -/
def FiniteCellClass.toTransportedIVClass
    (h : FiniteCellClass P N k c epsilon n) :
    TransportedIVClass P N k c epsilon n :=
  { h with }

/-! ## Deterministic transport geometry and slices -/

-- @env: S3
/-- Deterministic source/target covariate, weight, and propensity arrays. -/
structure Geometry (𝒳 : Type*) [MeasurableSpace 𝒳] where
  sourceX : ℕ → Measure 𝒳
    -- @realizes P_S^X(geometry source-law array)
  targetX : ℕ → Measure 𝒳
    -- @realizes P_T(geometry target-law array)
  weight : ℕ → 𝒳 → ℝ
    -- @realizes w(geometry density-ratio array)
  propensity : ℕ → 𝒳 → ℝ
    -- @realizes e(geometry propensity array)
  weight_measurable : ∀ n, Measurable (weight n)
  propensity_measurable : ∀ n, Measurable (propensity n)

-- @node: def:admissible-geometry-class
/-- Admissible deterministic geometry class. -/
def AdmissibleGeometry (g : Geometry 𝒳) (k : ℕ → ℕ) (epsilon : ℝ) : Prop :=
  (∀ n, IsProbabilityMeasure (g.sourceX n)) ∧
  (∀ n, IsProbabilityMeasure (g.targetX n)) ∧
  0 < epsilon ∧ epsilon < 1 / 2 ∧
  (∀ n x,
    epsilon ≤ g.propensity n x ∧ g.propensity n x ≤ 1 - epsilon) ∧
    -- @realizes e(pointwise geometry propensity in [epsilon,1-epsilon])
  (∀ n x, 0 ≤ g.weight n x ∧ g.weight n x ≤ 2 * (k n : ℝ)) ∧
    -- @realizes w(pointwise geometry weight in [0,2k_n])
  (∀ n, ∫ x, g.weight n x ∂g.sourceX n = 1) ∧
  (∀ n, ∫ x, (g.weight n x) ^ 2 ∂g.sourceX n ≤ (k n : ℝ)) ∧
  (∀ n A, MeasurableSet A →
    g.targetX n A =
      ENNReal.ofReal (∫ x in A, g.weight n x ∂g.sourceX n))
  -- @realizes \mathcal G(class of admissible geometry arrays)
  -- @realizes \mathfrak g((P_S^X,w,e) array satisfying these clauses)
  -- @realizes \kappa_n(geometry second moment)

-- @node: def:fixed-geometry-slice
/-- Laws whose source law, target law, and propensity equal geometry `g` at
index `n`, with the law-induced Radon--Nikodym weight equal to the geometry
weight source-almost everywhere.  The a.e. clause respects the fact that
density-ratio versions are determined only up to source-null sets. -/
def fixedGeometrySlice (P : TransportedArray 𝒳) (g : Geometry 𝒳)
    (N k : ℕ → ℕ) (c epsilon : ℝ) (n : ℕ) : Prop :=
  TransportedIVClass P N k c epsilon n ∧
    sourceXLaw P n = g.sourceX n ∧
    targetXLaw P n = g.targetX n ∧
    transportWeight P n =ᵐ[sourceXLaw P n] g.weight n ∧
    P.propensity n = g.propensity n
  -- @realizes \mathcal P_n(\mathfrak g)(fixed-geometry model slice)

-- @node: def:regular-finite-cell-class
/-- Regular nonuniform finite-cell subclass on a finite injected support whose
image has full source mass. -/
def RegularFiniteCellClass (P : TransportedArray 𝒳) (N k : ℕ → ℕ)
    (c epsilon cminus cplus : ℝ) (n : ℕ) : Prop :=
  TransportedIVClass P N k c epsilon n ∧
  0 < k n ∧
  0 < cminus ∧ cminus ≤ 1 ∧ 1 ≤ cplus ∧
  ∃ cell : Fin (k n) ↪ 𝒳,
    (∀ i : Fin (k n), MeasurableSet {cell i}) ∧
    sourceXLaw P n (Set.range cell) = 1 ∧
    ∀ i : Fin (k n),
      cminus / (k n : ℝ) ≤
        (sourceXLaw P n {cell i}).toReal ∧
      (sourceXLaw P n {cell i}).toReal ≤ cplus / (k n : ℝ)
    -- @realizes \mathcal X(the source's discrete cell space: the cells are
    --   measurable atoms, so every subset of the support is measurable)
    -- @realizes q_{x,n}(P_S^X{x})
    -- @realizes c_-(0<c_-≤1 and lower cell bound)
    -- @realizes c_+(1≤c_+ and upper cell bound)
    -- @realizes \mathcal X(finite injected support in the arbitrary fixed carrier)
    -- @realizes \mathcal N_n^{\mathrm{reg}}(regular finite-cell subclass)

/-! ## Scalar environment -/

-- @env: S4
variable (alpha rho t0 c0 C0 tc : ℝ)
  -- @realizes \rho((1-α)/8; range supplied by witness)

end CausalSmith.Stat.TransportedLateStrengthFrontier
