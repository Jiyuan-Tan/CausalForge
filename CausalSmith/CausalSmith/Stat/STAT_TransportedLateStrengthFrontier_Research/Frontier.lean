/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Honest expected-length frontier

Bundled confidence-set sequences carry their range and the graph measurability
appropriate to their declared deterministic inputs. The four honesty
predicates and four expected-length values use the paper's liminf/limsup and
infimum/supremum order.

`Causalean.Estimation.MinimaxATE.Model` and
`Causalean.PO.ID.Partial.Inference.Basic` are analogous packaging and coverage
modules, but their estimands and risks differ, so this layer is local.
-/

import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Causalean.Estimation.MinimaxATE.Model
import Causalean.PO.ID.Partial.Inference.Basic
import Causalean.Stat.Minimax.HonestConfidenceSet

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open Filter MeasureTheory
open scoped ENNReal Topology

variable {𝒳 : Type*} [MeasurableSpace 𝒳]
variable {N k : ℕ → ℕ} {c epsilon cminus cplus : ℝ}

/-! ## Procedure objects -/

/-- Oracle weight inputs use a carrier whose elements are nonnegative
pointwise, matching the density-ratio space. -/
abbrev NonnegativeWeight (𝒳 : Type*) := {w : 𝒳 → ℝ // ∀ x, 0 ≤ w x}
  -- @realizes w(oracle-input carrier 𝒳→[0,∞))

/-- The law-induced Radon--Nikodym weight as an admissible oracle input. -/
noncomputable def transportWeightInput (P : TransportedArray 𝒳) (n : ℕ) :
    NonnegativeWeight 𝒳 :=
  ⟨transportWeight P n, fun _ => ENNReal.toReal_nonneg⟩

/-- A measurable nonnegative version of a model row's transport density
ratio.  The paper determines `w` only source-law almost everywhere, so global
oracle honesty and risk range over this entire nonempty fiber rather than
silently selecting one Mathlib representative. -/
def TransportWeightVersion (P : TransportedArray 𝒳) (n : ℕ) :=
  {w : NonnegativeWeight 𝒳 //
    Measurable w.1 ∧ w.1 =ᵐ[sourceXLaw P n] transportWeight P n}

/-- The canonical Radon--Nikodym representative witnesses that every version
fiber is nonempty. -/
noncomputable def canonicalTransportWeightVersion
    (P : TransportedArray 𝒳) (n : ℕ) : TransportWeightVersion P n :=
  ⟨transportWeightInput P n,
    (Measure.measurable_rnDeriv (targetXLaw P n) (sourceXLaw P n)).ennreal_toReal,
    Filter.Eventually.of_forall fun _ => rfl⟩

/-- A fixed geometry's declared density-ratio version as an oracle input.
Admissible geometries take the first branch, so procedures receive exactly
`g.weight`; the zero fallback only totalizes this definition away from the
admissible geometry class. -/
noncomputable def geometryWeightInput (g : Geometry 𝒳) (n : ℕ) :
    NonnegativeWeight 𝒳 := by
  classical
  exact if h : ∀ x, 0 ≤ g.weight n x then
      ⟨g.weight n, h⟩
    else
      ⟨fun _ => 0, fun _ => le_rfl⟩

/-- Inputs available to an oracle procedure. -/
abbrev OracleInput (𝒳 : Type*) (N : ℕ → ℕ) (n : ℕ) :=
  TwoSample 𝒳 n (N n) × NonnegativeWeight 𝒳 × (𝒳 → ℝ)
  -- @realizes w(oracle-known nonnegative weight input)
  -- @realizes e(oracle-known propensity input)

/-- Inputs available to a feasible finite-cell procedure. `FiniteCellSource`
pins the row-`n` measure to the image of `Fin (k n)` inside the arbitrary
ambient carrier. -/
abbrev FiniteCellInput (𝒳 : Type*) (N _k : ℕ → ℕ) (n : ℕ) :=
  TwoSample 𝒳 n (N n)

/-- The realized regular-cell support inside the fixed ambient carrier.  The
embedding is part of the experiment, so a procedure is never compared across
an unrelated alternative support. -/
structure RegularCellDesign (𝒳 : Type*) [MeasurableSpace 𝒳] (m : ℕ) where
  cell : Fin m ↪ 𝒳
  measurableCell : ∀ i, MeasurableSet {cell i}

/-- Inputs available to a regular-cell procedure: samples, the true realized
support, and the known `Fin (k n)`-indexed cell-mass and propensity vectors,
but no transport weight and no arbitrary ambient extensions of those vectors. -/
structure RegularCellInput (𝒳 : Type*) [MeasurableSpace 𝒳]
    (N k : ℕ → ℕ) (n : ℕ) where
  sample : TwoSample 𝒳 n (N n)
  design : RegularCellDesign 𝒳 (k n)
  q : Fin (k n) → ℝ
    -- @realizes q_{x,n}(known source-cell array input)
  e : Fin (k n) → ℝ
    -- @realizes e(known cell-varying propensity input)

/-- Oracle confidence-set sequence with range and sample-by-parameter graph
measurability for every fixed ADMISSIBLE deterministic oracle input `(w,e)`,
i.e. every measurable pair.  The source supplies the oracle the model's own
density ratio and propensity, both measurable, so the measurability obligation
is imposed exactly on the inputs the source quantifies over; a nonmeasurable
`w` makes the sample-level score itself nonmeasurable, so demanding a
measurable graph there would be strictly stronger than the source and in
general unsatisfiable. -/
structure OracleProcedure (𝒳 : Type*) [MeasurableSpace 𝒳]
    (N k : ℕ → ℕ) (c epsilon : ℝ) where
  set : ∀ n, OracleInput 𝒳 N n → Set ℝ
    -- @realizes C_n(random subset of Theta)
  subset : ∀ n x, set n x ⊆ parameterSpace
    -- @realizes C_n(C_n⊆Theta)
  measurableGraph : ∀ n (w : NonnegativeWeight 𝒳) (e : 𝒳 → ℝ),
    Measurable w.1 → Measurable e →
    MeasurableSet {p : TwoSample 𝒳 n (N n) × ℝ |
      p.2 ∈ set n (p.1, w, e)}
    -- @realizes C_n(sample-by-theta measurable for each admissible oracle input)
  weightAEInvariant : ∀ n (P : TransportedArray 𝒳),
    TransportedIVClass P N k c epsilon n →
    ∀ w w' : TransportWeightVersion P n,
      ∀ᵐ s ∂twoSampleLaw P N n,
        set n (s, w.1, P.propensity n) =
          set n (s, w'.1, P.propensity n)
    -- @realizes C_n(law-indexed evaluation on the source-a.e. quotient of w)

/-- Sample-only finite-cell confidence-set sequence on the ambient carrier. -/
structure FiniteCellProcedure (𝒳 : Type*) [MeasurableSpace 𝒳]
    (N k : ℕ → ℕ) where
  set : ∀ n, FiniteCellInput 𝒳 N k n → Set ℝ
    -- @realizes C_n(sample-only finite-cell random set)
  subset : ∀ n x, set n x ⊆ parameterSpace
  measurableGraph : ∀ n (cell : Fin (k n) ↪ 𝒳), (∀ i, MeasurableSet {cell i}) →
    MeasurableSet {p : FiniteCellInput 𝒳 N k n × ℝ |
      ((∀ i, (p.1.1 i).1 ∈ Set.range cell) ∧ (∀ j, p.1.2 j ∈ Set.range cell)) ∧
        p.2 ∈ set n p.1}
    -- @realizes C_n(graph measurable on the realized finite-cell experiment)

/-- Finite-cell oracle procedures are global oracle procedures whose output on
the realized finite-cell experiment depends on the oracle weight and
propensity only through their values on the realized cells. -/
structure FiniteCellOracleProcedure (𝒳 : Type*) [MeasurableSpace 𝒳]
    (N k : ℕ → ℕ) (c epsilon : ℝ)
    extends OracleProcedure 𝒳 N k c epsilon where
  offCellInvariant : ∀ n (cell : Fin (k n) ↪ 𝒳)
      (w w' : NonnegativeWeight 𝒳) (e e' : 𝒳 → ℝ),
    (∀ i, w.1 (cell i) = w'.1 (cell i)) →
    (∀ i, e (cell i) = e' (cell i)) →
    ∀ s : TwoSample 𝒳 n (N n),
      ((∀ i, (s.1 i).1 ∈ Set.range cell) ∧
        (∀ j, s.2 j ∈ Set.range cell)) →
      set n (s, w, e) = set n (s, w', e')
    -- @realizes C_n(depends on w and e only through their realized cell vectors)

/-- Regular-cell confidence-set sequence structurally excluding `w`.  Its
known `q` and `e` inputs are finite vectors indexed by the bundled true
support, so there are no ambient off-support extensions to quotient out. -/
structure RegularCellProcedure (𝒳 : Type*) [MeasurableSpace 𝒳]
    (N k : ℕ → ℕ) where
  set : ∀ n, RegularCellInput 𝒳 N k n → Set ℝ
    -- @realizes C_n(regular-cell random set)
  subset : ∀ n x, set n x ⊆ parameterSpace
  measurableGraph : ∀ n (design : RegularCellDesign 𝒳 (k n))
      (q e : Fin (k n) → ℝ),
    MeasurableSet {p : TwoSample 𝒳 n (N n) × ℝ |
      ((∀ i, (p.1.1 i).1 ∈ Set.range design.cell) ∧
        (∀ j, p.1.2 j ∈ Set.range design.cell)) ∧
        p.2 ∈ set n ⟨p.1, design, q, e⟩}
    -- @realizes C_n(graph measurable on the realized regular-cell experiment)

/-- Lebesgue length restricted to the forced parameter interval. -/
noncomputable def setLength (A : Set ℝ) : ℝ :=
  (volume (A ∩ parameterSpace)).toReal

/-- Borel subsets of the forced parameter interval. -/
def BorelParameterSet :=
  {A : Set ℝ // MeasurableSet A ∧ A ⊆ parameterSpace}

/-- Lebesgue length on its exact paper domain and codomain. -/
noncomputable def paperSetLength (A : BorelParameterSet) : Set.Icc (0 : ℝ) 2 :=
  ⟨setLength A.1, ENNReal.toReal_nonneg, by
    unfold setLength parameterSpace
    calc
      (volume (A.1 ∩ Set.Icc (-1 : ℝ) 1)).toReal ≤
          (volume (Set.Icc (-1 : ℝ) 1)).toReal :=
        ENNReal.toReal_mono (by simp [Real.volume_Icc])
          (measure_mono Set.inter_subset_right)
      _ = 2 := by
        rw [Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num)]
        norm_num⟩
  -- @realizes \lambda(Lebesgue length on Borel subsets of Theta; codomain [0,2])

/-! ## Coverage and expected-length functionals -/

/-- Gives the confidence set produced by an oracle procedure from a two-sample dataset, the population transport weight, and the population propensity score. -/
noncomputable def oracleSet (C : OracleProcedure 𝒳 N k c epsilon)
    (P : TransportedArray 𝒳) (n : ℕ) (s : TwoSample 𝒳 n (N n)) : Set ℝ :=
  C.set n (s, transportWeightInput P n, P.propensity n)

/-- Auxiliary oracle evaluation at a declared measurable version in the model
row's density-ratio fiber.  Intrinsic procedure invariance identifies this
with the canonical paper-facing evaluation almost surely. -/
noncomputable def oracleSetAtWeight (C : OracleProcedure 𝒳 N k c epsilon)
    (P : TransportedArray 𝒳) (n : ℕ) (w : TransportWeightVersion P n)
    (s : TwoSample 𝒳 n (N n)) : Set ℝ :=
  C.set n (s, w.1, P.propensity n)

/-- Gives the probability that an oracle confidence set contains the target complier average causal effect. -/
noncomputable def oracleCoverage (C : OracleProcedure 𝒳 N k c epsilon)
    (P : TransportedArray 𝒳) (n : ℕ) : ℝ :=
  (twoSampleLaw P N n {s | targetCACE P n ∈ oracleSet C P n s}).toReal

/-- Gives the coverage probability of an oracle confidence set when evaluated with a specified admissible transport-weight version. -/
noncomputable def oracleCoverageAtWeight
    (C : OracleProcedure 𝒳 N k c epsilon)
    (P : TransportedArray 𝒳) (n : ℕ)
    (w : TransportWeightVersion P n) : ℝ :=
  (twoSampleLaw P N n
    {s | targetCACE P n ∈ oracleSetAtWeight C P n w s}).toReal

/-- The oracle procedure's expected confidence-set length under the two-sample law. -/
noncomputable def oracleExpectedLength
    (C : OracleProcedure 𝒳 N k c epsilon)
    (P : TransportedArray 𝒳) (n : ℕ) : ℝ :=
  ∫ s, setLength (oracleSet C P n s) ∂twoSampleLaw P N n

/-- The oracle procedure's expected confidence-set length when evaluated at a specified admissible transport-weight version. -/
noncomputable def oracleExpectedLengthAtWeight
    (C : OracleProcedure 𝒳 N k c epsilon)
    (P : TransportedArray 𝒳) (n : ℕ)
    (w : TransportWeightVersion P n) : ℝ :=
  ∫ s, setLength (oracleSetAtWeight C P n w s) ∂twoSampleLaw P N n

/-- A fixed-geometry oracle is evaluated with the geometry's chosen weight and
propensity versions, rather than the canonical `rnDeriv` representative
recovered from each law in the slice. -/
noncomputable def fixedGeometryOracleSet
    (C : OracleProcedure 𝒳 N k c epsilon)
    (g : Geometry 𝒳) (n : ℕ) (s : TwoSample 𝒳 n (N n)) : Set ℝ :=
  C.set n (s, geometryWeightInput g n, g.propensity n)

/-- Gives the coverage probability of an oracle confidence set under a fixed geometry and its declared weight and propensity functions. -/
noncomputable def fixedGeometryOracleCoverage
    (C : OracleProcedure 𝒳 N k c epsilon)
    (g : Geometry 𝒳) (P : TransportedArray 𝒳) (n : ℕ) : ℝ :=
  (twoSampleLaw P N n
    {s | targetCACE P n ∈ fixedGeometryOracleSet C g n s}).toReal

/-- Gives the expected length of an oracle confidence set under a fixed geometry and its declared weight and propensity functions. -/
noncomputable def fixedGeometryOracleExpectedLength
    (C : OracleProcedure 𝒳 N k c epsilon) (g : Geometry 𝒳)
    (P : TransportedArray 𝒳) (n : ℕ) : ℝ :=
  ∫ s, setLength (fixedGeometryOracleSet C g n s) ∂twoSampleLaw P N n

/-- The finite-cell procedure's coverage probability for the target CACE under the two-sample law. -/
noncomputable def finiteCellCoverage (C : FiniteCellProcedure 𝒳 N k)
    (n : ℕ) (P : TransportedArray 𝒳) : ℝ :=
  (twoSampleLaw P N n {s | targetCACE P n ∈ C.set n s}).toReal

/-- The finite-cell procedure's expected confidence-set length under the two-sample law. -/
noncomputable def finiteCellExpectedLength (C : FiniteCellProcedure 𝒳 N k)
    (n : ℕ) (P : TransportedArray 𝒳) : ℝ :=
  ∫ s, setLength (C.set n s) ∂twoSampleLaw P N n

/-- The confidence set produced by a finite-cell oracle procedure using the population transport weight and propensity. -/
noncomputable def finiteCellOracleSet
    (C : FiniteCellOracleProcedure 𝒳 N k c epsilon)
    (n : ℕ) (P : TransportedArray 𝒳)
    (s : TwoSample 𝒳 n (N n)) : Set ℝ :=
  C.set n (s, transportWeightInput P n, P.propensity n)

/-- The probability that a finite-cell oracle confidence set contains the target CACE. -/
noncomputable def finiteCellOracleCoverage
    (C : FiniteCellOracleProcedure 𝒳 N k c epsilon)
    (n : ℕ) (P : TransportedArray 𝒳) : ℝ :=
  (twoSampleLaw P N n
    {s | targetCACE P n ∈ finiteCellOracleSet C n P s}).toReal

/-- The expected length of a finite-cell oracle confidence set under the two-sample law. -/
noncomputable def finiteCellOracleExpectedLength
    (C : FiniteCellOracleProcedure 𝒳 N k c epsilon)
    (n : ℕ) (P : TransportedArray 𝒳) : ℝ :=
  ∫ s, setLength (finiteCellOracleSet C n P s) ∂twoSampleLaw P N n

/-- The known source-cell mass function. -/
noncomputable def sourceCellMass (P : TransportedArray 𝒳) (n : ℕ) : 𝒳 → ℝ :=
  fun x => (sourceXLaw P n {x}).toReal
  -- @realizes q_{x,n}(P_S^X{X=x})

/-- A regular-class witness packaged as the true support supplied to the
procedure. -/
noncomputable def regularCellDesignOfClass
    (P : TransportedArray 𝒳)
    (hP : RegularFiniteCellClass P N k c epsilon cminus cplus n) :
    RegularCellDesign 𝒳 (k n) := by
  classical
  let hw := hP.2.2.2.2.2
  exact ⟨Classical.choose hw, (Classical.choose_spec hw).1⟩

/-- Extend a finite cell vector only for reuse by ambient-function estimator
helpers.  Procedure inputs expose the finite vector itself, never this
arbitrary zero extension. -/
noncomputable def cellVectorExtension (design : RegularCellDesign 𝒳 m)
    (v : Fin m → ℝ) : 𝒳 → ℝ := by
  classical
  exact fun x => if h : ∃ i, design.cell i = x then v (Classical.choose h) else 0

/-- Constructs the regular-cell procedure input from a model in the regular finite-cell class and a two-sample dataset, including the class-supplied cell design, source-cell masses, and propensity scores. -/
noncomputable def regularCellInputOfClass
    (P : TransportedArray 𝒳)
    (hP : RegularFiniteCellClass P N k c epsilon cminus cplus n)
    (s : TwoSample 𝒳 n (N n)) : RegularCellInput 𝒳 N k n :=
  let design := regularCellDesignOfClass P hP
  ⟨s, design,
    fun i => sourceCellMass P n (design.cell i),
    fun i => P.propensity n (design.cell i)⟩

/-- The confidence set produced by a regular-cell procedure from a sample and the class-supplied cell design. -/
noncomputable def regularCellSet (C : RegularCellProcedure 𝒳 N k)
    (n : ℕ) (P : TransportedArray 𝒳)
    (hP : RegularFiniteCellClass P N k c epsilon cminus cplus n)
    (s : TwoSample 𝒳 n (N n)) : Set ℝ :=
  C.set n (regularCellInputOfClass P hP s)

/-- The probability that a regular-cell confidence set contains the target CACE over a regular finite-cell model. -/
noncomputable def regularCellCoverage (C : RegularCellProcedure 𝒳 N k)
    (n : ℕ)
    (P : {P : TransportedArray 𝒳 //
      RegularFiniteCellClass P N k c epsilon cminus cplus n}) : ℝ :=
  (twoSampleLaw P.1 N n
    {s | targetCACE P.1 n ∈ regularCellSet C n P.1 P.2 s}).toReal

/-- The expected length of a regular-cell confidence set under the corresponding two-sample law. -/
noncomputable def regularCellExpectedLength (C : RegularCellProcedure 𝒳 N k)
    (n : ℕ)
    (P : {P : TransportedArray 𝒳 //
      RegularFiniteCellClass P N k c epsilon cminus cplus n}) : ℝ :=
  ∫ s, setLength (regularCellSet C n P.1 P.2 s) ∂twoSampleLaw P.1 N n

/-! ## Honesty classes -/

-- @env: S5
variable (N k : ℕ → ℕ) (c epsilon alpha : ℝ)
  -- @realizes \mathcal P_n(main model class parameters)
  -- @realizes \mathcal N_n(finite-cell class parameters)
  -- @realizes \alpha(noncoverage level)

/-- The infimum of rowwise coverage, with the vacuous value one on an empty
model row. Coverage takes values in [0,1], so this is the bounded
paper-facing counterpart of the mathematical convention inf empty = +infinity. -/
noncomputable abbrev coverageInfOrOne {ι : Sort*} (f : ι → ℝ) : ℝ :=
  Causalean.Stat.coverageInfOrOne f

/-- Rowwise worst-case coverage indexed exactly by model rows.  The canonical
input represents the row's source-a.e. quotient, by intrinsic procedure
invariance. -/
noncomputable def oracleCoverageClassInf
    (C : OracleProcedure 𝒳 N k c epsilon)
    (n : ℕ) : ℝ :=
  coverageInfOrOne fun P : {P : TransportedArray 𝒳 //
      TransportedIVClass P N k c epsilon n} =>
    oracleCoverage C P.1 n

-- @node: def:oracle-honesty
/-- Oracle procedures have asymptotic uniform coverage over the main class;
their structure makes evaluation well-defined on the law-indexed source-a.e.
quotient of the declared density-ratio input. -/
noncomputable def OracleHonest
    (C : OracleProcedure 𝒳 N k c epsilon) : Prop :=
  0 < alpha ∧ alpha < 1 ∧ -- @realizes \alpha(noncoverage level in (0,1))
  1 - alpha ≤ Filter.liminf
    (oracleCoverageClassInf N k c epsilon C) atTop
  -- @realizes \mathfrak C^{\mathrm{or}}(oracle-honest procedure class)

-- @node: def:finite-cell-feasible-honesty
/-- Sample-only procedures have asymptotic uniform coverage over the finite-cell
subclass. -/
noncomputable def FiniteCellHonest
    (C : FiniteCellProcedure 𝒳 N k) : Prop :=
  0 < alpha ∧ alpha < 1 ∧ -- @realizes \alpha(noncoverage level in (0,1))
  1 - alpha ≤ Filter.liminf
    (fun n => coverageInfOrOne fun P : {P : TransportedArray 𝒳 //
        FiniteCellClass P N k c epsilon n} =>
      finiteCellCoverage C n P) atTop
  -- @realizes \mathfrak C^{\mathrm{cell}}(weight-unknown finite-cell procedures)

/-- Oracle procedures are honest over the full transported-IV class on the
same carrier; the risk may subsequently be restricted to cells. -/
noncomputable def FiniteCellOracleHonest
    (C : FiniteCellOracleProcedure 𝒳 N k c epsilon) : Prop :=
  OracleHonest (𝒳 := 𝒳) N k c epsilon alpha C.toOracleProcedure

-- @node: def:fixed-geometry-honesty
/-- Oracle procedures honest uniformly over a fixed geometry slice. -/
noncomputable def FixedGeometryOracleHonest
    (g : {g : Geometry 𝒳 // AdmissibleGeometry g k epsilon})
    (C : OracleProcedure 𝒳 N k c epsilon) : Prop :=
  0 < alpha ∧ alpha < 1 ∧ -- @realizes \alpha(noncoverage level in (0,1))
  1 - alpha ≤ Filter.liminf
    (fun n => coverageInfOrOne fun P : {P : TransportedArray 𝒳 //
        fixedGeometrySlice P g.1 N k c epsilon n} =>
      fixedGeometryOracleCoverage C g.1 P n) atTop
  -- @realizes \mathfrak C^{\mathrm{or}}(\mathfrak g)(slice-honest oracle class)

-- @node: def:regular-cell-feasible-honesty
/-- Procedures using known source-cell masses and propensity, but not `w`, are
honest over the regular finite-cell class. -/
noncomputable def RegularCellHonest (cminus cplus : ℝ)
    (C : RegularCellProcedure 𝒳 N k) : Prop :=
  0 < alpha ∧ alpha < 1 ∧ -- @realizes \alpha(noncoverage level in (0,1))
  1 - alpha ≤ Filter.liminf
    (fun n => coverageInfOrOne fun P : {P : TransportedArray 𝒳 //
        RegularFiniteCellClass P N k c epsilon cminus cplus n} =>
      regularCellCoverage (c := c) (epsilon := epsilon)
        (cminus := cminus) (cplus := cplus) C n P) atTop
  -- @realizes \mathfrak C^{\mathrm{reg}}(regular-cell weight-unknown procedures)

/-! ## Risk and minimax values -/

/-- Positive frontier thresholds, the exact paper domain of every tagged risk
and minimax value function. -/
def PositiveThreshold := {t0 : ℝ // 0 < t0}

/-- Rowwise global oracle risk over exactly the model rows satisfying the
strength restriction.  There is no additional weight-version supremum. -/
noncomputable def frontierRiskRow
    (C : OracleProcedure 𝒳 N k c epsilon)
    (t0 : ℝ) (n : ℕ) : ℝ :=
  ⨆ P : {P : TransportedArray 𝒳 //
      TransportedIVClass P N k c epsilon n ∧
        t0 ≤ effectiveStrength P n},
    oracleExpectedLength C P.1 n

/-- The corresponding rowwise risk restricted to the finite-cell submodel. -/
noncomputable def finiteCellOracleRiskRow
    (C : OracleProcedure 𝒳 N k c epsilon)
    (t0 : ℝ) (n : ℕ) : ℝ :=
  ⨆ P : {P : TransportedArray 𝒳 //
      FiniteCellClass P N k c epsilon n ∧
        t0 ≤ effectiveStrength P n},
    oracleExpectedLength C P.1 n

/-- Total computational risk at an arbitrary real threshold. -/
noncomputable def frontierRiskTotal
    (C : OracleProcedure 𝒳 N k c epsilon) (t0 : ℝ) : ℝ :=
  Filter.limsup (frontierRiskRow N k c epsilon C t0) atTop

-- @node: def:frontier-risk
/-- Paper-facing risk on the declared positive threshold domain. -/
noncomputable def frontierRisk
    (C : OracleProcedure 𝒳 N k c epsilon)
    (t0 : PositiveThreshold) : ℝ :=
  frontierRiskTotal N k c epsilon C t0.1
  -- @realizes R(limsup_n sup_{P∈P_n:t_n≥t_0} E[lambda(C_n)])

/-- Gives the limiting worst-case expected length of an oracle procedure over finite-cell model rows whose effective strength meets the supplied threshold. -/
noncomputable def finiteCellOracleRisk
    (C : OracleProcedure 𝒳 N k c epsilon)
    (t0 : ℝ) : ℝ :=
  Filter.limsup (finiteCellOracleRiskRow N k c epsilon C t0) atTop

/-- Gives the limiting worst-case expected length of an oracle procedure over model rows in a fixed geometry whose effective strength meets the supplied threshold. -/
noncomputable def fixedGeometryRisk (g : Geometry 𝒳)
    (C : OracleProcedure 𝒳 N k c epsilon) (t0 : ℝ) : ℝ :=
  Filter.limsup
    (fun n => ⨆ P : {P : TransportedArray 𝒳 //
        fixedGeometrySlice P g N k c epsilon n ∧
          t0 ≤ effectiveStrength P n},
      fixedGeometryOracleExpectedLength C g P n) atTop

/-- The asymptotic worst-case expected length of a regular-cell procedure over regular finite-cell models whose effective strength exceeds a given threshold. -/
noncomputable def regularCellRisk (cminus cplus : ℝ)
    (C : RegularCellProcedure 𝒳 N k) (t0 : ℝ) : ℝ :=
  Filter.limsup
    (fun n => ⨆ P : {P : TransportedArray 𝒳 //
        RegularFiniteCellClass P N k c epsilon cminus cplus n ∧
          t0 ≤ effectiveStrength P n},
      regularCellExpectedLength (c := c) (epsilon := epsilon)
        (cminus := cminus) (cplus := cplus) C n ⟨P.1, P.2.1⟩) atTop

/-- The asymptotic worst-case expected length of a finite-cell procedure over finite-cell models whose effective strength exceeds a given threshold. -/
noncomputable def feasibleFiniteCellRisk
    (C : FiniteCellProcedure 𝒳 N k)
    (t0 : ℝ) : ℝ :=
  Filter.limsup
    (fun n => ⨆ P : {P : TransportedArray 𝒳 //
        FiniteCellClass P N k c epsilon n ∧
          t0 ≤ effectiveStrength P n},
      finiteCellExpectedLength C n P) atTop

/-- Total computational helper underlying the paper-facing oracle value. -/
noncomputable def oracleValueTotal (t0 : ℝ) : ℝ :=
  ⨅ C : {C : OracleProcedure 𝒳 N k c epsilon //
      OracleHonest N k c epsilon alpha C},
    frontierRiskTotal N k c epsilon C.1 t0

-- @node: def:oracle-value
/-- Oracle minimax expected-length frontier on its declared positive domain. -/
noncomputable def oracleValue (t0 : PositiveThreshold) : ℝ :=
  oracleValueTotal (𝒳 := 𝒳) N k c epsilon alpha t0.1
  -- @realizes V^\star(oracle minimax frontier on t_0>0)

/- The global oracle-honest procedure class, with risk restricted to the
growing finite-cell submodel.  This total helper is untagged. -/
/-- Gives the smallest limiting worst-case expected length attainable by an oracle-honest procedure over finite-cell models at the supplied strength threshold. -/
noncomputable def finiteCellOracleValueTotal (t0 : ℝ) : ℝ :=
  ⨅ C : {C : OracleProcedure 𝒳 N k c epsilon //
      OracleHonest N k c epsilon alpha C},
    finiteCellOracleRisk N k c epsilon C.1 t0

-- @node: def:finite-cell-oracle-value
/-- The global oracle-honest procedure class, with risk restricted to the
growing finite-cell submodel, on the declared positive threshold domain. -/
noncomputable def finiteCellOracleValue (t0 : PositiveThreshold) : ℝ :=
  finiteCellOracleValueTotal (𝒳 := 𝒳) N k c epsilon alpha t0.1
  -- @realizes V_{\mathcal N}^\star(finite-cell oracle minimax frontier on t_0>0)

/-- Total computational helper underlying the fixed-geometry value. -/
noncomputable def fixedGeometryValueTotal
    (g : {g : Geometry 𝒳 // AdmissibleGeometry g k epsilon})
    (t0 : ℝ) : ℝ :=
  ⨅ C : {C : OracleProcedure 𝒳 N k c epsilon //
      FixedGeometryOracleHonest N k c epsilon alpha g C},
    fixedGeometryRisk N k c epsilon g.1 C.1 t0

-- @node: def:fixed-geometry-value
/-- Conditional minimax frontier at an admissible deterministic geometry, on the
declared positive threshold domain. -/
noncomputable def fixedGeometryValue
    (g : {g : Geometry 𝒳 // AdmissibleGeometry g k epsilon})
    (t0 : PositiveThreshold) : ℝ :=
  fixedGeometryValueTotal N k c epsilon alpha g t0.1
  -- @realizes V_{\mathfrak g}^\star(fixed-geometry minimax frontier on t_0>0)

end CausalSmith.Stat.TransportedLateStrengthFrontier
