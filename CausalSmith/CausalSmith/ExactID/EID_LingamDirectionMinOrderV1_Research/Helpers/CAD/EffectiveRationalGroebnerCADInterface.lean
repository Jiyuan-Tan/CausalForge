/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Effective rational Gröbner elimination and cylindrical algebraic decomposition

This file states the effective Gröbner interface over `ℚ` and `ℚ(i)`, together with its effective
rational real-CAD specialization.  The rational result includes the algebraically closed Closure
Theorem: after extension to `ℂ`, its elimination basis cuts out exactly the Zariski closure of the
corresponding coordinate projection.  Its declarations are independent of every later
specialization.
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.CAD.CADInterface
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Rat.Encodable
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.Tactic.DeriveEncodable

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

noncomputable section

open scoped BigOperators

/-- Provides a procedure that decides whether two values of this data type are equal. -/
local instance rationalPolynomialDecidableEq (r : ℕ) :
    DecidableEq (MvPolynomial (Fin r) ℚ) := Classical.decEq _

/-- Provides a procedure that decides whether two values of this data type are equal. -/
local instance realPolynomialDecidableEq (r : ℕ) :
    DecidableEq (MvPolynomial (Fin r) ℝ) := Classical.decEq _

/-- Finite rational syntax for a multivariate polynomial. -/
structure EffectivePolynomialCode (r : ℕ) where
  terms : List (ℚ × List (Fin r × ℕ))
  deriving Encodable

/-- Interpretation of rational polynomial syntax. -/
def EffectivePolynomialCode.toPolynomial {r : ℕ} (code : EffectivePolynomialCode r) :
    MvPolynomial (Fin r) ℚ :=
  code.terms.foldl (fun P term =>
    P + MvPolynomial.monomial
      (term.2.foldl (fun exponents xe => exponents + Finsupp.single xe.1 xe.2) 0)
      term.1) 0

/-- Canonical code for the zero polynomial. -/
def effectiveZeroPolynomialCode (r : ℕ) : EffectivePolynomialCode r :=
  ⟨[]⟩

/-- Canonical code for the constant polynomial one. -/
def effectiveOnePolynomialCode (r : ℕ) : EffectivePolynomialCode r :=
  ⟨[(1, [])]⟩

/-- Canonical code for one coordinate variable. -/
def effectiveVariablePolynomialCode {r : ℕ} (i : Fin r) : EffectivePolynomialCode r :=
  ⟨[(1, [(i, 1)])]⟩

/-- The fixed finite machine substrate containing `0`, `1`, and every coordinate variable.
These codes are available to primitive arithmetic, but are not registered as algorithm input
families. -/
def effectiveCanonicalPolynomialPool (r : ℕ) : List (EffectivePolynomialCode r) :=
  effectiveZeroPolynomialCode r :: effectiveOnePolynomialCode r ::
    List.ofFn effectiveVariablePolynomialCode

@[simp] theorem effectiveZeroPolynomialCode_toPolynomial (r : ℕ) :
    (effectiveZeroPolynomialCode r).toPolynomial = 0 := by
  simp [effectiveZeroPolynomialCode, EffectivePolynomialCode.toPolynomial]

@[simp] theorem effectiveOnePolynomialCode_toPolynomial (r : ℕ) :
    (effectiveOnePolynomialCode r).toPolynomial = 1 := by
  simp [effectiveOnePolynomialCode, EffectivePolynomialCode.toPolynomial]

@[simp] theorem effectiveVariablePolynomialCode_toPolynomial {r : ℕ} (i : Fin r) :
    (effectiveVariablePolynomialCode i).toPolynomial = MvPolynomial.X i := by
  simp [effectiveVariablePolynomialCode, EffectivePolynomialCode.toPolynomial,
    MvPolynomial.X]

/-- A displayed list of rational codes realizes exactly a finite polynomial family. -/
def EffectivePolynomialCodesRealize {r : ℕ} (codes : List (EffectivePolynomialCode r))
    (family : Finset (MvPolynomial (Fin r) ℚ)) : Prop :=
  codes.Nodup ∧ (codes.map EffectivePolynomialCode.toPolynomial).toFinset = family

/-- The Gaussian rational field `ℚ(i)`, presented by the relation `i² = -1`. -/
abbrev GaussianRational := QuadraticAlgebra ℚ (-1) 0

local instance gaussianRationalIrreducible :
    Fact (∀ q : ℚ, q ^ 2 ≠ (-1 : ℚ) + 0 * q) := by
  constructor
  intro q hq
  have hq' : q ^ 2 = (-1 : ℚ) := by simpa using hq
  have hnonneg : 0 ≤ q ^ 2 := sq_nonneg q
  rw [hq'] at hnonneg
  exact (not_le_of_gt neg_one_lt_zero) hnonneg

noncomputable local instance gaussianRationalEncodable : Encodable GaussianRational :=
  Encodable.ofEquiv (ℚ × ℚ) (QuadraticAlgebra.equivProd (-1) 0)

/-- Finite syntax for a polynomial over an arbitrary encodable coefficient field. This is used
only by the paper-independent Gröbner interface; the real CAD specialization below remains over
`ℚ`, as required by the cited algorithms. -/
structure EffectivePolynomialCodeOver (K : Type) (r : ℕ) where
  terms : List (K × List (Fin r × ℕ))
  deriving Encodable

/-- Interpretation of finite polynomial syntax over its coefficient field. -/
def EffectivePolynomialCodeOver.toPolynomial {K : Type} [Field K] {r : ℕ}
    (code : EffectivePolynomialCodeOver K r) : MvPolynomial (Fin r) K :=
  code.terms.foldl (fun P term =>
    P + MvPolynomial.monomial
      (term.2.foldl (fun exponents xe => exponents + Finsupp.single xe.1 xe.2) 0)
      term.1) 0

/-- A displayed list of coefficient-field codes realizes exactly a finite polynomial family. -/
def EffectivePolynomialCodesRealizeOver {K : Type} [Field K] [DecidableEq K] {r : ℕ}
    (codes : List (EffectivePolynomialCodeOver K r))
    (family : Finset (MvPolynomial (Fin r) K)) : Prop :=
  codes.Nodup ∧
    (codes.map EffectivePolynomialCodeOver.toPolynomial).toFinset = family

/-- A finite, machine-readable presentation of a supplied semantic monomial order. The comparison
program is part of the input to the uniform Buchberger machine; `Realizes` below prevents an
arbitrary code from being passed off as the requested order. -/
structure EffectiveMonomialOrderCode (r : ℕ) where
  comparison : Nat.Partrec.Code
  deriving Encodable

/-- Exact total comparison semantics for a finite presentation of a monomial order. Terminating
comparison is required on every pair of exponents, and the Boolean answer is exactly strict
comparison in the supplied admissible Mathlib `MonomialOrder`. -/
def EffectiveMonomialOrderCode.Realizes {r : ℕ} (code : EffectiveMonomialOrderCode r)
    (monomialOrder : MonomialOrder.{0, 0} (Fin r)) : Prop :=
  ∀ left right : Fin r →₀ ℕ, ∃ fuel : ℕ,
    code.comparison.evaln fuel (Encodable.encode (left, right)) =
      some (Encodable.encode (decide
        (monomialOrder.toSyn left < monomialOrder.toSyn right)))

/-- A polynomial over `K` uses only the retained variables of an elimination block. -/
def UsesOnlyEffectiveVariablesOver {K : Type} [Field K] {r : ℕ}
    (keep : Finset (Fin r)) (P : MvPolynomial (Fin r) K) : Prop :=
  P.vars ⊆ keep

/-- An admissible monomial order is an elimination order for `keep` when every monomial using an
eliminated variable is strictly larger than every monomial supported on `keep`. This is a
condition on the supplied order, not a claim that every `MonomialOrder` is an elimination order. -/
def IsEffectiveEliminationMonomialOrder {r : ℕ}
    (monomialOrder : MonomialOrder.{0, 0} (Fin r)) (keep : Finset (Fin r)) : Prop :=
  ∀ eliminated retained : Fin r →₀ ℕ,
    retained.support ⊆ keep → ¬eliminated.support ⊆ keep →
      monomialOrder.toSyn retained < monomialOrder.toSyn eliminated

/-- The standard finite block-elimination order is effectively presentable for
every concrete retained coordinate block.  This is an existence statement for
the cited construction's canonical block order, not the false assertion that
every abstract `MonomialOrder` is effectively presentable. -/
def StandardFiniteBlockEliminationOrderInterface : Prop :=
  ∀ (r : ℕ) (keep : Finset (Fin r)),
    ∃ monomialOrder : MonomialOrder.{0, 0} (Fin r),
      ∃ suppliedOrder : EffectiveMonomialOrderCode r,
        suppliedOrder.Realizes monomialOrder ∧
          IsEffectiveEliminationMonomialOrder monomialOrder keep

/-- Exact Gröbner-basis semantics for an arbitrary admissible monomial order. Mathlib's
`MonomialOrder` already packages well-foundedness, compatibility with addition, and `0` as the
least monomial, so no lexicographic restriction is hidden in this interface. -/
def IsExactGroebnerBasisForMonomialOrder {K : Type} [Field K] [DecidableEq K] {r : ℕ}
    (monomialOrder : MonomialOrder.{0, 0} (Fin r))
    (input basis : Finset (MvPolynomial (Fin r) K))
    (normalForm : MvPolynomial (Fin r) K → MvPolynomial (Fin r) K) : Prop :=
  (∀ G ∈ basis, G ≠ 0) ∧
    Ideal.span (input : Set (MvPolynomial (Fin r) K)) =
      Ideal.span (basis : Set (MvPolynomial (Fin r) K)) ∧
    (∀ P ∈ Ideal.span (input : Set (MvPolynomial (Fin r) K)), P ≠ 0 →
      ∃ G ∈ basis, G ≠ 0 ∧ monomialOrder.degree G ≤ monomialOrder.degree P) ∧
    ∀ P,
      (normalForm P = 0 ↔ P ∈ Ideal.span (input : Set (MvPolynomial (Fin r) K))) ∧
      ∃ quotients : basis → MvPolynomial (Fin r) K,
        P = normalForm P + ∑ Q : basis, quotients Q * Q.1 ∧
          ∀ exponent ∈ (normalForm P).support, ∀ G ∈ basis,
            ¬monomialOrder.degree G ≤ exponent

/-- Exact elimination-ideal output over an arbitrary coefficient field. Its use with the
Gröbner output below is conditional on the supplied monomial order satisfying
`IsEffectiveEliminationMonomialOrder`. -/
def IsExactEliminationBasisOver {K : Type} [Field K] [DecidableEq K] {r : ℕ}
    (input : Finset (MvPolynomial (Fin r) K)) (keep : Finset (Fin r))
    (output : Finset (MvPolynomial (Fin r) K)) : Prop :=
  (∀ P ∈ output, UsesOnlyEffectiveVariablesOver keep P) ∧
    ∀ P, UsesOnlyEffectiveVariablesOver keep P →
      (P ∈ Ideal.span (output : Set (MvPolynomial (Fin r) K)) ↔
        P ∈ Ideal.span (input : Set (MvPolynomial (Fin r) K)))

/-- Exact ideal-intersection output over an arbitrary coefficient field. -/
def IsExactIdealIntersectionBasisOver {K : Type} [Field K] [DecidableEq K] {r : ℕ}
    (left right output : Finset (MvPolynomial (Fin r) K)) : Prop :=
  Ideal.span (output : Set (MvPolynomial (Fin r) K)) =
    Ideal.span (left : Set (MvPolynomial (Fin r) K)) ⊓
      Ideal.span (right : Set (MvPolynomial (Fin r) K))

/-- Exact saturation output over an arbitrary coefficient field, characterized by membership
after multiplication by a power of the saturating polynomial. -/
def IsExactSaturationBasisOver {K : Type} [Field K] [DecidableEq K] {r : ℕ}
    (input : Finset (MvPolynomial (Fin r) K))
    (saturating : MvPolynomial (Fin r) K)
    (output : Finset (MvPolynomial (Fin r) K)) : Prop :=
  ∀ P, P ∈ Ideal.span (output : Set (MvPolynomial (Fin r) K)) ↔
    ∃ k : ℕ, saturating ^ k * P ∈ Ideal.span (input : Set (MvPolynomial (Fin r) K))

/-- High-level stages in a coefficient-polymorphic exact algebra trace. -/
inductive EffectiveGroebnerTraceOperation
  | buchberger
  | elimination
  | idealIntersection
  | saturation
  deriving DecidableEq, Encodable

/-- Primitive charged field operations used by the exact algebra trace. -/
inductive EffectiveGroebnerPrimitiveOperation
  | coefficientAddition
  | coefficientMultiplication
  | coefficientInversion
  deriving DecidableEq, Encodable

/-- One state of a continuous coefficient-polymorphic symbolic execution. -/
structure EffectiveGroebnerMachineState (K : Type) (r : ℕ) where
  polynomialPool : List (EffectivePolynomialCodeOver K r)
  familyRegisters : List (List (EffectivePolynomialCodeOver K r))

/-- Extensional availability of a coefficient-field polynomial code in the
computed pool. -/
def EffectivePolynomialCodeOver.AvailableIn {K : Type} [Field K] {r : ℕ}
    (required : EffectivePolynomialCodeOver K r)
    (pool : List (EffectivePolynomialCodeOver K r)) : Prop :=
  ∃ computed ∈ pool, computed.toPolynomial = required.toPolynomial

/-- Exact transition semantics for one charged field operation. -/
def EffectiveGroebnerPrimitiveTransition {K : Type} [Field K] {r : ℕ} :
    EffectiveGroebnerPrimitiveOperation → EffectiveGroebnerMachineState K r →
      EffectiveGroebnerMachineState K r → Prop
  | .coefficientAddition, before, after =>
      ∃ left ∈ before.polynomialPool, ∃ right ∈ before.polynomialPool, ∃ result,
        result.toPolynomial = left.toPolynomial + right.toPolynomial ∧
          after = { before with polynomialPool := before.polynomialPool ++ [result] }
  | .coefficientMultiplication, before, after =>
      ∃ left ∈ before.polynomialPool, ∃ right ∈ before.polynomialPool, ∃ result,
        result.toPolynomial = left.toPolynomial * right.toPolynomial ∧
          after = { before with polynomialPool := before.polynomialPool ++ [result] }
  | .coefficientInversion, before, after =>
      ∃ source ∈ before.polynomialPool, ∃ exponent,
        source.toPolynomial.coeff exponent ≠ 0 ∧ ∃ result,
        result.toPolynomial =
            MvPolynomial.C (source.toPolynomial.coeff exponent)⁻¹ * source.toPolynomial ∧
          after = { before with polynomialPool := before.polynomialPool ++ [result] }

/-- Continuous execution of a list of charged coefficient-field operations. -/
def EffectiveGroebnerPrimitiveProgramRuns {K : Type} [Field K] {r : ℕ} :
    List EffectiveGroebnerPrimitiveOperation → EffectiveGroebnerMachineState K r →
      EffectiveGroebnerMachineState K r → Prop
  | [], initial, final => final = initial
  | operation :: operations, initial, final =>
      ∃ next, EffectiveGroebnerPrimitiveTransition operation initial next ∧
        EffectiveGroebnerPrimitiveProgramRuns operations next final

/-- One supplied-input high-level algebra step and its exact charged primitive
program. -/
structure EffectiveGroebnerTraceStep (K : Type) (r : ℕ) where
  operation : EffectiveGroebnerTraceOperation
  inputFamilies : List (List (EffectivePolynomialCodeOver K r))
  outputFamilies : List (List (EffectivePolynomialCodeOver K r))
  primitiveOperations : List EffectiveGroebnerPrimitiveOperation
  deriving Encodable

/-- Exact operation count of a coefficient-polymorphic trace step. -/
def EffectiveGroebnerTraceStep.operationCount {K : Type} {r : ℕ}
    (step : EffectiveGroebnerTraceStep K r) : ℕ :=
  step.primitiveOperations.length

/-- Extensional availability of a displayed family register. -/
def EffectiveGroebnerFamilyAvailable {K : Type} [Field K] [DecidableEq K] {r : ℕ}
    (required : List (EffectivePolynomialCodeOver K r))
    (registers : List (List (EffectivePolynomialCodeOver K r))) : Prop :=
  ∃ registered ∈ registers,
    (registered.map EffectivePolynomialCodeOver.toPolynomial).toFinset =
      (required.map EffectivePolynomialCodeOver.toPolynomial).toFinset

/-- A high-level algebra step consumes only registered families and computes
every displayed output during this step's charged suffix, before registering
those outputs for later steps. -/
def EffectiveGroebnerTraceStep.Runs {K : Type} [Field K] [DecidableEq K] {r : ℕ}
    (step : EffectiveGroebnerTraceStep K r)
    (before after : EffectiveGroebnerMachineState K r) : Prop :=
  (∀ family ∈ step.inputFamilies,
      EffectiveGroebnerFamilyAvailable family before.familyRegisters) ∧
    ∃ primitiveFinal,
      EffectiveGroebnerPrimitiveProgramRuns step.primitiveOperations before primitiveFinal ∧
      (∀ output ∈ step.outputFamilies.flatten,
        output.AvailableIn
          (primitiveFinal.polynomialPool.drop before.polynomialPool.length)) ∧
      after = { primitiveFinal with
        familyRegisters := before.familyRegisters ++ step.outputFamilies }

/-- The complete coefficient-polymorphic trace is one continuous execution;
no step is reset with a fresh polynomial pool. -/
def EffectiveGroebnerTraceRuns {K : Type} [Field K] [DecidableEq K] {r : ℕ} :
    List (EffectiveGroebnerTraceStep K r) → EffectiveGroebnerMachineState K r →
      EffectiveGroebnerMachineState K r → Prop
  | [], initial, final => final = initial
  | step :: steps, initial, final =>
      ∃ next, step.Runs initial next ∧ EffectiveGroebnerTraceRuns steps next final

/-- Canonical zero, one, negative one, and coordinate-variable codes available before every
coefficient-polymorphic algebra run.  The `-1` code makes exact negation and subtraction
expressible by the charged multiplication transition. -/
def effectiveGroebnerCanonicalPolynomialPool (K : Type) [Field K] (r : ℕ) :
    List (EffectivePolynomialCodeOver K r) :=
  ⟨[]⟩ :: ⟨[(1, [])]⟩ :: ⟨[(-1, [])]⟩ ::
    List.ofFn fun i : Fin r => ⟨[(1, [(i, 1)])]⟩

/-- Finite machine output for one Gröbner computation over an encodable coefficient field. Its
input presentation fields are required below to equal the presentations supplied before the
output existential. -/
structure EffectiveGroebnerPayloadOver (K : Type) (r : ℕ) where
  input : List (EffectivePolynomialCodeOver K r)
  secondInput : List (EffectivePolynomialCodeOver K r)
  saturatingPolynomial : EffectivePolynomialCodeOver K r
  groebnerBasis : List (EffectivePolynomialCodeOver K r)
  eliminationBasis : List (EffectivePolynomialCodeOver K r)
  intersectionBasis : List (EffectivePolynomialCodeOver K r)
  saturationBasis : List (EffectivePolynomialCodeOver K r)
  saturatedGroebnerBasis : List (EffectivePolynomialCodeOver K r)
  saturatedEliminationBasis : List (EffectivePolynomialCodeOver K r)
  trace : List (EffectiveGroebnerTraceStep K r)
  deriving Encodable

/-- The exact charged operation count is definitionally the length sum of the
continuous coefficient-polymorphic execution. -/
def EffectiveGroebnerPayloadOver.symbolicOperationCount {K : Type} {r : ℕ}
    (payload : EffectiveGroebnerPayloadOver K r) : ℕ :=
  (payload.trace.map EffectiveGroebnerTraceStep.operationCount).sum

/-- A terminating exact Gröbner/elimination/intersection/saturation computation for one supplied
finite presentation and one effectively supplied admissible monomial order. -/
structure EffectiveGroebnerResultOver {K : Type} [Field K] [DecidableEq K] [Encodable K]
    {r : ℕ} (input secondInput : Finset (MvPolynomial (Fin r) K))
    (monomialOrder : MonomialOrder.{0, 0} (Fin r)) (keep : Finset (Fin r))
    (saturating : MvPolynomial (Fin r) K)
    (suppliedInput suppliedSecondInput : List (EffectivePolynomialCodeOver K r))
    (suppliedSaturating : EffectivePolynomialCodeOver K r)
    (suppliedOrder : EffectiveMonomialOrderCode r)
    (suppliedRetainedVariables : List (Fin r)) where
  groebnerBasis : Finset (MvPolynomial (Fin r) K)
  eliminationBasis : Finset (MvPolynomial (Fin r) K)
  intersectionBasis : Finset (MvPolynomial (Fin r) K)
  saturationBasis : Finset (MvPolynomial (Fin r) K)
  saturatedGroebnerBasis : Finset (MvPolynomial (Fin r) K)
  saturatedEliminationBasis : Finset (MvPolynomial (Fin r) K)
  normalForm : MvPolynomial (Fin r) K → MvPolynomial (Fin r) K
  saturatedNormalForm : MvPolynomial (Fin r) K → MvPolynomial (Fin r) K
  groebner_exact :
    IsExactGroebnerBasisForMonomialOrder monomialOrder input groebnerBasis normalForm
  elimination_exact : IsEffectiveEliminationMonomialOrder monomialOrder keep →
    IsExactEliminationBasisOver input keep eliminationBasis
  intersection_exact :
    IsExactIdealIntersectionBasisOver input secondInput intersectionBasis
  saturation_exact : IsExactSaturationBasisOver input saturating saturationBasis
  saturated_groebner_exact :
    IsExactGroebnerBasisForMonomialOrder monomialOrder saturationBasis
      saturatedGroebnerBasis saturatedNormalForm
  saturated_elimination_exact : IsEffectiveEliminationMonomialOrder monomialOrder keep →
    IsExactEliminationBasisOver saturationBasis keep saturatedEliminationBasis
  payload : EffectiveGroebnerPayloadOver K r
  payload_uses_supplied_input : payload.input = suppliedInput
  payload_uses_supplied_second_input : payload.secondInput = suppliedSecondInput
  payload_uses_supplied_saturating : payload.saturatingPolynomial = suppliedSaturating
  encoded_input : EffectivePolynomialCodesRealizeOver payload.input input
  encoded_second_input : EffectivePolynomialCodesRealizeOver payload.secondInput secondInput
  encoded_saturating : payload.saturatingPolynomial.toPolynomial = saturating
  encoded_groebner : EffectivePolynomialCodesRealizeOver payload.groebnerBasis groebnerBasis
  encoded_elimination :
    EffectivePolynomialCodesRealizeOver payload.eliminationBasis eliminationBasis
  encoded_intersection :
    EffectivePolynomialCodesRealizeOver payload.intersectionBasis intersectionBasis
  encoded_saturation :
    EffectivePolynomialCodesRealizeOver payload.saturationBasis saturationBasis
  encoded_saturated_groebner :
    EffectivePolynomialCodesRealizeOver payload.saturatedGroebnerBasis saturatedGroebnerBasis
  encoded_saturated_elimination :
    EffectivePolynomialCodesRealizeOver payload.saturatedEliminationBasis
      saturatedEliminationBasis
  trace_buchberger : ∃ step ∈ payload.trace,
    step.operation = .buchberger ∧ step.inputFamilies = [payload.input] ∧
      step.outputFamilies = [payload.groebnerBasis]
  trace_elimination : ∃ step ∈ payload.trace,
    step.operation = .elimination ∧ step.inputFamilies = [payload.groebnerBasis] ∧
      step.outputFamilies = [payload.eliminationBasis]
  trace_intersection : ∃ step ∈ payload.trace,
    step.operation = .idealIntersection ∧
      step.inputFamilies = [payload.input, payload.secondInput] ∧
      step.outputFamilies = [payload.intersectionBasis]
  trace_saturation : ∃ step ∈ payload.trace,
    step.operation = .saturation ∧
      step.inputFamilies = [payload.input, [payload.saturatingPolynomial]] ∧
      step.outputFamilies = [payload.saturationBasis]
  trace_saturated_buchberger : ∃ step ∈ payload.trace,
    step.operation = .buchberger ∧ step.inputFamilies = [payload.saturationBasis] ∧
      step.outputFamilies = [payload.saturatedGroebnerBasis]
  trace_saturated_elimination : ∃ step ∈ payload.trace,
    step.operation = .elimination ∧
      step.inputFamilies = [payload.saturatedGroebnerBasis] ∧
      step.outputFamilies = [payload.saturatedEliminationBasis]
  trace_execution_exact : ∃ finalState,
    EffectiveGroebnerTraceRuns payload.trace
      ⟨effectiveGroebnerCanonicalPolynomialPool K r ++ payload.input ++
          payload.secondInput ++ [payload.saturatingPolynomial],
        [payload.input, payload.secondInput, [payload.saturatingPolynomial]]⟩
      finalState ∧
    (∀ required ∈ payload.groebnerBasis ++ payload.eliminationBasis ++
        payload.intersectionBasis ++ payload.saturationBasis ++
          payload.saturatedGroebnerBasis ++ payload.saturatedEliminationBasis,
      required.AvailableIn finalState.polynomialPool) ∧
    finalState.familyRegisters =
      [payload.input, payload.secondInput, [payload.saturatingPolynomial]] ++
        (payload.trace.flatMap fun step => step.outputFamilies)
  trace_steps_nonempty : ∀ step ∈ payload.trace, step.primitiveOperations ≠ []
  machineCode : Nat.Partrec.Code
  machineFuel : ℕ
  machine_halts : machineCode.evaln machineFuel
    (Encodable.encode (r, suppliedOrder, suppliedInput, suppliedSecondInput,
      suppliedSaturating, suppliedRetainedVariables)) =
      some (Encodable.encode payload)

/-- Buchberger's terminating exact algorithm and its standard elimination, ideal-intersection,
and saturation constructions over every effectively supplied admissible monomial order. One
machine code is fixed before the dimension, order presentation, or any polynomial presentation;
the input code lists are supplied and realized before the output existential. -/
def EffectiveGroebnerAlgorithmOver (K : Type) [Field K] [DecidableEq K] [Encodable K] : Prop :=
  ∃ machineCode : Nat.Partrec.Code,
    ∀ (r : ℕ) (monomialOrder : MonomialOrder.{0, 0} (Fin r))
        (suppliedOrder : EffectiveMonomialOrderCode r)
        (suppliedInput suppliedSecondInput : List (EffectivePolynomialCodeOver K r))
        (suppliedSaturating : EffectivePolynomialCodeOver K r)
        (suppliedRetainedVariables : List (Fin r))
        (input secondInput : Finset (MvPolynomial (Fin r) K)) (keep : Finset (Fin r))
        (saturating : MvPolynomial (Fin r) K),
      suppliedOrder.Realizes monomialOrder →
      EffectivePolynomialCodesRealizeOver suppliedInput input →
      EffectivePolynomialCodesRealizeOver suppliedSecondInput secondInput →
      suppliedSaturating.toPolynomial = saturating →
      suppliedRetainedVariables.Nodup → suppliedRetainedVariables.toFinset = keep →
        ∃ result : EffectiveGroebnerResultOver input secondInput monomialOrder keep saturating
            suppliedInput suppliedSecondInput suppliedSaturating suppliedOrder
            suppliedRetainedVariables,
          result.machineCode = machineCode

/-- One fully supplied coefficient-field algebra job. All semantic input,
presentation, and monomial-order obligations are fixed before its output is
chosen. -/
structure EffectiveGroebnerJobOver (K : Type) [Field K] [DecidableEq K] where
  r : ℕ
  monomialOrder : MonomialOrder.{0, 0} (Fin r)
  suppliedOrder : EffectiveMonomialOrderCode r
  suppliedInput : List (EffectivePolynomialCodeOver K r)
  suppliedSecondInput : List (EffectivePolynomialCodeOver K r)
  suppliedSaturating : EffectivePolynomialCodeOver K r
  suppliedRetainedVariables : List (Fin r)
  input : Finset (MvPolynomial (Fin r) K)
  secondInput : Finset (MvPolynomial (Fin r) K)
  keep : Finset (Fin r)
  saturating : MvPolynomial (Fin r) K
  order_realizes : suppliedOrder.Realizes monomialOrder
  input_realizes : EffectivePolynomialCodesRealizeOver suppliedInput input
  second_input_realizes :
    EffectivePolynomialCodesRealizeOver suppliedSecondInput secondInput
  saturating_realizes : suppliedSaturating.toPolynomial = saturating
  retained_nodup : suppliedRetainedVariables.Nodup
  retained_realizes : suppliedRetainedVariables.toFinset = keep

/-- Input size charged to one coefficient-field algebra job. -/
def EffectiveGroebnerJobOver.sourcePolynomialCount {K : Type} [Field K]
    [DecidableEq K] (job : EffectiveGroebnerJobOver K) : ℕ :=
  job.input.card + job.secondInput.card + 1

/-- A uniform degree bound for one coefficient-field algebra job. -/
def EffectiveGroebnerJobOver.DegreeBoundedBy {K : Type} [Field K]
    [DecidableEq K] (job : EffectiveGroebnerJobOver K) (D : ℕ) : Prop :=
  ∀ P ∈ job.input ∪ job.secondInput ∪ {job.saturating}, P.totalDegree ≤ D

/-- A common degree envelope for a concrete finite polynomial family.  Unlike
`EffectiveGroebnerJobOver.DegreeBoundedBy`, this predicate can be applied to
families produced by a completed exact computation, after those outputs have
been chosen. -/
def EffectivePolynomialFamilyDegreeBoundedBy {K : Type} [CommSemiring K] {r : ℕ}
    (family : Finset (MvPolynomial (Fin r) K)) (D : ℕ) : Prop :=
  ∀ P ∈ family, P.totalDegree ≤ D

/-- The exact output of one supplied algebra job, tied to a machine code fixed
before every job in its batch. -/
structure EffectiveGroebnerCompletedJobOver (K : Type) [Field K] [DecidableEq K]
    [Encodable K] (machineCode : Nat.Partrec.Code)
    (job : EffectiveGroebnerJobOver K) where
  result : EffectiveGroebnerResultOver job.input job.secondInput job.monomialOrder
    job.keep job.saturating job.suppliedInput job.suppliedSecondInput
    job.suppliedSaturating job.suppliedOrder job.suppliedRetainedVariables
  machine_code_eq : result.machineCode = machineCode

/-- Rename a finite rational polynomial family between two supplied finite
coordinate presentations.  The map is data: the dependent pipeline below does
not silently identify the retained variables of two different jobs. -/
def effectiveRenameRationalFamily {r s : ℕ} (coordinateMap : Fin r → Fin s)
    (family : Finset (MvPolynomial (Fin r) ℚ)) :
    Finset (MvPolynomial (Fin s) ℚ) :=
  family.image (MvPolynomial.rename coordinateMap)

/-- A caller-supplied cross-source coordinate relation is jointly presentable when it is a
partial matching: one coordinate on either side cannot be identified with two different
coordinates on the other side.  This is exactly the coherence forced by injective forward and
reverse maps into one common finite coordinate presentation.  The guard is supplied before the
dependent pipeline is returned; it prevents the effective interface from asserting an impossible
joint presentation for an arbitrary many-to-many relation. -/
def IsJointlyPresentableSharedCoordinateRelation {r s : ℕ}
    (relation : Fin r → Fin s → Prop) : Prop :=
  (∀ i j₁ j₂, relation i j₁ → relation i j₂ → j₁ = j₂) ∧
    ∀ i₁ i₂ j, relation i₁ j → relation i₂ j → i₁ = i₂

/-- A source-matched dependent rational-algebra execution.  The two supplied
incidence jobs run first.  Only after their exact elimination outputs exist is
the intersection job supplied, and its two semantic inputs are exactly the
renamed elimination outputs.  The caller fixes which cross-source coordinates
are shared before this pipeline is returned; the two coordinate maps realize
exactly that relation while remaining injective within each source.  Thus the
third job cannot be an unrelated member of a preselected batch. -/
structure EffectiveDependentRationalEliminationPipeline
    (machineCode : Nat.Partrec.Code)
    (forwardJob reverseJob : EffectiveGroebnerJobOver ℚ)
    (sharedCoordinateRelation : Fin forwardJob.r → Fin reverseJob.r → Prop) where
  forwardResult : EffectiveGroebnerCompletedJobOver ℚ machineCode forwardJob
  reverseResult : EffectiveGroebnerCompletedJobOver ℚ machineCode reverseJob
  intersectionJob : EffectiveGroebnerJobOver ℚ
  forwardToIntersection : Fin forwardJob.r → Fin intersectionJob.r
  reverseToIntersection : Fin reverseJob.r → Fin intersectionJob.r
  forwardToIntersection_injective : Function.Injective forwardToIntersection
  reverseToIntersection_injective : Function.Injective reverseToIntersection
  forward_reverse_eq_iff : ∀ i j,
    forwardToIntersection i = reverseToIntersection j ↔ sharedCoordinateRelation i j
  intersection_input_from_forward :
    intersectionJob.input = effectiveRenameRationalFamily forwardToIntersection
      forwardResult.result.saturatedEliminationBasis
  intersection_input_from_reverse :
    intersectionJob.secondInput = effectiveRenameRationalFamily reverseToIntersection
      reverseResult.result.saturatedEliminationBasis
  intersectionResult :
    EffectiveGroebnerCompletedJobOver ℚ machineCode intersectionJob

/-- Every returned dependent pipeline certifies that its caller-supplied relation is jointly
presentable.  This is a consequence of the two within-source injections and the exact cross-map
equality condition, rather than an independently assumed property of the output. -/
theorem EffectiveDependentRationalEliminationPipeline.sharedCoordinateRelation_jointlyPresentable
    {machineCode : Nat.Partrec.Code}
    {forwardJob reverseJob : EffectiveGroebnerJobOver ℚ}
    {sharedCoordinateRelation : Fin forwardJob.r → Fin reverseJob.r → Prop}
    (pipeline : EffectiveDependentRationalEliminationPipeline machineCode
      forwardJob reverseJob sharedCoordinateRelation) :
    IsJointlyPresentableSharedCoordinateRelation sharedCoordinateRelation := by
  constructor
  · intro i j₁ j₂ hij₁ hij₂
    apply pipeline.reverseToIntersection_injective
    calc
      pipeline.reverseToIntersection j₁ = pipeline.forwardToIntersection i :=
        (pipeline.forward_reverse_eq_iff i j₁).2 hij₁ |>.symm
      _ = pipeline.reverseToIntersection j₂ :=
        (pipeline.forward_reverse_eq_iff i j₂).2 hij₂
  · intro i₁ i₂ j hi₁j hi₂j
    apply pipeline.forwardToIntersection_injective
    calc
      pipeline.forwardToIntersection i₁ = pipeline.reverseToIntersection j :=
        (pipeline.forward_reverse_eq_iff i₁ j).2 hi₁j
      _ = pipeline.forwardToIntersection i₂ :=
        (pipeline.forward_reverse_eq_iff i₂ j).2 hi₂j |>.symm

/-- Exact charged operation count of the dependent two-eliminations-then-
intersection execution. -/
def EffectiveDependentRationalEliminationPipeline.symbolicOperationCount
    {machineCode : Nat.Partrec.Code}
    {forwardJob reverseJob : EffectiveGroebnerJobOver ℚ}
    {sharedCoordinateRelation : Fin forwardJob.r → Fin reverseJob.r → Prop}
    (pipeline : EffectiveDependentRationalEliminationPipeline machineCode
      forwardJob reverseJob sharedCoordinateRelation) : ℕ :=
  pipeline.forwardResult.result.payload.symbolicOperationCount +
    pipeline.reverseResult.result.payload.symbolicOperationCount +
      pipeline.intersectionResult.result.payload.symbolicOperationCount

/-- A post-elimination degree envelope for one concrete dependent execution.
It bounds the two supplied source jobs, their actual saturated elimination
outputs, the dependent intersection job built from those outputs, and its
actual intersection basis.  In particular, this predicate is evaluated only
after `pipeline` has been returned; it does not assert that elimination
preserves a source-only degree bound. -/
def EffectiveDependentRationalEliminationPipeline.DegreeBoundedBy
    {machineCode : Nat.Partrec.Code}
    {forwardJob reverseJob : EffectiveGroebnerJobOver ℚ}
    {sharedCoordinateRelation : Fin forwardJob.r → Fin reverseJob.r → Prop}
    (pipeline : EffectiveDependentRationalEliminationPipeline machineCode
      forwardJob reverseJob sharedCoordinateRelation) (D : ℕ) : Prop :=
  forwardJob.DegreeBoundedBy D ∧
    reverseJob.DegreeBoundedBy D ∧
    EffectivePolynomialFamilyDegreeBoundedBy
      pipeline.forwardResult.result.saturatedEliminationBasis D ∧
    EffectivePolynomialFamilyDegreeBoundedBy
      pipeline.reverseResult.result.saturatedEliminationBasis D ∧
    pipeline.intersectionJob.DegreeBoundedBy D ∧
    EffectivePolynomialFamilyDegreeBoundedBy
      pipeline.intersectionResult.result.intersectionBasis D

/-- Results for a finite batch of supplied algebra jobs over one coefficient
field. -/
inductive EffectiveGroebnerBatchResultsOver (K : Type) [Field K] [DecidableEq K]
    [Encodable K] (machineCode : Nat.Partrec.Code) :
    List (EffectiveGroebnerJobOver K) → Type 2
  | nil : EffectiveGroebnerBatchResultsOver K machineCode []
  | cons {job jobs} (head : EffectiveGroebnerCompletedJobOver K machineCode job)
      (tail : EffectiveGroebnerBatchResultsOver K machineCode jobs) :
      EffectiveGroebnerBatchResultsOver K machineCode (job :: jobs)

/-- Sum of the exact charged symbolic traces in a coefficient-field batch. -/
def EffectiveGroebnerBatchResultsOver.symbolicOperationCount
    {K : Type} [Field K] [DecidableEq K] [Encodable K]
    {machineCode : Nat.Partrec.Code} :
    {jobs : List (EffectiveGroebnerJobOver K)} →
      EffectiveGroebnerBatchResultsOver K machineCode jobs → ℕ
  | [], .nil => 0
  | _ :: _, .cons head tail =>
      head.result.payload.symbolicOperationCount + tail.symbolicOperationCount

/-- Aggregate supplied input size of a finite algebra batch. -/
def effectiveGroebnerBatchSourcePolynomialCount {K : Type} [Field K]
    [DecidableEq K] : List (EffectiveGroebnerJobOver K) → ℕ
  | [] => 0
  | job :: jobs => job.sourcePolynomialCount +
      effectiveGroebnerBatchSourcePolynomialCount jobs

/-- Every job in a finite batch lies in the common ambient-dimension and
degree envelope used by the single combined complexity bound. -/
def EffectiveGroebnerBatchInputsBounded {K : Type} [Field K] [DecidableEq K] :
    List (EffectiveGroebnerJobOver K) → ℕ → ℕ → Prop
  | [], _, _ => True
  | job :: jobs, N, D =>
      job.r ≤ N ∧ job.DegreeBoundedBy D ∧
        EffectiveGroebnerBatchInputsBounded jobs N D

/-- Coefficient extension of a rational family to the real closed field. -/
def rationalPolynomialFamilyToReal {r : ℕ} (family : Finset (MvPolynomial (Fin r) ℚ)) :
    Finset (MvPolynomial (Fin r) ℝ) :=
  family.image (MvPolynomial.map (Rat.castHom ℝ))

/-- Coefficient extension of a rational family to the algebraically closed
field used by the elimination-closure theorem. -/
def rationalPolynomialFamilyToComplex {r : ℕ}
    (family : Finset (MvPolynomial (Fin r) ℚ)) :
    Finset (MvPolynomial (Fin r) ℂ) :=
  family.image (MvPolynomial.map (Rat.castHom ℂ))

/-- Common complex zero set of a finite rational polynomial family. -/
def effectiveComplexZeroSet {r : ℕ}
    (family : Finset (MvPolynomial (Fin r) ℚ)) : Set (Fin r → ℂ) :=
  {x | ∀ P ∈ family,
    MvPolynomial.eval x (MvPolynomial.map (Rat.castHom ℂ) P) = 0}

/-- Zariski closure in a finite complex affine space, written directly as the
zero set of every complex polynomial vanishing on the supplied set. -/
def effectiveComplexZariskiClosure {r : ℕ} (S : Set (Fin r → ℂ)) :
    Set (Fin r → ℂ) :=
  {x | ∀ P : MvPolynomial (Fin r) ℂ,
    (∀ y ∈ S, MvPolynomial.eval y P = 0) → MvPolynomial.eval x P = 0}

/-- Cylinder over the coordinate projection of a complex affine set onto a
retained variable block. -/
def effectiveComplexProjectionCylinder {r : ℕ}
    (keep : Finset (Fin r)) (S : Set (Fin r → ℂ)) : Set (Fin r → ℂ) :=
  {x | ∃ y ∈ S, ∀ i ∈ keep, x i = y i}

/-- The algebraically closed elimination-closure theorem for a displayed
rational elimination basis.  This is the exact geometric conclusion used after
Groebner elimination: the output zero set is the Zariski closure of the input
projection, not the projection itself. -/
def IsExactComplexProjectionClosure {r : ℕ}
    (input : Finset (MvPolynomial (Fin r) ℚ)) (keep : Finset (Fin r))
    (output : Finset (MvPolynomial (Fin r) ℚ)) : Prop :=
  effectiveComplexZeroSet output =
    effectiveComplexZariskiClosure
      (effectiveComplexProjectionCylinder keep (effectiveComplexZeroSet input))

/-- A polynomial uses only the retained variables of an elimination block. -/
def UsesOnlyEffectiveVariables {r : ℕ} (keep : Finset (Fin r))
    (P : MvPolynomial (Fin r) ℚ) : Prop :=
  P.vars ⊆ keep

/-- Lexicographic comparison of monomials in the explicitly supplied variable order. -/
def effectiveLexMonomialLT {r : ℕ} :
    List (Fin r) → (Fin r →₀ ℕ) → (Fin r →₀ ℕ) → Prop
  | [], _, _ => False
  | x :: xs, left, right =>
      left x < right x ∨
        (left x = right x ∧ effectiveLexMonomialLT xs left right)

/-- The specified variable order is complete, duplicate-free, and is an elimination order for
the retained block: every eliminated variable precedes every retained variable. -/
def IsEffectiveEliminationVariableOrder {r : ℕ} (order : List (Fin r))
    (keep : Finset (Fin r)) : Prop :=
  ∃ eliminated retained : List (Fin r),
    order = eliminated ++ retained ∧
      eliminated.Nodup ∧ retained.Nodup ∧ Disjoint eliminated.toFinset retained.toFinset ∧
      eliminated.toFinset = Finset.univ \ keep ∧ retained.toFinset = keep

/-- `exponent` is the leading exponent of `P` for the displayed lexicographic order. -/
def IsEffectiveLeadingExponent {r : ℕ} (order : List (Fin r))
    (P : MvPolynomial (Fin r) ℚ) (exponent : Fin r →₀ ℕ) : Prop :=
  exponent ∈ P.support ∧
    ∀ other ∈ P.support,
      other = exponent ∨ effectiveLexMonomialLT order other exponent

/-- An exact Gröbner-basis certificate for the specified monomial order. Besides ideal equality
and exact normal-form division, every leading monomial in the input ideal is divisible by a
leading monomial of the displayed basis, and the normal form contains no reducible monomial. -/
def IsExactGroebnerBasis {r : ℕ} (order : List (Fin r))
    (input basis : Finset (MvPolynomial (Fin r) ℚ))
    (normalForm : MvPolynomial (Fin r) ℚ → MvPolynomial (Fin r) ℚ) : Prop :=
  (∀ G ∈ basis, G ≠ 0) ∧
    Ideal.span (input : Set (MvPolynomial (Fin r) ℚ)) =
      Ideal.span (basis : Set (MvPolynomial (Fin r) ℚ)) ∧
    (∀ P ∈ Ideal.span (input : Set (MvPolynomial (Fin r) ℚ)), P ≠ 0 →
      ∀ leadingP, IsEffectiveLeadingExponent order P leadingP →
        ∃ G ∈ basis, ∃ leadingG,
          IsEffectiveLeadingExponent order G leadingG ∧ leadingG ≤ leadingP) ∧
    ∀ P,
      (normalForm P = 0 ↔ P ∈ Ideal.span (input : Set (MvPolynomial (Fin r) ℚ))) ∧
      ∃ quotients : basis → MvPolynomial (Fin r) ℚ,
        P = normalForm P + ∑ Q : basis, quotients Q * Q.1 ∧
          ∀ exponent ∈ (normalForm P).support, ∀ G ∈ basis, ∀ leadingG,
            IsEffectiveLeadingExponent order G leadingG → ¬leadingG ≤ exponent

/-- Exact elimination-ideal output on the retained variable block. -/
def IsExactEliminationBasis {r : ℕ} (input : Finset (MvPolynomial (Fin r) ℚ))
    (keep : Finset (Fin r)) (output : Finset (MvPolynomial (Fin r) ℚ)) : Prop :=
  (∀ P ∈ output, UsesOnlyEffectiveVariables keep P) ∧
    ∀ P, UsesOnlyEffectiveVariables keep P →
      (P ∈ Ideal.span (output : Set (MvPolynomial (Fin r) ℚ)) ↔
        P ∈ Ideal.span (input : Set (MvPolynomial (Fin r) ℚ)))

/-- Exact ideal-intersection output. -/
def IsExactIdealIntersectionBasis {r : ℕ}
    (left right output : Finset (MvPolynomial (Fin r) ℚ)) : Prop :=
  Ideal.span (output : Set (MvPolynomial (Fin r) ℚ)) =
    Ideal.span (left : Set (MvPolynomial (Fin r) ℚ)) ⊓
      Ideal.span (right : Set (MvPolynomial (Fin r) ℚ))

/-- Exact saturation output, characterized by membership after multiplication by a power. -/
def IsExactSaturationBasis {r : ℕ} (input : Finset (MvPolynomial (Fin r) ℚ))
    (saturating : MvPolynomial (Fin r) ℚ)
    (output : Finset (MvPolynomial (Fin r) ℚ)) : Prop :=
  ∀ P, P ∈ Ideal.span (output : Set (MvPolynomial (Fin r) ℚ)) ↔
    ∃ k : ℕ, saturating ^ k * P ∈ Ideal.span (input : Set (MvPolynomial (Fin r) ℚ))

/-- The three-valued exact sign alphabet emitted by the effective CAD algorithm. -/
inductive EffectivePolynomialSign
  | negative
  | zero
  | positive
  deriving DecidableEq, Encodable

/-- Exact interpretation of an encoded sign. -/
def EffectivePolynomialSign.Realizes : EffectivePolynomialSign → ℝ → Prop
  | .negative, x => x < 0
  | .zero, x => x = 0
  | .positive, x => 0 < x

/-- Iterated differentiation in one CAD lifting variable. -/
def effectiveIteratedPDeriv {σ : Type} [DecidableEq σ] (x : σ) :
    ℕ → MvPolynomial σ ℝ → MvPolynomial σ ℝ
  | 0, P => P
  | k + 1, P => effectiveIteratedPDeriv x k (MvPolynomial.pderiv x P)

/-- Finite exact algebraic-root data: a defining rational polynomial, its index in the complete
ordered root stack, and its complete Thom-sign row. -/
structure EffectiveAlgebraicRootCertificate (r : ℕ) where
  definingPolynomial : EffectivePolynomialCode r
  rootIndex : ℕ
  thomSigns : List EffectivePolynomialSign
  deriving Encodable

/-- A root certificate denotes the indexed CAD root and gives the exact signs of every iterated
derivative of its displayed defining polynomial along the section. -/
def EffectiveAlgebraicRootCertificate.Realizes {r : ℕ}
    (certificate : EffectiveAlgebraicRootCertificate r) (x : Fin r)
    (base : Set (CADSpace r)) (root : CADSpace r → ℝ)
    (family : Finset (MvPolynomial (Fin r) ℝ)) : Prop :=
  let P := MvPolynomial.map (Rat.castHom ℝ) certificate.definingPolynomial.toPolynomial
  P ∈ family ∧
    IsCADAlgebraicRoot x base certificate.rootIndex root family ∧
    (∀ a ∈ base, MvPolynomial.eval (Function.update a x (root a)) P = 0) ∧
    certificate.thomSigns.length = P.totalDegree + 1 ∧
    ∀ k (sign : EffectivePolynomialSign), certificate.thomSigns[k]? = some sign → ∀ a ∈ base,
      EffectivePolynomialSign.Realizes sign (MvPolynomial.eval (Function.update a x (root a))
        (effectiveIteratedPDeriv x k P))

/-- Finite syntax for recursive CAD lifting, enriched at every section/sector boundary by exact
algebraic-root and Thom-sign certificates. -/
inductive EffectiveCADCellCertificate (r : ℕ)
  | point
  | wholeFiber (base : EffectiveCADCellCertificate r)
  | section (root : EffectiveAlgebraicRootCertificate r)
      (base : EffectiveCADCellCertificate r)
  | lowerSector (upper : EffectiveAlgebraicRootCertificate r)
      (base : EffectiveCADCellCertificate r)
  | boundedSector (lower upper : EffectiveAlgebraicRootCertificate r)
      (base : EffectiveCADCellCertificate r)
  | upperSector (lower : EffectiveAlgebraicRootCertificate r)
      (base : EffectiveCADCellCertificate r)
  deriving Encodable

/-- Exact interpretation of an algebraic-root-certified CAD cell. -/
def EffectiveCADCellCertificate.Realizes {r : ℕ} :
    Finset (MvPolynomial (Fin r) ℝ) → List (Fin r) → EffectiveCADCellCertificate r →
      Set (CADSpace r) → Prop
  | _, [], .point, cell => cell = { a | ∀ x, a x = 0 }
  | family, x :: xs, .wholeFiber baseCertificate, cell =>
      ∃ base, Realizes (cadProjectionStep x family) xs baseCertificate base ∧
        (∀ a ∈ base, cadRealRootsAt x family a = ∅) ∧
        cell = { a | cadEraseCoordinate x a ∈ base }
  | family, x :: xs, .section rootCertificate baseCertificate, cell =>
      ∃ base, Realizes (cadProjectionStep x family) xs baseCertificate base ∧
        ∃ root, rootCertificate.Realizes x base root family ∧
          cell = { a | cadEraseCoordinate x a ∈ base ∧
            a x = root (cadEraseCoordinate x a) }
  | family, x :: xs, .lowerSector upperCertificate baseCertificate, cell =>
      ∃ base, Realizes (cadProjectionStep x family) xs baseCertificate base ∧
        ∃ upper, upperCertificate.rootIndex = 0 ∧
          upperCertificate.Realizes x base upper family ∧
          cell = { a | cadEraseCoordinate x a ∈ base ∧
            a x < upper (cadEraseCoordinate x a) }
  | family, x :: xs, .boundedSector lowerCertificate upperCertificate baseCertificate, cell =>
      ∃ base, Realizes (cadProjectionStep x family) xs baseCertificate base ∧
        ∃ lower upper,
          upperCertificate.rootIndex = lowerCertificate.rootIndex + 1 ∧
          lowerCertificate.Realizes x base lower family ∧
          upperCertificate.Realizes x base upper family ∧
          (∀ a ∈ base, lower a < upper a) ∧
          cell = { a | cadEraseCoordinate x a ∈ base ∧
            lower (cadEraseCoordinate x a) < a x ∧
            a x < upper (cadEraseCoordinate x a) }
  | family, x :: xs, .upperSector lowerCertificate baseCertificate, cell =>
      ∃ base, Realizes (cadProjectionStep x family) xs baseCertificate base ∧
        ∃ lower, lowerCertificate.Realizes x base lower family ∧
          IsCADLastAlgebraicRoot x base lowerCertificate.rootIndex lower family ∧
          cell = { a | cadEraseCoordinate x a ∈ base ∧
            lower (cadEraseCoordinate x a) < a x }
  | _, _, _, _ => False

/-- Number of exact algebraic-sign answers explicitly stored in a recursive cell certificate. -/
def EffectiveCADCellCertificate.signOperationCount {r : ℕ} :
    EffectiveCADCellCertificate r → ℕ
  | .point => 0
  | .wholeFiber base => base.signOperationCount
  | .section root base => root.thomSigns.length + base.signOperationCount
  | .lowerSector upper base => upper.thomSigns.length + base.signOperationCount
  | .boundedSector lower upper base =>
      lower.thomSigns.length + upper.thomSigns.length + base.signOperationCount
  | .upperSector lower base => lower.thomSigns.length + base.signOperationCount

/-- A cell's encoded geometry together with an exhaustive exact sign row for the input and
generated projection polynomials. -/
structure EffectiveCertifiedCADCell (r : ℕ) where
  geometry : EffectiveCADCellCertificate r
  signs : List (EffectivePolynomialCode r × EffectivePolynomialSign)
  deriving Encodable

/-- The encoded cell certificate realizes both its recursive algebraic-root geometry and its
complete constant-sign table. -/
def EffectiveCertifiedCADCell.Realizes {r : ℕ} (certificate : EffectiveCertifiedCADCell r)
    (family signFamily : Finset (MvPolynomial (Fin r) ℚ)) (order : List (Fin r))
    (cell : Set (CADSpace r)) : Prop :=
  certificate.geometry.Realizes (rationalPolynomialFamilyToReal family) order cell ∧
    EffectivePolynomialCodesRealize (certificate.signs.map Prod.fst) signFamily ∧
    ∀ code (sign : EffectivePolynomialSign), (code, sign) ∈ certificate.signs →
      ∀ a ∈ cell, EffectivePolynomialSign.Realizes sign (MvPolynomial.eval a
        (MvPolynomial.map (Rat.castHom ℝ) code.toPolynomial))

/-- Number of exact root/Thom/cell-sign answers carried by one complete cell certificate. -/
def EffectiveCertifiedCADCell.signOperationCount {r : ℕ}
    (certificate : EffectiveCertifiedCADCell r) : ℕ :=
  certificate.geometry.signOperationCount + certificate.signs.length

/-- Every polynomial presentation contained in one exact algebraic-root certificate. -/
def EffectiveAlgebraicRootCertificate.polynomialCodes {r : ℕ}
    (certificate : EffectiveAlgebraicRootCertificate r) : List (EffectivePolynomialCode r) :=
  [certificate.definingPolynomial]

/-- Recursive extraction of every defining polynomial used by a CAD cell certificate. -/
def EffectiveCADCellCertificate.polynomialCodes {r : ℕ} :
    EffectiveCADCellCertificate r → List (EffectivePolynomialCode r)
  | .point => []
  | .wholeFiber base => base.polynomialCodes
  | .section root base => root.polynomialCodes ++ base.polynomialCodes
  | .lowerSector upper base => upper.polynomialCodes ++ base.polynomialCodes
  | .boundedSector lower upper base =>
      lower.polynomialCodes ++ upper.polynomialCodes ++ base.polynomialCodes
  | .upperSector lower base => lower.polynomialCodes ++ base.polynomialCodes

/-- A recursive cell geometry requires an algebraic-root isolation stage exactly when it has a
nontrivial lifting layer. A `wholeFiber` still requires certifying that the root stack is empty. -/
def EffectiveCADCellCertificate.RequiresRootIsolation {r : ℕ} :
    EffectiveCADCellCertificate r → Prop
  | .point => False
  | .wholeFiber _ | .section _ _ | .lowerSector _ _ | .boundedSector _ _ _ |
      .upperSector _ _ => True

/-- A recursive cell geometry contains a section-lifting layer. -/
def EffectiveCADCellCertificate.ContainsSection {r : ℕ} :
    EffectiveCADCellCertificate r → Prop
  | .point => False
  | .wholeFiber base => base.ContainsSection
  | .section _ _ => True
  | .lowerSector _ base | .boundedSector _ _ base | .upperSector _ base =>
      base.ContainsSection

/-- A recursive cell geometry contains a sector-lifting layer. -/
def EffectiveCADCellCertificate.ContainsSector {r : ℕ} :
    EffectiveCADCellCertificate r → Prop
  | .point => False
  | .wholeFiber base | .section _ base => base.ContainsSector
  | .lowerSector _ _ | .boundedSector _ _ _ | .upperSector _ _ => True

/-- Every polynomial presentation on which a certified CAD cell depends: recursive root-defining
polynomials together with the complete displayed constant-sign family. -/
def EffectiveCertifiedCADCell.polynomialCodes {r : ℕ}
    (certificate : EffectiveCertifiedCADCell r) : List (EffectivePolynomialCode r) :=
  certificate.geometry.polynomialCodes ++ certificate.signs.map Prod.fst

/-- A finite encoded sign-condition query. -/
structure EffectiveCADSignQuery (r : ℕ) where
  equations : List (EffectivePolynomialCode r)
  nonnegative : List (EffectivePolynomialCode r)
  positive : List (EffectivePolynomialCode r)
  deriving Encodable

/-- Every polynomial presentation read by a sign-condition query. -/
def EffectiveCADSignQuery.polynomialCodes {r : ℕ}
    (query : EffectiveCADSignQuery r) : List (EffectivePolynomialCode r) :=
  query.equations ++ query.nonnegative ++ query.positive

/-- Exact decoding of a sign-condition query. -/
def EffectiveCADSignQuery.Realizes {r : ℕ} (query : EffectiveCADSignQuery r)
    (equations nonnegative positive : Finset (MvPolynomial (Fin r) ℚ)) : Prop :=
  EffectivePolynomialCodesRealize query.equations equations ∧
    EffectivePolynomialCodesRealize query.nonnegative nonnegative ∧
    EffectivePolynomialCodesRealize query.positive positive

/-- One exhaustive encoded cellwise truth row. -/
structure EffectiveCADTruthRow (r : ℕ) where
  query : EffectiveCADSignQuery r
  cellIndex : ℕ
  truth : Bool
  deriving Encodable

/-- Every polynomial presentation read to produce a truth row. -/
def EffectiveCADTruthRow.polynomialCodes {r : ℕ}
    (row : EffectiveCADTruthRow r) : List (EffectivePolynomialCode r) :=
  row.query.polynomialCodes

/-- One exhaustive encoded witness-retention row. -/
structure EffectiveCADRetentionRow (r : ℕ) where
  query : EffectiveCADSignQuery r
  retainedCellIndices : List ℕ
  deriving Encodable

/-- Every polynomial presentation read to produce a witness-retention row. -/
def EffectiveCADRetentionRow.polynomialCodes {r : ℕ}
    (row : EffectiveCADRetentionRow r) : List (EffectivePolynomialCode r) :=
  row.query.polynomialCodes

/-- Erase a supplied prefix of lifting coordinates.  This is the geometric projection naturally
paired with `IsRecursivelyLiftedCADCell`: the recursive cell language peels the head of the lifting
order and applies `cadEraseCoordinate` at every dropped layer. -/
def effectiveCADErasePrefix {r : ℕ} (eliminated : List (Fin r))
    (point : CADSpace r) : CADSpace r :=
  eliminated.foldl (fun projected x => cadEraseCoordinate x projected) point

/-- The recursion-varying BPR family after dropping a prefix of lifting layers.  Unlike the public
accumulated `generatedCADProjectionFamily`, this is the stage family consumed by the recursive
cell certificate over the retained suffix. -/
def effectiveCADFamilyAfterPrefix {r : ℕ} (eliminated : List (Fin r))
    (family : Finset (MvPolynomial (Fin r) ℝ)) : Finset (MvPolynomial (Fin r) ℝ) :=
  eliminated.foldl (fun projected x => cadProjectionStep x projected) family

/-- Finite exact sign-vector syntax for one basic CAD cell presentation.  Negative signs are kept
explicitly, rather than encoding them by silently adjoining negated polynomials to the supplied
family. -/
structure EffectiveCADBasicSignCondition (r : ℕ) where
  conditions : List (EffectivePolynomialCode r × EffectivePolynomialSign)
  deriving Encodable

/-- The subset of the erased-prefix affine slice cut out by an encoded exact sign vector.  The
explicit zero-coordinate guard is part of the ambient representation: projected cells still use
`CADSpace r`, so their eliminated coordinates must not be left as free cylindrical directions. -/
def EffectiveCADBasicSignCondition.set {r : ℕ} (eliminated : List (Fin r))
    (condition : EffectiveCADBasicSignCondition r) : Set (CADSpace r) :=
  { point | (∀ x ∈ eliminated, point x = 0) ∧
      ∀ code sign, (code, sign) ∈ condition.conditions →
        EffectivePolynomialSign.Realizes sign
          (MvPolynomial.eval point
            (MvPolynomial.map (Rat.castHom ℝ) code.toPolynomial)) }

/-- An encoded sign vector lists every polynomial in the displayed rational family, uses no
polynomial outside that family, and cuts out exactly the displayed cell.  The coverage direction
is required by prefix-projected CAD consumers: soundness for the signs that happen to be listed
does not by itself make the list an exact sign vector for the displayed family. -/
def EffectiveCADBasicSignCondition.Realizes {r : ℕ}
    (condition : EffectiveCADBasicSignCondition r)
    (eliminated retained : List (Fin r))
    (family : Finset (MvPolynomial (Fin r) ℝ)) (cell : Set (CADSpace r)) : Prop :=
  ((∀ code sign, (code, sign) ∈ condition.conditions →
      MvPolynomial.map (Rat.castHom ℝ) code.toPolynomial ∈ family ∧
        code.toPolynomial.vars ⊆ retained.toFinset) ∧
    (∀ P ∈ family, ∃ code sign, (code, sign) ∈ condition.conditions ∧
      MvPolynomial.map (Rat.castHom ℝ) code.toPolynomial = P)) ∧
    cell = condition.set eliminated

/-- Every polynomial presentation read by a basic sign-condition certificate. -/
def EffectiveCADBasicSignCondition.polynomialCodes {r : ℕ}
    (condition : EffectiveCADBasicSignCondition r) : List (EffectivePolynomialCode r) :=
  condition.conditions.map Prod.fst

/-- One fully encoded prefix-projected CAD cell certificate.  The source-cell code and the exact
truth/retention-row code lists link the projected cell back to all of the finite decision data
emitted for its source cell. -/
structure EffectiveCADPrefixProjectionCertificate (r : ℕ) where
  eliminatedVariables : List (Fin r)
  retainedVariables : List (Fin r)
  sourceCellIndex : ℕ
  sourceCellCertificateCode : ℕ
  projectedGeometry : EffectiveCADCellCertificate r
  projectedGeometryCode : ℕ
  basicSignCondition : EffectiveCADBasicSignCondition r
  truthRowCodes : List ℕ
  retentionRowCodes : List ℕ
  deriving Encodable

/-- Every polynomial presentation required by a prefix-projected cell artifact. -/
def EffectiveCADPrefixProjectionCertificate.polynomialCodes {r : ℕ}
    (certificate : EffectiveCADPrefixProjectionCertificate r) :
    List (EffectivePolynomialCode r) :=
  certificate.projectedGeometry.polynomialCodes ++
    certificate.basicSignCondition.polynomialCodes

/-- Exact root/Thom and basic-cell sign answers stored in one prefix projection artifact. -/
def EffectiveCADPrefixProjectionCertificate.signOperationCount {r : ℕ}
    (certificate : EffectiveCADPrefixProjectionCertificate r) : ℕ :=
  certificate.projectedGeometry.signOperationCount +
    certificate.basicSignCondition.conditions.length

/-- Exact finite data for one charged member of a BPR reducta family.  The source code and
iteration number are retained so the primitive trace records how the output code was obtained,
rather than merely asserting that an extensionally equal polynomial eventually appeared. -/
structure EffectiveReductumCertificate (r : ℕ) where
  sourcePolynomial : EffectivePolynomialCode r
  reductumVariable : Fin r
  reductumIteration : ℕ
  outputPolynomial : EffectivePolynomialCode r
  deriving Encodable

/-- A reductum certificate denotes exactly the displayed nonzero iterate, within the finite
degree range used by `cadReducta`.  Coefficient extension to `ℝ` is injective, so this equality
also fixes the underlying rational output polynomial. -/
def EffectiveReductumCertificate.Realizes {r : ℕ}
    (certificate : EffectiveReductumCertificate r) : Prop :=
  let sourceReal :=
    MvPolynomial.map (Rat.castHom ℝ) certificate.sourcePolynomial.toPolynomial
  let outputReal :=
    MvPolynomial.map (Rat.castHom ℝ) certificate.outputPolynomial.toPolynomial
  certificate.reductumIteration <
      (cadAsUnivariate certificate.reductumVariable sourceReal).natDegree + 1 ∧
    outputReal =
      (cadReductum certificate.reductumVariable)^[certificate.reductumIteration] sourceReal ∧
    outputReal ∈ cadReducta certificate.reductumVariable sourceReal

/-- General symbolic operations supplied by the cited rational algebra and CAD algorithms. -/
inductive EffectiveAlgebraTraceOperation
  | buchberger
  | elimination
  | idealIntersection
  | saturation
  | reductaGeneration
  | coefficientProjection
  | discriminantProjection
  | principalSubresultantProjection
  | projectionClosure
  | rootIsolation
  | sectionLifting
  | sectorLifting
  | prefixCellProjection
  | signConditionTruth
  | witnessCellRetention
  deriving DecidableEq, Encodable

/-- Primitive operations in the real-algebraic cost model. Exact algebraic-sign queries are
primitive here; this does not claim Turing-computable comparison of arbitrary real numbers. -/
inductive EffectiveRealAlgebraicPrimitiveOperation
  | rationalAddition
  | rationalMultiplication
  | rationalInversion
  | emitReductumCertificate (code : ℕ)
  | exactAlgebraicSign
  | emitCellCertificate (code : ℕ)
  | emitPrefixProjectionCertificate (code : ℕ)
  | emitTruthRow (code : ℕ)
  | emitRetentionRow (code : ℕ)
  deriving DecidableEq, Encodable

/-- One certified high-level trace step, including the polynomial families it reads and emits,
the injective encodings of any CAD certificates/truth rows/retention rows it produces, and the
complete list of primitive real-algebraic operations charged to that step. The artifact fields
use `Nat` solely to avoid a circular datatype dependency; result-level equalities below identify
them extensionally with the actual typed payload objects. -/
structure EffectiveAlgebraTraceStep (r : ℕ) where
  operation : EffectiveAlgebraTraceOperation
  inputFamilies : List (List (EffectivePolynomialCode r))
  outputFamilies : List (List (EffectivePolynomialCode r))
  producedReductumCertificateCodes : List ℕ
  producedCellCertificateCodes : List ℕ
  producedPrefixProjectionCertificateCodes : List ℕ
  producedTruthRowCodes : List ℕ
  producedRetentionRowCodes : List ℕ
  variableOrder : List (Fin r)
  activeVariable : Option (Fin r)
  retainedVariables : List (Fin r)
  primitiveOperations : List EffectiveRealAlgebraicPrimitiveOperation
  deriving Encodable

/-- Exact real-algebraic cost of one trace step. -/
def EffectiveAlgebraTraceStep.operationCount {r : ℕ}
    (step : EffectiveAlgebraTraceStep r) : ℕ :=
  step.primitiveOperations.length

/-- Every typed output artifact attributed to a trace step consumes a charged exact-sign event.
The stronger result-level bound below additionally charges every Thom/cell sign stored inside the
produced cell certificates. -/
def EffectiveAlgebraTraceStep.ArtifactOutputsCharged {r : ℕ}
    (step : EffectiveAlgebraTraceStep r) : Prop :=
  step.producedCellCertificateCodes.length +
      step.producedPrefixProjectionCertificateCodes.length +
      step.producedTruthRowCodes.length + step.producedRetentionRowCodes.length ≤
    step.primitiveOperations.count .exactAlgebraicSign

/-- Artifact outputs occur only at the corresponding CAD/QE stages. -/
def EffectiveAlgebraTraceStep.ArtifactKindsCorrect {r : ℕ}
    (step : EffectiveAlgebraTraceStep r) : Prop :=
  (step.producedReductumCertificateCodes ≠ [] →
      step.operation = .reductaGeneration) ∧
    (step.producedCellCertificateCodes ≠ [] →
      step.operation ∈ [.rootIsolation, .sectionLifting, .sectorLifting]) ∧
    (step.producedPrefixProjectionCertificateCodes ≠ [] →
      step.operation = .prefixCellProjection) ∧
    (step.producedTruthRowCodes ≠ [] → step.operation = .signConditionTruth) ∧
    (step.producedRetentionRowCodes ≠ [] → step.operation = .witnessCellRetention)

/-- A trace step is tied to a particular high-level operation and its displayed input/output
polynomial families. -/
def EffectiveAlgebraTraceStep.Links {r : ℕ} (step : EffectiveAlgebraTraceStep r)
    (operation : EffectiveAlgebraTraceOperation)
    (inputs outputs : List (List (EffectivePolynomialCode r))) : Prop :=
  step.operation = operation ∧ step.inputFamilies = inputs ∧ step.outputFamilies = outputs

/-- The rational polynomial family decoded from one finite code list. -/
def effectiveDecodedPolynomialFamily {r : ℕ} (codes : List (EffectivePolynomialCode r)) :
    Finset (MvPolynomial (Fin r) ℚ) :=
  (codes.map EffectivePolynomialCode.toPolynomial).toFinset

/-- The real interpretation of one displayed rational code family. -/
def effectiveDecodedRealPolynomialFamily {r : ℕ}
    (codes : List (EffectivePolynomialCode r)) : Finset (MvPolynomial (Fin r) ℝ) :=
  rationalPolynomialFamilyToReal (effectiveDecodedPolynomialFamily codes)

/-- The reductum-certificate code, when a primitive is a reductum-emission event. -/
def EffectiveRealAlgebraicPrimitiveOperation.reductumCertificateCode :
    EffectiveRealAlgebraicPrimitiveOperation → Option ℕ
  | .emitReductumCertificate code => some code
  | _ => none

/-- The displayed reductum-certificate register is exactly the corresponding subsequence of the
charged primitive program.  Thus a reducta stage cannot list certificates beside an unrelated
arithmetic trace. -/
def EffectiveAlgebraTraceStep.ReductumPrimitiveCodesExact {r : ℕ}
    (step : EffectiveAlgebraTraceStep r) : Prop :=
  step.primitiveOperations.filterMap
      EffectiveRealAlgebraicPrimitiveOperation.reductumCertificateCode =
    step.producedReductumCertificateCodes

/-- A reducta-generation step charges one exact certificate for every displayed output code.
Each certificate starts from a code in the declared input family, uses the declared active
variable, and realizes the indicated finite reductum iterate. -/
def EffectiveAlgebraTraceStep.ReductaOutputsExactlyCharged {r : ℕ}
    (step : EffectiveAlgebraTraceStep r) (input output : List (EffectivePolynomialCode r))
    (x : Fin r) : Prop :=
  ∃ certificates : List (EffectiveReductumCertificate r),
    certificates.map Encodable.encode = step.producedReductumCertificateCodes ∧
      certificates.map EffectiveReductumCertificate.outputPolynomial = output ∧
      ∀ certificate ∈ certificates,
        certificate.sourcePolynomial ∈ input ∧
          certificate.reductumVariable = x ∧ certificate.Realizes

/-- One state of the primitive rational-arithmetic execution underlying a high-level trace step. -/
structure EffectivePolynomialMachineState (r : ℕ) where
  polynomialPool : List (EffectivePolynomialCode r)
  familyRegisters : List (List (EffectivePolynomialCode r))
  reductumCertificateCodes : List ℕ
  cellCertificateCodes : List ℕ
  prefixProjectionCertificateCodes : List ℕ
  truthRowCodes : List ℕ
  retentionRowCodes : List ℕ

/-- A required polynomial presentation is extensionally available in the computed register pool.
The exact code need not be byte-identical, but it must denote the same rational polynomial. -/
def EffectivePolynomialCode.AvailableIn {r : ℕ} (required : EffectivePolynomialCode r)
    (pool : List (EffectivePolynomialCode r)) : Prop :=
  ∃ computed ∈ pool, computed.toPolynomial = required.toPolynomial

/-- Exact transition semantics for every charged primitive operation. Polynomial arithmetic adds
the computed rational polynomial to the register pool; artifact-emission steps append the exact
encoded object to the corresponding output register. Hence typed CAD/QE output is generated by,
not merely listed beside, the bounded primitive execution. -/
def EffectivePrimitiveTransition {r : ℕ} :
    EffectiveRealAlgebraicPrimitiveOperation → EffectivePolynomialMachineState r →
      EffectivePolynomialMachineState r → Prop
  | .rationalAddition, before, after =>
      ∃ left ∈ before.polynomialPool, ∃ right ∈ before.polynomialPool, ∃ result,
        result.toPolynomial = left.toPolynomial + right.toPolynomial ∧
          after = { before with polynomialPool := before.polynomialPool ++ [result] }
  | .rationalMultiplication, before, after =>
      ∃ left ∈ before.polynomialPool, ∃ right ∈ before.polynomialPool, ∃ result,
        result.toPolynomial = left.toPolynomial * right.toPolynomial ∧
          after = { before with polynomialPool := before.polynomialPool ++ [result] }
  | .rationalInversion, before, after =>
      ∃ scalar : ℚ, scalar ≠ 0 ∧ ∃ source ∈ before.polynomialPool, ∃ result,
        result.toPolynomial = MvPolynomial.C scalar⁻¹ * source.toPolynomial ∧
          after = { before with polynomialPool := before.polynomialPool ++ [result] }
  | .emitReductumCertificate code, before, after =>
      ∃ certificate : EffectiveReductumCertificate r,
        Encodable.encode certificate = code ∧
          certificate.sourcePolynomial ∈ before.polynomialPool ∧ certificate.Realizes ∧
          after =
            { before with
              polynomialPool := before.polynomialPool ++ [certificate.outputPolynomial]
              reductumCertificateCodes := before.reductumCertificateCodes ++ [code] }
  | .exactAlgebraicSign, before, after => after = before
  | .emitCellCertificate code, before, after =>
      ∃ certificate : EffectiveCertifiedCADCell r,
        Encodable.encode certificate = code ∧
          (∀ required ∈ certificate.polynomialCodes,
            required.AvailableIn before.polynomialPool) ∧
          after =
            { before with cellCertificateCodes := before.cellCertificateCodes ++ [code] }
  | .emitPrefixProjectionCertificate code, before, after =>
      ∃ certificate : EffectiveCADPrefixProjectionCertificate r,
        Encodable.encode certificate = code ∧
          (∀ required ∈ certificate.polynomialCodes,
            required.AvailableIn before.polynomialPool) ∧
          after =
            { before with prefixProjectionCertificateCodes :=
                before.prefixProjectionCertificateCodes ++ [code] }
  | .emitTruthRow code, before, after =>
      ∃ row : EffectiveCADTruthRow r,
        Encodable.encode row = code ∧
          (∀ required ∈ row.polynomialCodes,
            required.AvailableIn before.polynomialPool) ∧
          after = { before with truthRowCodes := before.truthRowCodes ++ [code] }
  | .emitRetentionRow code, before, after =>
      ∃ row : EffectiveCADRetentionRow r,
        Encodable.encode row = code ∧
          (∀ required ∈ row.polynomialCodes,
            required.AvailableIn before.polynomialPool) ∧
          after = { before with retentionRowCodes := before.retentionRowCodes ++ [code] }

/-- Execution of the displayed primitive-operation list, with no hidden uncharged transitions. -/
def EffectivePrimitiveProgramRuns {r : ℕ} :
    List EffectiveRealAlgebraicPrimitiveOperation → EffectivePolynomialMachineState r →
      EffectivePolynomialMachineState r → Prop
  | [], initial, final => final = initial
  | operation :: operations, initial, final =>
      ∃ next, EffectivePrimitiveTransition operation initial next ∧
        EffectivePrimitiveProgramRuns operations next final

/-- A displayed polynomial family is already present, extensionally, in a family register created
by the supplied input or by an earlier trace step. -/
def EffectivePolynomialFamilyAvailable {r : ℕ}
    (required : List (EffectivePolynomialCode r))
    (registers : List (List (EffectivePolynomialCode r))) : Prop :=
  ∃ registered ∈ registers,
    effectiveDecodedPolynomialFamily registered = effectiveDecodedPolynomialFamily required

/-- Operation-specific mathematical semantics for the input and output families of a high-level
trace step. This connects the encoded trace to the exact Gröbner, elimination, projection, and
CAD operations whose primitive execution is charged. -/
def EffectiveAlgebraTraceStep.SemanticallyCorrect {r : ℕ}
    (step : EffectiveAlgebraTraceStep r) : Prop :=
  match step.operation, step.inputFamilies, step.outputFamilies, step.activeVariable with
  | .buchberger, [input], [output], _ =>
      ∃ normalForm, IsExactGroebnerBasis step.variableOrder
        (effectiveDecodedPolynomialFamily input) (effectiveDecodedPolynomialFamily output)
        normalForm
  | .elimination, [input], [output], _ =>
      IsEffectiveEliminationVariableOrder step.variableOrder
          step.retainedVariables.toFinset ∧
        IsExactEliminationBasis (effectiveDecodedPolynomialFamily input)
          step.retainedVariables.toFinset (effectiveDecodedPolynomialFamily output)
  | .idealIntersection, [left, right], [output], _ =>
      IsExactIdealIntersectionBasis (effectiveDecodedPolynomialFamily left)
        (effectiveDecodedPolynomialFamily right) (effectiveDecodedPolynomialFamily output)
  | .saturation, [input, [saturating]], [output], _ =>
      IsExactSaturationBasis (effectiveDecodedPolynomialFamily input) saturating.toPolynomial
        (effectiveDecodedPolynomialFamily output)
  | .reductaGeneration, [input], [output], some x =>
      effectiveDecodedRealPolynomialFamily output =
          cadReductaFamily x (effectiveDecodedRealPolynomialFamily input) ∧
        step.ReductaOutputsExactlyCharged input output x
  | .coefficientProjection, [input], [output], some x =>
      effectiveDecodedRealPolynomialFamily output =
        cadCoefficients x (effectiveDecodedRealPolynomialFamily input)
  | .discriminantProjection, [input], [output], some x =>
      effectiveDecodedRealPolynomialFamily output =
        cadDiscriminants x (effectiveDecodedRealPolynomialFamily input)
  | .principalSubresultantProjection, [input], [output], some x =>
      effectiveDecodedRealPolynomialFamily output =
        cadPrincipalSubresultants x (effectiveDecodedRealPolynomialFamily input)
  | .projectionClosure, [current, coefficients, discriminants, subresultants], [output], some _ =>
      effectiveDecodedRealPolynomialFamily output =
        effectiveDecodedRealPolynomialFamily current ∪
          effectiveDecodedRealPolynomialFamily coefficients ∪
            effectiveDecodedRealPolynomialFamily discriminants ∪
              effectiveDecodedRealPolynomialFamily subresultants
  | .projectionClosure, [input], [output], none =>
      effectiveDecodedRealPolynomialFamily output =
        generatedCADProjectionFamily step.variableOrder
          (effectiveDecodedRealPolynomialFamily input)
  | .rootIsolation, [_], [], some _ =>
      step.producedCellCertificateCodes ≠ []
  | .sectionLifting, [_], [], some _ =>
      step.producedCellCertificateCodes ≠ []
  | .sectorLifting, [_], [], some _ =>
      step.producedCellCertificateCodes ≠ []
  | .prefixCellProjection, [_], [], _ =>
      step.producedPrefixProjectionCertificateCodes ≠ []
  | .signConditionTruth, [_], [], _ =>
      step.producedTruthRowCodes ≠ []
  | .witnessCellRetention, [_], [], _ =>
      step.producedRetentionRowCodes ≠ []
  | _, _, _, _ => False

/-- One high-level trace step runs from the previous global state. No step can introduce a fresh
input family: every input must already be registered extensionally. Its named semantic operation
is correct, its primitive program starts from that same state, and every displayed output is
available in the resulting pool. The pool may additionally retain charged intermediate results. -/
def EffectiveAlgebraTraceStep.Runs {r : ℕ} (step : EffectiveAlgebraTraceStep r)
    (before after : EffectivePolynomialMachineState r) : Prop :=
  step.SemanticallyCorrect ∧
    step.ReductumPrimitiveCodesExact ∧
    (∀ family ∈ step.inputFamilies,
      EffectivePolynomialFamilyAvailable family before.familyRegisters) ∧
    ∃ primitiveFinal,
      EffectivePrimitiveProgramRuns step.primitiveOperations before primitiveFinal ∧
      (∀ output ∈ step.outputFamilies.flatten,
        output.AvailableIn primitiveFinal.polynomialPool) ∧
      primitiveFinal.reductumCertificateCodes =
        before.reductumCertificateCodes ++ step.producedReductumCertificateCodes ∧
      primitiveFinal.cellCertificateCodes =
        before.cellCertificateCodes ++ step.producedCellCertificateCodes ∧
      primitiveFinal.prefixProjectionCertificateCodes =
        before.prefixProjectionCertificateCodes ++
          step.producedPrefixProjectionCertificateCodes ∧
      primitiveFinal.truthRowCodes = before.truthRowCodes ++ step.producedTruthRowCodes ∧
      primitiveFinal.retentionRowCodes =
        before.retentionRowCodes ++ step.producedRetentionRowCodes ∧
      after =
        { primitiveFinal with
          familyRegisters := before.familyRegisters ++ step.outputFamilies }

/-- The whole symbolic trace is one continuous bounded execution. Each step consumes exactly the
state produced by its predecessor; in particular no per-step polynomial pool is reset or supplied
afresh. -/
def EffectiveAlgebraTraceRuns {r : ℕ} :
    List (EffectiveAlgebraTraceStep r) → EffectivePolynomialMachineState r →
      EffectivePolynomialMachineState r → Prop
  | [], initial, final => final = initial
  | step :: steps, initial, final =>
      ∃ next, step.Runs initial next ∧ EffectiveAlgebraTraceRuns steps next final

/-- A trace step at the displayed position has the exact operation, code-family boundary, and
active CAD variable required by one projection round. -/
def EffectiveAlgebraTraceStep.AtProjectionIndex {r : ℕ}
    (steps : List (EffectiveAlgebraTraceStep r)) (index : ℕ)
    (operation : EffectiveAlgebraTraceOperation)
    (inputs outputs : List (List (EffectivePolynomialCode r)))
    (x : Fin r) : Prop :=
  ∃ step, steps[index]? = some step ∧ step.Links operation inputs outputs ∧
    step.activeVariable = some x

/-- Exact ordered BPR projection rounds.  Each round first registers all reducta of the current
accumulated family, then computes coefficients, discriminants, and principal subresultants from
that same registered reducta family, and finally registers the current family together with their
union.  The next round consumes that registered output directly, exactly matching the `foldl`
defining `generatedCADProjectionFamily`; no fresh uncharged family is introduced between rounds.

The natural `startIndex` makes the data-flow order explicit inside the one continuous trace; the
next round begins strictly after the current assembly step. -/
def EffectiveCADProjectionRoundChain {r : ℕ}
    (trace : List (EffectiveAlgebraTraceStep r)) :
    List (Fin r) → List (EffectivePolynomialCode r) →
      List (EffectivePolynomialCode r) → ℕ → Prop
  | [], current, finalFamily, _ =>
      effectiveDecodedRealPolynomialFamily finalFamily =
        effectiveDecodedRealPolynomialFamily current
  | x :: xs, current, finalFamily, startIndex =>
      ∃ reducta coefficients discriminants subresultants nextAccumulated,
        ∃ reductaIndex coefficientIndex discriminantIndex subresultantIndex assemblyIndex,
          startIndex ≤ reductaIndex ∧ reductaIndex < coefficientIndex ∧
          coefficientIndex < discriminantIndex ∧ discriminantIndex < subresultantIndex ∧
          subresultantIndex < assemblyIndex ∧
          EffectiveAlgebraTraceStep.AtProjectionIndex trace reductaIndex
            .reductaGeneration [current] [reducta] x ∧
          EffectiveAlgebraTraceStep.AtProjectionIndex trace coefficientIndex
            .coefficientProjection [reducta] [coefficients] x ∧
          EffectiveAlgebraTraceStep.AtProjectionIndex trace discriminantIndex
            .discriminantProjection [reducta] [discriminants] x ∧
          EffectiveAlgebraTraceStep.AtProjectionIndex trace subresultantIndex
            .principalSubresultantProjection [reducta] [subresultants] x ∧
          EffectiveAlgebraTraceStep.AtProjectionIndex trace assemblyIndex
            .projectionClosure [current, coefficients, discriminants, subresultants]
              [nextAccumulated] x ∧
          effectiveDecodedRealPolynomialFamily reducta =
            cadReductaFamily x (effectiveDecodedRealPolynomialFamily current) ∧
          effectiveDecodedRealPolynomialFamily coefficients =
            cadCoefficients x (effectiveDecodedRealPolynomialFamily reducta) ∧
          effectiveDecodedRealPolynomialFamily discriminants =
            cadDiscriminants x (effectiveDecodedRealPolynomialFamily reducta) ∧
          effectiveDecodedRealPolynomialFamily subresultants =
            cadPrincipalSubresultants x (effectiveDecodedRealPolynomialFamily reducta) ∧
          effectiveDecodedRealPolynomialFamily nextAccumulated =
            effectiveDecodedRealPolynomialFamily current ∪
              cadProjectionStep x (effectiveDecodedRealPolynomialFamily current) ∧
          EffectiveCADProjectionRoundChain trace xs nextAccumulated finalFamily
            (assemblyIndex + 1)

/-- Discrete output of one terminating general-purpose rational Gröbner/CAD run. -/
structure EffectiveRationalGroebnerCADPayload (r : ℕ) where
  input : List (EffectivePolynomialCode r)
  secondInput : List (EffectivePolynomialCode r)
  saturatingPolynomial : EffectivePolynomialCode r
  groebnerBasis : List (EffectivePolynomialCode r)
  eliminationBasis : List (EffectivePolynomialCode r)
  intersectionBasis : List (EffectivePolynomialCode r)
  saturationBasis : List (EffectivePolynomialCode r)
  projectionFamily : List (EffectivePolynomialCode r)
  variableOrder : List (Fin r)
  retainedVariables : List (Fin r)
  cellCertificates : List (EffectiveCertifiedCADCell r)
  prefixProjectionCertificates : List (EffectiveCADPrefixProjectionCertificate r)
  signRows : List (EffectiveCADTruthRow r)
  retainedCellRows : List (EffectiveCADRetentionRow r)
  trace : List (EffectiveAlgebraTraceStep r)
  deriving Encodable

/-- The symbolic operation count is definitionally the sum of the primitive arithmetic/sign
events recorded by the certified trace; it is not an independently chosen payload field. -/
def EffectiveRationalGroebnerCADPayload.symbolicOperationCount {r : ℕ}
    (payload : EffectiveRationalGroebnerCADPayload r) : ℕ :=
  (payload.trace.map EffectiveAlgebraTraceStep.operationCount).sum

/-- Number of exact root/Thom/cell-sign answers explicitly certified by the payload. -/
def EffectiveRationalGroebnerCADPayload.certifiedSignOperationCount {r : ℕ}
    (payload : EffectiveRationalGroebnerCADPayload r) : ℕ :=
  (payload.cellCertificates.map EffectiveCertifiedCADCell.signOperationCount).sum

/-- Number of exact root/Thom/basic-cell signs stored in all prefix projection artifacts. -/
def EffectiveRationalGroebnerCADPayload.prefixProjectionSignOperationCount {r : ℕ}
    (payload : EffectiveRationalGroebnerCADPayload r) : ℕ :=
  (payload.prefixProjectionCertificates.map
    EffectiveCADPrefixProjectionCertificate.signOperationCount).sum

/-- Two assignments agree on the coordinates retained after witness elimination. -/
def SameOnEffectiveCoordinates {r : ℕ} (keep : Finset (Fin r))
    (x y : CADSpace r) : Prop :=
  ∀ i ∈ keep, x i = y i

/-- Real sign-condition set associated with rational polynomial input. -/
def effectiveRationalSignConditionSet {r : ℕ}
    (equations nonnegative positive : Finset (MvPolynomial (Fin r) ℚ)) : Set (CADSpace r) :=
  signConditionSet (rationalPolynomialFamilyToReal equations)
    (rationalPolynomialFamilyToReal nonnegative) (rationalPolynomialFamilyToReal positive)

/-- A complete semantically certified output of the general effective algorithms. The machine
halts with the exact encoding of the displayed finite payload. Its fuel is deliberately unrelated
to `payload.symbolicOperationCount`, which counts the primitive rational-arithmetic and exact
algebraic-sign events recorded in the symbolic trace. -/
structure EffectiveRationalGroebnerCADResult {r : ℕ}
    (input secondInput : Finset (MvPolynomial (Fin r) ℚ))
    (order : List (Fin r)) (keep : Finset (Fin r))
    (saturating : MvPolynomial (Fin r) ℚ) where
  groebnerBasis : Finset (MvPolynomial (Fin r) ℚ)
  eliminationBasis : Finset (MvPolynomial (Fin r) ℚ)
  intersectionBasis : Finset (MvPolynomial (Fin r) ℚ)
  saturationBasis : Finset (MvPolynomial (Fin r) ℚ)
  projectionFamily : Finset (MvPolynomial (Fin r) ℚ)
  normalForm : MvPolynomial (Fin r) ℚ → MvPolynomial (Fin r) ℚ
  groebner_exact : IsExactGroebnerBasis order (input ∪ secondInput) groebnerBasis normalForm
  elimination_exact : IsExactEliminationBasis (input ∪ secondInput) keep eliminationBasis
  /-- Cox--Little--O'Shea's Closure Theorem, after coefficient extension from
  `ℚ` to `ℂ`.  Ideal equality alone does not imply this geometric statement
  without the algebraically closed elimination-closure argument. -/
  complex_projection_closure_exact :
    IsExactComplexProjectionClosure (input ∪ secondInput) keep eliminationBasis
  intersection_exact : IsExactIdealIntersectionBasis input secondInput intersectionBasis
  saturation_exact : IsExactSaturationBasis (input ∪ secondInput) saturating saturationBasis
  projection_exact : rationalPolynomialFamilyToReal projectionFamily =
    generatedCADProjectionFamily order
      (rationalPolynomialFamilyToReal (input ∪ secondInput))
  cellCount : ℕ
  cell : Fin cellCount → Set (CADSpace r)
  cellCertificate : Fin cellCount → EffectiveCertifiedCADCell r
  adapted_cad : IsAdaptedCAD
    (rationalPolynomialFamilyToReal (input ∪ secondInput)) order cell
  cell_certificate_exact : ∀ i,
    (cellCertificate i).Realizes (input ∪ secondInput)
      (input ∪ secondInput ∪ projectionFamily) order (cell i)
  /-- The exact cell obtained by erasing an arbitrary prefix of the supplied lifting order. -/
  prefixProjectedCell : List (Fin r) → Fin cellCount → Set (CADSpace r)
  prefix_projected_cell_exact : ∀ eliminated retained,
    order = eliminated ++ retained → ∀ i,
      prefixProjectedCell eliminated i = effectiveCADErasePrefix eliminated '' cell i
  truthValue :
    Finset (MvPolynomial (Fin r) ℚ) → Finset (MvPolynomial (Fin r) ℚ) →
      Finset (MvPolynomial (Fin r) ℚ) → Fin cellCount → Bool
  truth_exact : ∀ equations nonnegative positive,
    equations ⊆ input ∪ secondInput → nonnegative ⊆ input ∪ secondInput →
      positive ⊆ input ∪ secondInput → ∀ i,
      (truthValue equations nonnegative positive i = true ↔
        cell i ⊆ effectiveRationalSignConditionSet equations nonnegative positive)
  retainedCells :
    Finset (MvPolynomial (Fin r) ℚ) → Finset (MvPolynomial (Fin r) ℚ) →
      Finset (MvPolynomial (Fin r) ℚ) → Finset (Fin cellCount)
  retained_exact : ∀ equations nonnegative positive,
    equations ⊆ input ∪ secondInput → nonnegative ⊆ input ∪ secondInput →
      positive ⊆ input ∪ secondInput → ∀ i,
      (i ∈ retainedCells equations nonnegative positive ↔
        truthValue equations nonnegative positive i = true)
  witness_projection_exact : ∀ equations nonnegative positive,
    equations ⊆ input ∪ secondInput → nonnegative ⊆ input ∪ secondInput →
      positive ⊆ input ∪ secondInput → ∀ x,
      ((∃ y ∈ effectiveRationalSignConditionSet equations nonnegative positive,
          SameOnEffectiveCoordinates keep x y) ↔
        ∃ i ∈ retainedCells equations nonnegative positive, ∃ y ∈ cell i,
          SameOnEffectiveCoordinates keep x y)
  payload : EffectiveRationalGroebnerCADPayload r
  encoded_input : EffectivePolynomialCodesRealize payload.input input
  encoded_second_input : EffectivePolynomialCodesRealize payload.secondInput secondInput
  encoded_saturating : payload.saturatingPolynomial.toPolynomial = saturating
  encoded_groebner : EffectivePolynomialCodesRealize payload.groebnerBasis groebnerBasis
  encoded_elimination : EffectivePolynomialCodesRealize payload.eliminationBasis eliminationBasis
  encoded_intersection : EffectivePolynomialCodesRealize payload.intersectionBasis intersectionBasis
  encoded_saturation : EffectivePolynomialCodesRealize payload.saturationBasis saturationBasis
  encoded_projection : EffectivePolynomialCodesRealize payload.projectionFamily projectionFamily
  encoded_order : payload.variableOrder = order
  encoded_retained_variables :
    payload.retainedVariables.Nodup ∧ payload.retainedVariables.toFinset = keep
  encoded_cells : payload.cellCertificates = List.ofFn cellCertificate
  /-- Every emitted prefix artifact is source-exact, realizes the dropped recursive geometry over
  the corresponding stage family, presents the projected cell by signs from the decoded
  input/generated family, and links exactly to all truth and retention rows for its source. -/
  encoded_prefix_projection_certificates_sound :
    ∀ certificate ∈ payload.prefixProjectionCertificates,
      ∃ i : Fin cellCount,
        order = certificate.eliminatedVariables ++ certificate.retainedVariables ∧
        certificate.sourceCellIndex = i.val ∧
        certificate.sourceCellCertificateCode = Encodable.encode (cellCertificate i) ∧
        certificate.projectedGeometryCode = Encodable.encode certificate.projectedGeometry ∧
        certificate.projectedGeometry.Realizes
          (effectiveCADFamilyAfterPrefix certificate.eliminatedVariables
            (rationalPolynomialFamilyToReal (input ∪ secondInput)))
          certificate.retainedVariables
          (prefixProjectedCell certificate.eliminatedVariables i) ∧
        certificate.basicSignCondition.Realizes
          certificate.eliminatedVariables certificate.retainedVariables
          (effectiveCADFamilyAfterPrefix certificate.eliminatedVariables
            (rationalPolynomialFamilyToReal (input ∪ secondInput)))
          (prefixProjectedCell certificate.eliminatedVariables i) ∧
        certificate.truthRowCodes =
          (payload.signRows.filter fun row => row.cellIndex = i.val).map Encodable.encode ∧
        certificate.retentionRowCodes =
          (payload.retainedCellRows.filter fun row =>
            i.val ∈ row.retainedCellIndices).map Encodable.encode
  /-- Every split of the lifting order and every source cell has an emitted generic prefix
  certificate. -/
  encoded_prefix_projection_certificates_complete : ∀ eliminated retained,
    order = eliminated ++ retained → ∀ i : Fin cellCount,
      ∃ certificate ∈ payload.prefixProjectionCertificates,
        certificate.eliminatedVariables = eliminated ∧
        certificate.retainedVariables = retained ∧
        certificate.sourceCellIndex = i.val
  encoded_truth_rows_sound : ∀ row ∈ payload.signRows,
    ∃ equations nonnegative positive,
      row.query.Realizes equations nonnegative positive ∧
      equations ⊆ input ∪ secondInput ∧ nonnegative ⊆ input ∪ secondInput ∧
      positive ⊆ input ∪ secondInput ∧
      ∃ i : Fin cellCount,
        row.cellIndex = i.val ∧ row.truth = truthValue equations nonnegative positive i
  encoded_truth_rows_complete : ∀ equations nonnegative positive,
    equations ⊆ input ∪ secondInput → nonnegative ⊆ input ∪ secondInput →
      positive ⊆ input ∪ secondInput → ∀ i,
      ∃ row ∈ payload.signRows,
        row.query.Realizes equations nonnegative positive ∧
        row.cellIndex = i.val ∧ row.truth = truthValue equations nonnegative positive i
  encoded_retained_rows_sound : ∀ row ∈ payload.retainedCellRows,
    ∃ equations nonnegative positive,
      row.query.Realizes equations nonnegative positive ∧
      equations ⊆ input ∪ secondInput ∧ nonnegative ⊆ input ∪ secondInput ∧
      positive ⊆ input ∪ secondInput ∧
      row.retainedCellIndices.Nodup ∧
      (∀ index ∈ row.retainedCellIndices, index < cellCount) ∧
      ∀ i : Fin cellCount,
        (i.val ∈ row.retainedCellIndices ↔
          i ∈ retainedCells equations nonnegative positive)
  encoded_retained_rows_complete : ∀ equations nonnegative positive,
    equations ⊆ input ∪ secondInput → nonnegative ⊆ input ∪ secondInput →
      positive ⊆ input ∪ secondInput →
      ∃ row ∈ payload.retainedCellRows,
        row.query.Realizes equations nonnegative positive ∧
        row.retainedCellIndices.Nodup ∧
        (∀ index ∈ row.retainedCellIndices, index < cellCount) ∧
        ∀ i : Fin cellCount,
          (i.val ∈ row.retainedCellIndices ↔
            i ∈ retainedCells equations nonnegative positive)
  trace_cell_outputs_exact :
    (payload.trace.flatMap fun step => step.producedCellCertificateCodes) =
      payload.cellCertificates.map Encodable.encode
  trace_prefix_projection_outputs_exact :
    (payload.trace.flatMap fun step => step.producedPrefixProjectionCertificateCodes) =
      payload.prefixProjectionCertificates.map Encodable.encode
  trace_prefix_projection_certificates_linked :
    ∀ certificate ∈ payload.prefixProjectionCertificates,
      ∃ step ∈ payload.trace,
        step.Links .prefixCellProjection
          [payload.input ++ payload.secondInput ++ payload.projectionFamily] [] ∧
        Encodable.encode certificate ∈ step.producedPrefixProjectionCertificateCodes
  trace_truth_outputs_exact :
    (payload.trace.flatMap fun step => step.producedTruthRowCodes) =
      payload.signRows.map Encodable.encode
  trace_retention_outputs_exact :
    (payload.trace.flatMap fun step => step.producedRetentionRowCodes) =
      payload.retainedCellRows.map Encodable.encode
  trace_buchberger : ∃ step ∈ payload.trace,
    step.Links .buchberger [payload.input ++ payload.secondInput] [payload.groebnerBasis]
  trace_elimination : ∃ step ∈ payload.trace,
    step.Links .elimination [payload.groebnerBasis] [payload.eliminationBasis]
  trace_intersection : ∃ step ∈ payload.trace,
    step.Links .idealIntersection [payload.input, payload.secondInput]
      [payload.intersectionBasis]
  trace_saturation : ∃ step ∈ payload.trace,
    step.Links .saturation
      [payload.input ++ payload.secondInput, [payload.saturatingPolynomial]]
      [payload.saturationBasis]
  /-- Every variable in the supplied CAD order is processed by one ordered, data-dependent
  reducta/coefficient/discriminant/subresultant round.  Each assembly step registers the
  accumulated family consumed by the next round, and the final registered family is exactly the
  payload projection family, so the closure cannot bypass the displayed rounds. -/
  trace_projection_rounds :
    EffectiveCADProjectionRoundChain payload.trace payload.variableOrder
      (payload.input ++ payload.secondInput) payload.projectionFamily 0
  trace_projection : ∃ step ∈ payload.trace,
    step.Links .projectionClosure [payload.input ++ payload.secondInput]
      [payload.projectionFamily]
  trace_root_stage_present :
    (∃ certificate ∈ payload.cellCertificates,
      certificate.geometry.RequiresRootIsolation) →
      ∃ step ∈ payload.trace, step.operation = .rootIsolation
  trace_section_stage_present :
    (∃ certificate ∈ payload.cellCertificates, certificate.geometry.ContainsSection) →
      ∃ step ∈ payload.trace, step.operation = .sectionLifting
  trace_sector_stage_present :
    (∃ certificate ∈ payload.cellCertificates, certificate.geometry.ContainsSector) →
      ∃ step ∈ payload.trace, step.operation = .sectorLifting
  trace_prefix_projection_stage_present : payload.prefixProjectionCertificates ≠ [] →
    ∃ step ∈ payload.trace, step.operation = .prefixCellProjection
  trace_truth_stage_present : payload.signRows ≠ [] →
    ∃ step ∈ payload.trace, step.operation = .signConditionTruth
  trace_retention_stage_present : payload.retainedCellRows ≠ [] →
    ∃ step ∈ payload.trace, step.operation = .witnessCellRetention
  trace_execution_exact : ∃ finalState,
    EffectiveAlgebraTraceRuns payload.trace
      ⟨effectiveCanonicalPolynomialPool r ++ payload.input ++ payload.secondInput ++
          [payload.saturatingPolynomial],
        [payload.input, payload.secondInput, payload.input ++ payload.secondInput,
          [payload.saturatingPolynomial]], [], [], [], [], []⟩
      finalState ∧
    (∀ required ∈
        payload.input ++ payload.secondInput ++ [payload.saturatingPolynomial] ++
          payload.groebnerBasis ++ payload.eliminationBasis ++ payload.intersectionBasis ++
          payload.saturationBasis ++ payload.projectionFamily,
      required.AvailableIn finalState.polynomialPool) ∧
    finalState.familyRegisters =
      [payload.input, payload.secondInput, payload.input ++ payload.secondInput,
        [payload.saturatingPolynomial]] ++
        (payload.trace.flatMap fun step => step.outputFamilies) ∧
    finalState.reductumCertificateCodes =
      payload.trace.flatMap (fun step => step.producedReductumCertificateCodes) ∧
    finalState.cellCertificateCodes = payload.cellCertificates.map Encodable.encode ∧
    finalState.prefixProjectionCertificateCodes =
      payload.prefixProjectionCertificates.map Encodable.encode ∧
    finalState.truthRowCodes = payload.signRows.map Encodable.encode ∧
    finalState.retentionRowCodes = payload.retainedCellRows.map Encodable.encode
  trace_artifact_outputs_charged : ∀ step ∈ payload.trace,
    step.ArtifactOutputsCharged
  trace_artifact_kinds_correct : ∀ step ∈ payload.trace,
    step.ArtifactKindsCorrect
  trace_sign_queries_charged : ∀ step ∈ payload.trace,
    step.operation ∈ [.rootIsolation, .prefixCellProjection, .signConditionTruth,
        .witnessCellRetention] →
      .exactAlgebraicSign ∈ step.primitiveOperations
  trace_certified_sign_operations_charged :
    payload.certifiedSignOperationCount + payload.prefixProjectionSignOperationCount +
        payload.signRows.length + payload.retainedCellRows.length ≤
    (payload.trace.flatMap fun step => step.primitiveOperations).count .exactAlgebraicSign
  trace_steps_nonempty : ∀ step ∈ payload.trace, step.primitiveOperations ≠ []
  machineCode : Nat.Partrec.Code
  machineFuel : ℕ
  machine_halts : machineCode.evaln machineFuel
    (Encodable.encode (r, payload.input, payload.secondInput, payload.saturatingPolynomial,
      payload.variableOrder, payload.retainedVariables)) = some (Encodable.encode payload)

/-- One fully supplied rational real-CAD/QE job. -/
structure EffectiveRationalCADJob where
  r : ℕ
  suppliedInput : List (EffectivePolynomialCode r)
  suppliedSecondInput : List (EffectivePolynomialCode r)
  suppliedSaturating : EffectivePolynomialCode r
  order : List (Fin r)
  suppliedRetainedVariables : List (Fin r)
  input : Finset (MvPolynomial (Fin r) ℚ)
  secondInput : Finset (MvPolynomial (Fin r) ℚ)
  keep : Finset (Fin r)
  saturating : MvPolynomial (Fin r) ℚ
  input_realizes : EffectivePolynomialCodesRealize suppliedInput input
  second_input_realizes :
    EffectivePolynomialCodesRealize suppliedSecondInput secondInput
  saturating_realizes : suppliedSaturating.toPolynomial = saturating
  retained_nodup : suppliedRetainedVariables.Nodup
  retained_realizes : suppliedRetainedVariables.toFinset = keep
  elimination_order : IsEffectiveEliminationVariableOrder order keep

/-- A rational CAD/QE job built from the exact ideal-intersection basis emitted by a completed
dependent elimination pipeline.  The CAD ambient may be larger than the observable-intersection
ambient because later real source presentations can add witness and loading coordinates.
`intersectionToCAD` is therefore an exact embedding, and `input_from_intersection` says that the
first CAD input is precisely the computed basis after that injective rename, not an independently
selected Groebner basis.  The CAD job's `secondInput` remains available for the simultaneous real
incidence and sign-query polynomials. -/
structure EffectiveDependentRationalCADJob
    {machineCode : Nat.Partrec.Code}
    {forwardJob reverseJob : EffectiveGroebnerJobOver ℚ}
    {sharedCoordinateRelation : Fin forwardJob.r → Fin reverseJob.r → Prop}
    (pipeline : EffectiveDependentRationalEliminationPipeline machineCode
      forwardJob reverseJob sharedCoordinateRelation) where
  job : EffectiveRationalCADJob
  intersectionToCAD : Fin pipeline.intersectionJob.r ↪ Fin job.r
  input_from_intersection :
    job.input = effectiveRenameRationalFamily intersectionToCAD
      pipeline.intersectionResult.result.intersectionBasis

/-- Input size charged to the rational CAD/QE job. -/
def EffectiveRationalCADJob.sourcePolynomialCount
    (job : EffectiveRationalCADJob) : ℕ :=
  job.input.card + job.secondInput.card + 1

/-- A uniform degree bound for the rational CAD/QE job. -/
def EffectiveRationalCADJob.DegreeBoundedBy
    (job : EffectiveRationalCADJob) (D : ℕ) : Prop :=
  ∀ P ∈ job.input ∪ job.secondInput ∪ {job.saturating}, P.totalDegree ≤ D

/-- Exact rational CAD/QE output tied to the uniform machine code. -/
structure EffectiveRationalCADCompletedJob (machineCode : Nat.Partrec.Code)
    (job : EffectiveRationalCADJob) where
  result : EffectiveRationalGroebnerCADResult job.input job.secondInput job.order
    job.keep job.saturating
  payload_uses_supplied_input : result.payload.input = job.suppliedInput
  payload_uses_supplied_second_input :
    result.payload.secondInput = job.suppliedSecondInput
  payload_uses_supplied_saturating :
    result.payload.saturatingPolynomial = job.suppliedSaturating
  payload_uses_supplied_order : result.payload.variableOrder = job.order
  payload_uses_supplied_retained_variables :
    result.payload.retainedVariables = job.suppliedRetainedVariables
  machine_code_eq : result.machineCode = machineCode

/-- The general Cox--Little--O'Shea Closure Theorem after scalar extension to
the algebraically closed field `ℂ`. It is stated for arbitrary rational input
and retained coordinate blocks and contains no paper-specific object. -/
def RationalComplexEliminationClosureTheorem : Prop :=
  ∀ (r : ℕ) (input output : Finset (MvPolynomial (Fin r) ℚ))
      (keep : Finset (Fin r)),
    IsExactEliminationBasis input keep output →
      IsExactComplexProjectionClosure input keep output

/-- Universal source-matched combined complexity certificate. The constants
and all three uniform machine codes are fixed before every rational or Gaussian-
rational algebra batch and before the rational CAD/QE input. In the dependent
clause, the caller fixes the cross-source shared-coordinate relation before the
two elimination results and their exact intersection result are returned; only
then is a CAD/QE job consuming that pipeline's intersection basis quantified.
The one displayed inequality charges the same returned pipeline and CAD/QE
result together; partial-recursive fuel is deliberately absent from this cost
statement. -/
def UniversalEffectiveCombinedGroebnerCADBound (a b : ℕ) : Prop :=
  1 ≤ a ∧
    ∃ rationalAlgebraMachine gaussianAlgebraMachine rationalCADMachine :
        Nat.Partrec.Code,
      (∀ (rationalJobs : List (EffectiveGroebnerJobOver ℚ))
          (gaussianJobs : List (EffectiveGroebnerJobOver GaussianRational))
          (cadJob : EffectiveRationalCADJob) (N s D : ℕ),
        1 ≤ D →
        effectiveGroebnerBatchSourcePolynomialCount rationalJobs +
              effectiveGroebnerBatchSourcePolynomialCount gaussianJobs +
              cadJob.sourcePolynomialCount ≤ s →
        EffectiveGroebnerBatchInputsBounded rationalJobs N D →
        EffectiveGroebnerBatchInputsBounded gaussianJobs N D →
        cadJob.r ≤ N → cadJob.DegreeBoundedBy D →
          ∃ rationalResults : EffectiveGroebnerBatchResultsOver ℚ
                rationalAlgebraMachine rationalJobs,
            ∃ gaussianResults : EffectiveGroebnerBatchResultsOver GaussianRational
                gaussianAlgebraMachine gaussianJobs,
              ∃ cadResult : EffectiveRationalCADCompletedJob rationalCADMachine cadJob,
                rationalResults.symbolicOperationCount +
                    gaussianResults.symbolicOperationCount +
                    cadResult.result.payload.symbolicOperationCount ≤
                  (max 2 (s * D)) ^ (2 ^ (a * N + b))) ∧
      (∀ (forwardJob reverseJob : EffectiveGroebnerJobOver ℚ)
          (sharedCoordinateRelation : Fin forwardJob.r → Fin reverseJob.r → Prop),
        IsJointlyPresentableSharedCoordinateRelation sharedCoordinateRelation →
          ∃ pipeline : EffectiveDependentRationalEliminationPipeline
              rationalAlgebraMachine forwardJob reverseJob sharedCoordinateRelation,
          ∀ (dependentCADJob : EffectiveDependentRationalCADJob pipeline)
              (N s D : ℕ),
            1 ≤ D →
            forwardJob.sourcePolynomialCount + reverseJob.sourcePolynomialCount +
                  dependentCADJob.job.sourcePolynomialCount ≤ s →
            forwardJob.r ≤ N → reverseJob.r ≤ N →
            dependentCADJob.job.r ≤ N →
            pipeline.DegreeBoundedBy D →
            dependentCADJob.job.DegreeBoundedBy D →
              ∃ cadResult : EffectiveRationalCADCompletedJob rationalCADMachine
                    dependentCADJob.job,
                pipeline.symbolicOperationCount +
                    cadResult.result.payload.symbolicOperationCount ≤
                  (max 2 (s * D)) ^ (2 ^ (a * N + b)))

/-- Backward-compatible public name used by atlas complexity certificates. It
now denotes the single combined algebra-plus-CAD batch bound, not a separate
rational-CAD-only inequality. -/
def UniversalEffectiveRationalGroebnerCADBound (a b : ℕ) : Prop :=
  UniversalEffectiveCombinedGroebnerCADBound a b

/-- The complete general effective interface: uniform exact Gröbner algorithms on supplied
presentations over `ℚ` and `ℚ(i)` and a rational specialization carrying both the algebraically
closed elimination-closure theorem and real CAD, whose actual finite certificate/truth/retention
outputs are produced by its bounded trace. -/
def EffectiveRationalGroebnerCADInterface : Prop :=
  StandardFiniteBlockEliminationOrderInterface ∧
    EffectiveGroebnerAlgorithmOver ℚ ∧
    EffectiveGroebnerAlgorithmOver GaussianRational ∧
    RationalComplexEliminationClosureTheorem ∧
    ∃ a b : ℕ, UniversalEffectiveRationalGroebnerCADBound a b

/-- **Effective rational Gröbner/CAD interface — cited external tool.** For every finite
polynomial presentation over `ℚ` or `ℚ(i)` and every effectively supplied admissible
`MonomialOrder`, the interface
supplies a terminating exact Buchberger/Gröbner computation, exact elimination output whenever
the supplied order has the encoded elimination property, and exact ideal-intersection and
saturation output, including a charged saturation–Gröbner–elimination chain.  It also supplies a
computably realized standard finite block-elimination order for every concrete retained block.
For rational input it supplies the standard Closure Theorem after coefficient extension to `ℂ`:
the elimination-basis zero set is exactly the Zariski closure of the
input zero set's retained-coordinate projection. Its rational real-polynomial specialization
additionally supplies an effective sign-invariant recursively section/sector CAD for the union
of both supplied real sign families, with exact
algebraic-root indices, cellwise sign truth, quantifier elimination by witness-cell retention,
and, for every lifting-order prefix and source cell, an exact erased-prefix cell with dropped-layer
recursive geometry, a finite basic sign presentation, and exact truth/retention-row links. All of
these data are emitted by a finite certified symbolic trace.
Polynomial and order presentations are supplied before output selection; the algorithm codes are
fixed uniformly before those inputs, the supplied order code is required to realize the semantic
monomial order, and injective encodings tie the bounded trace extensionally to every emitted cell
certificate, root/sign row, truth row, and retained-witness row. An artifact-emission transition is
permitted only after every polynomial presentation recursively contained in that artifact has
already been computed extensionally in the trace's polynomial register.

The arithmetic/sign-operation bound has the source-matched form
`(max 2 (s*D))^(2^(a*N+b))`, where natural constants `a ≥ 1` and `b` are chosen by the general
algorithm before every dimension and input family. One combined certificate bounds the sum of a
finite batch of rational algebra traces, a finite batch of Gaussian-rational algebra traces, and
the rational CAD/QE trace; it is not a collection of independently chosen bounds. The same fixed
rational machine and constants certify the dependent execution in which a caller first supplies
a jointly presentable cross-source coordinate relation, then two supplied saturated elimination
jobs finish before their renamed outputs become the two inputs of the ideal-intersection job.
In that dependent clause, the positive `D` is a post-elimination envelope: it bounds the supplied
source jobs, the two actual saturated elimination bases, the resulting intersection job and
intersection basis, and the CAD input job. It is not restricted to the pre-elimination source
degree, and it does not purport to bound the internally generated CAD projection families.
The returned injective renamings identify a forward and reverse coordinate exactly when that
predeclared relation holds. The rational CAD result is adapted to the simultaneous union of its two
supplied real input families. Its recursive lifting uses the shared CAD root operator, so a
globally nonzero polynomial whose specialization at a base point is identically zero contributes
no lifting roots there. Terminating
partial-recursive fuel is a separate cost model and is not compared with that bound.

Sources (`cite:effective-rational-groebner-cad`): Cox–Little–O'Shea, *Ideals, Varieties, and
Algorithms*, 4th ed., Ch. 3 §2, Theorem 3 (Closure Theorem), and Ch. 2; Collins (1975);
Basu–Pollack–Roy, *Algorithms in Real Algebraic Geometry*, Chs. 11 and 14; Basu (2017),
§2.1.2, Thm. 2.4. -/
-- @node: def:effective-rational-groebner-cad-interface
def effectiveRationalGroebnerCADOutput : Prop := EffectiveRationalGroebnerCADInterface

end

/-- General effective-algebra trace operations have a decidable equality test: any two operations
can be effectively determined to be the same or different. -/
add_decl_doc instDecidableEqEffectiveAlgebraTraceOperation

/-- Every general effective-algebra trace operation has an effective numerical encoding and
decoding. -/
add_decl_doc instEncodableEffectiveAlgebraTraceOperation

/-- Every certified effective-algebra trace step, including its input, output, certificate, and
primitive-operation data, has an effective numerical encoding and decoding. -/
add_decl_doc instEncodableEffectiveAlgebraTraceStep

/-- Every finite payload produced by the effective rational Gröbner/CAD computation has an
effective numerical encoding and decoding. -/
add_decl_doc instEncodableEffectiveRationalGroebnerCADPayload

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
