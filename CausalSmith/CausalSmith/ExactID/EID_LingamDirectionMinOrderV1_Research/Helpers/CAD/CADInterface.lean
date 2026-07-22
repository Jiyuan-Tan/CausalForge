/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The cited external interface: cylindrical algebraic decomposition adapted to a finite
# polynomial family, and Tarski–Seidenberg real quantifier elimination

This file **states** — it never proves — the classical external theory the note CITES.  Everything
here is a statement about an **arbitrary** finite family of real polynomials in an **arbitrary**
number of variables: nothing in this file mentions this paper's cumulants, parameters, incidence
sets, or exceptional locus.

That generality is the whole point.  A `cited` node is a *borrowed classical fact*, so its Lean
proposition must encode the **theorem of record**, not a bespoke existence claim about the objects
we happen to want.  Tailoring the cited statement to this paper's objects would make the
source-match vacuously true while smuggling in unproved content — the failure mode the source-match
gate exists to catch.

## Source of record (`cite:bcr-bpr-cad`)

The fact assumed here is the **mathematical** cell-decomposition theorem, *not* a decision
procedure:

* **Bochnak–Coste–Roy**, *Real Algebraic Geometry* (Ergebnisse 36, 1998), §2.3 "Decomposition of
  Semi-algebraic Sets" (the cylindrical sign-invariant decomposition) and **Thm 2.2.1**
  (Tarski–Seidenberg / projection).
* **Basu–Pollack–Roy**, *Algorithms in Real Algebraic Geometry*, **Ch. 5** — Def. 5.1 (cylindrical
  decomposition; section/sector cells), Def. 5.5 (`P`-invariance, "cad *adapted to* `P`"),
  **Thm 5.6** ("for every finite set `P` of polynomials in `R[X₁,…,X_k]` there is a cylindrical
  decomposition of `R^k` adapted to `P`"), Notation 5.15 (the `Elim` projection operator) and
  Thm 5.16 (lifting over an `Elim`-invariant cell).  BPR Ch. 5 is *mathematics*; the algorithms
  live in BPR Ch. 11 and are **not** cited.

This node was previously sourced to Collins (1975).  That was the wrong source of record: Collins'
paper is an **algorithm** (a decision procedure with a computing-time bound), so its statement
carries effectivity/computability content that this `Prop` does not encode — and must not, since
nothing in this development consumes CAD effectivity (we assume only the *existence and structure*
of a sign-invariant cell decomposition).  The BCR/BPR theorems state exactly the existence +
structure fact that is used.

## The statement of record, and how it is encoded

* **Adapted decomposition (existence + sign-invariance).**  For every dimension, every finite family
  `A` and every variable order, a finite cylindrical decomposition into semialgebraic cells exists,
  and every member of `A` has constant sign on every cell (BPR Thm 5.6 + Def. 5.5).
* **Projection family.**  Sign-invariance holds not merely for `A` but for the family the projection
  operator *generates* from `A` — the successive nonzero truncations/reducta, their coefficients and
  discriminants, and their derivative/pair principal subresultants, iterated down the variable order
  (`generatedCADProjectionFamily`; BPR Notation 5.15 + Thm 5.16).
* **Section / sector lifting.**  Every cell is a *recursively lifted* section/sector cell of that
  generated family: at each variable it is the graph of an indexed continuous real-algebraic root
  function, or a sector below the first root, between two consecutive roots, or above the last
  (`IsRecursivelyLiftedCADCell`; BPR Def. 5.1 + Thm 5.16).
* **Decision (set-theoretic) / quantifier elimination.**  Every polynomial sign condition built from
  `A` is decided by the cell a point lies in — each cell is contained in, or disjoint from, the
  condition's solution set (BPR Def. 5.5: a cad adapted to `P` is adapted to every `P`-semialgebraic
  set) — and the projection of a semialgebraic set is semialgebraic (Tarski–Seidenberg).  This is
  *decision by the cells*, a statement about `ℝ^r`; it is **not** a claim that the cells are
  computable.

## Two normalizations, disclosed (neither strengthens the cited content)

1. **Variable order.**  The printed theorems fix the order `X₁,…,X_k` and eliminate `X_k` first.  The
   arbitrary-order form quantified over below is the immediate corollary obtained by *relabelling
   coordinates*, which is why it is stated that way here.
2. **Discriminants.**  BPR's `Elim` lists the principal subresultant coefficients of `(R, ∂R/∂X_k)`
   together with `lcof(R)`; the discriminant is `sRes₀(R, ∂R/∂X_k)` divided by `lcof(R)` up to sign.
   So sign-invariance for BPR's generated family already *implies* sign-invariance for the
   discriminant family named here: including discriminants (the Collins / Arnon–Collins–McCallum
   phrasing of the same operator) demands nothing beyond BPR's `Elim`.

Everything the statements use is defined here, so the interface is self-contained: no free abstract
variable, no class named only in prose.
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Selector
import Mathlib.RingTheory.Polynomial.Resultant.Basic

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ### Semialgebraic subsets of `ℝ^r` -/

/-- The affine space `ℝ^r` the cited decomposition lives in. -/
abbrev CADSpace (r : ℕ) : Type := Fin r → ℝ

/-- A **basic semialgebraic** subset of `ℝ^r`: the common solution set of finitely many polynomial
equations, finitely many non-strict polynomial inequalities and finitely many strict polynomial
inequalities.  These are the sets the cells are cut out by. -/
def IsBasicSemialgebraic {r : ℕ} (S : Set (CADSpace r)) : Prop :=
  ∃ equations nonnegative positive : Finset (MvPolynomial (Fin r) ℝ),
    S = { x | (∀ P ∈ equations, MvPolynomial.eval x P = 0) ∧
              (∀ P ∈ nonnegative, 0 ≤ MvPolynomial.eval x P) ∧
              (∀ P ∈ positive, 0 < MvPolynomial.eval x P) }

/-- A **semialgebraic** subset of `ℝ^r`: a finite union of basic semialgebraic sets. -/
def IsSemialgebraicSet {r : ℕ} (S : Set (CADSpace r)) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (piece : ι → Set (CADSpace r)),
    (∀ i, IsBasicSemialgebraic (piece i)) ∧ S = ⋃ i, piece i

/-! ### The projection phase

The projection operator (BPR Notation 5.15, `Elim`): regard each polynomial as univariate in the
lifting variable, form all of its successive nonzero reducta by deleting the current leading term,
and adjoin the coefficients and discriminant of every reductum together with the principal
subresultants of every reductum against its derivative and of every pair of reducta.  Iterating down
the variable order produces the projection family the decomposition is built from.  These operators
are stated for an arbitrary coordinate index type `σ`; the cited theorem instantiates them at
`σ = Fin r`, and this paper's atlas (`Handles.lean`) instantiates the same operators at its own
incidence coordinates. -/

/-- Regard a multivariate polynomial as a univariate polynomial in the selected CAD lifting
variable, with all other variables retained in its coefficient ring. -/
def cadAsUnivariate {σ : Type} [DecidableEq σ] (x : σ)
    (P : MvPolynomial σ ℝ) : Polynomial (MvPolynomial σ ℝ) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun y => if y = x then Polynomial.X else Polynomial.C (MvPolynomial.X y)) P

/-- Delete the current leading term when `P` is regarded as a polynomial in `x`.  Iterating this
operation gives BPR's successive truncations/reducta. -/
def cadReductum {σ : Type} [DecidableEq σ] (x : σ)
    (P : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  let univariate := cadAsUnivariate x P
  P - univariate.coeff univariate.natDegree *
    MvPolynomial.X x ^ univariate.natDegree

/-- A coefficient lies in the real ground field, rather than depending on any remaining variable.
Using empty variable support makes the predicate decidable for the finite projection algorithm;
over `MvPolynomial σ ℝ` it is equivalent to being a constant polynomial. -/
def IsCADGroundCoefficient {σ : Type} (C : MvPolynomial σ ℝ) : Prop :=
  C.vars = ∅

/-- A nonzero member of the real ground field. -/
def IsCADNonzeroGroundCoefficient {σ : Type} (C : MvPolynomial σ ℝ) : Prop :=
  C ≠ 0 ∧ IsCADGroundCoefficient C

/-- The leading coefficient in the selected lifting variable. -/
def cadLeadingCoefficient {σ : Type} [DecidableEq σ] (x : σ)
    (P : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  (cadAsUnivariate x P).coeff (cadAsUnivariate x P).natDegree

/-- Successive BPR truncations with their exact stopping rule.  A nonzero current reductum is
retained.  Recursion continues only when its leading coefficient is not a nonzero ground-field
constant; zero terminates immediately.  The fuel is the original `x`-degree plus one. -/
def cadReductaAux {σ : Type} [DecidableEq σ] (x : σ) :
    ℕ → MvPolynomial σ ℝ → Finset (MvPolynomial σ ℝ)
  | 0, _ => ∅
  | fuel + 1, P =>
      if P = 0 then ∅
      else insert P (if IsCADNonzeroGroundCoefficient (cadLeadingCoefficient x P) then ∅
        else cadReductaAux x fuel (cadReductum x P))

/-- Every relevant nonzero truncation/reductum of `P` in the selected variable, exactly stopping
at a nonzero ground-field leading coefficient as in BPR's `Tru(P)`. -/
def cadReducta {σ : Type} [DecidableEq σ] (x : σ)
    (P : MvPolynomial σ ℝ) : Finset (MvPolynomial σ ℝ) :=
  cadReductaAux x ((cadAsUnivariate x P).natDegree + 1) P

/-- The nonzero reducta of every polynomial in a finite stage family. -/
def cadReductaFamily {σ : Type} [DecidableEq σ] (x : σ)
    (family : Finset (MvPolynomial σ ℝ)) : Finset (MvPolynomial σ ℝ) :=
  family.biUnion (cadReducta x)

/-- Every generated reductum is nonzero. -/
theorem mem_cadReducta_ne_zero {σ : Type} [DecidableEq σ] {x : σ}
    {P R : MvPolynomial σ ℝ} (hR : R ∈ cadReducta x P) : R ≠ 0 := by
  simp only [cadReducta] at hR
  generalize (cadAsUnivariate x P).natDegree + 1 = fuel at hR
  induction fuel generalizing P with
  | zero => simp [cadReductaAux] at hR
  | succ fuel ih =>
      simp only [cadReductaAux] at hR
      split at hR
      · simp_all
      · simp only [Finset.mem_insert] at hR
        rcases hR with rfl | hR
        · assumption
        · split at hR
          · simp_all
          · exact ih hR

/-- A nonzero polynomial occurs as the zeroth member of its own reducta family. -/
theorem self_mem_cadReducta {σ : Type} [DecidableEq σ] (x : σ)
    {P : MvPolynomial σ ℝ} (hP : P ≠ 0) : P ∈ cadReducta x P := by
  simp [cadReducta, cadReductaAux, hP]

/-- The zero polynomial contributes no reductum. -/
@[simp] theorem cadReducta_zero {σ : Type} [DecidableEq σ] (x : σ) :
    cadReducta x (0 : MvPolynomial σ ℝ) = ∅ := by
  simp [cadReducta, cadReductaAux, cadAsUnivariate]

/-- The empty stage has no reducta. -/
@[simp] theorem cadReductaFamily_empty {σ : Type} [DecidableEq σ] (x : σ) :
    cadReductaFamily x (∅ : Finset (MvPolynomial σ ℝ)) = ∅ := by
  simp [cadReductaFamily]

/-- Focused zero-polynomial receipt: filtering is preserved after taking a family union. -/
@[simp] theorem cadReductaFamily_singleton_zero {σ : Type} [DecidableEq σ] (x : σ) :
    cadReductaFamily x ({0} : Finset (MvPolynomial σ ℝ)) = ∅ := by
  simp [cadReductaFamily]

/-- The coefficient projection operation in variable `x`. -/
def cadCoefficients {σ : Type} [DecidableEq σ] (x : σ)
    (family : Finset (MvPolynomial σ ℝ)) : Finset (MvPolynomial σ ℝ) :=
  family.biUnion fun P =>
    (Finset.range ((cadAsUnivariate x P).natDegree + 1)).image
      fun k => (cadAsUnivariate x P).coeff k

/-- The discriminant projection operation in variable `x`. -/
def cadDiscriminants {σ : Type} [DecidableEq σ] (x : σ)
    (family : Finset (MvPolynomial σ ℝ)) : Finset (MvPolynomial σ ℝ) :=
  family.image fun P => (cadAsUnivariate x P).discr

/-- The square leading block of the Sylvester--Habicht matrix at index `j`.  Its rows are the
coefficient vectors of `X^(q-j-1) P, ..., P, Q, ..., X^(p-j-1) Q` in the descending monomial basis;
the first `p+q-2j` columns give the principal subresultant coefficient. -/
def cadPrincipalSubresultantMatrix {R : Type} [CommRing R]
    (P Q : Polynomial R) (p q j : ℕ) :
    Matrix (Fin (p + q - 2 * j)) (Fin (p + q - 2 * j)) R :=
  fun row column =>
    let targetDegree := p + q - j - 1 - column.val
    if hrow : row.val < q - j then
      let shift := q - j - 1 - row.val
      if shift ≤ targetDegree then P.coeff (targetDegree - shift) else 0
    else
      let shift := row.val - (q - j)
      if shift ≤ targetDegree then Q.coeff (targetDegree - shift) else 0

/-- The unsigned principal subresultant coefficient at index `j`.  BPR uses the signed
normalization `sRes_j`; the two differ by a fixed unit `±1`, so they have identical zero loci and
constant-sign partitions.  This determinant is the actual Sylvester--Habicht principal minor, not
`Polynomial.resultant` with artificially reduced degree parameters. -/
def cadPrincipalSubresultantCoefficient {σ : Type} [DecidableEq σ] (x : σ)
    (P Q : MvPolynomial σ ℝ) (j : ℕ) : MvPolynomial σ ℝ :=
  let univariateP := cadAsUnivariate x P
  let univariateQ := cadAsUnivariate x Q
  (cadPrincipalSubresultantMatrix univariateP univariateQ
    univariateP.natDegree univariateQ.natDegree j).det

/-- In BPR's equal-degree branch, replace `R` by
`lcof(S) R - lcof(R) S`, whose leading term cancels. -/
def cadEqualDegreeCombination {σ : Type} [DecidableEq σ] (x : σ)
    (R S : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  cadLeadingCoefficient x S * R - cadLeadingCoefficient x R * S

/-- Derivative principal subresultants of every reductum, with BPR's exact range
`j = 0, ..., degree(R)-2`. -/
def cadDerivativePrincipalSubresultants {σ : Type} [DecidableEq σ] (x : σ)
    (family : Finset (MvPolynomial σ ℝ)) : Finset (MvPolynomial σ ℝ) :=
  family.biUnion fun R =>
    (Finset.range ((cadAsUnivariate x R).natDegree - 1)).image fun j =>
      cadPrincipalSubresultantCoefficient x R (MvPolynomial.pderiv x R) j

/-- Pair principal subresultants of all reducta.  Unequal degrees put the larger-degree polynomial
first and use indices below the smaller degree.  Equal degrees use BPR's leading-term-cancelling
combination before taking the principal subresultants. -/
def cadPairPrincipalSubresultants {σ : Type} [DecidableEq σ] (x : σ)
    (family : Finset (MvPolynomial σ ℝ)) : Finset (MvPolynomial σ ℝ) :=
  family.biUnion fun R => family.biUnion fun S =>
    let degreeR := (cadAsUnivariate x R).natDegree
    let degreeS := (cadAsUnivariate x S).natDegree
    if degreeS < degreeR then
      (Finset.range degreeS).image fun j => cadPrincipalSubresultantCoefficient x R S j
    else if degreeR < degreeS then
      (Finset.range degreeR).image fun j => cadPrincipalSubresultantCoefficient x S R j
    else
      let reducedR := cadEqualDegreeCombination x R S
      (Finset.range (cadAsUnivariate x reducedR).natDegree).image fun j =>
        cadPrincipalSubresultantCoefficient x S reducedR j

/-- The derivative and pair principal subresultant coefficients required by BPR Notation 5.15.
Ground-field constants are omitted, since their signs are already globally constant. -/
def cadPrincipalSubresultants {σ : Type} [DecidableEq σ] (x : σ)
    (family : Finset (MvPolynomial σ ℝ)) : Finset (MvPolynomial σ ℝ) :=
  (cadDerivativePrincipalSubresultants x family ∪
    cadPairPrincipalSubresultants x family).filter fun C => ¬ IsCADGroundCoefficient C

/-- One projection step (BPR Notation 5.15): coefficients and discriminants of every nonzero
reductum, and all derivative/pair principal subresultants of those reducta. -/
def cadProjectionStep {σ : Type} [DecidableEq σ] (x : σ)
    (family : Finset (MvPolynomial σ ℝ)) : Finset (MvPolynomial σ ℝ) :=
  cadCoefficients x (cadReductaFamily x family) ∪
    cadDiscriminants x (cadReductaFamily x family) ∪
      cadPrincipalSubresultants x (cadReductaFamily x family)

/-- The **cylindrifying family** generated along the supplied order (BPR §11.1): at every round,
retain the family computed so far and adjoin its complete BPR elimination family.  Thus the next
round starts from `fam ∪ cadProjectionStep x fam`, and the final result contains the input,
every nonzero truncation/reductum projection stage, and every later projection of the accumulated
family.  The `foldl` shape is load-bearing: replacing the family at each round would leave only the
last constants and make lifting vacuous.

This accumulated public family is distinct from the recursion-varying family in
`IsRecursivelyLiftedCADCell`: recursive lifting still projects its current stage family once at
each descent. -/
def generatedCADProjectionFamily {σ : Type} [DecidableEq σ]
    (order : List σ) (family : Finset (MvPolynomial σ ℝ)) : Finset (MvPolynomial σ ℝ) :=
  order.foldl (fun fam x => fam ∪ cadProjectionStep x fam) family

/-! ### The base and extension phases: the recursive section/sector cell language -/

/-- Erase the current lifting coordinate before consulting the recursively constructed base cell. -/
def cadEraseCoordinate {σ : Type} [DecidableEq σ] (x : σ) (a : σ → ℝ) : σ → ℝ := Function.update a x 0

/-- The specialization of `P` at the base point `a`, leaving only the lifting coordinate `x`, is
not the zero univariate polynomial.  This is deliberately stronger than the global condition
`P ≠ 0`: a globally nonzero polynomial can nullify after the base coordinates are fixed. -/
def CADSpecializationNonzeroAt {σ : Type} [DecidableEq σ] (x : σ) (a : σ → ℝ)
    (P : MvPolynomial σ ℝ) : Prop :=
  ∃ y : ℝ, MvPolynomial.eval (Function.update a x y) P ≠ 0

/-- The union of the real roots, in the current lifting coordinate, of every polynomial whose
**specialization at the current base point is nonzero**.  A polynomial that specializes
identically to zero in the lifting variable is ignored, as in standard CAD lifting.  This excludes
both a globally zero input and a globally nonzero input nullified on the current base cell; without
the latter guard, `{X₁}` lifted first in `X₀` would contribute all of `ℝ` above the base `X₁ = 0`,
contradicting the finiteness required of algebraic sections.  Sections are selected from this whole
ordered root stack, rather than being required to be the unique root of one polynomial. -/
def cadRealRootsAt {σ : Type} [DecidableEq σ] (x : σ) (family : Finset (MvPolynomial σ ℝ)) (a : σ → ℝ) : Set ℝ :=
  { z | ∃ P ∈ family, CADSpecializationNonzeroAt x a P ∧
      MvPolynomial.eval (Function.update a x z) P = 0 }

/-- If every member of the stage family specializes to the zero univariate polynomial over a base
point, then that base point has no CAD lifting roots. -/
theorem cadRealRootsAt_eq_empty_of_specializes_zero {σ : Type} [DecidableEq σ] (x : σ)
    (family : Finset (MvPolynomial σ ℝ)) (a : σ → ℝ)
    (hzero : ∀ P ∈ family, ∀ z : ℝ, MvPolynomial.eval (Function.update a x z) P = 0) :
    cadRealRootsAt x family a = ∅ := by
  ext z
  simp only [cadRealRootsAt, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨P, hP, ⟨y, hy⟩, -⟩
  exact hy (hzero P hP y)

/-- **Nullified-specialization non-vacuity receipt.**  The globally nonzero polynomial `X₁`
specializes identically to zero in the first lifting coordinate over a base point with `X₁ = 0`,
so it contributes no roots there.  This is the two-variable counterexample that a merely global
`P ≠ 0` guard failed to exclude. -/
theorem cadRealRootsAt_singleton_other_variable_eq_empty (a : Fin 2 → ℝ) (ha : a 1 = 0) :
    cadRealRootsAt (0 : Fin 2) ({MvPolynomial.X 1} : Finset (MvPolynomial (Fin 2) ℝ)) a = ∅ := by
  apply cadRealRootsAt_eq_empty_of_specializes_zero
  intro P hP z
  have hP' : P = MvPolynomial.X (1 : Fin 2) := by simpa using hP
  subst P
  simp [Function.update, ha]

/-- An indexed continuous real-algebraic **section** of the projection family.  `rootIndex` is its
zero-based position in the ordered set of real roots at every point of the recursively lifted base,
so an ordinary selected root of a polynomial with several real roots is permitted; no uniqueness
hypothesis is made. -/
def IsCADAlgebraicRoot {σ : Type} [DecidableEq σ] (x : σ) (base : Set (σ → ℝ)) (rootIndex : ℕ)
    (root : (σ → ℝ) → ℝ) (family : Finset (MvPolynomial σ ℝ)) : Prop :=
  ContinuousOn root base ∧
  ∀ a ∈ base,
    (cadRealRootsAt x family a).Finite ∧
    root a ∈ cadRealRootsAt x family a ∧
    Set.ncard { z ∈ cadRealRootsAt x family a | z < root a } = rootIndex

/-- The selected section is the greatest root in the complete ordered root stack — the boundary of
the upper-unbounded sector. -/
def IsCADLastAlgebraicRoot {σ : Type} [DecidableEq σ] (x : σ) (base : Set (σ → ℝ)) (rootIndex : ℕ)
    (root : (σ → ℝ) → ℝ) (family : Finset (MvPolynomial σ ℝ)) : Prop :=
  IsCADAlgebraicRoot x base rootIndex root family ∧
  ∀ a ∈ base, ∀ z ∈ cadRealRootsAt x family a, z ≤ root a

/-- **Recursive cylindrical section/sector geometry** in the declared variable order — the output of
the section/sector lifting of BPR Def. 5.1 + Thm 5.16.  Over a cell of the base decomposition the
polynomials of the *stage* family have finitely many real roots `ξ_1 < … < ξ_ℓ` in the lifting
coordinate, and the cells above it are exactly: the whole fibre when `ℓ = 0`; otherwise the graph of
an indexed root (a *section*), the sector below the first root, a sector between two consecutive
indexed roots, or the sector above the last root.

Two things are load-bearing here, and both were wrong in an earlier encoding (which made this `Prop`
*unsatisfiable*, hence the cited statement `False`):

* **The family is stage-specific.**  It is threaded through the recursion and *projected* (via
  `cadProjectionStep`) on each descent, exactly as BPR's `C_i(A) = Elim_{X_{i+1}}(C_{i+1}(A))`: roots
  in the lifting coordinate `x` are roots of the family that still involves `x`, while the base is
  decomposed by the family with `x` eliminated.  Passing one fully projected family at every stage is
  not the cited theorem.
* **The `ℓ = 0` cell exists.**  When the stage family has no real root over the base, the cited
  decomposition puts a single cell — the entire fibre — above it.  Omitting this case is what made
  the statement false at, e.g., `r = 1`, `A = ∅`, where the theorem plainly supplies the cell `ℝ`. -/
def IsRecursivelyLiftedCADCell {σ : Type} [DecidableEq σ] :
    Finset (MvPolynomial σ ℝ) → List σ → Set (σ → ℝ) → Prop
  | _, [], cell => cell = { a | ∀ x, a x = 0 }
  | family, x :: xs, cell =>
      ∃ base, IsRecursivelyLiftedCADCell (cadProjectionStep x family) xs base ∧
        (((∀ a ∈ base, cadRealRootsAt x family a = ∅) ∧
            cell = { a | cadEraseCoordinate x a ∈ base }) ∨
         (∃ rootIndex root, IsCADAlgebraicRoot x base rootIndex root family ∧
            cell = { a | cadEraseCoordinate x a ∈ base ∧
              a x = root (cadEraseCoordinate x a) }) ∨
         (∃ upper, IsCADAlgebraicRoot x base 0 upper family ∧
            cell = { a | cadEraseCoordinate x a ∈ base ∧
              a x < upper (cadEraseCoordinate x a) }) ∨
         (∃ lowerIndex lower upper,
            IsCADAlgebraicRoot x base lowerIndex lower family ∧
            IsCADAlgebraicRoot x base (lowerIndex + 1) upper family ∧
            (∀ a ∈ base, lower a < upper a) ∧
            cell = { a | cadEraseCoordinate x a ∈ base ∧
              lower (cadEraseCoordinate x a) < a x ∧
              a x < upper (cadEraseCoordinate x a) }) ∨
         (∃ lowerIndex lower, IsCADLastAlgebraicRoot x base lowerIndex lower family ∧
            cell = { a | cadEraseCoordinate x a ∈ base ∧
              lower (cadEraseCoordinate x a) < a x }))

/-- **Non-vacuity receipt.**  With the empty family in one variable the cited theorem supplies the
single cell `ℝ`, and the cell language now contains it: this is exactly the point at which the
earlier encoding (no `ℓ = 0` case, one fully projected family at every stage) was *unsatisfiable*,
which would have made the cited `Prop` `False`. -/
theorem isRecursivelyLiftedCADCell_univ_of_empty :
    IsRecursivelyLiftedCADCell (∅ : Finset (MvPolynomial (Fin 1) ℝ)) [0] Set.univ := by
  refine ⟨{ a | ∀ x, a x = 0 }, rfl, Or.inl ⟨?_, ?_⟩⟩
  · intro a _
    simp [cadRealRootsAt]
  · ext a
    have hmem : cadEraseCoordinate (0 : Fin 1) a ∈ { b : Fin 1 → ℝ | ∀ x, b x = 0 } := by
      intro x
      fin_cases x
      simp [cadEraseCoordinate]
    simp [hmem]
    simp [cadEraseCoordinate]

/-- **Singleton-zero non-vacuity receipt.**  The identically zero polynomial contributes no section
roots, so the one-variable CAD for the family `{0}` consists of the same root-free whole-fibre cell
as the empty-family decomposition.  This rules out the former counterexample in which `{0}` made
the root stack equal to all of `ℝ`. -/
theorem isRecursivelyLiftedCADCell_univ_of_singleton_zero :
    IsRecursivelyLiftedCADCell ({0} : Finset (MvPolynomial (Fin 1) ℝ)) [0] Set.univ := by
  refine ⟨{ a | ∀ x, a x = 0 }, rfl, Or.inl ⟨?_, ?_⟩⟩
  · intro a _
    apply cadRealRootsAt_eq_empty_of_specializes_zero
    simp
  · ext a
    have hmem : cadEraseCoordinate (0 : Fin 1) a ∈ { b : Fin 1 → ℝ | ∀ x, b x = 0 } := by
      intro x
      fin_cases x
      simp [cadEraseCoordinate]
    simp [hmem]
    simp [cadEraseCoordinate]

/-! ### Cylindrical arrangement, sign invariance, and decision -/

/-- Project onto the coordinates still **live** at a given depth of the lifting order: every
coordinate outside `live` is zeroed.

This is the projection the cited decomposition is cylindrical over, and it must be read off `order`,
not off the natural index numbering.  `IsRecursivelyLiftedCADCell` peels the **head** of the order
first and zeroes it (`cadEraseCoordinate`), so at depth `k` the base cell lives in exactly the
coordinates of `order.drop k`. -/
def cadOrderTruncate {σ : Type} [DecidableEq σ] (live : List σ) (a : σ → ℝ) : σ → ℝ :=
  fun i => if i ∈ live then a i else 0

/-- **Cylindrical arrangement** (the cylindricity condition of BPR Def. 5.1), **relative to the
lifting order**.  At every depth `k` of the order, the projections of any two cells onto the
coordinates still live there (`order.drop k`) are either identical or disjoint — i.e. the cells are
stacked in cylinders over the cells of the induced decomposition of every stage.

The order-relativity is load-bearing.  An earlier encoding fixed cylindricity to the **natural
coordinate-index prefixes** (`cadTruncate`) while `AdaptedCADConstruction` quantifies over *every*
variable order and the recursion lifts along that order.  The two then disagree for all but one
order — and even there they name opposite coordinate sets (index prefix vs. order suffix) — so the
assumed `Prop` was false, not merely over-strong. -/
def IsCylindricallyArranged {σ : Type} [DecidableEq σ] {ι : Type}
    (order : List σ) (cell : ι → Set (σ → ℝ)) : Prop :=
  ∀ (k : ℕ) (i j : ι),
    cadOrderTruncate (order.drop k) '' cell i = cadOrderTruncate (order.drop k) '' cell j ∨
      Disjoint (cadOrderTruncate (order.drop k) '' cell i)
        (cadOrderTruncate (order.drop k) '' cell j)

/-- The polynomial `P` has **constant sign** on `S`. -/
def HasConstantSignOn {r : ℕ} (S : Set (CADSpace r)) (P : MvPolynomial (Fin r) ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S,
    polynomialSign (MvPolynomial.eval x P) = polynomialSign (MvPolynomial.eval y P)

/-- The solution set of a finite system of polynomial sign conditions. -/
def signConditionSet {r : ℕ} (equations nonnegative positive : Finset (MvPolynomial (Fin r) ℝ)) :
    Set (CADSpace r) :=
  { x | (∀ P ∈ equations, MvPolynomial.eval x P = 0) ∧
        (∀ P ∈ nonnegative, 0 ≤ MvPolynomial.eval x P) ∧
        (∀ P ∈ positive, 0 < MvPolynomial.eval x P) }

/-- **A cylindrical algebraic decomposition adapted to the finite family `A`** in the variable order
`order` (BPR Def. 5.1 + Def. 5.5): finitely many nonempty, pairwise disjoint, cylindrically arranged
semialgebraic cells covering `ℝ^r`, obtained by recursive lifting of the *generated projection
family*, on each of which every polynomial of `A` and of the projection family has constant sign, and
which therefore *decide* every sign condition built from `A`. -/
structure IsAdaptedCAD {r : ℕ} {ι : Type} (A : Finset (MvPolynomial (Fin r) ℝ))
    (order : List (Fin r)) (cell : ι → Set (CADSpace r)) : Prop where
  /-- The decomposition has finitely many cells. -/
  finite_cells : Finite ι
  /-- Every cell is nonempty. -/
  nonempty_cell : ∀ i, (cell i).Nonempty
  /-- Every cell is a basic semialgebraic set. -/
  semialgebraic_cell : ∀ i, IsBasicSemialgebraic (cell i)
  /-- Distinct cells are disjoint. -/
  disjoint_cells : Pairwise (Function.onFun Disjoint cell)
  /-- The cells cover the whole space. -/
  covers : (⋃ i, cell i) = Set.univ
  /-- The cells are cylindrically arranged in the coordinate order. -/
  cylindrical : IsCylindricallyArranged order cell
  /-- **Projection.**  Every polynomial of the input family *and* of the family the projection
  operator generates from it has constant sign on every cell (BPR Notation 5.15 + Thm 5.16). -/
  sign_invariant : ∀ P ∈ A ∪ generatedCADProjectionFamily order A, ∀ i, HasConstantSignOn (cell i) P
  /-- **Section / sector lifting.**  Every cell is a recursively lifted section/sector cell, in the
  declared variable order (BPR Def. 5.1 + Thm 5.16).  The recursion starts from the *input* family
  `A` and projects it (`cadProjectionStep`) on each descent, so each stage is decomposed by the
  family that still involves that stage's lifting variable — BPR's `C_i(A)`. -/
  recursively_lifted : ∀ i, IsRecursivelyLiftedCADCell A order (cell i)
  /-- **Decision.**  Every polynomial sign condition built from `A` is decided by the cell: each cell
  is either contained in the condition's solution set or disjoint from it, so the condition's truth
  value is read off the cell's sign vector, and the solution set is a union of cells. -/
  decides : ∀ equations nonnegative positive : Finset (MvPolynomial (Fin r) ℝ),
    ↑equations ⊆ (A : Set (MvPolynomial (Fin r) ℝ)) →
    ↑nonnegative ⊆ (A : Set (MvPolynomial (Fin r) ℝ)) →
    ↑positive ⊆ (A : Set (MvPolynomial (Fin r) ℝ)) →
    ∀ i, cell i ⊆ signConditionSet equations nonnegative positive ∨
      Disjoint (cell i) (signConditionSet equations nonnegative positive)

/-- **Non-vacuity of the whole `IsAdaptedCAD` record.**  At the trivial instance the cited theorem
supplies the single cell `ℝ`, and *every* field of the record is satisfied by it simultaneously.

This is the anti-vacuity receipt for the cited statement: `AdaptedCADConstruction` is an ASSUMED
`Prop`, so if `IsAdaptedCAD` were unsatisfiable we would be assuming a falsehood and every consumer
of the citation would hold vacuously — the exact failure mode a `cited` gate exists to catch.  Two
earlier encodings *were* unsatisfiable (a projection family folded down to constants with no `ℓ = 0`
cell; a cylindricity condition fixed to natural index prefixes while the lifting ran along an
arbitrary order).  Proving this record inhabited pins all fields against each other. -/
theorem isAdaptedCAD_univ_of_empty :
    IsAdaptedCAD (∅ : Finset (MvPolynomial (Fin 1) ℝ)) [0] (fun _ : Unit => Set.univ) where
  finite_cells := inferInstance
  nonempty_cell := fun _ => Set.univ_nonempty
  semialgebraic_cell := fun _ => ⟨∅, ∅, ∅, by ext a; simp⟩
  disjoint_cells := by
    intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  covers := Set.iUnion_const _
  cylindrical := fun _ _ _ => Or.inl rfl
  sign_invariant := by
    intro P hP
    simp [generatedCADProjectionFamily, cadProjectionStep, cadCoefficients, cadDiscriminants,
      cadPrincipalSubresultants, cadDerivativePrincipalSubresultants,
      cadPairPrincipalSubresultants, cadReductaFamily] at hP
  recursively_lifted := fun _ => isRecursivelyLiftedCADCell_univ_of_empty
  decides := by
    intro equations nonnegative positive he hn hp _
    refine Or.inl ?_
    intro a _
    refine ⟨fun P hPmem => ?_, fun P hPmem => ?_, fun P hPmem => ?_⟩
    · exact absurd (he hPmem) (by simp)
    · exact absurd (hn hPmem) (by simp)
    · exact absurd (hp hPmem) (by simp)

/-- **Non-vacuity of the full adapted-CAD record for `{0}`.**  Ignoring an identically zero
polynomial in the lifting root stack is compatible with every other field of `IsAdaptedCAD`: the
single cell `ℝ` is semialgebraic, cylindrical, sign-invariant for the generated family, recursively
root-free, and decides every sign condition built from `{0}`. -/
theorem isAdaptedCAD_univ_of_singleton_zero :
    IsAdaptedCAD ({0} : Finset (MvPolynomial (Fin 1) ℝ)) [0] (fun _ : Unit => Set.univ) where
  finite_cells := inferInstance
  nonempty_cell := fun _ => Set.univ_nonempty
  semialgebraic_cell := fun _ => ⟨∅, ∅, ∅, by ext a; simp⟩
  disjoint_cells := by
    intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  covers := Set.iUnion_const _
  cylindrical := fun _ _ _ => Or.inl rfl
  sign_invariant := by
    intro P hP _
    simp [generatedCADProjectionFamily, cadProjectionStep, cadCoefficients, cadDiscriminants,
      cadPrincipalSubresultants, cadDerivativePrincipalSubresultants,
      cadPairPrincipalSubresultants, cadReductaFamily, cadAsUnivariate] at hP
    subst P
    simp [HasConstantSignOn]
  recursively_lifted := fun _ => isRecursivelyLiftedCADCell_univ_of_singleton_zero
  decides := by
    intro equations nonnegative positive he hn hp _
    by_cases hzero : (0 : MvPolynomial (Fin 1) ℝ) ∈ positive
    · refine Or.inr (Set.disjoint_left.2 ?_)
      intro a _ ha
      have hpositive := ha.2.2 0 hzero
      simpa using hpositive
    · refine Or.inl ?_
      intro a _
      refine ⟨?_, ?_, ?_⟩
      · intro P hPmem
        have hPzero : P = 0 := by simpa using he hPmem
        subst P
        simp
      · intro P hPmem
        have hPzero : P = 0 := by simpa using hn hPmem
        subst P
        simp
      · intro P hPmem
        have hPzero : P = 0 := by simpa using hp hPmem
        exact (hzero (hPzero ▸ hPmem)).elim

/-! ### The cited theorems (assumed, never proved here) -/

/-- **Cylindrical algebraic decomposition adapted to a finite polynomial family** — BPR Thm 5.6
(with Def. 5.1, Def. 5.5, Notation 5.15, Thm 5.16); BCR §2.3.

*Statement of record.*  For **any** number of variables `r`, **any** finite family `A` of real
polynomials in `r` variables, and **any** variable order, `ℝ^r` admits a cylindrical algebraic
decomposition adapted to `A`: finitely many nonempty, pairwise disjoint, cylindrically arranged
semialgebraic cells, obtained by recursive section/sector lifting of the generated projection family
(coefficients, discriminants, principal subresultants), on each of which every member of `A` and of
that projection family has constant sign — so that every sign condition built from `A` is decided by
the cell a point lies in.

ASSUMED, not proved: CAD is absent from Mathlib.  This is the **mathematical** theorem (BPR Ch. 5),
not Collins' algorithm: no computability, effectivity or complexity claim is made here, and none is
consumed anywhere in this development.  The arbitrary variable order is the coordinate-relabelling
corollary of the printed fixed-order statement (see the module docstring, normalization 1); the
discriminants are already implied by BPR's `Elim` family (normalization 2). -/
def AdaptedCADConstruction : Prop :=
  ∀ (r : ℕ) (A : Finset (MvPolynomial (Fin r) ℝ)) (order : List (Fin r)),
    order.Nodup → (∀ x : Fin r, x ∈ order) →
      ∃ (ι : Type) (cell : ι → Set (CADSpace r)), IsAdaptedCAD A order cell

/-- **Tarski–Seidenberg projection theorem** — BCR Thm 2.2.1; BPR Ch. 2 (Projection Theorem for
Semi-Algebraic Sets).

*Statement of record.*  The image of a semialgebraic subset of `ℝ^{r+1}` under the projection that
forgets the last coordinate is a semialgebraic subset of `ℝ^r`.  Equivalently: semialgebraic
conditions are closed under existential quantification, so a quantified polynomial condition is
equivalent to a quantifier-free one.

This is the *set-theoretic* projection/quantifier-elimination statement, not the effective decision
procedure.  Universally quantified over the ambient dimension and the set; ASSUMED, not proved. -/
def TarskiSeidenbergProjection : Prop :=
  ∀ (r : ℕ) (S : Set (CADSpace (r + 1))),
    IsSemialgebraicSet S →
      IsSemialgebraicSet { x : CADSpace r | ∃ z : ℝ, (Fin.snoc x z : CADSpace (r + 1)) ∈ S }

/-- The **cited external real-closed-field interface** in full (`cite:bcr-bpr-cad`): the cylindrical
algebraic decomposition adapted to an arbitrary finite real-polynomial family (BPR Thm 5.6; BCR
§2.3), together with the Tarski–Seidenberg projection theorem (BCR Thm 2.2.1).  Both conjuncts are
general theorems about arbitrary finite real-polynomial families in arbitrary dimension; neither
mentions this paper's objects, and neither asserts effectivity. -/
def RealClosedFieldCADInterface : Prop :=
  AdaptedCADConstruction ∧ TarskiSeidenbergProjection

end

/-- The property that a polynomial remains nonzero after specializing all coordinates except the
lifting coordinate is unchanged when equal coordinates, points, and polynomials are substituted. -/
add_decl_doc CADSpecializationNonzeroAt.congr_simp

/-- Erasing a chosen coordinate from an assignment gives the same assignment whenever the chosen
coordinate and the original assignment are unchanged. -/
add_decl_doc cadEraseCoordinate.congr_simp

/-- The recursively generated set of reducta is determined by the supplied lifting coordinate,
recursion budget, and polynomial according to its defining stopping rule. -/
add_decl_doc cadReductaAux.eq_def

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
