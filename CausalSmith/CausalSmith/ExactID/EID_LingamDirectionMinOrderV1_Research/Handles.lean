/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Worked compatibility instances and construction / atlas handles

Statable set / certificate / incidence pieces used by the deferred conjectures.
The external decision-procedure content — the sign-invariant CAD stratification
of `\bar E_m(ℝ)` (interface `I-3`) and the truncated-moment-problem atomic
representation (interface `I-4`) — is NOT built here; these `def`s supply only
the project's own statable reductions.
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Basic
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Selector
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.Varieties
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.CAD.CADInterface
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.CAD.EffectiveRationalGroebnerCADInterface
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Rat.Encodable
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.DeriveEncodable

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

deriving instance Encodable for Direction

/-- Provides the stated computational structure for this data type. -/
local instance atlasGaussianRationalIrreducible :
    Fact (∀ q : ℚ, q ^ 2 ≠ (-1 : ℚ) + 0 * q) := by
  constructor
  intro q hq
  have hq' : q ^ 2 = (-1 : ℚ) := by simpa using hq
  have hnonneg : 0 ≤ q ^ 2 := sq_nonneg q
  rw [hq'] at hnonneg
  exact (not_le_of_gt neg_one_lt_zero) hnonneg

/-- Provides an effective numerical encoding for this finite data type. -/
noncomputable local instance atlasGaussianRationalEncodable :
    Encodable GaussianRational :=
  Encodable.ofEquiv (ℚ × ℚ) (QuadraticAlgebra.equivProd (-1) 0)

/-- Worked compatibility incidence systems `A_m` — the explicit **complex**
full-fiber incidence equations at the two worked cases `m = 1` (`K = 4`, the
12-equation system `A_1`) and `m = 2` (`K = 6`, the 25-equation system `A_2`).  A
pair `(θ, η)` of **complex** loading-and-cumulant lists is in the system iff its
forward and reverse simultaneous binary-form decompositions agree at every
retained coordinate `(r, a)` through order `K = 2m + 2` — the 12 scalar equations
`t_{r,a} = c_{0r}γ^a + c_{1r}ρ^a + c_{2r}1{a=r} = d_{0r}1{a=0} + d_{1r}σ^{r-a}
+ d_{2r}δ^{r-a}` for `m = 1`, and the analogous 25 for `m = 2` — **and** at least one
of the two generic-locus inequations holds (`θ ∈ Θ^{right,∘}` or `η ∈ Θ^{left,∘}`),
matching the paper's generic-locus disjunction.  These are the explicit complex
incidence equations the note requests (not a real-image complexification).  The
stated common-axis subfamily is `workedCompatibilityCommonAxis` below, which is a
subset of this system (recorded in `oeq:generic-exceptional-locus`).

Both members of the pair are pinned to the paper's finite ambient
`Θ^{right}_{m,K} × Θ^{left}_{m,K}` via `bandSupportedParams`.  The generic-locus
disjunction band-pins only *whichever* member satisfies it, so without these two
explicit conjuncts the other member's off-band source weights would stay free and
`A_m` would be a *cylinder* over them — exactly the restriction already imposed on
`genericFullFiberCompatibility` and `genericCompatibilityPreimage`. -/
def workedCompatibilityInstances (m : ℕ) : Set (ParamSpace ℂ m × ParamSpace ℂ m) :=
  { p | (m = 1 ∨ m = 2) ∧
        p.1 ∈ bandSupportedParams m (2 * m + 2) ∧
        p.2 ∈ bandSupportedParams m (2 * m + 2) ∧
        forwardCumulantMap m (2 * m + 2) p.1 = reverseCumulantMap m (2 * m + 2) p.2 ∧
        (p.1 ∈ genericParameterLocus m (2 * m + 2) ∨
         p.2 ∈ genericParameterLocus m (2 * m + 2)) }

/-- Common-axis subfamily of the worked incidence systems `A_m` (`m ∈ {1, 2}`).
Shared across both worked cases: the first latent slope vanishes on both arrows
(`ρ_1 = 0`, `σ_1 = 0`, read off the loading families at the first middle index),
the direct edges are reciprocal (`δγ = 1`), and the weight relations
`d_{0r} = c_{1r}`, `d_{1r} = c_{m+1,r}`, `d_{m+1,r} = c_{0r}γ^r` hold on the
retained band (for `m = 1` these are `d_{1r} = c_{2r}`, for `m = 2`
`d_{1r} = c_{3r}`; the `m = 2`-only relations `σ₂ρ₂ = 1`, `d_{2r} = c_{2r}ρ₂^r`
specialise the same pattern). -/
-- Stated over `ℂ` so that it is a subfamily of the complex worked incidence
-- system `workedCompatibilityInstances`.
def workedCompatibilityCommonAxis (m : ℕ) : Set (ParamSpace ℂ m × ParamSpace ℂ m) :=
  { p | (m = 1 ∨ m = 2) ∧
        -- the common-axis subfamily lives in the SAME finite ambient
        -- `Θ^{right}_{m,K} × Θ^{left}_{m,K}` as `A_m` itself (see
        -- `workedCompatibilityInstances`), so both members are band-pinned.
        p.1 ∈ bandSupportedParams m (2 * m + 2) ∧
        p.2 ∈ bandSupportedParams m (2 * m + 2) ∧
        (forwardLoading m p.1.1 p.1.2.1 ⟨1, by omega⟩).2 = 0 ∧
        (reverseLoading m p.2.1 p.2.2.1 ⟨1, by omega⟩).1 = 0 ∧
        p.2.1 * p.1.1 = 1 ∧
        (∀ r, 2 ≤ r → r ≤ 2 * m + 2 →
            p.2.2.2 ⟨0, by omega⟩ r = p.1.2.2 ⟨1, by omega⟩ r) ∧
        (∀ r, 2 ≤ r → r ≤ 2 * m + 2 →
            p.2.2.2 ⟨1, by omega⟩ r = p.1.2.2 ⟨m + 1, by omega⟩ r) ∧
        (∀ r, 2 ≤ r → r ≤ 2 * m + 2 →
            p.2.2.2 ⟨m + 1, by omega⟩ r = p.1.2.2 ⟨0, by omega⟩ r * p.1.1 ^ r) ∧
        -- `m = 2`-only reciprocal second-axis and its weight relation:
        -- `σ₂ρ₂ = 1` and `d_{2r} = c_{2r} ρ₂^r`.
        (∀ h : m = 2, p.1.2.1 ⟨1, by omega⟩ * p.2.2.1 ⟨1, by omega⟩ = 1) ∧
        (∀ h : m = 2, ∀ r, 2 ≤ r → r ≤ 2 * m + 2 →
            p.2.2.2 ⟨2, by omega⟩ r = p.1.2.2 ⟨2, by omega⟩ r * (p.1.2.1 ⟨1, by omega⟩) ^ r) }

/-- **Worked compatibility systems** `A_m` (`m ∈ {1, 2}`) — the full object the
paper's `def:worked-compatibility-instances` defines, bundled so the extracted
definition carries *both* the explicit incidence system and its common-axis
subfamily with all its explicit parameter relations (not only the incidence
equations):

* `.1` = `workedCompatibilityInstances m`, the 12-equation `A_1` (`m = 1`, `K = 4`) /
  25-equation `A_2` (`m = 2`, `K = 6`) incidence systems with the generic-locus
  disjunction;
* `.2` = the common-axis **subfamily of the worked incidence system**,
  `workedCompatibilityCommonAxis m ∩ workedCompatibilityInstances m`: the paper's
  explicit common-axis relations (`ρ₁ = σ₁ = 0`, `δγ = 1`, the `d_{jr}` weight
  relations, and for `m = 2` additionally `σ₂ρ₂ = 1`, `d_{2r} = c_{2r}ρ₂^r`)
  **intersected with `A_m`**, so that `.2 ⊆ .1` holds definitionally.  The bare
  common-axis predicate `workedCompatibilityCommonAxis` admits zero-weight points
  lying in neither generic locus and hence outside `A_m`; intersecting with the
  incidence system restricts it to an actual subfamily of `A_m`, as the paper states.
@realizes E_m(worked incidence systems `A_m` + common-axis subfamily of `A_m`) -/
-- @node: def:worked-compatibility-instances
def workedCompatibilitySystems (m : ℕ) :
    Set (ParamSpace ℂ m × ParamSpace ℂ m) × Set (ParamSpace ℂ m × ParamSpace ℂ m) :=
  (workedCompatibilityInstances m,
   workedCompatibilityCommonAxis m ∩ workedCompatibilityInstances m)

/-- Compactly-supported real feasible region: like `realFeasibleRegion` but each
source law is additionally required to be **compactly supported** (supported in a
bounded set).  This is strictly stronger than `realFeasibleRegion`, which allows
arbitrary realizing non-Gaussian laws.

*On the note's "truncated-moment-matrix perturbation".*  The note reaches this region by a
perturbation of a positive compactly-supported density.  That is the note's **method of exhibiting**
the realizing laws, not a property of the laws it exhibits: "was obtained by a perturbation" is not
a predicate on a measure, so it is not — and must not be — a conjunct here.  Adding one would make
the Lean predicate *strictly stronger* than the object the note defines.  The perturbation content the
development actually uses is a **proved theorem**, not an assumed clause: `truncatedMomentInterior`
(`Causalean.Stat.MomentProblems.truncatedMomentInterior`, 0 `sorry`) supplies exactly the
moment-cone-interior /
neighbourhood-realizability fact for which the perturbation is invoked. -/
def compactlySupportedFeasibleRegion (m L : ℕ) : Set (ParamSpace ℝ m) :=
  { p |
      p.1 ≠ 0 ∧
      Function.Injective (Fin.cons p.1 p.2.1 : Fin (m + 1) → ℝ) ∧
      (∀ j : Fin (m + 2), ∀ r : ℕ, (r < 2 ∨ L < r) → p.2.2 j r = 0) ∧
      ∀ j : Fin (m + 2), ∃ ν : Measure ℝ,
        IsProbabilityMeasure ν ∧
        (∫ x, x ∂ν = 0) ∧
        ¬ IsGaussianLaw ν ∧
        (∃ B : ℝ, 0 ≤ B ∧ ν {x : ℝ | B < |x|} = 0) ∧
        MemLp (id : ℝ → ℝ) (L : ℝ≥0∞) ν ∧
        ∀ r, 2 ≤ r → r ≤ L → sourceCumulant ν id r = p.2.2 j r }

/-- Real lower-order twin construction handle: existence of forward and reverse
parameters whose source cumulant lists are realized by **compactly supported**
non-Gaussian laws (obtained through the truncated-moment-matrix perturbation), and
whose axis-conditioned simultaneous binary-form decompositions agree through the
one-order-lower truncation `K₋ = 2m + 1`. -/
-- @node: def:real-twin-construction-handle
def realTwinConstructionHandle (m : ℕ) : Prop :=
  ∃ θ η : ParamSpace ℝ m,
    θ ∈ compactlySupportedFeasibleRegion m (2 * m + 1) ∧
    η ∈ compactlySupportedFeasibleRegion m (2 * m + 1) ∧
    forwardCumulantMap m (2 * m + 1) θ = reverseCumulantMap m (2 * m + 1) η

/-- A cumulant vector has exactly the finite atlas coordinate band
`2 ≤ r ≤ 2m+2`, `0 ≤ a ≤ r`; every other coordinate is zero. -/
def IsAtlasBandLimited (m : ℕ) (t : CumVec ℝ) : Prop :=
  ∀ r a : ℕ, ¬ (2 ≤ r ∧ r ≤ 2 * m + 2 ∧ a ≤ r) → t r a = 0

/-- Real exceptional-locus atlas handle, forward incidence set
`Γ_right = {(t, λ) : J_m(t) = 0, Φ^right(λ) = t, right-loading inequalities,
Q_K(λ) for every source}`, the project's own statable reduction.  Here
`J_m(t) = 0` is realized as `t ∈ \bar E_m(ℝ)` (membership of the complexified
observable in the compatibility closure), the right-loading inequalities are the
nonzero direct slope and pairwise-distinct finite slopes, and `Q_K` is the finite
atomic (Hankel-PSD) certificate on each source cumulant list.  The reverse mirror
is `realAtlasHandleReverse`.  The simultaneous sign-invariant CAD stratification
(interface `I-3`) and the atomic-certificate ↔ real-source equivalence (interface
`I-4`) are external and not built here. -/
def realAtlasHandle (m : ℕ) : Set (CumVec ℝ × ParamSpace ℝ m) :=
  { p |
      -- observable coordinates above the retained band `K = 2m + 2` are pinned to
      -- `0` (the atlas fixes `T_K` and leaves nothing above `K` free):
      IsAtlasBandLimited m p.1 ∧
      complexifyCumVec p.1 ∈ genericCompatibilityClosure m ∧
      -- the parameter `λ` lives in the paper's FINITE ambient `Θ^b_{m,K} = ℝ^{m+1} × ℝ^{n(K-1)}`:
      -- every off-band source weight is pinned to `0`.  Without this the sections
      -- `realAtlasForwardSection` would be cylinders over free off-band weights rather than the
      -- band-pinned `R^b_{m,K}(t) ∩ F^b_{m,K}` the note outputs.
      p.2 ∈ bandSupportedParams m (2 * m + 2) ∧
      forwardCumulantMap m (2 * m + 2) p.2 = p.1 ∧
      p.2.1 ≠ 0 ∧
      Function.Injective (Fin.cons p.2.1 p.2.2.1 : Fin (m + 1) → ℝ) ∧
      ∀ j : Fin (m + 2),
        atomicCertificate (m + 2) (2 * m + 2) (fun r => if 2 ≤ r then p.2.2.2 j r else 0) }

/-- Real exceptional-locus atlas handle, **reverse** incidence set
`Γ_left = {(t, λ) : J_m(t) = 0, Φ^left(λ) = t, left-loading inequalities,
Q_K(λ)}` — the reverse mirror of `realAtlasHandle`, supplying the reverse
incidence component the paper's atlas requires. -/
def realAtlasHandleReverse (m : ℕ) : Set (CumVec ℝ × ParamSpace ℝ m) :=
  { p |
      IsAtlasBandLimited m p.1 ∧
      complexifyCumVec p.1 ∈ genericCompatibilityClosure m ∧
      -- `λ` lives in the paper's FINITE ambient `Θ^b_{m,K}` (see `realAtlasHandle`).
      p.2 ∈ bandSupportedParams m (2 * m + 2) ∧
      reverseCumulantMap m (2 * m + 2) p.2 = p.1 ∧
      p.2.1 ≠ 0 ∧
      Function.Injective (Fin.cons p.2.1 p.2.2.1 : Fin (m + 1) → ℝ) ∧
      ∀ j : Fin (m + 2),
        atomicCertificate (m + 2) (2 * m + 2) (fun r => if 2 ≤ r then p.2.2.2 j r else 0) }

/-- Forward atlas **section** over an observable `t`: the `t`-fiber of the forward
incidence set `Γ_right`, i.e. the local description of `R^right_{m,K}(t) ∩ F^right`
that the atlas outputs cellwise.  (The section varies with `t`; the finite
sign-invariant CAD `t`-cell stratification that makes it constant per cell is the
external interface `I-3`.) -/
def realAtlasForwardSection (m : ℕ) (t : CumVec ℝ) : Set (ParamSpace ℝ m) :=
  { lam | (t, lam) ∈ realAtlasHandle m }

/-- Reverse atlas section over `t`: the `t`-fiber of `Γ_left` (local description of
`R^left_{m,K}(t) ∩ F^left`). -/
def realAtlasReverseSection (m : ℕ) (t : CumVec ℝ) : Set (ParamSpace ℝ m) :=
  { lam | (t, lam) ∈ realAtlasHandleReverse m }

/-- Forward atlas **nonemptiness label** `ε^right(t)`: whether the forward incidence
stack over `t` is nonempty — the cell label the CAD stratification attaches. -/
def realAtlasForwardLabel (m : ℕ) (t : CumVec ℝ) : Prop :=
  (realAtlasForwardSection m t).Nonempty

/-- Reverse atlas nonemptiness label `ε^left(t)`. -/
def realAtlasReverseLabel (m : ℕ) (t : CumVec ℝ) : Prop :=
  (realAtlasReverseSection m t).Nonempty

/-- Coordinates of the full CAD incidence system: observable coordinates,
loading/cumulant coordinates, and the atomic `(w,z)` witnesses. -/
abbrev AtlasIncidenceCoord (m : ℕ) :=
  (ℕ × ℕ) ⊕ RealParamCoord m ⊕ (Fin (m + 2) × Fin (m + 2) × Bool)

/-- Equality between indices of the atlas-incidence coordinate system can be decided. -/
local instance atlasIncidenceCoordDecidableEq (m : ℕ) :
    DecidableEq (AtlasIncidenceCoord m) := Classical.decEq _

/-- Equality between real polynomials in the atlas-incidence coordinates can be decided. -/
local instance atlasPolynomialDecidableEq (m : ℕ) :
    DecidableEq (MvPolynomial (AtlasIncidenceCoord m) ℝ) := Classical.decEq _

/-- Evaluation of a full incidence polynomial at `(t, λ, w, z)`. -/
def atlasIncidenceEval {m : ℕ} (t : CumVec ℝ) (lam : ParamSpace ℝ m)
    (w z : Fin (m + 2) → Fin (m + 2) → ℝ) : AtlasIncidenceCoord m → ℝ
  | Sum.inl ra => t ra.1 ra.2
  | Sum.inr (Sum.inl coord) => realParamEval lam coord
  | Sum.inr (Sum.inr (j, h, isWeight)) => if isWeight then w j h else z j h

/-- A finite polynomial sign presentation is generated from, and defines exactly,
one of the two incidence sets `Γ_b`, including its atomic witnesses.

The presentation cuts `Γ_b` out **inside the paper's finite ambient**
`ℝ^{q_K} × Θ^b_{m,K}`: the band memberships of `t` and `lam` are conjoined on the
right-hand side, exactly as `IsSemialgebraicCumCell` already does for observable cells.
This is forced, not cosmetic.  `realAtlasHandle` pins *infinitely* many off-band
coordinates of `t` and `lam` to `0`, whereas a `Finset` of polynomials constrains only
*finitely* many variables; an unguarded biconditional would therefore be unsatisfiable,
making both incidence sets empty, `RealAtlasCADData` uninhabitable and
`realAtlasCADStratification` vacuous — so the cited CAD engine could not inhabit it. -/
def DefinesAtlasIncidenceEquations (m : ℕ) (b : Direction)
    (equations nonnegative positive : Finset (MvPolynomial (AtlasIncidenceCoord m) ℝ)) : Prop :=
  equations.Nonempty ∧
  ∀ t lam,
    ((t, lam) ∈ if b = .forward then realAtlasHandle m else realAtlasHandleReverse m) ↔
      (t ∈ bandSupportedCumulants (2 * m + 2) ∧
       lam ∈ bandSupportedParams m (2 * m + 2) ∧
       ∃ w z : Fin (m + 2) → Fin (m + 2) → ℝ,
        (∀ P ∈ equations, MvPolynomial.eval (atlasIncidenceEval t lam w z) P = 0) ∧
        (∀ P ∈ nonnegative, 0 ≤ MvPolynomial.eval (atlasIncidenceEval t lam w z) P) ∧
        (∀ P ∈ positive, 0 < MvPolynomial.eval (atlasIncidenceEval t lam w z) P))

-- The CAD projection operators (`cadAsUnivariate`, `cadCoefficients`, `cadDiscriminants`,
-- `cadPrincipalSubresultants`, `cadProjectionStep`, `generatedCADProjectionFamily`) are GENERAL
-- CAD machinery and live in `Helpers/CAD/CADInterface.lean`, where the cited theorem of record is
-- stated.  They are coordinate-index-generic, so the atlas below instantiates the very same
-- operators the cited statement quantifies over — rather than a private lookalike copy.

/-- The block occupied by a concrete coordinate of the full incidence system. -/
def atlasIncidenceVariableBlock {m : ℕ} :
    AtlasIncidenceCoord m → FiberDecisionVariableBlock
  | Sum.inl _ => .observable
  | Sum.inr (Sum.inl _) => .loadingAndCumulants
  | Sum.inr (Sum.inr _) => .atomicWitnesses

/-- Every coordinate occurring in an incidence polynomial occurs in the CAD list,
and its actual list position obeys the recursive lifting/elimination order: atomic
witnesses first, then `λ`, then the observable base `t`.  The Lean CAD recursion
peels and erases the **head** of this list, so this is the typed orientation of the
paper's conventional base-first description `t`, then `λ`, then witnesses.
Thus the prescribed block relation is a property of `order` itself, not a
separately quantified relation unrelated to the incidence coordinates. -/
def IsAtlasIncidenceVariableOrder {m : ℕ}
    (incidence : Finset (MvPolynomial (AtlasIncidenceCoord m) ℝ))
    (order : List (AtlasIncidenceCoord m)) : Prop :=
  (∀ P ∈ incidence, ∀ x ∈ P.vars, x ∈ order) ∧
  (∀ x ∈ order, ∀ y ∈ order,
    atlasIncidenceVariableBlock x = .atomicWitnesses →
    atlasIncidenceVariableBlock y = .loadingAndCumulants →
    order.idxOf x < order.idxOf y) ∧
  (∀ x ∈ order, ∀ y ∈ order,
    atlasIncidenceVariableBlock x = .atomicWitnesses →
    atlasIncidenceVariableBlock y = .observable →
    order.idxOf x < order.idxOf y) ∧
  (∀ x ∈ order, ∀ y ∈ order,
    atlasIncidenceVariableBlock x = .loadingAndCumulants →
    atlasIncidenceVariableBlock y = .observable →
    order.idxOf x < order.idxOf y)

/-- The projection family is generated stage-by-stage from the incidence
presentation in an order containing all of its variables in the required blocks. -/
def IsGeneratedCADProjectionFamily {m : ℕ}
    (incidence : Finset (MvPolynomial (AtlasIncidenceCoord m) ℝ))
    (order : List (AtlasIncidenceCoord m))
    (projectionFamily : Finset (MvPolynomial (AtlasIncidenceCoord m) ℝ)) : Prop :=
  incidence.Nonempty ∧ order.Nodup ∧ IsAtlasIncidenceVariableOrder incidence order ∧
  projectionFamily = generatedCADProjectionFamily order incidence

/-- The real exceptional locus in the finite observable coordinate space used by
the incidence handles: membership in `bar E_m(ℝ)` together with zero coordinates
off the retained band `2 ≤ r ≤ 2m+2`, `0 ≤ a ≤ r`. -/
def bandLimitedRealExceptionalLocus (m : ℕ) : Set (CumVec ℝ) :=
  { t | IsAtlasBandLimited m t ∧
      complexifyCumVec t ∈ genericCompatibilityClosure m }

/-- A retained-observable cell of the paper's finite cumulant coordinate space `ℝ^{q_K}`:
after the off-band coordinates are pinned to zero (`bandSupportedCumulants (2m+2)`), it is
cut out by finitely many real polynomial sign conditions.

The `bandSupportedCumulants` conjunct is load-bearing, exactly as in the parallel
`IsSemialgebraicCumVec` (`TAtlas.lean`).  Without it a cell would be cut out by finitely
many `MvPolynomial (ℕ × ℕ)` sign conditions alone, hence a *cylinder* over all but finitely
many `(r, a)` coordinates; a finite union of such cylinders can never equal
`bandLimitedRealExceptionalLocus m`, which pins infinitely many off-band coordinates to `0`.
`RealAtlasCADData` would then be uninhabitable and `realAtlasHandleOutput` a vacuous `False`
that the cited CAD interface could not inhabit. -/
def IsSemialgebraicCumCell (m : ℕ) (cell : Set (CumVec ℝ)) : Prop :=
  ∃ equations nonnegative positive : Finset (MvPolynomial (ℕ × ℕ) ℝ),
    cell = { t |
      t ∈ bandSupportedCumulants (2 * m + 2) ∧
      (∀ P ∈ equations, MvPolynomial.eval (fun ra => t ra.1 ra.2) P = 0) ∧
      (∀ P ∈ nonnegative, 0 ≤ MvPolynomial.eval (fun ra => t ra.1 ra.2) P) ∧
      (∀ P ∈ positive, 0 < MvPolynomial.eval (fun ra => t ra.1 ra.2) P) }

/-- A polynomial has constant sign on a cell. -/
def atlasObservableEval {m : ℕ} (t : CumVec ℝ) : AtlasIncidenceCoord m → ℝ
  | Sum.inl ra => t ra.1 ra.2
  | Sum.inr _ => 0

/-- A polynomial has the same sign at every pair of observable cumulant vectors in the cell.

The polynomial is first evaluated using the atlas map associated with each cumulant vector. -/
def SignInvariantOn {m : ℕ} (cell : Set (CumVec ℝ))
    (P : MvPolynomial (AtlasIncidenceCoord m) ℝ) : Prop :=
  ∀ t ∈ cell, ∀ t' ∈ cell,
    polynomialSign (MvPolynomial.eval (atlasObservableEval t) P) =
      polynomialSign (MvPolynomial.eval (atlasObservableEval t') P)

/-- Cylindricity of observable cells in lexicographic `(r,a)` order: whenever two
cells meet over the same prefix, their projections to that prefix coincide. -/
def CylindricalCumCells {ι : Type} (cell : ι → Set (CumVec ℝ)) : Prop :=
  ∀ i j, ∀ k : ℕ,
    (∃ t ∈ cell i, ∃ t' ∈ cell j,
      ∀ r a, r < k → t r a = t' r a) →
    (∀ t ∈ cell i, ∃ t' ∈ cell j, ∀ r a, r < k → t r a = t' r a) ∨
    (∀ t' ∈ cell j, ∃ t ∈ cell i, ∀ r a, r < k → t r a = t' r a)

/-- A full point of the CAD incidence space, including the atomic witnesses. -/
abbrev AtlasAssignment (m : ℕ) := AtlasIncidenceCoord m → ℝ

-- The recursive CAD section/sector cell language (`cadEraseCoordinate`, `cadRealRootsAt`,
-- `IsCADAlgebraicRoot`, `IsCADLastAlgebraicRoot`, `IsRecursivelyLiftedCADCell`) is the output of
-- the section/sector lifting of the cited theorem, so it too lives in `Helpers/CAD/CADInterface.lean`
-- as part of the
-- cited statement of record, generic in the coordinate index.  `AtlasAssignment m` unfolds to
-- `AtlasIncidenceCoord m → ℝ`, so the atlas below uses those very predicates.

/-- An actual finite, simultaneous CAD atlas.  All arrays are indexed by `Fin`, so
finiteness is data rather than an existential proposition.  Its selected cells
live in the full `(t, λ, w, z)` coordinate space, arise by recursive lifting from
the incidence-generated projection family, and project exactly to the two
feasible fibers over every observable base cell. -/
structure RealAtlasCADData (m : ℕ) where
  forwardEquations : Finset (MvPolynomial (AtlasIncidenceCoord m) ℝ)
  forwardNonnegative : Finset (MvPolynomial (AtlasIncidenceCoord m) ℝ)
  forwardPositive : Finset (MvPolynomial (AtlasIncidenceCoord m) ℝ)
  reverseEquations : Finset (MvPolynomial (AtlasIncidenceCoord m) ℝ)
  reverseNonnegative : Finset (MvPolynomial (AtlasIncidenceCoord m) ℝ)
  reversePositive : Finset (MvPolynomial (AtlasIncidenceCoord m) ℝ)
  order : List (AtlasIncidenceCoord m)
  projectionFamily : Finset (MvPolynomial (AtlasIncidenceCoord m) ℝ)
  forward_presents_incidence : DefinesAtlasIncidenceEquations m .forward
    forwardEquations forwardNonnegative forwardPositive
  reverse_presents_incidence : DefinesAtlasIncidenceEquations m .reverse
    reverseEquations reverseNonnegative reversePositive
  projection_generated : IsGeneratedCADProjectionFamily
    (forwardEquations ∪ forwardNonnegative ∪ forwardPositive ∪
      reverseEquations ∪ reverseNonnegative ∪ reversePositive)
    order projectionFamily
  baseCellCount : ℕ
  baseCell : Fin baseCellCount → Set (CumVec ℝ)
  base_semialgebraic : ∀ i, IsSemialgebraicCumCell m (baseCell i)
  base_cylindrical : CylindricalCumCells baseCell
  base_disjoint : ∀ i j, i ≠ j → Disjoint (baseCell i) (baseCell j)
  base_covers : (⋃ i, baseCell i) = bandLimitedRealExceptionalLocus m
  projection_sign_invariant : ∀ i P, P ∈ projectionFamily → SignInvariantOn (baseCell i) P
  forwardLabel : Fin baseCellCount → Bool
  reverseLabel : Fin baseCellCount → Bool
  labels_exact : ∀ i t, t ∈ baseCell i →
    (forwardLabel i = true ↔ realAtlasForwardLabel m t) ∧
    (reverseLabel i = true ↔ realAtlasReverseLabel m t)
  forwardCellCount : Fin baseCellCount → ℕ
  reverseCellCount : Fin baseCellCount → ℕ
  forwardCell : ∀ i, Fin (forwardCellCount i) → Set (AtlasAssignment m)
  reverseCell : ∀ i, Fin (reverseCellCount i) → Set (AtlasAssignment m)
  -- The recursion starts from the INCIDENCE presentation and projects on each descent (BPR's
  -- stage-specific `C_i`), exactly as the cited `IsAdaptedCAD.recursively_lifted` does.  Starting it
  -- from the already fully-accumulated `projectionFamily` would not match the cited theorem.
  forward_recursive : ∀ i k,
    IsRecursivelyLiftedCADCell
      (forwardEquations ∪ forwardNonnegative ∪ forwardPositive ∪
        reverseEquations ∪ reverseNonnegative ∪ reversePositive)
      order (forwardCell i k)
  reverse_recursive : ∀ i k,
    IsRecursivelyLiftedCADCell
      (forwardEquations ∪ forwardNonnegative ∪ forwardPositive ∪
        reverseEquations ∪ reverseNonnegative ∪ reversePositive)
      order (reverseCell i k)
  forward_fiber_exact : ∀ i t, t ∈ baseCell i →
    {lam | ∃ w z, ∃ k, atlasIncidenceEval t lam w z ∈ forwardCell i k} =
      realAtlasForwardSection m t
  reverse_fiber_exact : ∀ i t, t ∈ baseCell i →
    {lam | ∃ w z, ∃ k, atlasIncidenceEval t lam w z ∈ reverseCell i k} =
      realAtlasReverseSection m t

/-- Coordinates remaining after the atomic moment witnesses have been eliminated:
the retained observable coordinates `t`, followed by the structural coordinates
`lambda`. -/
abbrev AtlasFiberCoord (m : ℕ) := (ℕ × ℕ) ⊕ RealParamCoord m

/-- A point of the witness-eliminated `(t, lambda)` coordinate space. -/
abbrev AtlasFiberAssignment (m : ℕ) := AtlasFiberCoord m → ℝ

/-- Coordinates of the complex generic two-arrow incidence used in Step 2:
observable cumulants, forward parameters, reverse parameters, and one saturation
coordinate for each arrow-genericity product.  Atomic real moment witnesses do
not occur in this coordinate type. -/
abbrev AtlasComplexIncidenceCoord (m : ℕ) :=
  (ℕ × ℕ) ⊕ ParamCoord m ⊕ ParamCoord m ⊕ Direction

/-- Evaluation of a witness-eliminated fiber polynomial at `(t, lambda)`. -/
def atlasFiberEval {m : ℕ} (t : CumVec ℝ) (lam : ParamSpace ℝ m) :
    AtlasFiberAssignment m
  | Sum.inl ra => t ra.1 ra.2
  | Sum.inr coord => realParamEval lam coord

/-- Equality on the witness-eliminated coordinate index. -/
local instance atlasFiberCoordDecidableEq (m : ℕ) :
    DecidableEq (AtlasFiberCoord m) := Classical.decEq _

/-- The variable block occupied by a witness-eliminated fiber coordinate. -/
def atlasFiberVariableBlock {m : ℕ} :
    AtlasFiberCoord m → FiberDecisionVariableBlock
  | Sum.inl _ => .observable
  | Sum.inr _ => .loadingAndCumulants

/-- The recursive fiber CAD eliminates the structural `lambda` prefix before
reaching the observable base.  Since `IsRecursivelyLiftedCADCell` peels the
head of its order, every displayed loading/cumulant coordinate must precede
every displayed observable coordinate. -/
def IsAtlasFiberVariableOrder {m : ℕ} (order : List (AtlasFiberCoord m)) : Prop :=
  ∀ x ∈ order, ∀ y ∈ order,
    atlasFiberVariableBlock x = .loadingAndCumulants →
    atlasFiberVariableBlock y = .observable →
    order.idxOf x < order.idxOf y

/-- Equality on observable polynomials used by the finite sign-oracle program. -/
local instance atlasObservablePolynomialDecidableEq :
    DecidableEq (MvPolynomial (ℕ × ℕ) ℝ) := Classical.decEq _

local instance atlasComplexIncidenceCoordDecidableEq (m : ℕ) :
    DecidableEq (AtlasComplexIncidenceCoord m) := Classical.decEq _

local instance atlasComplexIncidencePolynomialDecidableEq (m : ℕ) :
    DecidableEq (MvPolynomial (AtlasComplexIncidenceCoord m) ℂ) := Classical.decEq _

local instance atlasComplexObservablePolynomialDecidableEq :
    DecidableEq (MvPolynomial (ℕ × ℕ) ℂ) := Classical.decEq _

/-- One exhaustive row of the finite exact-real sign-oracle lookup program. -/
structure AtlasSignOracleRow where
  signs : List PolynomialSign
  forwardValue : Bool
  reverseValue : Bool

/-- A finite sign-oracle program.  Its only real-number primitive is exact sign
evaluation of the displayed finite polynomial test list; no computable comparison
operation on arbitrary real inputs is asserted. -/
structure AtlasSignOracleProgram where
  tests : List (MvPolynomial (ℕ × ℕ) ℝ)
  tests_nodup : tests.Nodup
  rows : List AtlasSignOracleRow
  row_width : ∀ row ∈ rows, row.signs.length = tests.length
  rows_exhaustive : ∀ signs : List PolynomialSign, signs.length = tests.length →
    ∃ row ∈ rows, row.signs = signs
  rows_functional : ∀ row₁ ∈ rows, ∀ row₂ ∈ rows, row₁.signs = row₂.signs →
    row₁.forwardValue = row₂.forwardValue ∧ row₁.reverseValue = row₂.reverseValue

/-- The only non-discrete primitive used when an atlas program is evaluated:
an exact sign query for a displayed observable polynomial. -/
abbrev AtlasExactSignOracle :=
  MvPolynomial (ℕ × ℕ) ℝ → CumVec ℝ → PolynomialSign

/-- An oracle answers each query by the mathematical sign of the corresponding
real polynomial value.  This is an exact-real oracle contract, not a claim that
comparison of arbitrary real numbers is Turing computable. -/
def IsExactAtlasSignOracle (oracle : AtlasExactSignOracle) : Prop :=
  ∀ P t, oracle P t = polynomialSign
    (MvPolynomial.eval (fun ra => t ra.1 ra.2) P)

/-- Evaluate the finite lookup program *relative to* an exact-sign oracle.  Once
the finite sign answers are supplied, this is ordinary executable list lookup;
no noncomputable comparison on `ℝ` occurs in this interpreter. -/
def AtlasSignOracleProgram.evaluateWith
    (program : AtlasSignOracleProgram) (oracle : AtlasExactSignOracle)
    (t : CumVec ℝ) : Bool × Bool :=
  let signs := program.tests.map fun P => oracle P t
  match program.rows.find? (fun row => row.signs = signs) with
  | some row => (row.forwardValue, row.reverseValue)
  | none => (false, false)

/-- The canonical mathematical exact-sign oracle. -/
noncomputable def exactAtlasSignOracle : AtlasExactSignOracle := fun P t =>
  polynomialSign (MvPolynomial.eval (fun ra => t ra.1 ra.2) P)

theorem exactAtlasSignOracle_isExact :
    IsExactAtlasSignOracle exactAtlasSignOracle := by
  intro P t
  rfl

/-- Families carried between the full incidence, witness-eliminated fiber, and
observable stages of the certified symbolic construction. -/
inductive AtlasTraceFamily (m : ℕ)
  | complexIncidence
      (family : Finset (MvPolynomial (AtlasComplexIncidenceCoord m) ℂ))
  | complexObservable (family : Finset (MvPolynomial (ℕ × ℕ) ℂ))
  | incidence (family : Finset (MvPolynomial (AtlasIncidenceCoord m) ℝ))
  | fiber (family : Finset (MvPolynomial (AtlasFiberCoord m) ℝ))
  | observable (family : Finset (MvPolynomial (ℕ × ℕ) ℝ))

/-- View an observable polynomial family inside the full incidence coordinate
space.  This is how the dependent intersection basis is supplied to the final
simultaneous real CAD/QE job. -/
noncomputable def atlasObservableIncidenceFamily (m : ℕ)
    (family : Finset (MvPolynomial (ℕ × ℕ) ℝ)) :
    Finset (MvPolynomial (AtlasIncidenceCoord m) ℝ) := by
  classical
  exact family.image fun P => P.rename Sum.inl

/-- Operations appearing in the paper's finite elimination/projection/lifting
construction trace. -/
inductive AtlasTraceOperation
  | saturationGroebnerElimination (b : Direction)
  | idealIntersection
  | realImaginarySplit
  | cadBuchberger
  | cadElimination
  | cadIdealIntersection
  | cadSaturation
  | cadReductaGeneration
  | coefficientProjection
  | discriminantProjection
  | principalSubresultantProjection
  | cadProjectionClosure
  | prefixCellProjection
  | witnessCellRetention (b : Direction) (baseIndex cellIndex : ℕ)
  | realRootIsolation
  | sectionLifting
  | sectorLifting
  | signConditionTruth
  deriving DecidableEq, Encodable

/-- The three rational algebra jobs used by the paper-specific atlas.  The
general cited interface also supports Gaussian-rational jobs, but this atlas
starts from rational incidence equations and casts their outputs to `ℂ`, so its
Gaussian batch is empty. -/
inductive AtlasRationalAlgebraJob
  | forwardElimination
  | reverseElimination
  | observableIntersection
  deriving DecidableEq, Encodable

/-- One primitive operation charged by the cited effective computations, with
both its paper-side source job and its cited high-level trace stage retained.
This is the bridge between the semantic atlas trace and the primitive cost
model; it is deliberately unrelated to partial-recursive machine fuel. -/
inductive AtlasCitedPrimitiveCharge
  | rationalAlgebra (job : AtlasRationalAlgebraJob)
      (stage : EffectiveGroebnerTraceOperation)
      (primitive : EffectiveGroebnerPrimitiveOperation)
  | rationalCAD (sourceStepIndex : ℕ) (stage : EffectiveAlgebraTraceOperation)
      (primitive : EffectiveRealAlgebraicPrimitiveOperation)

/-- The actual combined cited result consumed by one paper-specific atlas:
exactly two rational incidence-elimination jobs, one rational observable-ideal
intersection job, no Gaussian-rational job, and one rational CAD/QE job.  The
three machine codes are kept distinct, as in the cited combined interface. -/
structure AtlasCitedEffectiveExecution where
  rationalAlgebraMachine : Nat.Partrec.Code
  gaussianAlgebraMachine : Nat.Partrec.Code
  rationalCADMachine : Nat.Partrec.Code
  forwardEliminationJob : EffectiveGroebnerJobOver ℚ
  reverseEliminationJob : EffectiveGroebnerJobOver ℚ
  /-- The caller-supplied identification of forward and reverse source
  coordinates.  The certified paper trace below closes this abstract relation
  against equality of the displayed observable-coordinate maps. -/
  sharedCoordinateRelation :
    Fin forwardEliminationJob.r → Fin reverseEliminationJob.r → Prop
  /-- The cited rational execution is sequential: the observable-intersection
  job is constructed only from the two saturated elimination outputs. -/
  dependentPipeline : EffectiveDependentRationalEliminationPipeline
    rationalAlgebraMachine forwardEliminationJob reverseEliminationJob
      sharedCoordinateRelation
  gaussianResults : EffectiveGroebnerBatchResultsOver GaussianRational
    gaussianAlgebraMachine []
  /-- The CAD/QE input is indexed by, and definitionally carried with, the
  completed forward/reverse/dependent-intersection pipeline. -/
  dependentCADJob : EffectiveDependentRationalCADJob dependentPipeline
  cadResult : EffectiveRationalCADCompletedJob rationalCADMachine dependentCADJob.job

/-- The observable intersection job constructed by the dependent cited run. -/
def AtlasCitedEffectiveExecution.observableIntersectionJob
    (execution : AtlasCitedEffectiveExecution) : EffectiveGroebnerJobOver ℚ :=
  execution.dependentPipeline.intersectionJob

/-- The rational CAD job consuming the exact dependent intersection result. -/
def AtlasCitedEffectiveExecution.cadJob
    (execution : AtlasCitedEffectiveExecution) : EffectiveRationalCADJob :=
  execution.dependentCADJob.job

/-- The dependent execution, viewed as the three-result batch used by the
generic combined cost bookkeeping. -/
def AtlasCitedEffectiveExecution.rationalResults
    (execution : AtlasCitedEffectiveExecution) :
    EffectiveGroebnerBatchResultsOver ℚ execution.rationalAlgebraMachine
      [execution.forwardEliminationJob, execution.reverseEliminationJob,
        execution.observableIntersectionJob] :=
  .cons execution.dependentPipeline.forwardResult
    (.cons execution.dependentPipeline.reverseResult
      (.cons execution.dependentPipeline.intersectionResult .nil))

/-- The rational job list supplied to the combined cited bound. -/
def AtlasCitedEffectiveExecution.rationalJobs
    (execution : AtlasCitedEffectiveExecution) : List (EffectiveGroebnerJobOver ℚ) :=
  [execution.forwardEliminationJob, execution.reverseEliminationJob,
    execution.observableIntersectionJob]

/-- The paper-specific Gaussian-rational job list is exactly empty. -/
def AtlasCitedEffectiveExecution.gaussianJobs
    (_execution : AtlasCitedEffectiveExecution) :
    List (EffectiveGroebnerJobOver GaussianRational) :=
  []

/-- Primitive charges of the specialized three-job rational batch, retaining
which of the forward, reverse, or intersection results produced each charge. -/
def atlasRationalBatchPrimitiveCharges
    {machineCode : Nat.Partrec.Code}
    {forwardJob reverseJob intersectionJob : EffectiveGroebnerJobOver ℚ} :
    EffectiveGroebnerBatchResultsOver ℚ machineCode
      [forwardJob, reverseJob, intersectionJob] → List AtlasCitedPrimitiveCharge
  | .cons forwardResult (.cons reverseResult (.cons intersectionResult .nil)) =>
      (forwardResult.result.payload.trace.flatMap fun step =>
        step.primitiveOperations.map fun primitive =>
          .rationalAlgebra .forwardElimination step.operation primitive) ++
      (reverseResult.result.payload.trace.flatMap fun step =>
        step.primitiveOperations.map fun primitive =>
          .rationalAlgebra .reverseElimination step.operation primitive) ++
      (intersectionResult.result.payload.trace.flatMap fun step =>
        step.primitiveOperations.map fun primitive =>
          .rationalAlgebra .observableIntersection step.operation primitive)

/-- Primitive charges of rational CAD source steps, indexed from a supplied
offset so the paper-side slice can point back to the exact source step. -/
def atlasRationalCADPrimitiveChargesFrom :
    ℕ → {r : ℕ} → List (EffectiveAlgebraTraceStep r) →
      List AtlasCitedPrimitiveCharge
  | _, _, [] => []
  | sourceStepIndex, _, step :: steps =>
      (step.primitiveOperations.map fun primitive =>
        .rationalCAD sourceStepIndex step.operation primitive) ++
      atlasRationalCADPrimitiveChargesFrom (sourceStepIndex + 1) steps

/-- Primitive charges of the one rational real-CAD/QE result. -/
def atlasRationalCADPrimitiveCharges
    {machineCode : Nat.Partrec.Code} {job : EffectiveRationalCADJob}
    (result : EffectiveRationalCADCompletedJob machineCode job) :
    List AtlasCitedPrimitiveCharge :=
  atlasRationalCADPrimitiveChargesFrom 0 result.result.payload.trace

theorem atlasRationalCADPrimitiveChargesFrom_length
    (sourceStepIndex : ℕ) {r : ℕ} (steps : List (EffectiveAlgebraTraceStep r)) :
    (atlasRationalCADPrimitiveChargesFrom sourceStepIndex steps).length =
      (steps.map EffectiveAlgebraTraceStep.operationCount).sum := by
  induction steps generalizing sourceStepIndex with
  | nil => simp [atlasRationalCADPrimitiveChargesFrom]
  | cons step steps ih =>
      simp [atlasRationalCADPrimitiveChargesFrom,
        EffectiveAlgebraTraceStep.operationCount, ih]

/-- Complete cited primitive stream for the paper-specific combined run.  No
Gaussian charges occur because `gaussianResults` is indexed by the empty job
list. -/
def AtlasCitedEffectiveExecution.primitiveCharges
    (execution : AtlasCitedEffectiveExecution) : List AtlasCitedPrimitiveCharge :=
  atlasRationalBatchPrimitiveCharges execution.rationalResults ++
    atlasRationalCADPrimitiveCharges execution.cadResult

/-- The exact operation count on the left side of the cited combined bound. -/
def AtlasCitedEffectiveExecution.symbolicOperationCount
    (execution : AtlasCitedEffectiveExecution) : ℕ :=
  execution.rationalResults.symbolicOperationCount +
    execution.gaussianResults.symbolicOperationCount +
    execution.cadResult.result.payload.symbolicOperationCount

/-- The completed forward job stored in the specialized rational batch. -/
def AtlasCitedEffectiveExecution.forwardResult
    (execution : AtlasCitedEffectiveExecution) :
    EffectiveGroebnerCompletedJobOver ℚ execution.rationalAlgebraMachine
      execution.forwardEliminationJob :=
  execution.dependentPipeline.forwardResult

/-- The completed reverse job stored in the specialized rational batch. -/
def AtlasCitedEffectiveExecution.reverseResult
    (execution : AtlasCitedEffectiveExecution) :
    EffectiveGroebnerCompletedJobOver ℚ execution.rationalAlgebraMachine
      execution.reverseEliminationJob :=
  execution.dependentPipeline.reverseResult

/-- The completed observable-ideal intersection job stored in the specialized
rational batch. -/
def AtlasCitedEffectiveExecution.intersectionResult
    (execution : AtlasCitedEffectiveExecution) :
    EffectiveGroebnerCompletedJobOver ℚ execution.rationalAlgebraMachine
      execution.observableIntersectionJob :=
  execution.dependentPipeline.intersectionResult

/-- Rename a finite rational polynomial family into a displayed coordinate
type and extend coefficients to `ℂ`.  The embedding is explicit, so finite
effective coordinates cannot be silently identified with unrelated paper
coordinates. -/
noncomputable def rationalFamilyToComplexAlong {r : ℕ} {σ : Type}
    [DecidableEq σ] (embedding : Fin r ↪ σ)
    (family : Finset (MvPolynomial (Fin r) ℚ)) :
    Finset (MvPolynomial σ ℂ) := by
  classical
  exact family.image fun P => (P.map (Rat.castHom ℂ)).rename embedding

/-- Rename a finite rational polynomial family into a displayed coordinate
type and extend coefficients to `ℝ`. -/
noncomputable def rationalFamilyToRealAlong {r : ℕ} {σ : Type}
    [DecidableEq σ] (embedding : Fin r ↪ σ)
    (family : Finset (MvPolynomial (Fin r) ℚ)) :
    Finset (MvPolynomial σ ℝ) := by
  classical
  exact family.image fun P => (P.map (Rat.castHom ℝ)).rename embedding

/-- Rename a rational family after elimination, when only the variables that
actually occur in the family must embed into the smaller retained coordinate
space.  This is the correct transport for `(t, lambda)` and observable outputs:
the eliminated full-space coordinates need no image. -/
noncomputable def rationalFamilyToComplexOnUsedCoordinates {r : ℕ} {σ : Type}
    [DecidableEq σ] (coordinateMap : Fin r → σ)
    (family : Finset (MvPolynomial (Fin r) ℚ)) :
    Finset (MvPolynomial σ ℂ) := by
  classical
  exact family.image fun P => (P.map (Rat.castHom ℂ)).rename coordinateMap

noncomputable def rationalFamilyToRealOnUsedCoordinates {r : ℕ} {σ : Type}
    [DecidableEq σ] (coordinateMap : Fin r → σ)
    (family : Finset (MvPolynomial (Fin r) ℚ)) :
    Finset (MvPolynomial σ ℝ) := by
  classical
  exact family.image fun P => (P.map (Rat.castHom ℝ)).rename coordinateMap

/-- Rename an already-real projected CAD family onto the displayed paper
coordinate space.  This is the transport used after the cited recursive
prefix projection; it performs no additional elimination. -/
noncomputable def realFamilyOnUsedCoordinates {r : ℕ} {σ : Type}
    [DecidableEq σ] (coordinateMap : Fin r → σ)
    (family : Finset (MvPolynomial (Fin r) ℝ)) :
    Finset (MvPolynomial σ ℝ) := by
  classical
  exact family.image fun P => P.rename coordinateMap

/-- Transport one cited rational sign-test code to observable coordinates.
The sign attached to the code is transported separately and unchanged. -/
noncomputable def effectiveCodeToObservablePolynomial {r : ℕ}
    (coordinateMap : Fin r → (ℕ × ℕ)) (code : EffectivePolynomialCode r) :
    MvPolynomial (ℕ × ℕ) ℝ :=
  (code.toPolynomial.map (Rat.castHom ℝ)).rename coordinateMap

/-- Extend one finite cited CAD assignment along the exact incidence-coordinate
embedding, using zero only outside the supplied finite coordinate image. -/
noncomputable def cadAssignmentAlong {r m : ℕ}
    (embedding : Fin r ↪ AtlasIncidenceCoord m) (point : CADSpace r) :
    AtlasAssignment m :=
  Function.extend embedding point 0

/-- Observable component of a finite cited CAD assignment. -/
noncomputable def cadObservableCumVec {r m : ℕ}
    (embedding : Fin r ↪ AtlasIncidenceCoord m) (point : CADSpace r) :
    CumVec ℝ := fun order exponent =>
  cadAssignmentAlong embedding point (Sum.inl (order, exponent))

/-- Witness-forgotten `(t, lambda)` component of a finite cited CAD assignment. -/
noncomputable def cadFiberAssignment {r m : ℕ}
    (embedding : Fin r ↪ AtlasIncidenceCoord m) (point : CADSpace r) :
    AtlasFiberAssignment m
  | Sum.inl orderExponent =>
      cadAssignmentAlong embedding point (Sum.inl orderExponent)
  | Sum.inr coord =>
      cadAssignmentAlong embedding point (Sum.inr (Sum.inl coord))

/-- Erasing two consecutive lifting prefixes is the same geometric projection
as erasing their concatenation.  This is the compatibility used by the
witness-to-fiber and fiber-to-observable transports. -/
theorem effectiveCADErasePrefix_append {r : ℕ}
    (first second : List (Fin r)) (point : CADSpace r) :
    effectiveCADErasePrefix (first ++ second) point =
      effectiveCADErasePrefix second (effectiveCADErasePrefix first point) := by
  simp [effectiveCADErasePrefix, List.foldl_append]

/-- A coordinate map is faithful on all variables that actually occur in a
displayed polynomial family.  It need not inject the already-eliminated ambient
coordinates into the smaller output space. -/
def IsInjectiveOnRationalFamilyVariables {r : ℕ} {σ : Type}
    (coordinateMap : Fin r → σ)
    (family : Finset (MvPolynomial (Fin r) ℚ)) : Prop :=
  ∀ P ∈ family, ∀ x ∈ P.vars, ∀ Q ∈ family, ∀ y ∈ Q.vars,
    coordinateMap x = coordinateMap y → x = y

/-- Interpret one actual rational CAD trace code-family in a displayed real or
complex atlas coordinate type, using an explicit finite-coordinate embedding.
Every branch ends in an equality of polynomial families, not an opaque label. -/
def EffectiveRationalCodeFamily.PopulatesAtlasFamily {r m : ℕ}
    (codes : List (EffectivePolynomialCode r)) : AtlasTraceFamily m → Prop
  | .complexIncidence family =>
      ∃ coordinateMap : Fin r → AtlasComplexIncidenceCoord m,
        IsInjectiveOnRationalFamilyVariables coordinateMap
            (effectiveDecodedPolynomialFamily codes) ∧
          rationalFamilyToComplexOnUsedCoordinates coordinateMap
            (effectiveDecodedPolynomialFamily codes) = family
  | .complexObservable family =>
      ∃ coordinateMap : Fin r → (ℕ × ℕ),
        IsInjectiveOnRationalFamilyVariables coordinateMap
            (effectiveDecodedPolynomialFamily codes) ∧
          rationalFamilyToComplexOnUsedCoordinates coordinateMap
            (effectiveDecodedPolynomialFamily codes) = family
  | .incidence family =>
      ∃ coordinateMap : Fin r → AtlasIncidenceCoord m,
        IsInjectiveOnRationalFamilyVariables coordinateMap
            (effectiveDecodedPolynomialFamily codes) ∧
          rationalFamilyToRealOnUsedCoordinates coordinateMap
            (effectiveDecodedPolynomialFamily codes) = family
  | .fiber family =>
      ∃ coordinateMap : Fin r → AtlasFiberCoord m,
        IsInjectiveOnRationalFamilyVariables coordinateMap
            (effectiveDecodedPolynomialFamily codes) ∧
          rationalFamilyToRealOnUsedCoordinates coordinateMap
            (effectiveDecodedPolynomialFamily codes) = family
  | .observable family =>
      ∃ coordinateMap : Fin r → (ℕ × ℕ),
        IsInjectiveOnRationalFamilyVariables coordinateMap
            (effectiveDecodedPolynomialFamily codes) ∧
          rationalFamilyToRealOnUsedCoordinates coordinateMap
            (effectiveDecodedPolynomialFamily codes) = family

/-- A cited truth/retention query is exactly one of this paper's displayed
full-incidence sign conditions after the fixed full-coordinate embedding. -/
def EffectiveCADSignQuery.PopulatesAtlasIncidenceSignCondition {r m : ℕ}
    (query : EffectiveCADSignQuery r) (embedding : Fin r ↪ AtlasIncidenceCoord m)
    (equations nonnegative positive :
      Finset (MvPolynomial (AtlasIncidenceCoord m) ℝ)) : Prop :=
  rationalFamilyToRealAlong embedding
      (effectiveDecodedPolynomialFamily query.equations) = equations ∧
    rationalFamilyToRealAlong embedding
      (effectiveDecodedPolynomialFamily query.nonnegative) = nonnegative ∧
    rationalFamilyToRealAlong embedding
      (effectiveDecodedPolynomialFamily query.positive) = positive

/-- A CAD-source primitive belongs to the indicated indexed cited trace step,
including exact agreement of the source high-level operation. -/
def AtlasCitedPrimitiveCharge.IsFromCADStep (sourceStepIndex : ℕ)
    (sourceOperation : EffectiveAlgebraTraceOperation) :
    AtlasCitedPrimitiveCharge → Prop
  | .rationalCAD index operation _ =>
      index = sourceStepIndex ∧ operation = sourceOperation
  | _ => False

/-- The explicit primitive stream has exactly the combined cited count. -/
theorem AtlasCitedEffectiveExecution.primitiveCharges_length
    (execution : AtlasCitedEffectiveExecution) :
    execution.primitiveCharges.length = execution.symbolicOperationCount := by
  rcases execution with
    ⟨rationalMachine, gaussianMachine, cadMachine, forwardJob, reverseJob,
      sharedCoordinateRelation, pipeline, gaussianResults, cadJob, cadResult⟩
  rcases pipeline with
    ⟨forwardResult, reverseResult, intersectionJob, forwardMap, reverseMap,
      forwardMapInjective, reverseMapInjective, forwardReverseExact,
      hforward, hreverse, intersectionResult⟩
  cases gaussianResults
  simp [AtlasCitedEffectiveExecution.primitiveCharges,
    AtlasCitedEffectiveExecution.rationalResults,
    atlasRationalBatchPrimitiveCharges,
    atlasRationalCADPrimitiveCharges,
    AtlasCitedEffectiveExecution.symbolicOperationCount,
    EffectiveGroebnerBatchResultsOver.symbolicOperationCount,
    EffectiveGroebnerPayloadOver.symbolicOperationCount,
    EffectiveRationalGroebnerCADPayload.symbolicOperationCount,
    atlasRationalCADPrimitiveChargesFrom_length,
    List.length_flatMap, Nat.add_assoc]
  rfl

/-- A cited primitive may be assigned only to the atlas operation consuming
its source job.  Rational algebra charges go to the corresponding forward,
reverse, or intersection step; CAD charges stay on real projection/lifting or
witness-retention steps.  The real/imaginary coefficient reinterpretation is
therefore necessarily an uncharged semantic step. -/
def AtlasCitedPrimitiveCharge.MatchesAtlasOperation :
    AtlasCitedPrimitiveCharge → AtlasTraceOperation → Prop
  | .rationalAlgebra .forwardElimination _ _,
      .saturationGroebnerElimination .forward => True
  | .rationalAlgebra .reverseElimination _ _,
      .saturationGroebnerElimination .reverse => True
  | .rationalAlgebra .observableIntersection _ _, .idealIntersection => True
  | .rationalCAD _ .buchberger _, .cadBuchberger => True
  | .rationalCAD _ .elimination _, .cadElimination => True
  | .rationalCAD _ .idealIntersection _, .cadIdealIntersection => True
  | .rationalCAD _ .saturation _, .cadSaturation => True
  | .rationalCAD _ .reductaGeneration _, .cadReductaGeneration => True
  | .rationalCAD _ .coefficientProjection _, .coefficientProjection => True
  | .rationalCAD _ .discriminantProjection _, .discriminantProjection => True
  | .rationalCAD _ .principalSubresultantProjection _,
      .principalSubresultantProjection => True
  | .rationalCAD _ .projectionClosure _, .cadProjectionClosure => True
  | .rationalCAD _ .prefixCellProjection _, .prefixCellProjection => True
  | .rationalCAD _ .witnessCellRetention _, .witnessCellRetention _ _ _ => True
  | .rationalCAD _ .rootIsolation _, .realRootIsolation => True
  | .rationalCAD _ .sectionLifting _, .sectionLifting => True
  | .rationalCAD _ .sectorLifting _, .sectorLifting => True
  | .rationalCAD _ .signConditionTruth _, .signConditionTruth => True
  | _, _ => False

/-- A declared input/output step of the finite symbolic atlas construction,
together with its contiguous slice of the cited primitive stream. -/
structure AtlasTraceStep (m : ℕ) where
  operation : AtlasTraceOperation
  inputs : List (AtlasTraceFamily m)
  output : AtlasTraceFamily m
  chargedPrimitives : List AtlasCitedPrimitiveCharge

/-- Operation-specific linkage from one high-level atlas step to one actual
step of the cited rational CAD result.  Its inputs and output must be populated
by the source step's decoded polynomial code families after explicit finite
coordinate renaming. -/
def AtlasTraceStep.IsLinkedToCitedCADStep {m r : ℕ}
    (step : AtlasTraceStep m) (sourceStepIndex : ℕ)
    (sourceStep : EffectiveAlgebraTraceStep r) : Prop :=
  (match sourceStep.operation, step.operation with
    | .buchberger, .cadBuchberger => True
    | .elimination, .cadElimination => True
    | .idealIntersection, .cadIdealIntersection => True
    | .saturation, .cadSaturation => True
    | .reductaGeneration, .cadReductaGeneration => True
    | .coefficientProjection, .coefficientProjection => True
    | .discriminantProjection, .discriminantProjection => True
    | .principalSubresultantProjection, .principalSubresultantProjection => True
    | .projectionClosure, .cadProjectionClosure => True
    | .prefixCellProjection, .prefixCellProjection => True
    | .rootIsolation, .realRootIsolation => True
    | .sectionLifting, .sectionLifting => True
    | .sectorLifting, .sectorLifting => True
    | .signConditionTruth, .signConditionTruth => True
    | .witnessCellRetention, .witnessCellRetention _ _ _ => True
    | _, _ => False) ∧
  (match sourceStep.operation with
    | .prefixCellProjection | .signConditionTruth | .witnessCellRetention => True
    | _ => ∀ family ∈ step.inputs, ∃ codes ∈ sourceStep.inputFamilies,
        EffectiveRationalCodeFamily.PopulatesAtlasFamily codes family) ∧
  (match sourceStep.operation with
    | .prefixCellProjection =>
        sourceStep.outputFamilies = [] ∧
          sourceStep.producedPrefixProjectionCertificateCodes ≠ []
    | .signConditionTruth =>
        sourceStep.outputFamilies = [] ∧ sourceStep.producedTruthRowCodes ≠ []
    | .witnessCellRetention =>
        sourceStep.outputFamilies = [] ∧ sourceStep.producedRetentionRowCodes ≠ []
    | .rootIsolation | .sectionLifting | .sectorLifting =>
        sourceStep.outputFamilies = [] ∧ ∃ codes ∈ sourceStep.inputFamilies,
          EffectiveRationalCodeFamily.PopulatesAtlasFamily codes step.output
    | _ => ∃ codes ∈ sourceStep.outputFamilies,
        EffectiveRationalCodeFamily.PopulatesAtlasFamily codes step.output) ∧
  ∀ charge ∈ step.chargedPrimitives,
    charge.IsFromCADStep sourceStepIndex sourceStep.operation

/-- Exactly the operations sourced from the rational CAD/QE result. -/
def AtlasTraceOperation.IsCitedCADOperation : AtlasTraceOperation → Prop
  | .cadBuchberger | .cadElimination | .cadIdealIntersection | .cadSaturation
  | .cadReductaGeneration | .coefficientProjection | .discriminantProjection
  | .principalSubresultantProjection | .cadProjectionClosure
  | .prefixCellProjection
  | .witnessCellRetention _ _ _ | .realRootIsolation | .sectionLifting
  | .sectorLifting | .signConditionTruth => True
  | _ => False

/-- Real polynomial-family variants used by the rational CAD/QE branch. -/
def AtlasTraceFamily.IsReal {m : ℕ} : AtlasTraceFamily m → Prop
  | .incidence _ | .fiber _ | .observable _ => True
  | _ => False

/-- Basic family shape for a cited CAD algebra/projection-closure step.  Its
full polynomial semantics comes from `IsLinkedToCitedCADStep`, which identifies
the actual semantically certified source step and its decoded families. -/
def AtlasTraceStep.HasCitedCADFamilyShape {m : ℕ} (step : AtlasTraceStep m) : Prop :=
  step.inputs ≠ [] ∧ (∀ family ∈ step.inputs, family.IsReal) ∧ step.output.IsReal

/-- The common real zero set of a finite observable polynomial family. -/
def atlasObservableZeroSet
    (m : ℕ) (family : Finset (MvPolynomial (ℕ × ℕ) ℝ)) : Set (CumVec ℝ) :=
  { t | t ∈ bandSupportedCumulants (2 * m + 2) ∧
    ∀ P ∈ family, MvPolynomial.eval (fun ra => t ra.1 ra.2) P = 0 }

/-- Evaluate the complex generic two-arrow incidence at `(t, theta, eta, s)`. -/
def atlasComplexIncidenceEval {m : ℕ} (t : CumVec ℂ)
    (theta eta : ParamSpace ℂ m) (s : Direction → ℂ) :
    AtlasComplexIncidenceCoord m → ℂ
  | Sum.inl ra => t ra.1 ra.2
  | Sum.inr (Sum.inl x) => paramEval theta x
  | Sum.inr (Sum.inr (Sum.inl x)) => paramEval eta x
  | Sum.inr (Sum.inr (Sum.inr b)) => s b

/-- A finite complex polynomial family presents the generic two-arrow incidence
with the indicated arrow's genericity product saturated.  This is the Step-2
incidence whose elimination produces observable equations for `bar E_m`; it is
separate from the Step-3 real incidence with atomic moment witnesses. -/
def DefinesComplexGenericIncidenceEquations (m : ℕ) (b : Direction)
    (family : Finset (MvPolynomial (AtlasComplexIncidenceCoord m) ℂ)) : Prop :=
  family.Nonempty ∧ ∀ t theta eta,
    (t ∈ bandSupportedCumulants (2 * m + 2) ∧
      theta ∈ bandSupportedParams m (2 * m + 2) ∧
      eta ∈ bandSupportedParams m (2 * m + 2) ∧
      forwardCumulantMap m (2 * m + 2) theta = t ∧
      reverseCumulantMap m (2 * m + 2) eta = t ∧
      (if b = .forward then theta ∈ genericParameterLocus m (2 * m + 2)
        else eta ∈ genericParameterLocus m (2 * m + 2))) ↔
    (t ∈ bandSupportedCumulants (2 * m + 2) ∧
      theta ∈ bandSupportedParams m (2 * m + 2) ∧
      eta ∈ bandSupportedParams m (2 * m + 2) ∧
      ∃ s : Direction → ℂ, ∀ P ∈ family,
        MvPolynomial.eval (atlasComplexIncidenceEval t theta eta s) P = 0)

/-- The common complex zero set of a finite observable polynomial family. -/
def atlasComplexObservableZeroSet
    (m : ℕ) (family : Finset (MvPolynomial (ℕ × ℕ) ℂ)) : Set (CumVec ℂ) :=
  { t | t ∈ bandSupportedCumulants (2 * m + 2) ∧
    ∀ P ∈ family, MvPolynomial.eval (fun ra => t ra.1 ra.2) P = 0 }

/-- Complex Zariski closure of the observable projection of the saturated
generic two-arrow incidence.  This is complex algebraic elimination only; it
does not describe projection over real atomic witnesses. -/
def atlasComplexObservableProjectionClosure (m : ℕ) (b : Direction) :
    Set (CumVec ℂ) :=
  zariskiClosure { t | t ∈ bandSupportedCumulants (2 * m + 2) ∧
    ∃ theta ∈ bandSupportedParams m (2 * m + 2),
    ∃ eta ∈ bandSupportedParams m (2 * m + 2),
      forwardCumulantMap m (2 * m + 2) theta = t ∧
      reverseCumulantMap m (2 * m + 2) eta = t ∧
      (if b = .forward then theta ∈ genericParameterLocus m (2 * m + 2)
        else eta ∈ genericParameterLocus m (2 * m + 2)) }

/-- A finite complex observable family cuts out exactly the complex projection
closure of a saturated generic incidence. -/
def IsExactComplexObservableElimination (m : ℕ) (b : Direction)
    (observable : Finset (MvPolynomial (ℕ × ℕ) ℂ)) : Prop :=
  atlasComplexObservableZeroSet m observable =
    atlasComplexObservableProjectionClosure m b

/-- Restriction of a full incidence assignment to the witness-eliminated
`(t, lambda)` coordinates. -/
def atlasForgetWitnesses {m : ℕ}
    (a : AtlasIncidenceCoord m → ℝ) : AtlasFiberAssignment m
  | Sum.inl ra => a (Sum.inl ra)
  | Sum.inr coord => a (Sum.inr (Sum.inl coord))

/-- Zariski closure of a real projection, retained only as a diagnostic notion
used by the counterexample module.  It is deliberately not the semantics of any
atlas construction-trace operation: complex Groebner elimination cannot compute
this real witness projection. -/
def atlasIncidenceProjectionClosure {m : ℕ}
    (family : Finset (MvPolynomial (AtlasIncidenceCoord m) ℝ)) :
    Set (AtlasFiberAssignment m) :=
  { a | ∀ Q : MvPolynomial (AtlasFiberCoord m) ℝ,
      (∀ x : AtlasIncidenceCoord m → ℝ,
        (∀ P ∈ family, MvPolynomial.eval x P = 0) →
        MvPolynomial.eval (atlasForgetWitnesses x) Q = 0) →
      MvPolynomial.eval a Q = 0 }

/-- Diagnostic predicate for exact real witness projection.  The effective atlas
does not require this predicate; Step 4 eliminates witnesses cellwise instead. -/
def IsExactWitnessElimination {m : ℕ}
    (incidence : Finset (MvPolynomial (AtlasIncidenceCoord m) ℝ))
    (fiber : Finset (MvPolynomial (AtlasFiberCoord m) ℝ)) : Prop :=
  { a | ∀ P ∈ fiber, MvPolynomial.eval a P = 0 } =
    atlasIncidenceProjectionClosure incidence

/-- Operation-specific semantics for every symbolic trace step.  Saturation and
Groebner elimination act only on the complex generic two-arrow incidence and
produce complex observable equations.  Real atomic witnesses are removed later,
cellwise, by `witnessCellRetention`; they are never assigned complex-elimination
semantics. -/
def AtlasTraceStep.IsSemanticallyCorrect {m : ℕ} (step : AtlasTraceStep m) : Prop :=
  match step.operation, step.inputs, step.output with
  | .saturationGroebnerElimination b, [.complexIncidence _], .complexObservable B =>
      IsExactComplexObservableElimination m b B
  | .idealIntersection, [.complexObservable A, .complexObservable B],
      .complexObservable C =>
      atlasComplexObservableZeroSet m C =
        atlasComplexObservableZeroSet m A ∪ atlasComplexObservableZeroSet m B
  | .realImaginarySplit, [.complexObservable A], .observable B =>
      atlasObservableZeroSet m B =
        { t | t ∈ bandSupportedCumulants (2 * m + 2) ∧
          complexifyCumVec t ∈ atlasComplexObservableZeroSet m A }
  | .cadBuchberger, _, _ => step.HasCitedCADFamilyShape
  | .cadElimination, _, _ => step.HasCitedCADFamilyShape
  | .cadIdealIntersection, _, _ => step.HasCitedCADFamilyShape
  | .cadSaturation, _, _ => step.HasCitedCADFamilyShape
  | .cadReductaGeneration, [.incidence A], .incidence B =>
      ∃ x, B = cadReductaFamily x A
  | .cadReductaGeneration, [.fiber A], .fiber B =>
      ∃ x, B = cadReductaFamily x A
  | .cadReductaGeneration, [.observable A], .observable B =>
      ∃ x, B = cadReductaFamily x A
  | .coefficientProjection, [.incidence A], .incidence B =>
      ∃ x, B = cadCoefficients x A
  | .coefficientProjection, [.fiber A], .fiber B =>
      ∃ x, B = cadCoefficients x A
  | .coefficientProjection, [.observable A], .observable B =>
      ∃ x, B = cadCoefficients x A
  | .discriminantProjection, [.incidence A], .incidence B =>
      ∃ x, B = cadDiscriminants x A
  | .discriminantProjection, [.fiber A], .fiber B =>
      ∃ x, B = cadDiscriminants x A
  | .discriminantProjection, [.observable A], .observable B =>
      ∃ x, B = cadDiscriminants x A
  | .principalSubresultantProjection, [.incidence A], .incidence B =>
      ∃ x, B = cadPrincipalSubresultants x A
  | .principalSubresultantProjection, [.fiber A], .fiber B =>
      ∃ x, B = cadPrincipalSubresultants x A
  | .principalSubresultantProjection, [.observable A], .observable B =>
      ∃ x, B = cadPrincipalSubresultants x A
  | .cadProjectionClosure, _, _ => step.HasCitedCADFamilyShape
  | .prefixCellProjection, [.incidence _], .observable _ => True
  | .prefixCellProjection, [.incidence _], .fiber _ => True
  | .witnessCellRetention _ _ _, [.fiber A], .fiber B => B = A
  | .realRootIsolation, [.fiber A], .fiber B => B = A
  | .realRootIsolation, [.observable A], .observable B => B = A
  | .sectionLifting, [.fiber A], .fiber B => B = A
  | .sectorLifting, [.fiber A], .fiber B => B = A
  | .signConditionTruth, [.fiber A], .fiber B => B = A
  | .signConditionTruth, [.observable A], .observable B => B = A
  | _, _, _ => False

/-- Exact arithmetic/sign-operation charge for one certified atlas step: the
length of its displayed slice of the cited primitive execution. -/
def AtlasTraceStep.operationCost {m : ℕ} (step : AtlasTraceStep m) : ℕ :=
  step.chargedPrimitives.length

/-- Complex-incidence families read or emitted by a trace step. -/
def AtlasTraceStep.complexIncidenceFamilies {m : ℕ} (step : AtlasTraceStep m) :
    List (Finset (MvPolynomial (AtlasComplexIncidenceCoord m) ℂ)) :=
  (step.inputs ++ [step.output]).filterMap fun family => match family with
    | .complexIncidence A => some A
    | _ => none

/-- Complex-observable families read or emitted by a trace step. -/
def AtlasTraceStep.complexObservableFamilies {m : ℕ} (step : AtlasTraceStep m) :
    List (Finset (MvPolynomial (ℕ × ℕ) ℂ)) :=
  (step.inputs ++ [step.output]).filterMap fun family => match family with
    | .complexObservable A => some A
    | _ => none

/-- Incidence-coordinate families read or emitted by a trace step. -/
def AtlasTraceStep.incidenceFamilies {m : ℕ} (step : AtlasTraceStep m) :
    List (Finset (MvPolynomial (AtlasIncidenceCoord m) ℝ)) :=
  (step.inputs ++ [step.output]).filterMap fun family => match family with
    | .incidence A => some A
    | _ => none

/-- Witness-eliminated fiber families read or emitted by a trace step. -/
def AtlasTraceStep.fiberFamilies {m : ℕ} (step : AtlasTraceStep m) :
    List (Finset (MvPolynomial (AtlasFiberCoord m) ℝ)) :=
  (step.inputs ++ [step.output]).filterMap fun family => match family with
    | .fiber A => some A
    | _ => none

/-- Observable families read or emitted by a trace step. -/
def AtlasTraceStep.observableFamilies {m : ℕ} (step : AtlasTraceStep m) :
    List (Finset (MvPolynomial (ℕ × ℕ) ℝ)) :=
  (step.inputs ++ [step.output]).filterMap fun family => match family with
    | .observable A => some A
    | _ => none

/-- An observable polynomial has constant mathematical sign on a base cell. -/
def ObservableSignInvariantOn (cell : Set (CumVec ℝ))
    (P : MvPolynomial (ℕ × ℕ) ℝ) : Prop :=
  ∀ t ∈ cell, ∀ t' ∈ cell,
    polynomialSign (MvPolynomial.eval (fun ra => t ra.1 ra.2) P) =
      polynomialSign (MvPolynomial.eval (fun ra => t' ra.1 ra.2) P)

/-- A trace step has the correct symbolic stage shape.  In particular, the
three CAD projection operations are not mere labels: their output family is
definitionally the corresponding shared generic CAD operator applied to the
declared input family.  The remaining operations change or preserve stages as
specified by the paper's elimination/lifting pipeline; their global correctness
is certified by the endpoint, retained-cell, and exact-section fields of
`EffectiveRealAtlasOutput`. -/
def AtlasTraceStep.IsWellTyped {m : ℕ} (step : AtlasTraceStep m) : Prop :=
  match step.operation, step.inputs, step.output with
  | .saturationGroebnerElimination _, [.complexIncidence _], .complexObservable _ => True
  | .idealIntersection, [.complexObservable _, .complexObservable _],
      .complexObservable _ => True
  | .realImaginarySplit, [.complexObservable _], .observable _ => True
  | .cadBuchberger, _, _ => step.HasCitedCADFamilyShape
  | .cadElimination, _, _ => step.HasCitedCADFamilyShape
  | .cadIdealIntersection, _, _ => step.HasCitedCADFamilyShape
  | .cadSaturation, _, _ => step.HasCitedCADFamilyShape
  | .cadReductaGeneration, [.incidence A], .incidence B =>
      ∃ x, B = cadReductaFamily x A
  | .cadReductaGeneration, [.fiber A], .fiber B =>
      ∃ x, B = cadReductaFamily x A
  | .cadReductaGeneration, [.observable A], .observable B =>
      ∃ x, B = cadReductaFamily x A
  | .coefficientProjection, [.incidence A], .incidence B =>
      ∃ x, B = cadCoefficients x A
  | .coefficientProjection, [.fiber A], .fiber B =>
      ∃ x, B = cadCoefficients x A
  | .coefficientProjection, [.observable A], .observable B =>
      ∃ x, B = cadCoefficients x A
  | .discriminantProjection, [.incidence A], .incidence B =>
      ∃ x, B = cadDiscriminants x A
  | .discriminantProjection, [.fiber A], .fiber B =>
      ∃ x, B = cadDiscriminants x A
  | .discriminantProjection, [.observable A], .observable B =>
      ∃ x, B = cadDiscriminants x A
  | .principalSubresultantProjection, [.incidence A], .incidence B =>
      ∃ x, B = cadPrincipalSubresultants x A
  | .principalSubresultantProjection, [.fiber A], .fiber B =>
      ∃ x, B = cadPrincipalSubresultants x A
  | .principalSubresultantProjection, [.observable A], .observable B =>
      ∃ x, B = cadPrincipalSubresultants x A
  | .cadProjectionClosure, _, _ => step.HasCitedCADFamilyShape
  | .prefixCellProjection, [.incidence _], .observable _ => True
  | .prefixCellProjection, [.incidence _], .fiber _ => True
  | .witnessCellRetention _ _ _, [.fiber _], .fiber _ => True
  | .realRootIsolation, [.fiber _], .fiber _ => True
  | .realRootIsolation, [.observable _], .observable _ => True
  | .sectionLifting, [.fiber _], .fiber _ => True
  | .sectorLifting, [.fiber _], .fiber _ => True
  | .signConditionTruth, [.fiber _], .fiber _ => True
  | .signConditionTruth, [.observable _], .observable _ => True
  | _, _, _ => False

/-- An observable polynomial family explicitly presents every base cell. -/
def DefinesAtlasBaseCellFamily (m : ℕ) {ι : Type}
    (cell : ι → Set (CumVec ℝ))
    (family : Finset (MvPolynomial (ℕ × ℕ) ℝ)) : Prop :=
  family.Nonempty ∧ ∀ i, ∃ equations nonnegative positive,
    equations ∪ nonnegative ∪ positive ⊆ family ∧
    cell i = { t |
      t ∈ bandSupportedCumulants (2 * m + 2) ∧
      (∀ P ∈ equations, MvPolynomial.eval (fun ra => t ra.1 ra.2) P = 0) ∧
      (∀ P ∈ nonnegative, 0 ≤ MvPolynomial.eval (fun ra => t ra.1 ra.2) P) ∧
      (∀ P ∈ positive, 0 < MvPolynomial.eval (fun ra => t ra.1 ra.2) P) }

/-- A finite construction trace starts Step 2 from the two complex generic
incidences, produces their observable elimination ideals and their intersection,
then runs real CAD and Step-4 witness-cell retention on the separately displayed
real incidence and `(t, lambda)` families. -/
structure CertifiedAtlasConstructionTrace (m : ℕ) (atlas : RealAtlasCADData m)
    (forwardComplexIncidence reverseComplexIncidence :
      Finset (MvPolynomial (AtlasComplexIncidenceCoord m) ℂ))
    (forwardComplexObservable reverseComplexObservable complexExceptional :
      Finset (MvPolynomial (ℕ × ℕ) ℂ))
    (forwardFamily reverseFamily : Finset (MvPolynomial (AtlasFiberCoord m) ℝ))
    (baseObservableFamily baseGeometryFamily :
      Finset (MvPolynomial (ℕ × ℕ) ℝ)) where
  steps : List (AtlasTraceStep m)
  citedExecution : AtlasCitedEffectiveExecution
  forwardIncidenceEmbedding :
    Fin citedExecution.forwardEliminationJob.r ↪ AtlasComplexIncidenceCoord m
  forwardObservableCoordinateMap :
    Fin citedExecution.forwardEliminationJob.r → (ℕ × ℕ)
  forward_observable_coordinates_injective :
    IsInjectiveOnRationalFamilyVariables forwardObservableCoordinateMap
      citedExecution.forwardResult.result.saturatedEliminationBasis
  forward_retained_coordinates_exact :
    ∀ i ∈ citedExecution.forwardEliminationJob.keep,
      forwardIncidenceEmbedding i = Sum.inl (forwardObservableCoordinateMap i)
  forward_cited_input_exact :
    rationalFamilyToComplexAlong forwardIncidenceEmbedding
      citedExecution.forwardEliminationJob.input = forwardComplexIncidence
  forward_cited_order_is_elimination :
    IsEffectiveEliminationMonomialOrder
      citedExecution.forwardEliminationJob.monomialOrder
      citedExecution.forwardEliminationJob.keep
  forward_cited_output_exact :
    rationalFamilyToComplexOnUsedCoordinates forwardObservableCoordinateMap
      citedExecution.forwardResult.result.saturatedEliminationBasis =
        forwardComplexObservable
  reverseIncidenceEmbedding :
    Fin citedExecution.reverseEliminationJob.r ↪ AtlasComplexIncidenceCoord m
  reverseObservableCoordinateMap :
    Fin citedExecution.reverseEliminationJob.r → (ℕ × ℕ)
  reverse_observable_coordinates_injective :
    IsInjectiveOnRationalFamilyVariables reverseObservableCoordinateMap
      citedExecution.reverseResult.result.saturatedEliminationBasis
  reverse_retained_coordinates_exact :
    ∀ i ∈ citedExecution.reverseEliminationJob.keep,
      reverseIncidenceEmbedding i = Sum.inl (reverseObservableCoordinateMap i)
  reverse_cited_input_exact :
    rationalFamilyToComplexAlong reverseIncidenceEmbedding
      citedExecution.reverseEliminationJob.input = reverseComplexIncidence
  reverse_cited_order_is_elimination :
    IsEffectiveEliminationMonomialOrder
      citedExecution.reverseEliminationJob.monomialOrder
      citedExecution.reverseEliminationJob.keep
  reverse_cited_output_exact :
    rationalFamilyToComplexOnUsedCoordinates reverseObservableCoordinateMap
      citedExecution.reverseResult.result.saturatedEliminationBasis =
        reverseComplexObservable
  intersectionObservableEmbedding :
    Fin citedExecution.observableIntersectionJob.r ↪ (ℕ × ℕ)
  forward_intersection_coordinates_exact :
    ∀ i ∈ citedExecution.forwardEliminationJob.keep,
      intersectionObservableEmbedding
          (citedExecution.dependentPipeline.forwardToIntersection i) =
        forwardObservableCoordinateMap i
  reverse_intersection_coordinates_exact :
    ∀ i ∈ citedExecution.reverseEliminationJob.keep,
      intersectionObservableEmbedding
          (citedExecution.dependentPipeline.reverseToIntersection i) =
        reverseObservableCoordinateMap i
  intersection_cited_left_input_exact :
    rationalFamilyToComplexAlong intersectionObservableEmbedding
      citedExecution.observableIntersectionJob.input = forwardComplexObservable
  intersection_cited_right_input_exact :
    rationalFamilyToComplexAlong intersectionObservableEmbedding
      citedExecution.observableIntersectionJob.secondInput = reverseComplexObservable
  intersection_cited_output_exact :
    rationalFamilyToComplexAlong intersectionObservableEmbedding
      citedExecution.intersectionResult.result.intersectionBasis = complexExceptional
  cadIncidenceEmbedding :
    Fin citedExecution.cadJob.r ↪ AtlasIncidenceCoord m
  cad_cited_exceptional_input_exact :
    rationalFamilyToRealAlong cadIncidenceEmbedding citedExecution.cadJob.input =
      atlasObservableIncidenceFamily m baseObservableFamily
  cad_cited_simultaneous_sign_input_exact :
    atlasObservableIncidenceFamily m baseObservableFamily ∪
        rationalFamilyToRealAlong cadIncidenceEmbedding citedExecution.cadJob.secondInput =
      (atlas.forwardEquations ∪ atlas.forwardNonnegative ∪ atlas.forwardPositive) ∪
        (atlas.reverseEquations ∪ atlas.reverseNonnegative ∪ atlas.reversePositive)
  cad_cited_complete_input_exact :
    rationalFamilyToRealAlong cadIncidenceEmbedding
        (citedExecution.cadJob.input ∪ citedExecution.cadJob.secondInput) =
      atlasObservableIncidenceFamily m baseObservableFamily ∪
        ((atlas.forwardEquations ∪ atlas.forwardNonnegative ∪ atlas.forwardPositive) ∪
          (atlas.reverseEquations ∪ atlas.reverseNonnegative ∪ atlas.reversePositive))
  cad_cited_order_exact :
    citedExecution.cadJob.order.map cadIncidenceEmbedding = atlas.order
  /-- Coordinate transports for the two cited prefix splits.  Their values on
  eliminated coordinates are irrelevant; injectivity is required exactly on
  variables occurring in the corresponding projected stage family. -/
  cadFiberCoordinateMap : Fin citedExecution.cadJob.r → AtlasFiberCoord m
  cadObservableCoordinateMap : Fin citedExecution.cadJob.r → (ℕ × ℕ)
  witnessPrefix : List (Fin citedExecution.cadJob.r)
  loadingPrefix : List (Fin citedExecution.cadJob.r)
  observableSuffix : List (Fin citedExecution.cadJob.r)
  cad_order_prefix_suffix_exact : citedExecution.cadJob.order =
    witnessPrefix ++ loadingPrefix ++ observableSuffix
  witness_prefix_exact : witnessPrefix.map cadIncidenceEmbedding =
    atlas.order.filter fun x => decide
      (atlasIncidenceVariableBlock x = .atomicWitnesses)
  loading_prefix_exact : loadingPrefix.map cadIncidenceEmbedding =
    atlas.order.filter fun x => decide
      (atlasIncidenceVariableBlock x = .loadingAndCumulants)
  observable_suffix_exact : observableSuffix.map cadIncidenceEmbedding =
    atlas.order.filter fun x => decide
      (atlasIncidenceVariableBlock x = .observable)
  fiber_coordinate_transport_exact : ∀ x ∈ loadingPrefix ++ observableSuffix,
    (match cadIncidenceEmbedding x with
      | Sum.inl ra => cadFiberCoordinateMap x = Sum.inl ra
      | Sum.inr (Sum.inl coord) => cadFiberCoordinateMap x = Sum.inr coord
      | Sum.inr (Sum.inr _) => False)
  observable_coordinate_transport_exact : ∀ x ∈ observableSuffix,
    ∃ ra, cadIncidenceEmbedding x = Sum.inl ra ∧
      cadObservableCoordinateMap x = ra
  fiber_projected_family_exact :
    let transported := realFamilyOnUsedCoordinates cadFiberCoordinateMap
      (effectiveCADFamilyAfterPrefix witnessPrefix
        (rationalPolynomialFamilyToReal
          (citedExecution.cadJob.input ∪ citedExecution.cadJob.secondInput)))
    transported = forwardFamily ∧ transported = reverseFamily
  base_geometry_family_exact :
    realFamilyOnUsedCoordinates cadObservableCoordinateMap
      (effectiveCADFamilyAfterPrefix (witnessPrefix ++ loadingPrefix)
        (rationalPolynomialFamilyToReal
          (citedExecution.cadJob.input ∪ citedExecution.cadJob.secondInput))) =
      baseGeometryFamily
  steps_nonempty : steps ≠ []
  steps_well_typed : ∀ step ∈ steps, step.IsWellTyped
  steps_semantically_correct : ∀ step ∈ steps, step.IsSemanticallyCorrect
  charged_primitives_match_operations : ∀ step ∈ steps,
    ∀ primitive ∈ step.chargedPrimitives,
      primitive.MatchesAtlasOperation step.operation
  /-- The per-step lists are contiguous slices whose concatenation is exactly
  the full cited primitive stream.  List equality supplies both coverage and
  disjoint positional use: no cited charge is dropped, duplicated, or silently
  reassigned outside these slices. -/
  charged_primitives_exact :
    steps.flatMap (fun step => step.chargedPrimitives) = citedExecution.primitiveCharges
  cited_cad_steps_linked : ∀ step ∈ steps,
    step.operation.IsCitedCADOperation →
      ∃ sourceStepIndex sourceStep,
        citedExecution.cadResult.result.payload.trace[sourceStepIndex]? = some sourceStep ∧
        step.IsLinkedToCitedCADStep sourceStepIndex sourceStep
  cited_cad_source_steps_consumed : ∀ sourceStepIndex sourceStep,
    citedExecution.cadResult.result.payload.trace[sourceStepIndex]? = some sourceStep →
      ∃ step ∈ steps, step.IsLinkedToCitedCADStep sourceStepIndex sourceStep
  cited_cad_retention_rows_present :
    ∃ sourceStep ∈ citedExecution.cadResult.result.payload.trace,
      sourceStep.operation = .witnessCellRetention ∧
      sourceStep.producedRetentionRowCodes ≠ []
  cited_cad_projects_observable_geometry :
    ∃ sourceStep ∈ citedExecution.cadResult.result.payload.trace,
      sourceStep.operation = .prefixCellProjection ∧
      sourceStep.producedPrefixProjectionCertificateCodes ≠ []
  starts_forward : ∃ step ∈ steps,
    step.operation = .saturationGroebnerElimination .forward ∧
    step.inputs = [.complexIncidence forwardComplexIncidence] ∧
    step.output = .complexObservable forwardComplexObservable
  starts_reverse : ∃ step ∈ steps,
    step.operation = .saturationGroebnerElimination .reverse ∧
    step.inputs = [.complexIncidence reverseComplexIncidence] ∧
    step.output = .complexObservable reverseComplexObservable
  has_ideal_intersection : ∃ step ∈ steps,
    step.operation = .idealIntersection ∧
    step.inputs = [.complexObservable forwardComplexObservable,
      .complexObservable reverseComplexObservable] ∧
    step.output = .complexObservable complexExceptional
  has_real_imaginary_split : ∃ step ∈ steps,
    step.operation = .realImaginarySplit ∧
    step.inputs = [.complexObservable complexExceptional] ∧
    step.output = .observable baseObservableFamily
  has_reducta_generation : ∃ step ∈ steps, step.operation = .cadReductaGeneration
  has_coefficient_projection : ∃ step ∈ steps, step.operation = .coefficientProjection
  has_discriminant_projection : ∃ step ∈ steps, step.operation = .discriminantProjection
  has_principal_subresultants : ∃ step ∈ steps,
    step.operation = .principalSubresultantProjection
  has_prefix_cell_projection : ∃ step ∈ steps,
    step.operation = .prefixCellProjection
  has_real_root_isolation : ∃ step ∈ steps, step.operation = .realRootIsolation
  has_section_lifting : ∃ step ∈ steps, step.operation = .sectionLifting
  has_sector_lifting : ∃ step ∈ steps, step.operation = .sectorLifting
  has_sign_condition_truth : ∃ step ∈ steps, step.operation = .signConditionTruth
  outputs_forward_family : ∃ step ∈ steps, step.output = .fiber forwardFamily
  outputs_reverse_family : ∃ step ∈ steps, step.output = .fiber reverseFamily
  outputs_base_observable_family : ∃ step ∈ steps,
    step.output = .observable baseObservableFamily
  outputs_base_geometry_family : ∃ step ∈ steps,
    step.operation = .prefixCellProjection ∧
      step.output = .observable baseGeometryFamily

/-- Exact accounting consequence of the slice certificate: the high-level
atlas total is the combined cited primitive count. -/
theorem CertifiedAtlasConstructionTrace.operationCost_sum_eq_cited
    {m : ℕ} {atlas : RealAtlasCADData m}
    {forwardComplexIncidence reverseComplexIncidence :
      Finset (MvPolynomial (AtlasComplexIncidenceCoord m) ℂ)}
    {forwardComplexObservable reverseComplexObservable complexExceptional :
      Finset (MvPolynomial (ℕ × ℕ) ℂ)}
    {forwardFamily reverseFamily : Finset (MvPolynomial (AtlasFiberCoord m) ℝ)}
    {baseObservableFamily baseGeometryFamily :
      Finset (MvPolynomial (ℕ × ℕ) ℝ)}
    (trace : CertifiedAtlasConstructionTrace m atlas
      forwardComplexIncidence reverseComplexIncidence
      forwardComplexObservable reverseComplexObservable complexExceptional
      forwardFamily reverseFamily baseObservableFamily baseGeometryFamily) :
    (trace.steps.map AtlasTraceStep.operationCost).sum =
      trace.citedExecution.symbolicOperationCount := by
  calc
    (trace.steps.map AtlasTraceStep.operationCost).sum =
        (trace.steps.flatMap (fun step => step.chargedPrimitives)).length := by
      rw [List.length_flatMap]
      rfl
    _ = trace.citedExecution.primitiveCharges.length :=
      congrArg List.length trace.charged_primitives_exact
    _ = trace.citedExecution.symbolicOperationCount :=
      trace.citedExecution.primitiveCharges_length

/-- Rational finite syntax for a polynomial.  Coefficients and exponent lists
are discrete data suitable for a genuine machine encoding. -/
structure AtlasPolynomialCode (σ : Type) where
  terms : List (ℚ × List (σ × ℕ))
  deriving Encodable

/-- Finite syntax for one recursively lifted CAD cell.  The six constructors
record the zero-dimensional point and all five lifting cases of
`IsRecursivelyLiftedCADCell`: a root-free whole fibre, a root section, and the
three lower/bounded/upper sectors.  Root indices are exact symbolic indices in
the ordered real-root stack; evaluating signs or comparing arbitrary reals is
not part of this discrete code. -/
inductive AtlasCellCode
  | point
  | wholeFiber (base : AtlasCellCode)
  | section (rootIndex : ℕ) (base : AtlasCellCode)
  | lowerSector (base : AtlasCellCode)
  | boundedSector (lowerIndex : ℕ) (base : AtlasCellCode)
  | upperSector (lowerIndex : ℕ) (base : AtlasCellCode)
  deriving Encodable

/-- Forget the effective cited certificate's rational root presentations and
sign row while retaining its exact recursive CAD-cell shape and root indices. -/
def EffectiveCADCellCertificate.toAtlasCellCode {r : ℕ} :
    EffectiveCADCellCertificate r → AtlasCellCode
  | .point => .point
  | .wholeFiber base => .wholeFiber base.toAtlasCellCode
  | .section root base => .section root.rootIndex base.toAtlasCellCode
  | .lowerSector baseRoot base => .lowerSector base.toAtlasCellCode
  | .boundedSector lower _upper base =>
      .boundedSector lower.rootIndex base.toAtlasCellCode
  | .upperSector lower base => .upperSector lower.rootIndex base.toAtlasCellCode

/-- Exact interpretation of finite cell syntax in the generic recursive CAD
cell language.  This ties every machine-emitted geometry code to the actual
section/sector set it denotes, rather than merely recording a constructor tag. -/
def AtlasCellCode.Realizes {σ : Type} [DecidableEq σ] :
    Finset (MvPolynomial σ ℝ) → List σ → AtlasCellCode → Set (σ → ℝ) → Prop
  | _, [], .point, cell => cell = { a | ∀ x, a x = 0 }
  | family, x :: xs, .wholeFiber baseCode, cell =>
      ∃ base, Realizes (cadProjectionStep x family) xs baseCode base ∧
        (∀ a ∈ base, cadRealRootsAt x family a = ∅) ∧
        cell = { a | cadEraseCoordinate x a ∈ base }
  | family, x :: xs, .section rootIndex baseCode, cell =>
      ∃ base, Realizes (cadProjectionStep x family) xs baseCode base ∧
        ∃ root, IsCADAlgebraicRoot x base rootIndex root family ∧
          cell = { a | cadEraseCoordinate x a ∈ base ∧
            a x = root (cadEraseCoordinate x a) }
  | family, x :: xs, .lowerSector baseCode, cell =>
      ∃ base, Realizes (cadProjectionStep x family) xs baseCode base ∧
        ∃ upper, IsCADAlgebraicRoot x base 0 upper family ∧
          cell = { a | cadEraseCoordinate x a ∈ base ∧
            a x < upper (cadEraseCoordinate x a) }
  | family, x :: xs, .boundedSector lowerIndex baseCode, cell =>
      ∃ base, Realizes (cadProjectionStep x family) xs baseCode base ∧
        ∃ lower upper,
          IsCADAlgebraicRoot x base lowerIndex lower family ∧
          IsCADAlgebraicRoot x base (lowerIndex + 1) upper family ∧
          (∀ a ∈ base, lower a < upper a) ∧
          cell = { a | cadEraseCoordinate x a ∈ base ∧
            lower (cadEraseCoordinate x a) < a x ∧
            a x < upper (cadEraseCoordinate x a) }
  | family, x :: xs, .upperSector lowerIndex baseCode, cell =>
      ∃ base, Realizes (cadProjectionStep x family) xs baseCode base ∧
        ∃ lower, IsCADLastAlgebraicRoot x base lowerIndex lower family ∧
          cell = { a | cadEraseCoordinate x a ∈ base ∧
            lower (cadEraseCoordinate x a) < a x }
  | _, _, _, _ => False

/-- Interpret rational polynomial syntax as an actual real multivariate
polynomial. -/
def AtlasPolynomialCode.toReal {σ : Type} [DecidableEq σ]
    (code : AtlasPolynomialCode σ) : MvPolynomial σ ℝ :=
  code.terms.foldl (fun P term =>
    P + MvPolynomial.monomial
      (term.2.foldl (fun exponents xe => exponents + Finsupp.single xe.1 xe.2) 0)
      (term.1 : ℝ)) 0

/-- Entire discrete symbolic payload emitted by the atlas construction machine.
Every polynomial list is rational syntax; the fields of
`EffectiveRealAtlasOutput` below identify its real interpretation with the
actual incidence, fiber, base, and sign-test families. -/
structure EncodedAtlasConstruction (m : ℕ) where
  forwardComplexIncidence : List (AtlasPolynomialCode (AtlasComplexIncidenceCoord m))
  reverseComplexIncidence : List (AtlasPolynomialCode (AtlasComplexIncidenceCoord m))
  forwardComplexObservable : List (AtlasPolynomialCode (ℕ × ℕ))
  reverseComplexObservable : List (AtlasPolynomialCode (ℕ × ℕ))
  complexExceptional : List (AtlasPolynomialCode (ℕ × ℕ))
  forwardIncidence : List (AtlasPolynomialCode (AtlasIncidenceCoord m))
  reverseIncidence : List (AtlasPolynomialCode (AtlasIncidenceCoord m))
  forwardFiber : List (AtlasPolynomialCode (AtlasFiberCoord m))
  reverseFiber : List (AtlasPolynomialCode (AtlasFiberCoord m))
  observableBase : List (AtlasPolynomialCode (ℕ × ℕ))
  observableGeometry : List (AtlasPolynomialCode (ℕ × ℕ))
  signTests : List (AtlasPolynomialCode (ℕ × ℕ))
  baseOrder : List (ℕ × ℕ)
  forwardOrder : List (AtlasFiberCoord m)
  reverseOrder : List (AtlasFiberCoord m)
  baseCellCount : ℕ
  baseCells : List AtlasCellCode
  forwardCandidateCellCounts : List ℕ
  reverseCandidateCellCounts : List ℕ
  forwardRetainedCellCounts : List ℕ
  reverseRetainedCellCounts : List ℕ
  forwardCandidateCells : List (List AtlasCellCode)
  reverseCandidateCells : List (List AtlasCellCode)
  forwardRetainedSelections : List (List ℕ)
  reverseRetainedSelections : List (List ℕ)
  traceIncidenceFamilies : List (List (AtlasPolynomialCode (AtlasIncidenceCoord m)))
  traceFiberFamilies : List (List (AtlasPolynomialCode (AtlasFiberCoord m)))
  traceObservableFamilies : List (List (AtlasPolynomialCode (ℕ × ℕ)))
  traceComplexIncidenceFamilies :
    List (List (AtlasPolynomialCode (AtlasComplexIncidenceCoord m)))
  traceComplexObservableFamilies : List (List (AtlasPolynomialCode (ℕ × ℕ)))
  operations : List AtlasTraceOperation
  lookupRows : List (List ℕ × Bool × Bool)
  deriving Encodable

/-- A real polynomial family is exactly the interpretation of a displayed list
of rational polynomial codes. -/
def PolynomialCodesRealize {σ : Type} [DecidableEq σ]
    (codes : List (AtlasPolynomialCode σ))
    (family : Finset (MvPolynomial σ ℝ)) : Prop :=
  codes.Nodup ∧ (codes.map AtlasPolynomialCode.toReal).toFinset = family

/-- Interpret the same rational syntax as a complex polynomial. -/
def AtlasPolynomialCode.toComplex {σ : Type} [DecidableEq σ]
    (code : AtlasPolynomialCode σ) : MvPolynomial σ ℂ :=
  code.terms.foldl (fun P term =>
    P + MvPolynomial.monomial
      (term.2.foldl (fun exponents xe => exponents + Finsupp.single xe.1 xe.2) 0)
      (term.1 : ℂ)) 0

/-- A complex polynomial family is exactly the interpretation of rational
polynomial codes. -/
def ComplexPolynomialCodesRealize {σ : Type} [DecidableEq σ]
    (codes : List (AtlasPolynomialCode σ))
    (family : Finset (MvPolynomial σ ℂ)) : Prop :=
  codes.Nodup ∧ (codes.map AtlasPolynomialCode.toComplex).toFinset = family

/-- Every intermediate family in a machine payload decodes, in order, to the
corresponding family actually read or emitted by the certified trace. -/
def PolynomialCodeFamiliesRealize {σ : Type} [DecidableEq σ]
    (codes : List (List (AtlasPolynomialCode σ)))
    (families : List (Finset (MvPolynomial σ ℝ))) : Prop :=
  List.Forall₂ PolynomialCodesRealize codes families

/-- Every complex intermediate family in the payload decodes to the family
actually read or emitted by the certified Step-2 trace. -/
def ComplexPolynomialCodeFamiliesRealize {σ : Type} [DecidableEq σ]
    (codes : List (List (AtlasPolynomialCode σ)))
    (families : List (Finset (MvPolynomial σ ℂ))) : Prop :=
  List.Forall₂ ComplexPolynomialCodesRealize codes families

/-- Encode the three-valued sign alphabet by natural numbers for the machine
payload. -/
def atlasPolynomialSignCode : PolynomialSign → ℕ
  | .negative => 0
  | .zero => 1
  | .positive => 2

/-- A concrete halting partial-recursive run producing the complete finite
symbolic payload.  Its output is required to be the `Encodable` code of the
payload actually used by the atlas, so the effectivity witness cannot be an
unrelated existence Prop.  The existential `evaln` fuel witnesses halting only;
it is not compared with the separate real-algebraic arithmetic/sign-operation
count. -/
structure AtlasMachineExecution (m : ℕ) (payload : EncodedAtlasConstruction m) where
  code : Nat.Partrec.Code
  inputCode : ℕ
  outputCode : ℕ
  fuel : ℕ
  input_eq : inputCode = m
  output_eq : outputCode = Encodable.encode payload
  halts_within : code.evaln fuel inputCode = some outputCode

/-- Observable-coordinate count `q_K`, for `K = 2m+2`. -/
def atlasObservableCoordinateCount (m : ℕ) : ℕ :=
  let K := 2 * m + 2
  K * (K + 3) / 2 - 2

/-- Structural-coordinate count `p_K = (m+2)K-1`. -/
def atlasParameterCoordinateCount (m : ℕ) : ℕ := (m + 2) * (2 * m + 2) - 1

/-- Number of real coordinates in the simultaneous two-arrow incidence input. -/
def atlasSourceCoordinateCount (m : ℕ) : ℕ :=
  atlasObservableCoordinateCount m + 2 * atlasParameterCoordinateCount m +
    4 * (m + 2) ^ 2

/-- Explicit degree bound from the cumulant/moment equations and the two
genericity-saturation products. -/
def atlasSourceDegreeBound (m : ℕ) : ℕ :=
  max (2 * m + 3) (1 + m + m * (m - 1) / 2 + (m + 2) * (2 * m + 1))

/-- The concrete incidence presentation has a positive degree envelope.  This
is derived from the displayed formula, rather than assumed by the atlas
theorem, and supplies the `1 ≤ D` domain premise of the cited complexity
interface. -/
theorem atlasSourceDegreeBound_positive (m : ℕ) :
    1 ≤ atlasSourceDegreeBound m := by
  unfold atlasSourceDegreeBound
  omega

/-- The largest total degree in one finite polynomial family.  This is a
paper-side bookkeeping operation: it is evaluated only after the cited
elimination output has been returned, so it does not pretend that the
pre-elimination incidence bound also bounds a Gröbner basis. -/
def atlasPolynomialFamilyDegreeMaximum {K : Type} [Field K] [DecidableEq K]
    {r : ℕ} (family : Finset (MvPolynomial (Fin r) K)) : ℕ :=
  family.sup MvPolynomial.totalDegree

/-- The largest total degree charged by one supplied algebra job. -/
def atlasGroebnerJobDegreeMaximum {K : Type} [Field K] [DecidableEq K]
    (job : EffectiveGroebnerJobOver K) : ℕ :=
  atlasPolynomialFamilyDegreeMaximum
    (job.input ∪ job.secondInput ∪ {job.saturating})

/-- The largest total degree charged by one supplied CAD input.  Generated CAD
projection polynomials are outputs of the cited run and are deliberately not
reclassified as inputs in this envelope. -/
def atlasCADJobDegreeMaximum (job : EffectiveRationalCADJob) : ℕ :=
  max (atlasPolynomialFamilyDegreeMaximum job.input)
    (max (atlasPolynomialFamilyDegreeMaximum job.secondInput)
      job.saturating.totalDegree)

theorem atlasPolynomialFamily_degreeBoundedBy_maximum
    {K : Type} [Field K] [DecidableEq K] {r : ℕ}
    (family : Finset (MvPolynomial (Fin r) K)) :
    EffectivePolynomialFamilyDegreeBoundedBy family
      (atlasPolynomialFamilyDegreeMaximum family) := by
  intro P hP
  exact Finset.le_sup hP

theorem atlasGroebnerJob_degreeBoundedBy_maximum
    {K : Type} [Field K] [DecidableEq K]
    (job : EffectiveGroebnerJobOver K) :
    job.DegreeBoundedBy (atlasGroebnerJobDegreeMaximum job) := by
  intro P hP
  exact Finset.le_sup hP

/-- Proves the stated mathematical property of atlas CADJob degree Bounded By maximum. -/
theorem atlasCADJob_degreeBoundedBy_maximum (job : EffectiveRationalCADJob) :
    job.DegreeBoundedBy (atlasCADJobDegreeMaximum job) := by
  intro P hP
  simp only [Finset.mem_union, Finset.mem_singleton] at hP
  rcases hP with (hP | hP) | rfl
  · exact (Finset.le_sup hP).trans (by
      unfold atlasCADJobDegreeMaximum atlasPolynomialFamilyDegreeMaximum
      omega)
  · exact (Finset.le_sup hP).trans (by
      unfold atlasCADJobDegreeMaximum atlasPolynomialFamilyDegreeMaximum
      omega)
  · unfold atlasCADJobDegreeMaximum atlasPolynomialFamilyDegreeMaximum
    omega

/-- Post-elimination degree envelope for the actual paper execution.  In
addition to the exact source-incidence degree, this finite maximum charges the
two supplied elimination jobs, their returned saturated elimination bases,
the dependent intersection job and its returned intersection basis, and the
CAD input that consumes that basis. -/
def atlasChargedDegreeBound (m : ℕ) (execution : AtlasCitedEffectiveExecution) : ℕ :=
  max (atlasSourceDegreeBound m)
    (max (atlasGroebnerJobDegreeMaximum execution.forwardEliminationJob)
      (max (atlasGroebnerJobDegreeMaximum execution.reverseEliminationJob)
        (max (atlasPolynomialFamilyDegreeMaximum
            execution.dependentPipeline.forwardResult.result.saturatedEliminationBasis)
          (max (atlasPolynomialFamilyDegreeMaximum
              execution.dependentPipeline.reverseResult.result.saturatedEliminationBasis)
            (max (atlasGroebnerJobDegreeMaximum
                execution.dependentPipeline.intersectionJob)
              (max (atlasPolynomialFamilyDegreeMaximum
                  execution.dependentPipeline.intersectionResult.result.intersectionBasis)
                (atlasCADJobDegreeMaximum execution.cadJob)))))))

/-- Proves the stated mathematical property of atlas Source Degree Bound le charged. -/
theorem atlasSourceDegreeBound_le_charged (m : ℕ)
    (execution : AtlasCitedEffectiveExecution) :
    atlasSourceDegreeBound m ≤ atlasChargedDegreeBound m execution := by
  exact Nat.le_max_left _ _

/-- Proves the stated mathematical property of atlas Charged Degree Bound positive. -/
theorem atlasChargedDegreeBound_positive (m : ℕ)
    (execution : AtlasCitedEffectiveExecution) :
    1 ≤ atlasChargedDegreeBound m execution :=
  (atlasSourceDegreeBound_positive m).trans
    (atlasSourceDegreeBound_le_charged m execution)

/-- The finite maximum really bounds every input and returned basis charged by
the dependent two-arrow elimination/intersection pipeline. -/
theorem atlasDependentPipeline_degreeBoundedBy_charged (m : ℕ)
    (execution : AtlasCitedEffectiveExecution) :
    execution.dependentPipeline.DegreeBoundedBy
      (atlasChargedDegreeBound m execution) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun P hP =>
      (atlasGroebnerJob_degreeBoundedBy_maximum
        execution.forwardEliminationJob P hP).trans (by
          unfold atlasChargedDegreeBound
          omega)
  · exact fun P hP =>
      (atlasGroebnerJob_degreeBoundedBy_maximum
        execution.reverseEliminationJob P hP).trans (by
          unfold atlasChargedDegreeBound
          omega)
  · exact fun P hP =>
      (atlasPolynomialFamily_degreeBoundedBy_maximum
        execution.dependentPipeline.forwardResult.result.saturatedEliminationBasis
          P hP).trans (by
            unfold atlasChargedDegreeBound
            omega)
  · exact fun P hP =>
      (atlasPolynomialFamily_degreeBoundedBy_maximum
        execution.dependentPipeline.reverseResult.result.saturatedEliminationBasis
          P hP).trans (by
            unfold atlasChargedDegreeBound
            omega)
  · exact fun P hP =>
      (atlasGroebnerJob_degreeBoundedBy_maximum
        execution.dependentPipeline.intersectionJob P hP).trans (by
          unfold atlasChargedDegreeBound
          omega)
  · exact fun P hP =>
      (atlasPolynomialFamily_degreeBoundedBy_maximum
        execution.dependentPipeline.intersectionResult.result.intersectionBasis
          P hP).trans (by
            unfold atlasChargedDegreeBound
            omega)

/-- The same charged maximum bounds the exact CAD input.  The generated CAD
projection family is intentionally absent: it is an output, not an input to the
universal complexity call. -/
theorem atlasCADJob_degreeBoundedBy_charged (m : ℕ)
    (execution : AtlasCitedEffectiveExecution) :
    execution.cadJob.DegreeBoundedBy (atlasChargedDegreeBound m execution) := by
  intro P hP
  exact (atlasCADJob_degreeBoundedBy_maximum execution.cadJob P hP).trans (by
    unfold atlasChargedDegreeBound
    omega)

/-- Explicit size and complexity receipt for the finite symbolic construction.
The source-incidence bound remains the displayed cumulant-equation formula;
the distinct charged bound is chosen after the cited elimination pipeline and
is the degree parameter used by the combined complexity theorem. -/
structure AtlasComplexityCertificate (m : ℕ) (traceLength : ℕ)
    (execution : AtlasCitedEffectiveExecution) where
  q : ℕ
  p : ℕ
  n : ℕ
  sourceCoordinateCount : ℕ
  sourcePolynomialCount : ℕ
  sourceDegreeBound : ℕ
  chargedDegreeBound : ℕ
  arithmeticSignOperations : ℕ
  exponentConstant : ℕ
  exponentOffset : ℕ
  recordedTraceLength : ℕ
  q_eq : q = atlasObservableCoordinateCount m
  p_eq : p = atlasParameterCoordinateCount m
  n_eq : n = m + 2
  source_coordinates_eq : sourceCoordinateCount = atlasSourceCoordinateCount m
  source_degree_eq : sourceDegreeBound = atlasSourceDegreeBound m
  source_degree_positive : 1 ≤ sourceDegreeBound
  charged_degree_eq : chargedDegreeBound = atlasChargedDegreeBound m execution
  source_degree_le_charged : sourceDegreeBound ≤ chargedDegreeBound
  charged_degree_positive : 1 ≤ chargedDegreeBound
  universal_algorithm_constants :
    UniversalEffectiveRationalGroebnerCADBound exponentConstant exponentOffset
  operations_le_bound : arithmeticSignOperations ≤
    (max 2 (sourcePolynomialCount * chargedDegreeBound)) ^
      (2 ^ (exponentConstant * sourceCoordinateCount + exponentOffset))
  trace_length_eq : recordedTraceLength = traceLength
  trace_length_le : recordedTraceLength ≤ arithmeticSignOperations

/-- The paper-specific **effective/evaluable** real exceptional atlas output.

Besides the raw full `(t, lambda, w, z)` construction, this record exposes the
post-elimination `(t, lambda)` cells themselves.  Their direct lambda sections —
not existential projections left in witness space — are exactly the complete
forward and reverse feasible fibers, including singular, nongeneric, and boundary
branches.  Effectivity is finite symbolic data: explicit polynomial families and
orders, an exhaustive finite sign-oracle lookup table, and a certified construction
trace with a displayed doubly-exponential operation bound.  The lookup tests are
the displayed CAD decision family, not merely the exceptional-closure equations:
they include the observable real/imaginary equations and every observable
coefficient, discriminant, principal subresultant, and retained-cell sign
polynomial carried by the real projection/retention trace.

The record is deliberately separate from `realAtlasHandleOutput`: the latter is
only the cited, paper-agnostic classical CAD theorem.  Producing this record is the
paper-specific conclusion of `exactRealExceptionalAtlas`. -/
structure EffectiveRealAtlasOutput (m : ℕ) where
  atlas : RealAtlasCADData m
  forwardComplexIncidenceFamily :
    Finset (MvPolynomial (AtlasComplexIncidenceCoord m) ℂ)
  reverseComplexIncidenceFamily :
    Finset (MvPolynomial (AtlasComplexIncidenceCoord m) ℂ)
  forwardComplexObservableFamily : Finset (MvPolynomial (ℕ × ℕ) ℂ)
  reverseComplexObservableFamily : Finset (MvPolynomial (ℕ × ℕ) ℂ)
  complexExceptionalFamily : Finset (MvPolynomial (ℕ × ℕ) ℂ)
  forward_complex_incidence_exact : DefinesComplexGenericIncidenceEquations m .forward
    forwardComplexIncidenceFamily
  reverse_complex_incidence_exact : DefinesComplexGenericIncidenceEquations m .reverse
    reverseComplexIncidenceFamily
  forward_complex_elimination_exact : IsExactComplexObservableElimination m .forward
    forwardComplexObservableFamily
  reverse_complex_elimination_exact : IsExactComplexObservableElimination m .reverse
    reverseComplexObservableFamily
  complex_exceptional_exact :
    atlasComplexObservableZeroSet m complexExceptionalFamily = genericCompatibilityClosure m
  baseObservableFamily : Finset (MvPolynomial (ℕ × ℕ) ℝ)
  /-- The effective CAD stage family after both the witness and structural
  prefixes have been projected.  Unlike `baseObservableFamily`, this family
  describes the recursive geometry of individual observable base cells. -/
  baseGeometryFamily : Finset (MvPolynomial (ℕ × ℕ) ℝ)
  baseOrder : List (ℕ × ℕ)
  base_order_nodup : baseOrder.Nodup
  base_order_covers : ∀ P ∈ baseGeometryFamily, ∀ x ∈ P.vars, x ∈ baseOrder
  baseCellCode : Fin atlas.baseCellCount → AtlasCellCode
  base_code_realizes : ∀ i,
    (baseCellCode i).Realizes baseGeometryFamily baseOrder
      { a : (ℕ × ℕ) → ℝ | (fun r s => a (r, s)) ∈ atlas.baseCell i }
  forwardFiberFamily : Finset (MvPolynomial (AtlasFiberCoord m) ℝ)
  reverseFiberFamily : Finset (MvPolynomial (AtlasFiberCoord m) ℝ)
  forwardFiberOrder : List (AtlasFiberCoord m)
  reverseFiberOrder : List (AtlasFiberCoord m)
  forward_order_nodup : forwardFiberOrder.Nodup
  reverse_order_nodup : reverseFiberOrder.Nodup
  forward_order_covers : ∀ P ∈ forwardFiberFamily, ∀ x ∈ P.vars, x ∈ forwardFiberOrder
  reverse_order_covers : ∀ P ∈ reverseFiberFamily, ∀ x ∈ P.vars, x ∈ reverseFiberOrder
  forward_order_loading_before_observable :
    IsAtlasFiberVariableOrder forwardFiberOrder
  reverse_order_loading_before_observable :
    IsAtlasFiberVariableOrder reverseFiberOrder
  forwardCandidateCellCount : Fin atlas.baseCellCount → ℕ
  reverseCandidateCellCount : Fin atlas.baseCellCount → ℕ
  forwardCandidateCell : ∀ i, Fin (forwardCandidateCellCount i) →
    Set (AtlasFiberAssignment m)
  reverseCandidateCell : ∀ i, Fin (reverseCandidateCellCount i) →
    Set (AtlasFiberAssignment m)
  forwardCandidateCellCode : ∀ i, Fin (forwardCandidateCellCount i) → AtlasCellCode
  reverseCandidateCellCode : ∀ i, Fin (reverseCandidateCellCount i) → AtlasCellCode
  forward_candidate_code_realizes : ∀ i k,
    (forwardCandidateCellCode i k).Realizes forwardFiberFamily forwardFiberOrder
      (forwardCandidateCell i k)
  reverse_candidate_code_realizes : ∀ i k,
    (reverseCandidateCellCode i k).Realizes reverseFiberFamily reverseFiberOrder
      (reverseCandidateCell i k)
  forwardRetainedCellCount : Fin atlas.baseCellCount → ℕ
  reverseRetainedCellCount : Fin atlas.baseCellCount → ℕ
  forwardRetainedCell : ∀ i, Fin (forwardRetainedCellCount i) → Set (AtlasFiberAssignment m)
  reverseRetainedCell : ∀ i, Fin (reverseRetainedCellCount i) → Set (AtlasFiberAssignment m)
  forwardRetainedSelection : ∀ i, Fin (forwardRetainedCellCount i) →
    Fin (forwardCandidateCellCount i)
  reverseRetainedSelection : ∀ i, Fin (reverseRetainedCellCount i) →
    Fin (reverseCandidateCellCount i)
  forward_retained_selected : ∀ i k,
    forwardRetainedCell i k = forwardCandidateCell i (forwardRetainedSelection i k)
  reverse_retained_selected : ∀ i k,
    reverseRetainedCell i k = reverseCandidateCell i (reverseRetainedSelection i k)
  forward_cell_nonempty : ∀ i k, (forwardRetainedCell i k).Nonempty
  reverse_cell_nonempty : ∀ i k, (reverseRetainedCell i k).Nonempty
  forward_recursive : ∀ i k,
    IsRecursivelyLiftedCADCell forwardFiberFamily forwardFiberOrder (forwardRetainedCell i k)
  reverse_recursive : ∀ i k,
    IsRecursivelyLiftedCADCell reverseFiberFamily reverseFiberOrder (reverseRetainedCell i k)
  forward_stack_disjoint : ∀ i k l, k ≠ l →
    Disjoint (forwardRetainedCell i k) (forwardRetainedCell i l)
  reverse_stack_disjoint : ∀ i k l, k ≠ l →
    Disjoint (reverseRetainedCell i k) (reverseRetainedCell i l)
  forward_stack_cylindrical : ∀ i,
    IsCylindricallyArranged forwardFiberOrder (forwardRetainedCell i)
  reverse_stack_cylindrical : ∀ i,
    IsCylindricallyArranged reverseFiberOrder (reverseRetainedCell i)
  forward_projects_base : ∀ i k,
    { t | ∃ lam, atlasFiberEval t lam ∈ forwardRetainedCell i k } = atlas.baseCell i
  reverse_projects_base : ∀ i k,
    { t | ∃ lam, atlasFiberEval t lam ∈ reverseRetainedCell i k } = atlas.baseCell i
  forward_witness_eliminated : ∀ i t, t ∈ atlas.baseCell i →
    { lam | ∃ w z, ∃ k, atlasIncidenceEval t lam w z ∈ atlas.forwardCell i k } =
      { lam | ∃ k, atlasFiberEval t lam ∈ forwardRetainedCell i k }
  reverse_witness_eliminated : ∀ i t, t ∈ atlas.baseCell i →
    { lam | ∃ w z, ∃ k, atlasIncidenceEval t lam w z ∈ atlas.reverseCell i k } =
      { lam | ∃ k, atlasFiberEval t lam ∈ reverseRetainedCell i k }
  forward_section_exact : ∀ i t, t ∈ atlas.baseCell i →
    { lam | ∃ k, atlasFiberEval t lam ∈ forwardRetainedCell i k } =
      realAtlasForwardSection m t
  reverse_section_exact : ∀ i t, t ∈ atlas.baseCell i →
    { lam | ∃ k, atlasFiberEval t lam ∈ reverseRetainedCell i k } =
      realAtlasReverseSection m t
  trace : CertifiedAtlasConstructionTrace m atlas
    forwardComplexIncidenceFamily reverseComplexIncidenceFamily
    forwardComplexObservableFamily reverseComplexObservableFamily complexExceptionalFamily
    forwardFiberFamily reverseFiberFamily baseObservableFamily baseGeometryFamily
  /-- Every displayed base/fiber cell indexes the cited prefix-projection
  artifact that produced it.  Raw full-cell certificates are retained only as
  source indices; no paper cell is manufactured by syntactically peeling a
  full recursive code. -/
  citedBaseSourceCell : Fin atlas.baseCellCount →
    Fin trace.citedExecution.cadResult.result.cellCount
  citedForwardCandidateSourceCell : ∀ i, Fin (forwardCandidateCellCount i) →
    Fin trace.citedExecution.cadResult.result.cellCount
  citedReverseCandidateSourceCell : ∀ i, Fin (reverseCandidateCellCount i) →
    Fin trace.citedExecution.cadResult.result.cellCount
  citedBasePrefixCertificate : Fin atlas.baseCellCount →
    Fin trace.citedExecution.cadResult.result.payload.prefixProjectionCertificates.length
  citedForwardCandidatePrefixCertificate : ∀ i, Fin (forwardCandidateCellCount i) →
    Fin trace.citedExecution.cadResult.result.payload.prefixProjectionCertificates.length
  citedReverseCandidatePrefixCertificate : ∀ i, Fin (reverseCandidateCellCount i) →
    Fin trace.citedExecution.cadResult.result.payload.prefixProjectionCertificates.length
  cited_base_cell_artifact_exact : ∀ i,
    let certificate :=
      trace.citedExecution.cadResult.result.payload.prefixProjectionCertificates.get
        (citedBasePrefixCertificate i)
    certificate.eliminatedVariables = trace.witnessPrefix ++ trace.loadingPrefix ∧
      certificate.retainedVariables = trace.observableSuffix ∧
      certificate.sourceCellIndex = (citedBaseSourceCell i).val ∧
      certificate.sourceCellCertificateCode = Encodable.encode
        (trace.citedExecution.cadResult.result.cellCertificate (citedBaseSourceCell i)) ∧
      certificate.projectedGeometryCode = Encodable.encode certificate.projectedGeometry ∧
      certificate.projectedGeometry.toAtlasCellCode = baseCellCode i
  cited_forward_candidate_artifact_exact : ∀ i k,
    let certificate :=
      trace.citedExecution.cadResult.result.payload.prefixProjectionCertificates.get
        (citedForwardCandidatePrefixCertificate i k)
    certificate.eliminatedVariables = trace.witnessPrefix ∧
      certificate.retainedVariables = trace.loadingPrefix ++ trace.observableSuffix ∧
      certificate.sourceCellIndex = (citedForwardCandidateSourceCell i k).val ∧
      certificate.sourceCellCertificateCode = Encodable.encode
        (trace.citedExecution.cadResult.result.cellCertificate
          (citedForwardCandidateSourceCell i k)) ∧
      certificate.projectedGeometryCode = Encodable.encode certificate.projectedGeometry ∧
      certificate.projectedGeometry.toAtlasCellCode = forwardCandidateCellCode i k
  cited_reverse_candidate_artifact_exact : ∀ i k,
    let certificate :=
      trace.citedExecution.cadResult.result.payload.prefixProjectionCertificates.get
        (citedReverseCandidatePrefixCertificate i k)
    certificate.eliminatedVariables = trace.witnessPrefix ∧
      certificate.retainedVariables = trace.loadingPrefix ++ trace.observableSuffix ∧
      certificate.sourceCellIndex = (citedReverseCandidateSourceCell i k).val ∧
      certificate.sourceCellCertificateCode = Encodable.encode
        (trace.citedExecution.cadResult.result.cellCertificate
          (citedReverseCandidateSourceCell i k)) ∧
      certificate.projectedGeometryCode = Encodable.encode certificate.projectedGeometry ∧
      certificate.projectedGeometry.toAtlasCellCode = reverseCandidateCellCode i k
  cited_base_cell_transport_exact : ∀ i,
    cadObservableCumVec trace.cadIncidenceEmbedding ''
        trace.citedExecution.cadResult.result.prefixProjectedCell
          (trace.witnessPrefix ++ trace.loadingPrefix) (citedBaseSourceCell i) =
      atlas.baseCell i
  cited_forward_candidate_transport_exact : ∀ i k,
    cadFiberAssignment trace.cadIncidenceEmbedding ''
        trace.citedExecution.cadResult.result.prefixProjectedCell trace.witnessPrefix
          (citedForwardCandidateSourceCell i k) =
      forwardCandidateCell i k
  cited_reverse_candidate_transport_exact : ∀ i k,
    cadFiberAssignment trace.cadIncidenceEmbedding ''
        trace.citedExecution.cadResult.result.prefixProjectedCell trace.witnessPrefix
          (citedReverseCandidateSourceCell i k) =
      reverseCandidateCell i k
  cited_base_prefix_artifact_traced : ∀ i,
    let certificate :=
      trace.citedExecution.cadResult.result.payload.prefixProjectionCertificates.get
        (citedBasePrefixCertificate i)
    ∃ step ∈ trace.citedExecution.cadResult.result.payload.trace,
      step.operation = .prefixCellProjection ∧
      Encodable.encode certificate ∈ step.producedPrefixProjectionCertificateCodes
  cited_forward_prefix_artifact_traced : ∀ i k,
    let certificate :=
      trace.citedExecution.cadResult.result.payload.prefixProjectionCertificates.get
        (citedForwardCandidatePrefixCertificate i k)
    ∃ step ∈ trace.citedExecution.cadResult.result.payload.trace,
      step.operation = .prefixCellProjection ∧
      Encodable.encode certificate ∈ step.producedPrefixProjectionCertificateCodes
  cited_reverse_prefix_artifact_traced : ∀ i k,
    let certificate :=
      trace.citedExecution.cadResult.result.payload.prefixProjectionCertificates.get
        (citedReverseCandidatePrefixCertificate i k)
    ∃ step ∈ trace.citedExecution.cadResult.result.payload.trace,
      step.operation = .prefixCellProjection ∧
      Encodable.encode certificate ∈ step.producedPrefixProjectionCertificateCodes
  citedForwardRetentionRow : Fin atlas.baseCellCount →
    Fin trace.citedExecution.cadResult.result.payload.retainedCellRows.length
  citedReverseRetentionRow : Fin atlas.baseCellCount →
    Fin trace.citedExecution.cadResult.result.payload.retainedCellRows.length
  /-- Retention is deduplication by equality of projected images.  Each kept
  projected cell has a retained source representative, representatives are
  distinct after projection, and every retained raw source is covered by one
  representative. -/
  cited_forward_retained_representative : ∀ i k,
    (citedForwardCandidateSourceCell i (forwardRetainedSelection i k)).val ∈
      (trace.citedExecution.cadResult.result.payload.retainedCellRows.get
        (citedForwardRetentionRow i)).retainedCellIndices
  cited_forward_retained_images_distinct : ∀ i k l, k ≠ l →
    trace.citedExecution.cadResult.result.prefixProjectedCell trace.witnessPrefix
        (citedForwardCandidateSourceCell i (forwardRetainedSelection i k)) ≠
      trace.citedExecution.cadResult.result.prefixProjectedCell trace.witnessPrefix
        (citedForwardCandidateSourceCell i (forwardRetainedSelection i l))
  cited_forward_retained_source_cover : ∀ i
      (source : Fin trace.citedExecution.cadResult.result.cellCount),
    source.val ∈
        (trace.citedExecution.cadResult.result.payload.retainedCellRows.get
          (citedForwardRetentionRow i)).retainedCellIndices →
      ∃ k,
        trace.citedExecution.cadResult.result.prefixProjectedCell trace.witnessPrefix source =
          trace.citedExecution.cadResult.result.prefixProjectedCell trace.witnessPrefix
            (citedForwardCandidateSourceCell i (forwardRetainedSelection i k))
  cited_forward_retention_query_exact : ∀ i,
    (trace.citedExecution.cadResult.result.payload.retainedCellRows.get
      (citedForwardRetentionRow i)).query.PopulatesAtlasIncidenceSignCondition
        trace.cadIncidenceEmbedding atlas.forwardEquations
          atlas.forwardNonnegative atlas.forwardPositive
  cited_reverse_retained_representative : ∀ i k,
    (citedReverseCandidateSourceCell i (reverseRetainedSelection i k)).val ∈
      (trace.citedExecution.cadResult.result.payload.retainedCellRows.get
        (citedReverseRetentionRow i)).retainedCellIndices
  cited_reverse_retained_images_distinct : ∀ i k l, k ≠ l →
    trace.citedExecution.cadResult.result.prefixProjectedCell trace.witnessPrefix
        (citedReverseCandidateSourceCell i (reverseRetainedSelection i k)) ≠
      trace.citedExecution.cadResult.result.prefixProjectedCell trace.witnessPrefix
        (citedReverseCandidateSourceCell i (reverseRetainedSelection i l))
  cited_reverse_retained_source_cover : ∀ i
      (source : Fin trace.citedExecution.cadResult.result.cellCount),
    source.val ∈
        (trace.citedExecution.cadResult.result.payload.retainedCellRows.get
          (citedReverseRetentionRow i)).retainedCellIndices →
      ∃ k,
        trace.citedExecution.cadResult.result.prefixProjectedCell trace.witnessPrefix source =
          trace.citedExecution.cadResult.result.prefixProjectedCell trace.witnessPrefix
            (citedReverseCandidateSourceCell i (reverseRetainedSelection i k))
  cited_reverse_retention_query_exact : ∀ i,
    (trace.citedExecution.cadResult.result.payload.retainedCellRows.get
      (citedReverseRetentionRow i)).query.PopulatesAtlasIncidenceSignCondition
        trace.cadIncidenceEmbedding atlas.reverseEquations
          atlas.reverseNonnegative atlas.reversePositive
  forward_retention_traced : ∀ (i : Fin atlas.baseCellCount)
      (k : Fin (forwardRetainedCellCount i)), ∃ step ∈ trace.steps,
    step.operation = .witnessCellRetention .forward i.val k.val ∧
    step.output = .fiber forwardFiberFamily
  reverse_retention_traced : ∀ (i : Fin atlas.baseCellCount)
      (k : Fin (reverseRetainedCellCount i)), ∃ step ∈ trace.steps,
    step.operation = .witnessCellRetention .reverse i.val k.val ∧
    step.output = .fiber reverseFiberFamily
  encodedConstruction : EncodedAtlasConstruction m
  encoded_forward_complex_incidence : ComplexPolynomialCodesRealize
    encodedConstruction.forwardComplexIncidence forwardComplexIncidenceFamily
  encoded_reverse_complex_incidence : ComplexPolynomialCodesRealize
    encodedConstruction.reverseComplexIncidence reverseComplexIncidenceFamily
  encoded_forward_complex_observable : ComplexPolynomialCodesRealize
    encodedConstruction.forwardComplexObservable forwardComplexObservableFamily
  encoded_reverse_complex_observable : ComplexPolynomialCodesRealize
    encodedConstruction.reverseComplexObservable reverseComplexObservableFamily
  encoded_complex_exceptional : ComplexPolynomialCodesRealize
    encodedConstruction.complexExceptional complexExceptionalFamily
  encoded_forward_incidence : PolynomialCodesRealize
    encodedConstruction.forwardIncidence
    (atlas.forwardEquations ∪ atlas.forwardNonnegative ∪ atlas.forwardPositive)
  encoded_reverse_incidence : PolynomialCodesRealize
    encodedConstruction.reverseIncidence
    (atlas.reverseEquations ∪ atlas.reverseNonnegative ∪ atlas.reversePositive)
  encoded_forward_fiber :
    PolynomialCodesRealize encodedConstruction.forwardFiber forwardFiberFamily
  encoded_reverse_fiber :
    PolynomialCodesRealize encodedConstruction.reverseFiber reverseFiberFamily
  encoded_observable_base :
    PolynomialCodesRealize encodedConstruction.observableBase baseObservableFamily
  encoded_observable_geometry :
    PolynomialCodesRealize encodedConstruction.observableGeometry baseGeometryFamily
  encoded_orders_exact :
    encodedConstruction.baseOrder = baseOrder ∧
    encodedConstruction.forwardOrder = forwardFiberOrder ∧
    encodedConstruction.reverseOrder = reverseFiberOrder
  encoded_base_cell_count : encodedConstruction.baseCellCount = atlas.baseCellCount
  encoded_base_cells : encodedConstruction.baseCells = List.ofFn baseCellCode
  encoded_forward_candidate_counts : encodedConstruction.forwardCandidateCellCounts =
    List.ofFn forwardCandidateCellCount
  encoded_reverse_candidate_counts : encodedConstruction.reverseCandidateCellCounts =
    List.ofFn reverseCandidateCellCount
  encoded_forward_retained_counts : encodedConstruction.forwardRetainedCellCounts =
    List.ofFn forwardRetainedCellCount
  encoded_reverse_retained_counts : encodedConstruction.reverseRetainedCellCounts =
    List.ofFn reverseRetainedCellCount
  encoded_forward_candidate_cells : encodedConstruction.forwardCandidateCells =
    List.ofFn fun i => List.ofFn (forwardCandidateCellCode i)
  encoded_reverse_candidate_cells : encodedConstruction.reverseCandidateCells =
    List.ofFn fun i => List.ofFn (reverseCandidateCellCode i)
  encoded_forward_retained_selections : encodedConstruction.forwardRetainedSelections =
    List.ofFn fun i => List.ofFn fun k => (forwardRetainedSelection i k).val
  encoded_reverse_retained_selections : encodedConstruction.reverseRetainedSelections =
    List.ofFn fun i => List.ofFn fun k => (reverseRetainedSelection i k).val
  encoded_trace_incidence : PolynomialCodeFamiliesRealize
    encodedConstruction.traceIncidenceFamilies
    (trace.steps.flatMap AtlasTraceStep.incidenceFamilies)
  encoded_trace_fiber : PolynomialCodeFamiliesRealize
    encodedConstruction.traceFiberFamilies
    (trace.steps.flatMap AtlasTraceStep.fiberFamilies)
  encoded_trace_observable : PolynomialCodeFamiliesRealize
    encodedConstruction.traceObservableFamilies
    (trace.steps.flatMap AtlasTraceStep.observableFamilies)
  encoded_trace_complex_incidence : ComplexPolynomialCodeFamiliesRealize
    encodedConstruction.traceComplexIncidenceFamilies
    (trace.steps.flatMap AtlasTraceStep.complexIncidenceFamilies)
  encoded_trace_complex_observable : ComplexPolynomialCodeFamiliesRealize
    encodedConstruction.traceComplexObservableFamilies
    (trace.steps.flatMap AtlasTraceStep.complexObservableFamilies)
  encoded_operations_exact :
    encodedConstruction.operations = trace.steps.map AtlasTraceStep.operation
  /-- Signed decision entries transported directly from the cited prefix basic
  sign conditions.  In particular a negative answer remains a negative sign on
  the original polynomial; it is not represented by inserting `-P`. -/
  decisionSignEntries :
    List (MvPolynomial (ℕ × ℕ) ℝ × EffectivePolynomialSign)
  decisionFamily : Finset (MvPolynomial (ℕ × ℕ) ℝ)
  decision_sign_entries_exact : ∀ P sign,
    (P, sign) ∈ decisionSignEntries ↔
      ∃ certificate ∈
          trace.citedExecution.cadResult.result.payload.prefixProjectionCertificates,
        certificate.eliminatedVariables = trace.witnessPrefix ++ trace.loadingPrefix ∧
        certificate.retainedVariables = trace.observableSuffix ∧
        ∃ code, (code, sign) ∈ certificate.basicSignCondition.conditions ∧
          P = effectiveCodeToObservablePolynomial
            trace.cadObservableCoordinateMap code
  decision_sign_entries_traced : ∀ P sign, (P, sign) ∈ decisionSignEntries →
    ∃ certificate ∈
        trace.citedExecution.cadResult.result.payload.prefixProjectionCertificates,
      ∃ step ∈ trace.citedExecution.cadResult.result.payload.trace,
        step.operation = .prefixCellProjection ∧
        Encodable.encode certificate ∈ step.producedPrefixProjectionCertificateCodes ∧
        ∃ code, (code, sign) ∈ certificate.basicSignCondition.conditions ∧
          P = effectiveCodeToObservablePolynomial
            trace.cadObservableCoordinateMap code
  decision_sign_transport_exact : ∀ P sign, (P, sign) ∈ decisionSignEntries →
    ∀ certificate ∈
        trace.citedExecution.cadResult.result.payload.prefixProjectionCertificates,
      certificate.eliminatedVariables = trace.witnessPrefix ++ trace.loadingPrefix →
      certificate.retainedVariables = trace.observableSuffix →
      ∀ code, (code, sign) ∈ certificate.basicSignCondition.conditions →
        P = effectiveCodeToObservablePolynomial
          trace.cadObservableCoordinateMap code →
        ∀ source : Fin trace.citedExecution.cadResult.result.cellCount,
          certificate.sourceCellIndex = source.val →
          ∀ point ∈ trace.citedExecution.cadResult.result.prefixProjectedCell
              (trace.witnessPrefix ++ trace.loadingPrefix) source,
            MvPolynomial.eval
                (fun ra => cadObservableCumVec trace.cadIncidenceEmbedding point ra.1 ra.2) P =
              MvPolynomial.eval point
                (MvPolynomial.map (Rat.castHom ℝ) code.toPolynomial)
  decision_family_exact : decisionFamily =
    (decisionSignEntries.map Prod.fst).toFinset
  exceptional_equations_are_decision_tests : baseObservableFamily ⊆ decisionFamily
  /-- Base cells are presented by the full CAD decision family, not merely by the
  exceptional-closure equations, which vanish identically on the locus. -/
  base_family_exact : DefinesAtlasBaseCellFamily m atlas.baseCell decisionFamily
  decision_sign_invariant : ∀ i P, P ∈ decisionFamily →
    ObservableSignInvariantOn (atlas.baseCell i) P
  program : AtlasSignOracleProgram
  signOracle : AtlasExactSignOracle
  signOracle_exact : IsExactAtlasSignOracle signOracle
  /-- A base label is the existential aggregate over every full source cell
  whose observable prefix projection is the displayed base cylinder.  Forward
  and reverse use separate sign queries and may be witnessed by different full
  source cells. -/
  cited_forward_truth_aggregate : ∀ i,
    atlas.forwardLabel i = true ↔
      ∃ row ∈ trace.citedExecution.cadResult.result.payload.signRows,
        ∃ source : Fin trace.citedExecution.cadResult.result.cellCount,
          row.cellIndex = source.val ∧ row.truth = true ∧
          trace.citedExecution.cadResult.result.prefixProjectedCell
              (trace.witnessPrefix ++ trace.loadingPrefix) source =
            trace.citedExecution.cadResult.result.prefixProjectedCell
              (trace.witnessPrefix ++ trace.loadingPrefix) (citedBaseSourceCell i) ∧
          row.query.PopulatesAtlasIncidenceSignCondition
            trace.cadIncidenceEmbedding atlas.forwardEquations
              atlas.forwardNonnegative atlas.forwardPositive
  cited_reverse_truth_aggregate : ∀ i,
    atlas.reverseLabel i = true ↔
      ∃ row ∈ trace.citedExecution.cadResult.result.payload.signRows,
        ∃ source : Fin trace.citedExecution.cadResult.result.cellCount,
          row.cellIndex = source.val ∧ row.truth = true ∧
          trace.citedExecution.cadResult.result.prefixProjectedCell
              (trace.witnessPrefix ++ trace.loadingPrefix) source =
            trace.citedExecution.cadResult.result.prefixProjectedCell
              (trace.witnessPrefix ++ trace.loadingPrefix) (citedBaseSourceCell i) ∧
          row.query.PopulatesAtlasIncidenceSignCondition
            trace.cadIncidenceEmbedding atlas.reverseEquations
              atlas.reverseNonnegative atlas.reversePositive
  encoded_sign_tests : PolynomialCodesRealize encodedConstruction.signTests program.tests.toFinset
  encoded_lookup_rows : encodedConstruction.lookupRows = program.rows.map fun row =>
    (row.signs.map atlasPolynomialSignCode, row.forwardValue, row.reverseValue)
  program_tests_exact : ∀ P, P ∈ program.tests ↔ P ∈ decisionFamily
  forward_finite_semialgebraic :
    IsFiniteSemialgebraicFunction (fun t => (program.evaluateWith signOracle t).1)
  reverse_finite_semialgebraic :
    IsFiniteSemialgebraicFunction (fun t => (program.evaluateWith signOracle t).2)
  forward_exact : ∀ t ∈ bandLimitedRealExceptionalLocus m,
    ((program.evaluateWith signOracle t).1 = true ↔
      (realAtlasForwardSection m t).Nonempty)
  reverse_exact : ∀ t ∈ bandLimitedRealExceptionalLocus m,
    ((program.evaluateWith signOracle t).2 = true ↔
      (realAtlasReverseSection m t).Nonempty)
  both_arrows_exact : ∀ t ∈ bandLimitedRealExceptionalLocus m,
    ((program.evaluateWith signOracle t).1 = true ∧
      (program.evaluateWith signOracle t).2 = true ↔
      (realAtlasForwardSection m t).Nonempty ∧ (realAtlasReverseSection m t).Nonempty)
  forward_cell_label : ∀ i t, t ∈ atlas.baseCell i →
    (program.evaluateWith signOracle t).1 = atlas.forwardLabel i
  reverse_cell_label : ∀ i t, t ∈ atlas.baseCell i →
    (program.evaluateWith signOracle t).2 = atlas.reverseLabel i
  forward_retained_selection_exact : ∀ i t, t ∈ atlas.baseCell i →
    ((program.evaluateWith signOracle t).1 = true ↔
      ∃ k, (forwardRetainedCell i k).Nonempty ∧
        forwardRetainedCell i k =
          forwardCandidateCell i (forwardRetainedSelection i k))
  reverse_retained_selection_exact : ∀ i t, t ∈ atlas.baseCell i →
    ((program.evaluateWith signOracle t).2 = true ↔
      ∃ k, (reverseRetainedCell i k).Nonempty ∧
        reverseRetainedCell i k =
          reverseCandidateCell i (reverseRetainedSelection i k))
  complexity : AtlasComplexityCertificate m trace.steps.length trace.citedExecution
  /-- Exact pre-elimination receipt: the displayed incidence formula bounds
  the supplied forward source presentation. -/
  cited_forward_source_input_degree_bounded :
    trace.citedExecution.forwardEliminationJob.DegreeBoundedBy
      complexity.sourceDegreeBound
  /-- Exact pre-elimination receipt for the reverse source presentation. -/
  cited_reverse_source_input_degree_bounded :
    trace.citedExecution.reverseEliminationJob.DegreeBoundedBy
      complexity.sourceDegreeBound
  /-- Charged post-elimination envelope for all three rational jobs. -/
  cited_rational_inputs_bounded : EffectiveGroebnerBatchInputsBounded
    trace.citedExecution.rationalJobs complexity.sourceCoordinateCount
      complexity.chargedDegreeBound
  cited_gaussian_inputs_bounded : EffectiveGroebnerBatchInputsBounded
    trace.citedExecution.gaussianJobs complexity.sourceCoordinateCount
      complexity.chargedDegreeBound
  cited_dependent_pipeline_degree_bounded :
    trace.citedExecution.dependentPipeline.DegreeBoundedBy complexity.chargedDegreeBound
  cited_cad_dimension_bounded :
    trace.citedExecution.cadJob.r ≤ complexity.sourceCoordinateCount
  cited_cad_degree_bounded :
    trace.citedExecution.cadJob.DegreeBoundedBy complexity.chargedDegreeBound
  operation_count_exact : complexity.arithmeticSignOperations =
    (trace.steps.map AtlasTraceStep.operationCost).sum
  cited_operation_count_exact : complexity.arithmeticSignOperations =
    trace.citedExecution.symbolicOperationCount
  cited_combined_bound : trace.citedExecution.symbolicOperationCount ≤
    (max 2 (complexity.sourcePolynomialCount * complexity.chargedDegreeBound)) ^
      (2 ^ (complexity.exponentConstant * complexity.sourceCoordinateCount +
        complexity.exponentOffset))
  source_polynomial_count_exact : complexity.sourcePolynomialCount =
    effectiveGroebnerBatchSourcePolynomialCount trace.citedExecution.rationalJobs +
      effectiveGroebnerBatchSourcePolynomialCount trace.citedExecution.gaussianJobs +
      trace.citedExecution.cadJob.sourcePolynomialCount
  displayed_source_polynomial_count_le :
    forwardComplexIncidenceFamily.card + reverseComplexIncidenceFamily.card +
    (atlas.forwardEquations ∪ atlas.forwardNonnegative ∪ atlas.forwardPositive ∪
      atlas.reverseEquations ∪ atlas.reverseNonnegative ∪ atlas.reversePositive).card ≤
        complexity.sourcePolynomialCount

/-- The **output shape** of the paper's atlas handle at complexity `m`: the engine returns a
value of `RealAtlasCADData m`.  This is a *definition of what the handle emits*, not an
assertion that it exists.  It is retained as an unasserted name for the weaker raw-CAD output
shape.  The proved paper-specific theorem concludes the strictly richer
`Nonempty (EffectiveRealAtlasOutput m)`, which also carries finite sign-table evaluators and
their exactness certificates. -/
def realAtlasCADStratification (m : ℕ) : Prop := Nonempty (RealAtlasCADData m)

/-- **Real exceptional-locus atlas handle — the CITED external interface** (`I-3`).

The note's `def:real-atlas-handle` opens by saying what it is: *"External (cited) interface,
not proved here.  The handle's correctness … is the classical real quantifier-elimination and
truncated-moment theory (Tarski–Seidenberg).  It is INVOKED as a cited external interface and
is not reproved in this note."*  This declaration is the Lean rendering of that cited interface,
and it therefore states the **theorem of record itself**: `RealClosedFieldCADInterface`
(`Helpers/CAD/CADInterface.lean`) — the cylindrical algebraic decomposition adapted to an
**arbitrary** finite family of real polynomials in an **arbitrary** number of variables, together
with the Tarski–Seidenberg projection theorem.  Both conjuncts are universally quantified and
self-contained; neither mentions this paper's objects.

*Source of record* (`cite:bcr-bpr-cad`): Bochnak–Coste–Roy, *Real Algebraic Geometry*, §2.3 and
Thm 2.2.1; Basu–Pollack–Roy, *Algorithms in Real Algebraic Geometry*, Ch. 5 (Thm 5.6, Def. 5.1,
Def. 5.5, Notation 5.15, Thm 5.16).  The node was previously sourced to Collins (1975); that is an
**algorithm** paper, whose statement of record carries effectivity/complexity content this `Prop`
does not encode.  Nothing in this development consumes CAD effectivity — we assume only the
existence and structure of a sign-invariant cell decomposition — so the mathematical theorem is the
correct source, and the `Prop` itself is unchanged.

It deliberately does **not** assert `Nonempty (RealAtlasCADData m)`.  That proposition is part of
our bespoke conclusion — the atlas the engine would emit for *our* incidence system — and asserting
it under the CAD citation would smuggle unproved paper-specific content (the elimination-ideal
generators of `\bar E_m`, the `Q_K` ⟺ real-source-feasibility equivalence, and the cellwise
witness elimination) in behind a citation that supplies none of it.  The decomposition theorem is
the *tool*; the effective atlas is the derived conclusion `exactRealExceptionalAtlas`.

The handle's *construction* — the two incidence sets `Γ_right`/`Γ_left` (`realAtlasHandle`,
`realAtlasHandleReverse`), the atomic certificate `Q_K`, the projection family, the cell
language and the atlas output record `RealAtlasCADData` — is rendered by the declarations above.
The cited engine is what would be *run* on that construction; its correctness is what is
borrowed here.  Its shared lifting language ignores a stage polynomial whenever its specialization
at the current base point is identically zero in the lifting variable; this is the standard CAD
nullification convention and prevents a nullified polynomial from creating an infinite root stack.
Nothing on the critical path of `thm:generic-apolar-arrow-recovery` depends on this interface: the
flagship is unconditional. -/
-- @node: def:real-atlas-handle
def realAtlasHandleOutput : Prop := RealClosedFieldCADInterface

end

/-- The symbolic-operation count of a batch is the sum of the exact trace costs of its jobs, with
an empty batch having cost zero. -/
add_decl_doc EffectiveGroebnerBatchResultsOver.symbolicOperationCount.eq_def

/-- The primitive-charge list of rational CAD trace steps is formed by charging every primitive
operation in each step and recording the step's offset in the trace. -/
add_decl_doc atlasRationalCADPrimitiveChargesFrom.eq_def

/-- Each causal direction has an effective numerical encoding and decoding. -/
add_decl_doc instEncodableDirection

/-- Atlas trace operations have a decidable equality test: any two operations can be effectively
determined to be the same or different. -/
add_decl_doc instDecidableEqAtlasTraceOperation

/-- Every atlas trace operation has an effective numerical encoding and decoding. -/
add_decl_doc instEncodableAtlasTraceOperation

/-- Every encoded atlas construction, including its finite polynomial and trace data, has an
effective numerical encoding and decoding. -/
add_decl_doc instEncodableEncodedAtlasConstruction

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
