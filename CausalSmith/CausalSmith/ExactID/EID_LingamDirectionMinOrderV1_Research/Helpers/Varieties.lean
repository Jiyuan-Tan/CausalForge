/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Cumulant-image varieties and exceptional compatibility loci (set level)

Set-level constructions only: the Zariski closure of a set in the cumulant
coordinate space, the axis-conditioned cumulant-image varieties, the generic
full-fiber compatibility locus `E_m` with its closure `\bar E_m` and
parameter-level preimages `H^b_m`, and the separation-handle comparison
predicate.  All dimension / codimension facts are deferred (they belong to the
deferred conjecture `oeq:generic-exceptional-locus`).

`bypass-justified`: no Causalean algebraic-variety substrate; Zariski closure is
built as the vanishing set of the vanishing ideal over `MvPolynomial`.
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

/-- **Zariski closure** of a set `A ⊆ ℂ^{q_L}` of cumulant vectors: the common
zero set of every polynomial (in the coordinate ring `ℂ[t_{r,a}]`) that vanishes
on `A`.  Coordinates are indexed by `(r, a) ∈ ℕ × ℕ`. -/
def zariskiClosure (A : Set (CumVec ℂ)) : Set (CumVec ℂ) :=
  { t | ∀ P : MvPolynomial (ℕ × ℕ) ℂ,
      (∀ s ∈ A, MvPolynomial.eval (fun p => s p.1 p.2) P = 0) →
      MvPolynomial.eval (fun p => t p.1 p.2) P = 0 }

/-- Coordinate index of the structural parameter space: the direct slope, the
`m` latent slopes, and the weight family `(j, r)`. -/
abbrev ParamCoord (m : ℕ) : Type := Unit ⊕ Fin m ⊕ (Fin (m + 2) × ℕ)

/-- Evaluate the parameter coordinates of `θ` at a coordinate index. -/
def paramEval {m : ℕ} (θ : ParamSpace ℂ m) : ParamCoord m → ℂ
  | Sum.inl _ => θ.1
  | Sum.inr (Sum.inl i) => θ.2.1 i
  | Sum.inr (Sum.inr jr) => θ.2.2 jr.1 jr.2

/-- Zariski closure of a set of structural parameters. -/
def zariskiClosureParam {m : ℕ} (A : Set (ParamSpace ℂ m)) : Set (ParamSpace ℂ m) :=
  { θ | ∀ P : MvPolynomial (ParamCoord m) ℂ,
      (∀ s ∈ A, MvPolynomial.eval (paramEval s) P = 0) →
      MvPolynomial.eval (paramEval θ) P = 0 }

/-- A Zariski-open subset of the parameter space (complement of a proper Zariski
closed set). -/
def IsZariskiOpenParam {m : ℕ} (U : Set (ParamSpace ℂ m)) : Prop :=
  ∃ Z : Set (ParamSpace ℂ m), zariskiClosureParam Z = Z ∧ Z ≠ Set.univ ∧ U = Zᶜ

/-- A Zariski-dense subset of the parameter space. -/
def IsZariskiDenseParam {m : ℕ} (U : Set (ParamSpace ℂ m)) : Prop :=
  zariskiClosureParam U = Set.univ

/-- The relative Zariski closure consists of the retained-band parameters at which
every polynomial vanishing on the original set also vanishes.

This is the paper's closure notion because its ambient parameter space is the finite
retained-band space `Θ^b_{m,L}`.  Closure or density in the full natural-number-indexed
function space is not the paper's claim. -/
def zariskiClosureParamIn {m : ℕ} (L : ℕ) (A : Set (ParamSpace ℂ m)) :
    Set (ParamSpace ℂ m) :=
  bandSupportedParams m L ∩
    { θ | ∀ P : MvPolynomial (ParamCoord m) ℂ,
        (∀ s ∈ A, MvPolynomial.eval (paramEval s) P = 0) →
        MvPolynomial.eval (paramEval θ) P = 0 }

/-- A relatively Zariski-open set is the complement, within the retained-band
parameter space, of a proper relatively closed set.

This is the paper's openness notion because its ambient parameter space is the finite
retained-band space `Θ^b_{m,L}`.  Openness in the full natural-number-indexed function
space is not the paper's claim. -/
def IsZariskiOpenParamIn {m : ℕ} (L : ℕ) (U : Set (ParamSpace ℂ m)) : Prop :=
  ∃ Z : Set (ParamSpace ℂ m), zariskiClosureParamIn L Z = Z ∧
    Z ≠ bandSupportedParams m L ∧ U = bandSupportedParams m L \ Z

/-- A relatively Zariski-dense set has the whole retained-band parameter space as
its relative Zariski closure.

This is the paper's density notion because its ambient parameter space is the finite
retained-band space `Θ^b_{m,L}`.  Density in the full natural-number-indexed function
space is not the paper's claim. -/
def IsZariskiDenseParamIn {m : ℕ} (L : ℕ) (U : Set (ParamSpace ℂ m)) : Prop :=
  zariskiClosureParamIn L U = bandSupportedParams m L

/-- An **irreducible** Zariski-closed subset of the cumulant coordinate space:
nonempty, Zariski-closed, and not the union of two *proper* Zariski-closed subsets.
A strictly increasing chain of such sets is a chain of irreducible subvarieties (a
prime chain in the coordinate ring), which is the dimension/codimension notion —
Krull dimension via irreducible-component chains — that a codimension statement
requires, as opposed to a chain of arbitrary Zariski-closed sets. -/
def IsIrreducibleZariskiClosed (Z : Set (CumVec ℂ)) : Prop :=
  zariskiClosure Z = Z ∧ Z.Nonempty ∧
    ∀ Z₁ Z₂ : Set (CumVec ℂ),
      zariskiClosure Z₁ = Z₁ → zariskiClosure Z₂ = Z₂ → Z = Z₁ ∪ Z₂ →
        Z = Z₁ ∨ Z = Z₂

/-- Complexification of a real structural parameter, coordinatewise. -/
def complexifyParam {m : ℕ} (p : ParamSpace ℝ m) : ParamSpace ℂ m :=
  ((p.1 : ℂ), (fun i => (p.2.1 i : ℂ)), (fun j r => (p.2.2 j r : ℂ)))

/-- Complexification of a real cumulant coordinate vector, coordinatewise. -/
def complexifyCumVec (t : CumVec ℝ) : CumVec ℂ := fun r a => (t r a : ℂ)

/-- Axis-conditioned cumulant-image variety `C^b_{m,L}`, the Zariski closure of
the image of the arrow map `Φ` over the whole complex parameter space.  The same
construction gives `C^right` (with `forwardCumulantMap`) and `C^left` (with
`reverseCumulantMap`).
@realizes C^right_{m,L},C^left_{m,L}(Zariski closure of the arrow-map image) -/
-- @node: def:image-varieties
def cumulantImageVariety {m : ℕ} (Φ : ParamSpace ℂ m → CumVec ℂ) : Set (CumVec ℂ) :=
  zariskiClosure (Set.range Φ)

/-- Generic full-fiber opposite-arrow compatibility locus `E_m ⊆ ℂ^{q_K}`
(`K = 2m + 2`): observable vectors `t` whose one arrow has a *generic*
full fiber and whose opposite arrow has a (possibly non-generic) full fiber.
This is the first of the four components of `def:generic-full-fiber-compatibility`
(bundled in `genericFullFiberCompatibilityLocus`).
@realizes E_m,barE_m,H^right_m,H^left_m(compatibility locus `E_m`) -/
def genericFullFiberCompatibility (m : ℕ) : Set (CumVec ℂ) :=
  -- `E_m ⊆ ℂ^{q_K}`: the observable vectors live in the paper's finite cumulant
  -- coordinate space, so the `ℕ`-indexed representation must be cut down to it.  Without
  -- this, `E_m` (and hence `\bar E_m` and the preimages `H^b_m`) would be a cylinder over
  -- unconstrained off-band cumulant coordinates.
  bandSupportedCumulants (2 * m + 2) ∩
  { t |
      ((fiberCorrespondence (2 * m + 2) (forwardCumulantMap m (2 * m + 2)) t
          ∩ genericParameterLocus m (2 * m + 2)).Nonempty
        ∧ (fiberCorrespondence (2 * m + 2) (reverseCumulantMap m (2 * m + 2)) t).Nonempty)
    ∨ ((fiberCorrespondence (2 * m + 2) (reverseCumulantMap m (2 * m + 2)) t
          ∩ genericParameterLocus m (2 * m + 2)).Nonempty
        ∧ (fiberCorrespondence (2 * m + 2) (forwardCumulantMap m (2 * m + 2)) t).Nonempty) }

/-- Zariski closure `\bar E_m` of the compatibility locus — the second component
of the compatibility-locus construction `def:generic-full-fiber-compatibility`
(`E_m`, `\bar E_m`, `H^right_m`, `H^left_m`).
@realizes E_m,barE_m,H^right_m,H^left_m(Zariski closure `\bar E_m`) -/
def genericCompatibilityClosure (m : ℕ) : Set (CumVec ℂ) :=
  zariskiClosure (genericFullFiberCompatibility m)

/-- Parameter-level preimage `H^b_m = Θ^{b,∘}_{m,K} ∩ (Φ^b)^{-1}(E_m)` — the third
and fourth components of `def:generic-full-fiber-compatibility` (`H^right_m` with
`Φ = forwardCumulantMap`, `H^left_m` with `Φ = reverseCumulantMap`).

`Θ^{b,∘}_{m,K}` is the paper's generic locus *inside the finite ambient*
`Θ^b_{m,K} = ℂ^{m+1} × ℂ^{n(K-1)}`, so the band factor `bandSupportedParams m L` is imposed
here explicitly alongside the genericity factor `genericParameterLocus m L` (see the
`genericParameterLocus` docstring for why the two factors are kept apart).  Without the band
factor `H^b_m` would be a *cylinder* over the unconstrained off-band source weights: every
`Φ^b` is `0` off the retained band by construction, so `(Φ^b)⁻¹(E_m)` places no constraint on
`c_{j,r}` for `r ∉ [2, L]` whatsoever.
@realizes E_m,barE_m,H^right_m,H^left_m(generic-locus preimage `H^b_m`) -/
def genericCompatibilityPreimage {m : ℕ} (L : ℕ) (Φ : ParamSpace ℂ m → CumVec ℂ) :
    Set (ParamSpace ℂ m) :=
  bandSupportedParams m L ∩ genericParameterLocus m L ∩
    Φ ⁻¹' (genericFullFiberCompatibility m)

/-- Right generic-locus preimage `H^right_m = Θ^{right,∘}_{m,K} ∩ (Φ^right)^{-1}(E_m)`
— the third component of `def:generic-full-fiber-compatibility`. -/
def genericCompatibilityPreimageRight (m : ℕ) : Set (ParamSpace ℂ m) :=
  genericCompatibilityPreimage (2 * m + 2) (forwardCumulantMap m (2 * m + 2))

/-- Left generic-locus preimage `H^left_m = Θ^{left,∘}_{m,K} ∩ (Φ^left)^{-1}(E_m)` —
the fourth component of `def:generic-full-fiber-compatibility`. -/
def genericCompatibilityPreimageLeft (m : ℕ) : Set (ParamSpace ℂ m) :=
  genericCompatibilityPreimage (2 * m + 2) (reverseCumulantMap m (2 * m + 2))

/-- **Generic full-fiber compatibility construction** — the full four-component
object the paper's `def:generic-full-fiber-compatibility` defines, bundled so the
extracted definition carries *all* of its parts (not only `E_m`):

* `.1` = `E_m`, the generic full-fiber opposite-arrow compatibility set;
* `.2.1` = `\bar E_m`, its Zariski closure;
* `.2.2.1` = `H^right_m = Θ^{right,∘}_{m,K} ∩ (Φ^right)^{-1}(E_m)`;
* `.2.2.2` = `H^left_m = Θ^{left,∘}_{m,K} ∩ (Φ^left)^{-1}(E_m)`,

the two generic parameter-level preimages of `E_m` on the two arrows.
@realizes E_m,barE_m,H^right_m,H^left_m(the four-component compatibility construction) -/
-- @node: def:generic-full-fiber-compatibility
def genericFullFiberCompatibilityLocus (m : ℕ) :
    Set (CumVec ℂ) × Set (CumVec ℂ) × Set (ParamSpace ℂ m) × Set (ParamSpace ℂ m) :=
  (genericFullFiberCompatibility m,
   genericCompatibilityClosure m,
   genericCompatibilityPreimageRight m,
   genericCompatibilityPreimageLeft m)

/-! ### Quotient fibers modulo admissible swaps and Jacobian ranks -/

/-- Orbit of `θ` under the admissible source-swap `G_m` action (the admissible
relabelings of the middle latent block). -/
def admissibleOrbit {m : ℕ} (θ : ParamSpace ℂ m) : Set (ParamSpace ℂ m) :=
  { θ' | ∃ π : Equiv.Perm (Fin m), θ' = admissibleSourceSwap m π θ }

/-- Same-arrow **quotient fiber** of `Φ` over `t`: the set of `G_m`-orbits
(admissible-source-swap classes) contained in the full fiber `Φ⁻¹(t)`.  This is the
quotient of the same-arrow fiber by the admissible-swap action, not an assertion
that the fiber is a *single* orbit. -/
def quotientFiber {m : ℕ} (L : ℕ) (Φ : ParamSpace ℂ m → CumVec ℂ) (t : CumVec ℂ) :
    Set (Set (ParamSpace ℂ m)) :=
  { O | ∃ θ' ∈ fiberCorrespondence L Φ t, O = admissibleOrbit θ' }

/-- Update the coordinate `k` of a complex structural parameter `θ` to the value `s`. -/
def updateParamCoord {m : ℕ} (θ : ParamSpace ℂ m) : ParamCoord m → ℂ → ParamSpace ℂ m
  | Sum.inl _, s => (s, θ.2.1, θ.2.2)
  | Sum.inr (Sum.inl i), s => (θ.1, Function.update θ.2.1 i s, θ.2.2)
  | Sum.inr (Sum.inr jr), s =>
      (θ.1, θ.2.1, Function.update θ.2.2 jr.1 (Function.update (θ.2.2 jr.1) jr.2 s))

/-- Finite **active** parameter coordinates through retained order `L`: the direct
slope, the `m` latent slopes, and the weights `c_{jr}` for `r ≤ L`. -/
abbrev ActiveParam (m L : ℕ) : Type := Unit ⊕ Fin m ⊕ (Fin (m + 2) × Fin (L + 1))

/-- The active parameter coordinate as a full parameter coordinate. -/
def toParamCoord {m L : ℕ} : ActiveParam m L → ParamCoord m
  | Sum.inl u => Sum.inl u
  | Sum.inr (Sum.inl i) => Sum.inr (Sum.inl i)
  | Sum.inr (Sum.inr (j, r)) => Sum.inr (Sum.inr (j, r.1))

/-- The **Jacobian matrix** of an arrow map `Φ` at `θ` over the retained finite
coordinate band up to order `L`: the partial derivative of each retained output
coordinate `(r, a)` with respect to each active parameter coordinate, taken with
Mathlib's `deriv` (each `Φ`-coordinate is polynomial in one substituted scalar). -/
noncomputable def jacobianMatrix {m : ℕ} (L : ℕ) (Φ : ParamSpace ℂ m → CumVec ℂ)
    (θ : ParamSpace ℂ m) :
    Matrix (Fin (L + 1) × Fin (L + 1)) (ActiveParam m L) ℂ :=
  fun ra k =>
    deriv (fun s => Φ (updateParamCoord θ (toParamCoord k) s) ra.1 ra.2)
      (paramEval θ (toParamCoord k))

/-- The **Jacobian rank** of the same-arrow fiber equation of `Φ` at `θ` (through
retained order `L`): the rank of `jacobianMatrix`.  The quantitative *value* of
this rank is the deferred content (interfaces `I-1`/`I-2`). -/
noncomputable def jacobianRank {m : ℕ} (L : ℕ) (Φ : ParamSpace ℂ m → CumVec ℂ)
    (θ : ParamSpace ℂ m) : ℕ :=
  (jacobianMatrix L Φ θ).rank

/-- Separation handle: the data used to compare the two axis-conditioned
decompositions after quotienting each same-arrow fiber by `G_m`.  It records the
shared-observable equation, the two complete quotient fibers, and the two Jacobian
ranks at the displayed representatives.  The fixed vertical/horizontal axes are
already built into `forwardCumulantMap` and `reverseCumulantMap`.

In particular this handle does not impose a universal cross-fiber rank equality:
the paper uses the quotient fibers and ranks as comparison data but does not
characterize the handle by equality of every pair of representative ranks. -/
-- @node: def:separation-handle
noncomputable def separationHandle (m L : ℕ) (θ η : ParamSpace ℂ m) :
    Prop × Set (Set (ParamSpace ℂ m)) × Set (Set (ParamSpace ℂ m)) × ℕ × ℕ :=
  (forwardCumulantMap m L θ = reverseCumulantMap m L η,
   quotientFiber L (forwardCumulantMap m L) (forwardCumulantMap m L θ),
   quotientFiber L (reverseCumulantMap m L) (reverseCumulantMap m L η),
   jacobianRank L (forwardCumulantMap m L) θ,
   jacobianRank L (reverseCumulantMap m L) η)

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
