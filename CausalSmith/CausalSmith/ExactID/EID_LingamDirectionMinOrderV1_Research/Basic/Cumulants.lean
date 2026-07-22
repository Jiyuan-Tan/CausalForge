/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Basic.World

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## The truncated-cumulant construction -/

/-- Stacked joint-cumulant truncation `T_L(P)`, coordinate `(r, a)` equal to
`κ_{r,a}(P) = Cum_P(X^{r-a}, Y^a)` for `2 ≤ r ≤ L`, `0 ≤ a ≤ r`, and `0` outside
the retained range.
@realizes T_L(P),t(coordinatewise κ_{r,a})
@realizes kappa_{r,a}(P)(κ_{r,a} = Cum_P(X^{r-a}, Y^a)) -/
-- @node: def:truncated-cumulant
noncomputable def truncatedCumulant (μ : Measure Ω) (X Y : Ω → ℝ) (L : ℕ) : CumVec ℝ :=
  fun r a => if 2 ≤ r ∧ r ≤ L ∧ a ≤ r then jointCumulant μ X Y (r - a) a else 0

/-! ## Axis-conditioned simultaneous binary-form cumulant maps -/

/-- Forward simultaneous binary-form map `Φ^right_{m,L}`, coordinate `(r, a)`:
`Σ_j c_{jr} u_{j1}^{r-a} u_{j2}^a` on the retained range, `0` outside.
@realizes Phi^right_{m,L},Phi^left_{m,L}(forward binary-form map) -/
-- @node: def:forward-cumulant-map
def forwardCumulantMap {R : Type*} [CommRing R] (m L : ℕ) (θ : ParamSpace R m) : CumVec R :=
  fun r a =>
    if 2 ≤ r ∧ r ≤ L ∧ a ≤ r then
      ∑ j : Fin (m + 2),
        θ.2.2 j r * (forwardLoading m θ.1 θ.2.1 j).1 ^ (r - a)
          * (forwardLoading m θ.1 θ.2.1 j).2 ^ a
    else 0

/-- Reverse simultaneous binary-form map `Φ^left_{m,L}`, coordinate `(r, a)`:
`Σ_j d_{jr} v_{j1}^{r-a} v_{j2}^a` on the retained range, `0` outside.
@realizes Phi^right_{m,L},Phi^left_{m,L}(reverse binary-form map) -/
-- @node: def:reverse-cumulant-map
def reverseCumulantMap {R : Type*} [CommRing R] (m L : ℕ) (η : ParamSpace R m) : CumVec R :=
  fun r a =>
    if 2 ≤ r ∧ r ≤ L ∧ a ≤ r then
      ∑ j : Fin (m + 2),
        η.2.2 j r * (reverseLoading m η.1 η.2.1 j).1 ^ (r - a)
          * (reverseLoading m η.1 η.2.1 j).2 ^ a
    else 0

/-! ## Generic parameter loci and fiber correspondences -/

/-- The paper's finite retained-coordinate parameter space, represented inside the
function-valued `ParamSpace` by pinning every off-band source weight to zero. -/
def bandSupportedParams {R : Type*} [Zero R] (m L : ℕ) : Set (ParamSpace R m) :=
  { θ | ∀ (j : Fin (m + 2)) (r : ℕ), (r < 2 ∨ L < r) → θ.2.2 j r = 0 }

/-- Generic retained-cumulant locus `Θ^{b,∘}_{m,L}`: the direct slope, all
pairwise loading-slope differences, and all retained weights are nonzero inside
the finite retained-band ambient `Θ^b_{m,L}`.  The
same predicate serves both arrows (forward `(γ, ρ, c)` and reverse `(δ, σ, d)`).
@realizes Theta^{right,circ}_{m,L},Theta^{left,circ}_{m,L}(finite-band ambient and nonvanishing generic product) -/
-- @node: def:generic-parameter-loci
def genericParameterLocus {R : Type*} [CommRing R] (m L : ℕ) :
    Set (ParamSpace R m) :=
  bandSupportedParams m L ∩ { θ |
      θ.1 * (∏ i : Fin m, (θ.1 - θ.2.1 i))
        * (∏ i : Fin m, ∏ i' : Fin m, if i < i' then θ.2.1 i - θ.2.1 i' else 1)
        * (∏ j : Fin (m + 2), ∏ r ∈ Finset.Icc 2 L, θ.2.2 j r) ≠ 0 }

/-- A generic parameter lies in the paper's finite retained-band ambient: its source-weight
coordinates vanish outside orders two through `L`. -/
lemma genericParameterLocus_bandSupported {R : Type*} [CommRing R] {m L : ℕ}
    {θ : ParamSpace R m} (hθ : θ ∈ genericParameterLocus m L) :
    θ ∈ bandSupportedParams m L := hθ.1

/-- At a generic parameter the defining product — direct slope, direct-to-latent slope gaps,
pairwise latent slope gaps, and all retained source weights — is nonzero. -/
lemma genericParameterLocus_prod_ne_zero {R : Type*} [CommRing R] {m L : ℕ}
    {θ : ParamSpace R m} (hθ : θ ∈ genericParameterLocus m L) :
    θ.1 * (∏ i : Fin m, (θ.1 - θ.2.1 i))
      * (∏ i : Fin m, ∏ i' : Fin m, if i < i' then θ.2.1 i - θ.2.1 i' else 1)
      * (∏ j : Fin (m + 2), ∏ r ∈ Finset.Icc 2 L, θ.2.2 j r) ≠ 0 := hθ.2

/-- The paper's finite cumulant coordinate space `ℂ^{q_L}`, represented inside the
`ℕ`-indexed `CumVec` by pinning every coordinate outside the retained range
`2 ≤ r ≤ L`, `a ≤ r` to zero.

Every truncation (`truncatedCumulant`) and every arrow map (`forwardCumulantMap`,
`reverseCumulantMap`) lands here by construction, so this is exactly the observable
coordinate space the paper works in.  Any set of observable vectors that the paper
carves out of `ℂ^{q_L}` must be intersected with it; otherwise the `ℕ`-indexed
representation silently turns it into a cylinder over unconstrained off-band
coordinates. -/
def bandSupportedCumulants {R : Type*} [Zero R] (L : ℕ) : Set (CumVec R) :=
  { t | ∀ r a : ℕ, ¬ (2 ≤ r ∧ r ≤ L ∧ a ≤ r) → t r a = 0 }

/-- Full complex fiber
`R^b_{m,L}(t) = { θ ∈ Θ^b_{m,L} : Φ^b_{m,L}(θ) = t }`, parameterized by the arrow
map `Φ`, restricted to the paper's finite retained-coordinate parameter space
`Θ^b_{m,L}` and compared against `t` on the paper's retained cumulant coordinates
`2 ≤ r ≤ L`, `a ≤ r` (i.e. in `ℂ^{q_L}`).

Both restrictions are faithful bookkeeping, not weakenings.  `ParamSpace`'s weight
family and `CumVec` are `ℕ`-indexed, whereas the paper's ambient spaces are the finite
`Θ^b_{m,L} = ℂ^{m+1} × ℂ^{n(L-1)}` and `ℂ^{q_L}`.  Comparing `Φ θ` and `t` at *every*
`ℕ × ℕ` coordinate would let off-band junk in `t` empty the fiber spuriously, and
leaving `θ` unpinned would make the fiber a cylinder over free off-band weights.  On the
`t` that actually arise here — `t = Φ^b_{m,L}(θ)`, which vanishes off the band by
construction — this definition agrees with the naive one, so no statement that quantifies
over `R^b_{m,L}(Φ^b(θ))` changes meaning.
@realizes R^right_{m,L}(t),R^left_{m,L}(t)(retained-band preimage fiber of Φ over t) -/
-- @node: def:fiber-correspondences
def fiberCorrespondence {R : Type*} [Zero R] (L : ℕ)
    (Φ : ParamSpace R m → CumVec R) (t : CumVec R) : Set (ParamSpace R m) :=
  bandSupportedParams m L ∩
    { θ | ∀ r a : ℕ, 2 ≤ r → r ≤ L → a ≤ r → Φ θ r a = t r a }

/-! ## Real moment-feasible parameter regions -/

/-- Real moment-feasible region `F^b_{m,L}`: real loading-and-cumulant lists with
nonzero direct slope, pairwise-distinct slopes, and every weight family
`c_{j·}` (resp. `d_{j·}`) realized by a centered non-Gaussian real source law with
finite `L`-th moment.  The same predicate serves both arrows.

The equivalence of the "realizable-by-a-source" clause with a finite atomic
(Hankel-PSD) certificate is threaded, where used, from the external truncated
Hamburger interface `I-4`; stating the region itself is unconditional.
@realizes F^right_{m,L},F^left_{m,L}(real feasible loading+cumulant lists)
@realizes S_j(source law ν realizing c_{j·}) -/
-- @node: def:real-feasible-regions
def realFeasibleRegion (m L : ℕ) : Set (ParamSpace ℝ m) :=
  { p |
      p.1 ≠ 0 ∧
      Function.Injective (Fin.cons p.1 p.2.1 : Fin (m + 1) → ℝ) ∧
      -- finite-dimensional cumulant coordinates: every weight coordinate outside
      -- the retained band `2 ≤ r ≤ L` is pinned to `0`, so the region lives in
      -- `ℝ^{m+1} × ℝ^{n(L-1)}` exactly (retains only the paper's coordinates).
      (∀ j : Fin (m + 2), ∀ r : ℕ, (r < 2 ∨ L < r) → p.2.2 j r = 0) ∧
      ∀ j : Fin (m + 2), ∃ ν : Measure ℝ,
        IsProbabilityMeasure ν ∧
        (∫ x, x ∂ν = 0) ∧
        ¬ IsGaussianLaw ν ∧
        MemLp (id : ℝ → ℝ) (L : ℝ≥0∞) ν ∧
        ∀ r, 2 ≤ r → r ≤ L → sourceCumulant ν id r = p.2.2 j r }

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
