/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Basic.Cumulants

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

/-! ## Admissible source swaps (the `G_m` action) -/

/-- Relabel the middle block `{1, …, m}` of source indices by `π`, fixing `0` and
`m + 1`. -/
def permMiddle (m : ℕ) (π : Equiv.Perm (Fin m)) : Fin (m + 2) → Fin (m + 2) :=
  fun j =>
    if _ : j.val = 0 then j
    else if _ : j.val = m + 1 then j
    else ⟨(π ⟨j.val - 1, by have := j.isLt; omega⟩).val + 1,
          by have := (π ⟨j.val - 1, by have := j.isLt; omega⟩).isLt; omega⟩

/-- Admissible source swap: `π ∈ G_m = Equiv.Perm (Fin m)` acts by relabeling the
latent slopes `ρ_i` (resp. `σ_i`) and their weights `c_{ir}` (resp. `d_{ir}`)
simultaneously, while fixing indices `0` and `m + 1`.  The same map realizes both
arrow actions.
@realizes G_m,pi,b(π-relabeling of the middle source block) -/
-- @node: def:admissible-source-swaps
def admissibleSourceSwap {R : Type*} (m : ℕ) (π : Equiv.Perm (Fin m))
    (θ : ParamSpace R m) : ParamSpace R m :=
  (θ.1, fun i => θ.2.1 (π i), fun j r => θ.2.2 (permMiddle m π j) r)

/-- Arrow index `b ∈ {right, left}`: the two-element type indexing the arrow
parameterization on which the `G_m` action acts (`right` = forward, `left` =
reverse).
@realizes G_m,pi,b(arrow index b ∈ {right, left}) -/
inductive Arrow
  | right
  | left
  deriving DecidableEq

/-- Arrow-tagged admissible source swap: the `G_m` action on arrow `b`.  The same
middle-block relabeling formula realizes both the forward (`right`) action on
`(ρ_i, c_{ir})` and the reverse (`left`) action on `(σ_i, d_{ir})`, so `b` is a
tag; indices `0` and `m + 1` are fixed in both cases.
@realizes G_m,pi,b(π-relabeling tagged by arrow b; same formula for both) -/
def admissibleSourceSwapArrow {R : Type*} (m : ℕ) (_b : Arrow) (π : Equiv.Perm (Fin m))
    (θ : ParamSpace R m) : ParamSpace R m :=
  admissibleSourceSwap m π θ

/-- The `G_m` action on the tagged space `Arrow × ParamSpace`: relabel the middle
source block and **preserve the arrow tag** `b`.  The swap fixes indices `0`, `m + 1`,
so it never converts a forward (`right`) axis pattern into a reverse (`left`) one; the
tag component is carried unchanged.
@realizes G_m,pi,b(tag-preserving G_m action on Arrow × ParamSpace) -/
def admissibleSourceSwapTagged {R : Type*} (m : ℕ) (π : Equiv.Perm (Fin m)) :
    Arrow × ParamSpace R m → Arrow × ParamSpace R m :=
  fun p => (p.1, admissibleSourceSwap m π p.2)

/-- Arrow-tagged `G_m`-orbit of `(b, θ)`: its images under all admissible swaps, every
member carrying the same tag `b`.  Right-tagged and left-tagged orbits are therefore
disjoint. -/
def arrowTaggedOrbit {R : Type*} (m : ℕ) (b : Arrow) (θ : ParamSpace R m) :
    Set (Arrow × ParamSpace R m) :=
  { p | ∃ π : Equiv.Perm (Fin m), p = admissibleSourceSwapTagged m π (b, θ) }

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
