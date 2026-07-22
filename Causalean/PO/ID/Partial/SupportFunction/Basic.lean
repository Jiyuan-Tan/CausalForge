/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Support function of a set (partial-identification spine)

The scalar engine of `PartialID/Basic.lean` characterises a *one-dimensional*
identified set as the range of a real objective over a feasible set.  Most
partial-identification problems, however, present a **convex feasible set** `C`
in a vector space together with a **linear target** `x ↦ ⟪d, x⟫` (an ATE, a
bridge functional, a reweighted mean); the sharp identified interval is then
governed by the *support function*

    supportFn C d = sup { ⟪d, x⟫ : x ∈ C }.

This file is the abstract spine: the definition over a real inner-product space
and the two monotone "sandwich" facts (`le_supportFn`, `supportFn_le`) that every
downstream sharpness proof consumes.  The support-function *calculus* lives in
`Calculus.lean`; the identified-interval characterisation `[-h(-d), h(d)]` and the
bridge to the scalar `IdentifiedInterval` engine live in `Interval.lean`.

Endpoints are reported through `sSup` (matching the `SandwichInterval` /
`RandomSet` convention), so boundedness hypotheses are carried explicitly rather
than baked into the type — the same discipline as the scalar engine.

## Main definitions

* `supportFn C d` — the support function `sup { ⟪d, x⟫ : x ∈ C }`.

## Main results

* `le_supportFn` — a feasible point's functional value is `≤` the support value.
* `supportFn_le` — a uniform upper bound on the functional bounds the support value.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! # Support functions for partial identification

This file defines the support function of a feasible set in a real inner-product space.
It supplies the basic lower and upper comparison principles used to turn convex
feasible sets into sharp bounds for linear causal targets. Boundedness and
nonemptiness side conditions are carried explicitly, matching the scalar
partial-identification convention. -/

open scoped RealInnerProductSpace

namespace Causalean
namespace PartialID

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **support function** of a set `C` in direction `d`:
`supportFn C d = sup { ⟪d, x⟫ : x ∈ C }`.  Outside the nonempty and
bounded-above regime, the raw `sSup` value is a convention and should not be
used mathematically; meaningful statements carry `Nonempty`/`BddAbove`
hypotheses (see `le_supportFn`, `supportFn_le`). -/
noncomputable def supportFn (C : Set E) (d : E) : ℝ :=
  sSup ((fun x => ⟪d, x⟫) '' C)

/-- The support function is definitionally the supremum of the linear target over the set.

This unfolding lemma exposes the image form used by comparison arguments. -/
lemma supportFn_eq_iSup_image (C : Set E) (d : E) :
    supportFn C d = sSup ((fun x => ⟪d, x⟫) '' C) := rfl

/-- **Lower sandwich.** If the functional `⟪d, ·⟫` is bounded above on `C`, then
every feasible point's value is at most the support value. -/
theorem le_supportFn {C : Set E} {d : E} {x : E} (hx : x ∈ C)
    (hbdd : BddAbove ((fun x => ⟪d, x⟫) '' C)) :
    ⟪d, x⟫ ≤ supportFn C d :=
  le_csSup hbdd ⟨x, hx, rfl⟩

/-- **Upper sandwich.** A uniform upper bound `b` on the functional over a
nonempty `C` bounds the support value: `supportFn C d ≤ b`. -/
theorem supportFn_le {C : Set E} {d : E} {b : ℝ} (hne : C.Nonempty)
    (hb : ∀ x ∈ C, ⟪d, x⟫ ≤ b) :
    supportFn C d ≤ b := by
  refine csSup_le ?_ ?_
  · exact (hne.image _)
  · rintro _ ⟨x, hx, rfl⟩; exact hb x hx

end PartialID
end Causalean
