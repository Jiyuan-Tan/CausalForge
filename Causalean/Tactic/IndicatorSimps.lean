/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Tactic.Attr
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.GroupWithZero.Indicator

/-!
# The `indicator_simps` normal form

**Normal form (one sentence): an indicator-weighted expression is carried to a single
`Set.indicator`-headed term, and an indicator whose membership test the context already
decides is eliminated to its value or `0`; `if-then-else` is never introduced.**

This file registers the Mathlib half of the set. Project lemmas declare their membership at
their own definition sites, so that this file stays leaf-most in the import graph.

## Why this direction, and not the other one

The attribute was provisionally registered with the opposite direction — push
`Set.indicator` and the project wrappers into `ite`, then case-split. Four pieces of
evidence reverse it.

*Call-site direction.* Across Causalean and the CausalSmith outputs, `Set.indicator_of_mem`
and `Set.indicator_of_notMem` — which eliminate the indicator in place, under a membership
hypothesis — are cited **564** times (312 + 252), against **15** citations of
`Set.indicator_apply`, the only lemma that moves an indicator toward `ite`. The library
already has a normal form and it is not `ite`. The project's own bridge lemmas point the same
way: `Causalean.Estimation.DTR.indEq_factualD0_eq_indicator` and its stage-one twin rewrite an
`ite`-defined treatment indicator *into* `POVar.indicator`, never the reverse.

*Mathlib's own choice.* `Set.indicator_of_mem` and `Set.indicator_of_notMem` are global
`@[simp]`; `Set.indicator_apply` deliberately is not, and it carries a `[Decidable (a ∈ s)]`
instance argument. Tagging it here would put it in direct competition with the two global
simp lemmas on every indicator application.

*Decidable-instance fragility.* Any rewrite toward `ite` pins a `Decidable` instance into the
result. `Causalean.Experimentation.DesignBased.FiniteDesign.map_p` is the cautionary case: its
right-hand side bakes in `Classical.propDecidable`, so it cannot match a goal whose `ite` came
from a `DecidableEq`-derived instance. A library-wide `ite` normal form inherits that failure
mode everywhere; a `Set.indicator` normal form carries no instance at all.

*Destructive unfolding.* Eagerly unfolding the design-based wrappers `FiniteDesign.ind` and
`expoInd` into `ite` would stop the existing `@[simp]` lemmas `FiniteDesign.E_ind` and
`E_expoInd` from firing, and those are how the whole design-based variance algebra reaches
`FiniteDesign.Pr` / `prop`. Unfolding costs more than it buys.

## What is deliberately excluded

- `Set.indicator_apply`, and the project lemmas that unfold a definition *into* an `ite`
  (`cellIndicator_apply`, `tailInd_apply`, `absorbingTreatment_eq`): they fight the direction.
  Their existing `@[simp]` attributes are left untouched — removing one could break distant
  proofs. `cellIndicator_apply`, the only `rfl`-level one of the three, carries
  `causal_defs_simps` instead, which is the set that owns "unfold my definition";
  `tailInd_apply` converts a `Set.indicator` definition into an `ite` rather than unfolding it,
  and `absorbingTreatment_eq` changes the decidability spelling, so neither qualifies there.
- `FiniteDesign.map_p`: excluded from every set, because its right-hand side pins
  `Classical.propDecidable`.
- `Set.indicator_mul_left` / `indicator_mul_right` / `indicator_mul_const` /
  `indicator_const_mul` / `inter_indicator_mul`: Mathlib states these in the *distributing*
  direction (indicator of a product becomes a product), which is the opposite of the
  single-head normal form. They stay name-called, or are used with `rw [← …]`.
- `Causalean.Panel.PO.Mobius.indicator_empty`: a different notion — that `indicator` builds a
  `Fin 2`-valued treatment history, not a `0/1` weight.
-/

namespace Set

/-! ### The two collecting rewrites Mathlib does not state

Mathlib states `Set.indicator_mul_left` and `Set.indicator_mul_right` in the *distributing*
direction, and has no `f = 1` specialisation at all. The collecting direction is what the
library actually wants — a product of a function with a `0/1` indicator is the indicator of
that function — because it is the form Mathlib's integral and conditional-expectation API
(`integral_indicator`, `Integrable.indicator`, `condExp_setIndicator_condExp_of_le`) is stated
in. Both are Mathlib-promotion candidates. -/

/-- [Multiplying a function by the zero-one indicator of a set, on the right, is the same as
restricting that function to the set](goal): off the set both sides are zero, and on the set the
indicator contributes a factor of one. -/
@[indicator_simps]
lemma mul_indicator_one {α M : Type*} [MulZeroOneClass M] (s : Set α) (f : α → M) (a : α) :
    f a * s.indicator (fun _ => (1 : M)) a = s.indicator f a := by
  by_cases h : a ∈ s <;> simp [h]

/-- Multiplying a function by the zero-one indicator of a set, on the left, is the same as
restricting that function to the set: off the set both sides are zero, and on the set the
indicator contributes a factor of one. -/
@[indicator_simps]
lemma indicator_one_mul {α M : Type*} [MulZeroOneClass M] (s : Set α) (f : α → M) (a : α) :
    s.indicator (fun _ => (1 : M)) a * f a = s.indicator f a := by
  by_cases h : a ∈ s <;> simp [h]

end Set

namespace Causalean.Tactic

/-! ### Eliminating an indicator whose membership test is decided -/

attribute [indicator_simps]
  Set.indicator_of_mem
  Set.indicator_of_notMem
  Set.indicator_apply_eq_zero

/-! ### Base cases -/

attribute [indicator_simps]
  Set.indicator_empty
  Set.indicator_univ
  Set.indicator_zero
  Set.indicator_zero'

/-! ### Reaching the single `Set.indicator` head -/

attribute [indicator_simps]
  Set.indicator_indicator
  Set.piecewise_eq_indicator
  Set.indicator_compl_add_self_apply
  Set.indicator_self_add_compl_apply

end Causalean.Tactic
