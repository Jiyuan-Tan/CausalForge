/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Tactic.Attr
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Field

/-!
# The `sum_algebra_simps` normal form

**Normal form (one sentence): `∑` floats to the outside and `+`/`-` float further out still —
products, scalar constants and divisions are distributed inside the summand, so every
expression becomes a signed combination of iterated sums whose bodies are plain products,
which is the shape `Finset.sum_congr` and `ring` consume.**

The point of the set is the one move `ring` cannot make: carrying a multiplication or a
division across the `Finset.sum` boundary. `ring`/`ring_nf` treat `∑ i, f i` as an opaque atom,
so `c * ∑ i, f i` and `∑ i, c * f i` are two different atoms to them; conversely simp alone
cannot reassociate the products that come out. The intended idiom is therefore
`simp only [sum_algebra_simps]` followed by `ring` (or by `Finset.sum_congr rfl` down to the
leaves and then `ring`), and the set carries the ring distributivity lemmas so that the two
halves interleave in a single simp pass rather than having to be alternated by hand.

## Why this direction

*Call-site direction, 707 : 161 for distributing.* Across `Causalean/` and the CausalSmith
outputs, `Finset.mul_sum` is cited 631 times (532 forward, 99 as `← Finset.mul_sum`) and
`Finset.sum_mul` 237 times (175 forward, 62 backward). Restricted to the design-based and panel
subtrees this is 107 : 16 and 52 : 16. The library already normalizes toward sum-of-products;
it just does it by hand, one `rw` at a time.

*The head symbol the workhorse tactic needs.* The dominant proof idiom over finite sums here is
`Finset.sum_congr rfl` down to a pointwise `ring` goal (1,673 `Finset.sum_congr` citations in
412 files). That tactic requires `∑` to be the head symbol of both sides, which is exactly what
distributing produces and what collecting destroys. `EdgeVarianceBound.lean` shows the cost of
having no normalizer: four nested `rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro _ _`
blocks to distribute one constant through a quadruple sum. One `simp only [sum_algebra_simps]`
closes that goal outright.

*Mathlib fixes the `-` direction for us.* `Finset.sum_sub_distrib` and `Finset.sum_neg_distrib`
(and their `∏` originals `Finset.prod_div_distrib`, `prod_inv_distrib`) are global `@[simp]`, in
the *splitting* direction. The collecting direction is therefore not merely a taste question: a
set containing `← Finset.sum_sub_distrib` would loop against the default simp set. So additive
structure splits, and `Finset.sum_add_distrib` — which Mathlib leaves untagged — is added here so
that `+` behaves like `-` instead of stalling halfway.

*Splitting `±` and distributing `*` only compose through ring distributivity.* Measured: because
simp rewrites innermost-first, the global `Finset.sum_sub_distrib` fires first and turns
`c * ∑ i, (f i - g i)` into `c * (∑ f - ∑ g)`, where `Finset.mul_sum` no longer matches; the goal
`c * ∑ i, (f i - g i) = ∑ i, c * f i - ∑ i, c * g i` is then left open. Adding `mul_sub` and its
siblings closes it. This is why the ring distributivity lemmas are members and not an
afterthought.

*Binder order is pinned by priority.* `Finset.sum_mul` and `Finset.mul_sum` both match
`(∑ i, f i) * ∑ j, g j` at the root, and the two orders of application yield the two different
binder orders `∑ i, ∑ j, …` and `∑ j, ∑ i, …` (measured both ways). `Finset.sum_mul` therefore
carries priority `1100`, so the *left* factor's binders end up outermost, agreeing with
`Finset.sum_mul_sum`.

## What is deliberately excluded

- `Finset.sum_comm` (147 citations). It is permutative, so simp would order the binders by term
  order rather than by anything a reader can predict, and the direction evidence is vacuous —
  all 147 citations are written forward because `rw [Finset.sum_comm]` and
  `rw [← Finset.sum_comm]` are the same rewrite. Re-indexing stays an explicit `rw`.
- `Finset.sum_congr` (1,673) and `Finset.sum_eq_single` (185). Neither is simp-shaped: the first
  is a congruence lemma simp already applies structurally, the second is conditional on two side
  goals. They are the *consumers* of this normal form, not members of it.
- The design-based expectation layer (`FiniteDesign.E_add`, `E_sub`, `E_const_mul`, `E_sum`, …).
  Those move `E` toward the leaves, which at the unfolded `∑ z, p z * X z` level is the
  *collecting* direction — the exact opposite of this set. They are a second normal form on a
  second layer, and they stay safe only because nothing here unfolds `FiniteDesign.E`. Linearity
  of a summation operator is the planned Phase-3 `integral_linearity`/`condexp_linearity` shape,
  not a simp set.
- `Finset.sum_smul` / `Finset.smul_sum` (11 citations library-wide) and `Finset.sum_apply` (57,
  and half of those are the `Measure`-valued homonym): each would pull a further import into this
  leaf file for a pattern that does not occur in the design-based or panel algebra.
  `nsmul_eq_mul` is a member because it is what `Finset.sum_const` leaves behind.
-/

namespace Causalean.Tactic

/-! ### Carrying a product across the `Finset.sum` boundary

`Finset.sum_mul` takes priority over `Finset.mul_sum` so that on `(∑ i, f i) * ∑ j, g j` the
left factor's binder ends up outermost, matching `Finset.sum_mul_sum`. -/

attribute [sum_algebra_simps 1100] Finset.sum_mul

attribute [sum_algebra_simps]
  Finset.mul_sum
  Finset.sum_div

/-! ### Floating `+` / `-` above the sums

`Finset.sum_sub_distrib` and `Finset.sum_neg_distrib` are already global `@[simp]`; they are
listed so that `simp only [sum_algebra_simps]` reaches the same normal form as
`simp [sum_algebra_simps]`. `Finset.sum_add_distrib` is not global `@[simp]` upstream, and is
what makes `+` behave like `-`. -/

attribute [sum_algebra_simps]
  Finset.sum_add_distrib
  Finset.sum_sub_distrib
  Finset.sum_neg_distrib

/-! ### Ring distributivity, so the two halves compose in one pass

Without these, splitting a subtraction out of a sum blocks the product from being distributed
into it and the pass stalls with the two sides of an identity in different shapes. -/

attribute [sum_algebra_simps]
  mul_add
  add_mul
  mul_sub
  sub_mul
  mul_neg
  neg_mul
  add_div
  sub_div
  neg_div

/-! ### Base cases: sums that collapse

All of these are already global `@[simp]`; membership makes the set self-contained under
`simp only`. `nsmul_eq_mul` and `Finset.card_univ` finish the `∑ _i : ι, c = Fintype.card ι * c`
chain that `Finset.sum_const` starts. -/

attribute [sum_algebra_simps]
  Finset.sum_empty
  Finset.sum_singleton
  Finset.sum_const
  Finset.sum_ite_eq
  Finset.sum_ite_eq'
  Finset.sum_boole
  Finset.card_univ
  nsmul_eq_mul

end Causalean.Tactic
