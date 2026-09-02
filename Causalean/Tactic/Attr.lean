/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Tactic.Attr.Register

/-!
Registers Causalean's custom simp attributes (Mathlib `*_simps` convention;
`Mathlib/Tactic/Attr/Register.lean` is the precedent file). This file is a leaf:
it must stay dependency-light and never import project mathematics, so that set
membership can be declared anywhere without rebuild cascades.

Each set is a documented normal form — the one-sentence statement of the
direction lives on the attribute itself; the populate files
(`Causalean/Tactic/*.lean`) carry the rationale. Per the tactic-abstraction
plan, sets are populated by evidence (usage-direction counts, confluence), and
membership never changes any statement.
-/

/-- Definitional-unfolding normal form: rewrites project definitions to their
defining equations (`foo_apply`/`foo_def`-shaped), replacing ad-hoc `unfold`
chains. Direction: always away from the project constant toward its body. -/
register_simp_attr causal_defs_simps

/-- Indicator normal form for causal weighting arguments. Direction: carry the
expression to a single `Set.indicator` head and eliminate an indicator whose
membership test the context decides, never introducing `ite`. -/
register_simp_attr indicator_simps

/-- Conditional-expectation wrapper normal form: unfolds Causalean's
conditioning wrappers (`POVar`/`POCFBundle` `condExpGiven`, `condExpRatio`, and
the event-level `eventCondExp`) to the Mathlib primitives they abbreviate —
`condExp` given the conditioning σ-algebra, and the restricted integral over
the event's mass — so the Mathlib API applies. Wrapper unfolding ONLY: condExp
linearity is `=ᵐ[μ]`-valued and out of simp's reach. -/
register_simp_attr condexp_simps

/-- Finite-sum algebra normal form for design-based/panel variance arguments:
sum-of-products form (`Finset.mul_sum` direction). Direction: distribute
products, scalars and divisions *inside* the summand so that `Finset.sum` floats
to the outside and `+`/`-` float outside the sums — the shape
`Finset.sum_congr` and `ring` consume. -/
register_simp_attr sum_algebra_simps
