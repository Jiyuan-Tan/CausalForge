/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Additive two-axis spans

For a generic index `R` equipped with two projections `f₁ : R → A` and
`f₂ : R → B`, the **additive span** is the linear subspace of `R → ℝ`
consisting of arrays of the form

    h r = a (f₁ r) + b (f₂ r)

for some `a : A → ℝ` and `b : B → ℝ`.  Specialized to `R = I × T`,
`f₁ = Prod.fst`, `f₂ = Prod.snd`, this is the classical two-way
fixed-effect subspace `H_twfe` used in `Causalean/Panel/FixedEffect.lean`
and across panel estimand-characterization arguments that residualize against
unit and time nuisance components.

This file generalizes the original
`Causalean/Panel/EstimandCharacterization/AdditiveSpan.lean`, which only carried
the `(I × T)`-shaped predicate.

## Main definitions

* `AdditiveSpan f₁ f₂` — the additive-span subspace of `R → ℝ`.
* `twoAxisAdditiveSpan I T` — specialization to `R = I × T` with
  `f₁ = Prod.fst`, `f₂ = Prod.snd`.
* `IsUnitTimeAdditive` — membership predicate for the two-axis unit/time case.

## Main lemmas

* `AdditiveSpan.const_mem` — constants live in the additive span.
* `AdditiveSpan.finiteDimensional` — under `[Fintype R]` the span is
  finite-dimensional.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Additive Two-Axis Spans

This file defines `AdditiveSpan`, the linear subspace of finite arrays that
decompose additively through two index maps. It provides the generic algebra
behind two-way fixed-effect nuisance spaces, the product-index specialization
`twoAxisAdditiveSpan`, and the unit/time membership predicate
`IsUnitTimeAdditive`. The main public facts expose membership, constants in the
span, and finite dimensionality over a finite support. -/

open scoped BigOperators

namespace Causalean
namespace Panel.Weighted

/-- The **additive span** of two projections `f₁ : R → A` and `f₂ : R → B`:
the subspace of `R → ℝ` consisting of arrays
`h r = a (f₁ r) + b (f₂ r)` for some `a : A → ℝ` and `b : B → ℝ`. -/
def AdditiveSpan {R A B : Type*} (f₁ : R → A) (f₂ : R → B) :
    Submodule ℝ (R → ℝ) where
  carrier := { h | ∃ a : A → ℝ, ∃ b : B → ℝ, ∀ r : R, h r = a (f₁ r) + b (f₂ r) }
  zero_mem' := ⟨fun _ => 0, fun _ => 0, by intro r; simp⟩
  add_mem' := by
    rintro h₁ h₂ ⟨a₁, b₁, hh₁⟩ ⟨a₂, b₂, hh₂⟩
    refine ⟨a₁ + a₂, b₁ + b₂, ?_⟩
    intro r
    simp [hh₁ r, hh₂ r, Pi.add_apply]; ring
  smul_mem' := by
    rintro s h ⟨a, b, hh⟩
    refine ⟨s • a, s • b, ?_⟩
    intro r
    simp [hh r, Pi.smul_apply, smul_eq_mul]; ring

namespace AdditiveSpan

variable {R A B : Type*} {f₁ : R → A} {f₂ : R → B}

/-- Membership unfolding for `AdditiveSpan`. -/
lemma mem_iff {h : R → ℝ} :
    h ∈ AdditiveSpan f₁ f₂ ↔
      ∃ a : A → ℝ, ∃ b : B → ℝ, ∀ r : R, h r = a (f₁ r) + b (f₂ r) :=
  Iff.rfl

/-- Constants belong to the additive span: take `a := fun _ => c₀`,
`b := fun _ => 0`. -/
lemma const_mem (f₁ : R → A) (f₂ : R → B) (c₀ : ℝ) :
    (fun _ : R => c₀) ∈ AdditiveSpan f₁ f₂ := by
  refine ⟨fun _ => c₀, fun _ => 0, ?_⟩
  intro r; simp

/-- Under `[Finite R]` the additive span sits inside the
finite-dimensional ambient space `R → ℝ`, hence is finite-dimensional. -/
instance finiteDimensional [Finite R] :
    Module.Finite ℝ (AdditiveSpan f₁ f₂) := by
  haveI : Fintype R := Fintype.ofFinite R
  haveI : Module.Finite ℝ (R → ℝ) := by infer_instance
  exact Module.Finite.of_injective (AdditiveSpan f₁ f₂).subtype
    (Subtype.val_injective)

end AdditiveSpan

/-- The two-axis additive span for the product index `R = I × T`:
specializes `AdditiveSpan` to `f₁ = Prod.fst`, `f₂ = Prod.snd`. -/
def twoAxisAdditiveSpan (I T : Type*) : Submodule ℝ ((I × T) → ℝ) :=
  AdditiveSpan (Prod.fst : I × T → I) (Prod.snd : I × T → T)

/-- Predicate for the unit/time additive class `h i t = a i + b t`. -/
def IsUnitTimeAdditive {Unit Time : Type*} (h : Unit → Time → ℝ) : Prop :=
  ∃ a : Unit → ℝ, ∃ b : Time → ℝ, ∀ i t, h i t = a i + b t

end Panel.Weighted
end Causalean
