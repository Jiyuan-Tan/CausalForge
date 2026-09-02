/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Integrability-free linearity of conditional expectation

Mathlib's `condExp_add`, `condExp_sub` and `condExp_finsetSum` take the integrability of
each summand as an explicit argument, so every call site must first *name* those facts —
in this library that is typically a chain of `have _ : Integrable …` lines whose only
content is `Integrable.add`/`Integrable.sub` bookkeeping.

This file restates the three lemmas with the integrability hypotheses as `autoParam`s
discharged by `fun_prop`, which the Causalean side-condition layer has been tagged for.
At a call site that already holds the witnesses, `fun_prop` finds them by `assumption`;
where the integrand is built from tagged project constructions, it proves them outright.
Passing the hypotheses explicitly still works, so the primed forms are a strict
convenience layer over the Mathlib originals — no mathematics is added.

The wrapper analogues for `POVar.condExpGiven` and `POCFBundle.condExpGiven` live next to
those definitions, in `Causalean/PO/Conditioning/`.
-/

open Filter

namespace MeasureTheory

variable {α E : Type*} {m₀ : MeasurableSpace α} {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f g : α → E}

/-- Conditional expectation is additive: the conditional expectation of a sum of [two
integrable functions](hyp:hf,hg) [is the sum of their conditional expectations, almost everywhere](goal).

Integrability-free restatement of `MeasureTheory.condExp_add`: the two integrability
hypotheses are `autoParam`s discharged by `fun_prop`, so a call site that holds the
witnesses in context — or whose integrands are built from `fun_prop`-tagged
constructions — supplies neither. -/
theorem condExp_add' (m : MeasurableSpace α)
    (hf : Integrable f μ := by fun_prop) (hg : Integrable g μ := by fun_prop) :
    μ[f + g | m] =ᵐ[μ] μ[f | m] + μ[g | m] :=
  condExp_add hf hg m

/-- Conditional expectation respects differences: the conditional expectation of the
difference of two integrable functions is the difference of their conditional
expectations, almost everywhere.

Integrability-free restatement of `MeasureTheory.condExp_sub`; see `condExp_add'`. -/
theorem condExp_sub' (m : MeasurableSpace α)
    (hf : Integrable f μ := by fun_prop) (hg : Integrable g μ := by fun_prop) :
    μ[f - g | m] =ᵐ[μ] μ[f | m] - μ[g | m] :=
  condExp_sub hf hg m

/-- Conditional expectation commutes with a finite sum: conditioning a finite sum of
integrable functions is the same, almost everywhere, as summing their conditional
expectations.

Integrability-free restatement of `MeasureTheory.condExp_finsetSum`; the family-wide
integrability hypothesis is an `autoParam` discharged by `fun_prop` after introducing the
index and its membership proof. -/
theorem condExp_finsetSum' {ι : Type*} {s : Finset ι} {F : ι → α → E}
    (m : MeasurableSpace α)
    (hF : ∀ i ∈ s, Integrable (F i) μ := by intro i _; fun_prop) :
    μ[∑ i ∈ s, F i | m] =ᵐ[μ] ∑ i ∈ s, μ[F i | m] :=
  condExp_finsetSum hF m

end MeasureTheory
