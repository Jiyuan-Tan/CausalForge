/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Two-way fixed-effect subspace

For `c : Cells I T`, the **two-way fixed-effect subspace** `H_twfe` is the
linear subspace of `(I × T) → ℝ` consisting of arrays of the form
`h (i, t) = a i + b t` for some `a : I → ℝ` and `b : T → ℝ`.

As of the `Causalean/Panel/Weighted/` refactor, `H_twfe` is a thin specialization
of the generic two-axis additive span
`Causalean.Panel.Weighted.twoAxisAdditiveSpan I T`
(itself `Causalean.Panel.Weighted.AdditiveSpan (Prod.fst) (Prod.snd)`).
All algebraic properties (constants membership, finite-dimensionality)
are inherited from the generic API.

This mirrors Definition 2.2 of
`CausalSmith/doc/general_projection_carryover_note.tex`.

## Main definitions

* `Cells.H_twfe c : Submodule ℝ ((I × T) → ℝ)` — the two-way fixed-effect
  subspace, defined as `Causalean.Panel.Weighted.twoAxisAdditiveSpan I T`.

## Main lemmas

* `Cells.const_mem_H_twfe` — constants are in `H_twfe`.
* `Cells.H_twfe_finiteDimensional` — `H_twfe` is finite-dimensional.
-/

import Causalean.Panel.Subspace
import Causalean.Panel.Weighted.AdditiveSpan

/-! # Two-Way Fixed Effects

This file defines the two-way fixed-effect subspace of panel arrays as the set
of unit-plus-period additive functions. It connects the panel notation to the
generic additive-span infrastructure and records basic membership and
finite-dimensionality facts. -/

open scoped BigOperators

namespace Causalean
namespace Panel
namespace Cells

variable {I T : Type*}
variable [Fintype I] [Fintype T] [DecidableEq I] [DecidableEq T]

/-- The two-way fixed-effect subspace.

`h ∈ H_twfe` iff there exist `a : I → ℝ` and `b : T → ℝ` such that
`h (i, t) = a i + b t` for all `(i, t)`.

Definitionally equal to `Causalean.Panel.Weighted.twoAxisAdditiveSpan I T`. -/
def H_twfe (_c : Cells I T) : Submodule ℝ (V I T) :=
  Causalean.Panel.Weighted.twoAxisAdditiveSpan I T

/-- `H_twfe` unfolds to the generic two-axis additive span. -/
lemma H_twfe_eq (c : Cells I T) :
    c.H_twfe = Causalean.Panel.Weighted.twoAxisAdditiveSpan I T := rfl

/-- Constants belong to `H_twfe`: delegates to `AdditiveSpan.const_mem`. -/
lemma const_mem_H_twfe (c : Cells I T) (c₀ : ℝ) :
    (fun _ : I × T => c₀) ∈ c.H_twfe :=
  Causalean.Panel.Weighted.AdditiveSpan.const_mem (Prod.fst : I × T → I) Prod.snd c₀

/-- `H_twfe` is finite-dimensional: inherits from
`AdditiveSpan.finiteDimensional`. -/
instance H_twfe_finiteDimensional (c : Cells I T) :
    Module.Finite ℝ (c.H_twfe) :=
  Causalean.Panel.Weighted.AdditiveSpan.finiteDimensional

end Cells
end Panel
end Causalean
