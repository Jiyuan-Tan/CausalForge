/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Observed panel cells with positive normalized weights

This file formalizes the substrate of Definition 2.1 of
`CausalSmith/doc/general_projection_carryover_note.tex`: a finite collection of
**observed unit-period cells** `R ⊆ I × T` together with strictly positive
weights `ω_r` summing to 1 over `R`.

As of the `Causalean/Panel/Weighted/` refactor, `Cells I T` is now a thin specialization
of the generic `Causalean.Panel.Weighted.WeightedSupport (I × T)`.  All algebraic
substrate (`ip`, `ipMat`, `proj`, `residualize`, `tildeX`, `tildeXVec`,
`Q_XX`, `rhsVec`, `thetaHat`, `RankCondition`) is inherited transparently
through the `abbrev`, and dot-notation `c.ip A B`, `c.tildeX H X`, etc.,
resolves to the `WeightedSupport.*` declarations.

The panel-specific `balanced` constructor (which depends on
`Fintype.card I * Fintype.card T`) is retained here.

## Main definitions

* `Cells I T` — abbreviation for `WeightedSupport (I × T)`.
* `Cells.balanced` — the balanced-panel special case
  `R = I × T`, `ω = 1 / (|I| · |T|)`.
-/

import Causalean.Panel.Weighted.Support
import Mathlib.Data.Fintype.Prod

/-! # Observed Panel Cells

This file provides the observed-cell substrate for panel regressions: a finite
set of observed unit-period cells with strictly positive normalized weights. It
specializes the generic weighted-support infrastructure to panel cell indices
and supplies the balanced-panel constructor. It mirrors Definition 2.1 of the
projection note.

**Relation to `Causalean.Panel.CellBridge`.** Both files use the word *cell*,
but for different objects. Here a cell is a **discrete index** `r = (i, t) ∈ I × T`
carrying a positive normalized weight — a finite-weighted-support object with no
measure theory. In `CellBridge` a cell is a **measurable level set**
`{ω | G ω = g}` of an observable map on a probability space. The two share no
declarations and neither imports the other; the only common substrate is
`Causalean.Panel.Weighted.IndicatorSpan`. -/

open scoped BigOperators

namespace Causalean
namespace Panel

variable (I T : Type*)

/-- Observed cells of a panel together with positive normalized weights.

This is a thin specialization of `Causalean.Panel.Weighted.WeightedSupport` to the
product index `R = I × T`.  All algebraic properties (`weight_nonneg`,
`sum_weight_univ`, `sum_weight_univ_eq_one`, …) and the entire FWL/WLS
substrate (`ip`, `ipMat`, `proj`, `residualize`, `tildeX`, `tildeXVec`,
`Q_XX`, `rhsVec`, `thetaHat`, `RankCondition`) are inherited transparently
through the abbreviation.

Mirrors Definition 2.1 of `CausalSmith/doc/general_projection_carryover_note.tex`. -/
abbrev Cells [Fintype I] [Fintype T] [DecidableEq I] [DecidableEq T] : Type _ :=
  Causalean.Panel.Weighted.WeightedSupport (I × T)

namespace Cells

variable {I T}
variable [Fintype I] [Fintype T] [DecidableEq I] [DecidableEq T]

/-! ### Balanced panel -/

section Balanced

variable [Nonempty I] [Nonempty T]

/-- The balanced panel: every cell is observed and every cell carries weight
`1 / (|I| · |T|)`. -/
noncomputable def balanced : Cells I T where
  observed := Finset.univ
  observed_nonempty := Finset.univ_nonempty
  weight _ := (1 : ℝ) / (Fintype.card I * Fintype.card T)
  weight_pos := by
    intro r _
    have hI : (0 : ℝ) < Fintype.card I := by
      exact_mod_cast Fintype.card_pos
    have hT : (0 : ℝ) < Fintype.card T := by
      exact_mod_cast Fintype.card_pos
    positivity
  weight_zero_off := by
    intro r hr
    exact (hr (Finset.mem_univ r)).elim
  weight_sum_one := by
    have hI : (Fintype.card I : ℝ) ≠ 0 := by
      have : 0 < Fintype.card I := Fintype.card_pos
      exact_mod_cast this.ne'
    have hT : (Fintype.card T : ℝ) ≠ 0 := by
      have : 0 < Fintype.card T := Fintype.card_pos
      exact_mod_cast this.ne'
    -- `∑_{r ∈ univ} 1/(|I|·|T|) = (|I|·|T|) · 1/(|I|·|T|) = 1`.
    rw [Finset.sum_const]
    have hcard : (Finset.univ : Finset (I × T)).card =
        Fintype.card I * Fintype.card T := by
      rw [Finset.card_univ, Fintype.card_prod]
    rw [hcard, nsmul_eq_mul]
    push_cast
    field_simp

/-- The balanced panel observes every unit-period cell. -/
@[simp] lemma balanced_observed :
    (balanced (I := I) (T := T)).observed = Finset.univ := rfl

/-- The balanced panel assigns the same normalized weight to every
unit-period cell. -/
@[simp] lemma balanced_weight (r : I × T) :
    (balanced (I := I) (T := T)).weight r =
      (1 : ℝ) / (Fintype.card I * Fintype.card T) := rfl

end Balanced

end Cells

end Panel
end Causalean
