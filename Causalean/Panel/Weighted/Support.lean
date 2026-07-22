/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Weighted support: a finite weighted-index probability object

This file formalizes the **substrate** of the FWL/WLS algebra used across
Causalean's identification and estimand-characterization layer: a finite index
set `R` (the *support*) together with strictly positive weights `ω_r` summing
to 1 over the observed subset.

This substrate is the algebraic foundation for Frisch-Waugh-Lovell: its
weighted projections (`Causalean/Panel/Weighted/Subspace.lean`) are the
solutions of the weighted-least-squares problem
(`Causalean/Panel/Weighted/WLS.lean`). Estimand-characterization arguments read
off implicit regression weights from `fwl_identity`
(`Causalean/Panel/Weighted/FWL.lean`).

This generalizes the panel-specific `Causalean/Panel/Cells.lean`, which now
becomes a thin abbreviation `Cells I T := WeightedSupport (I × T)`.

Mirrors Definition 2.1 of
`CausalSmith/doc/general_projection_carryover_note.tex`.

## Main definitions

* `WeightedSupport R` — a structure carrying the observed-index set, the
  weight function, and the positivity / normalization axioms.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! # Weighted finite supports

This file defines `WeightedSupport`, a finite observed support equipped with
strictly positive weights that sum to one on the observed set and vanish off it.
It also proves the basic normalization lemmas `weight_nonneg`,
`sum_weight_univ`, `sum_weight`, and `sum_weight_univ_eq_one`.

The resulting object is the common finite weighted-index substrate for weighted
inner products, weighted least squares, and Frisch-Waugh-Lovell decompositions. -/

open scoped BigOperators

namespace Causalean
namespace Panel.Weighted

/-- A finite weighted index together with positive normalized weights.

The pair `(observed, weight)` records:

* `observed : Finset R` — the observed subset of indices, required nonempty;
* `weight : R → ℝ` — a (total) weight function that is strictly positive
  on `observed`, vanishes off `observed`, and sums to 1 over `observed`.

This mirrors Definition 2.1 of
`CausalSmith/doc/general_projection_carryover_note.tex`. -/
structure WeightedSupport (R : Type*) [Fintype R] [DecidableEq R] where
  /-- The set of observed indices. -/
  observed : Finset R
  /-- Witness that the observed set is nonempty. -/
  observed_nonempty : observed.Nonempty
  /-- The weight `ω : R → ℝ`, defined on the whole index type for
  notational convenience. -/
  weight : R → ℝ
  /-- `ω_r > 0` for every observed index `r`. -/
  weight_pos : ∀ r ∈ observed, 0 < weight r
  /-- `ω_r = 0` for every index outside `observed`. -/
  weight_zero_off : ∀ r, r ∉ observed → weight r = 0
  /-- Normalization `∑_{r ∈ observed} ω_r = 1`. -/
  weight_sum_one : ∑ r ∈ observed, weight r = 1

namespace WeightedSupport

variable {R : Type*}
variable [Fintype R] [DecidableEq R]

/-- The weight function `ω` is nonnegative everywhere on `R`. -/
lemma weight_nonneg (c : WeightedSupport R) (r : R) : 0 ≤ c.weight r := by
  by_cases h : r ∈ c.observed
  · exact (c.weight_pos r h).le
  · simp [c.weight_zero_off r h]

/-- Summing `ω` over the full type `R` equals summing over `observed`,
because `ω` vanishes outside `observed`. -/
lemma sum_weight_univ (c : WeightedSupport R) :
    ∑ r, c.weight r = ∑ r ∈ c.observed, c.weight r := by
  classical
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro r _ hr
  exact c.weight_zero_off r hr

/-- Summing the weights over `observed` gives `1` (restated for convenience). -/
lemma sum_weight (c : WeightedSupport R) :
    ∑ r ∈ c.observed, c.weight r = 1 := c.weight_sum_one

/-- Summing the weights over `Finset.univ` gives `1`. -/
lemma sum_weight_univ_eq_one (c : WeightedSupport R) :
    ∑ r, c.weight r = 1 := by
  rw [c.sum_weight_univ, c.weight_sum_one]

end WeightedSupport

end Panel.Weighted
end Causalean
