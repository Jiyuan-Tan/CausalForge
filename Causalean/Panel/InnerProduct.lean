/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Weighted inner product on observed-cell arrays — thin re-export

For `c : Cells I T` (now an abbreviation for `WeightedSupport (I × T)`,
see `Causalean/Panel/Cells.lean`) and scalar arrays `A B : (I × T) → ℝ`, the
weighted inner product

    ⟨A, B⟩_ω  :=  ∑_{r ∈ R} ω_r · A_r · B_r

and its matrix-valued lift live entirely in
`Causalean/Panel/Weighted/InnerProduct.lean` (declarations `WeightedSupport.ip`,
`WeightedSupport.ipMat`, and their algebraic properties).  Because
`Cells I T` is defined as an `abbrev` of `WeightedSupport (I × T)`, all
dot-notation `c.ip A B`, `c.ipMat A B`, etc., resolves through the
abbreviation transparently — no shim is required here.

This file exists as the documentation anchor for the panel-level inner
product and to provide an import point for downstream panel files that
expect `Causalean.Panel.InnerProduct` to bring `ip`/`ipMat` into scope.

Mirrors Definition 2.1 of `CausalSmith/doc/general_projection_carryover_note.tex`.
-/

import Causalean.Panel.Cells
import Causalean.Panel.Weighted.InnerProduct

/-! # Panel Inner Products

This file provides the panel-facing import point for weighted inner products on
observed cell arrays. It restates the generic weighted-support inner-product
operations and algebraic lemmas under the panel cell namespace, including the
scalar aliases `Cells.ip`, `Cells.ip_eq_weighted`, the matrix-valued aliases
`Cells.ipMat`, `Cells.ipMat_eq_weighted`, and the symmetry, additivity,
homogeneity, nonnegativity, vanishing, and transpose lemmas used by panel
projection proofs. -/

namespace Causalean
namespace Panel
namespace Cells

variable {I T : Type*}
variable [Fintype I] [Fintype T] [DecidableEq I] [DecidableEq T]

-- Most scalar / matrix weighted-inner-product declarations live under
-- `Causalean.Panel.Weighted.WeightedSupport.*` and are inherited through the
-- `Cells := WeightedSupport (I × T)` abbreviation.

-- Name-level aliases under `Cells` for `unfold`-based proofs that
-- reference `Cells.ip` / `Cells.ipMat` by bare name (rather than
-- through dot-notation, which already resolves transparently).
--
-- These are defined with the same body as the `WeightedSupport`
-- counterparts so that `unfold ip` exposes the finset sum directly,
-- matching the behavior expected by the pre-refactor proof scripts.

/-- Bare-name alias for `c.ip`.  Defined with the explicit finset-sum body
(same as `WeightedSupport.ip`) so that `unfold ip` exposes the sum form
expected by the pre-refactor proof scripts.  Definitionally equal (by
`rfl`) to `Causalean.Panel.Weighted.WeightedSupport.ip`. -/
def ip (c : Cells I T) (A B : (I × T) → ℝ) : ℝ :=
  ∑ r ∈ c.observed, c.weight r * A r * B r

/-- `Cells.ip` is definitionally equal to `WeightedSupport.ip`. -/
lemma ip_eq_weighted (c : Cells I T) (A B : (I × T) → ℝ) :
    ip c A B = Causalean.Panel.Weighted.WeightedSupport.ip c A B := rfl

variable {K : ℕ}

/-- Bare-name alias for the matrix-valued panel inner product. Its `(j, k)`
entry is the scalar weighted inner product of the `j`th array in `A` with the
`k`th array in `B`. -/
def ipMat (c : Cells I T) (A B : Fin K → (I × T) → ℝ) :
    Matrix (Fin K) (Fin K) ℝ :=
  fun j k => c.ip (A j) (B k)

/-- `Cells.ipMat` is definitionally equal to `WeightedSupport.ipMat`. -/
lemma ipMat_eq_weighted (c : Cells I T) (A B : Fin K → (I × T) → ℝ) :
    ipMat c A B = Causalean.Panel.Weighted.WeightedSupport.ipMat c A B := rfl

/-! ### Panel-level wrappers of `WeightedSupport` inner-product lemmas

These restate the `WeightedSupport.*` algebraic lemmas under the `Cells.*`
namespace so that `rw [c.ip_add_right]`, `rw [c.ip_symm]`, etc., resolve to
panel-level lemmas whose statements use `Cells.ip` head-symbol (matching
the goals that arise from `c.ip` dot-notation on `Cells I T`). -/

/-- The panel weighted inner product unfolds to the weighted sum over observed
unit-period cells. -/
@[simp] lemma ip_def (c : Cells I T) (A B : (I × T) → ℝ) :
    c.ip A B = ∑ r ∈ c.observed, c.weight r * A r * B r := rfl

/-- The panel weighted inner product is symmetric in its two arrays. -/
lemma ip_symm (c : Cells I T) (A B : (I × T) → ℝ) :
    c.ip A B = c.ip B A :=
  Causalean.Panel.Weighted.WeightedSupport.ip_symm c A B

/-- The panel weighted inner product is additive in its left array. -/
lemma ip_add_left (c : Cells I T) (A A' B : (I × T) → ℝ) :
    c.ip (A + A') B = c.ip A B + c.ip A' B :=
  Causalean.Panel.Weighted.WeightedSupport.ip_add_left c A A' B

/-- The panel weighted inner product is additive in its right array. -/
lemma ip_add_right (c : Cells I T) (A B B' : (I × T) → ℝ) :
    c.ip A (B + B') = c.ip A B + c.ip A B' :=
  Causalean.Panel.Weighted.WeightedSupport.ip_add_right c A B B'

/-- The panel weighted inner product is homogeneous in its left array. -/
lemma ip_smul_left (c : Cells I T) (s : ℝ) (A B : (I × T) → ℝ) :
    c.ip (s • A) B = s * c.ip A B :=
  Causalean.Panel.Weighted.WeightedSupport.ip_smul_left c s A B

/-- The panel weighted inner product is homogeneous in its right array. -/
lemma ip_smul_right (c : Cells I T) (s : ℝ) (A B : (I × T) → ℝ) :
    c.ip A (s • B) = s * c.ip A B :=
  Causalean.Panel.Weighted.WeightedSupport.ip_smul_right c s A B

/-- The self inner product of any panel array is nonnegative. -/
lemma ip_self_nonneg (c : Cells I T) (A : (I × T) → ℝ) :
    0 ≤ c.ip A A :=
  Causalean.Panel.Weighted.WeightedSupport.ip_self_nonneg c A

/-- A panel array has zero self inner product exactly when it vanishes on all
observed cells. -/
lemma ip_self_eq_zero_iff (c : Cells I T) (A : (I × T) → ℝ) :
    c.ip A A = 0 ↔ ∀ r ∈ c.observed, A r = 0 :=
  Causalean.Panel.Weighted.WeightedSupport.ip_self_eq_zero_iff c A

/-- The matrix-valued panel inner product has entries equal to scalar inner
products of the corresponding array columns. -/
@[simp] lemma ipMat_apply (c : Cells I T) (A B : Fin K → (I × T) → ℝ)
    (j k : Fin K) :
    c.ipMat A B j k = c.ip (A j) (B k) := rfl

/-- Swapping the two tuples of arrays transposes the matrix-valued panel inner
product. -/
lemma ipMat_transpose (c : Cells I T) (A B : Fin K → (I × T) → ℝ) :
    (c.ipMat A B).transpose = c.ipMat B A :=
  Causalean.Panel.Weighted.WeightedSupport.ipMat_transpose c A B

/-- The matrix-valued panel inner product is additive in its left tuple of
arrays. -/
lemma ipMat_add_left (c : Cells I T) (A A' B : Fin K → (I × T) → ℝ) :
    c.ipMat (A + A') B = c.ipMat A B + c.ipMat A' B :=
  Causalean.Panel.Weighted.WeightedSupport.ipMat_add_left c A A' B

/-- The matrix-valued panel inner product is additive in its right tuple of
arrays. -/
lemma ipMat_add_right (c : Cells I T) (A B B' : Fin K → (I × T) → ℝ) :
    c.ipMat A (B + B') = c.ipMat A B + c.ipMat A B' :=
  Causalean.Panel.Weighted.WeightedSupport.ipMat_add_right c A B B'

/-- The matrix-valued panel inner product is homogeneous in its left tuple of
arrays. -/
lemma ipMat_smul_left (c : Cells I T) (s : ℝ) (A B : Fin K → (I × T) → ℝ) :
    c.ipMat (s • A) B = s • c.ipMat A B :=
  Causalean.Panel.Weighted.WeightedSupport.ipMat_smul_left c s A B

/-- The matrix-valued panel inner product is homogeneous in its right tuple of
arrays. -/
lemma ipMat_smul_right (c : Cells I T) (s : ℝ) (A B : Fin K → (I × T) → ℝ) :
    c.ipMat A (s • B) = s • c.ipMat A B :=
  Causalean.Panel.Weighted.WeightedSupport.ipMat_smul_right c s A B

end Cells
end Panel
end Causalean
