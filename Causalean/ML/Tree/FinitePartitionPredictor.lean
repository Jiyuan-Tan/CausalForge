/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Core

/-! # Finite-partition predictors (regression trees)

A regression tree, abstracted to its essential structure: a finite set of cells, a
map sending each input to its cell, and a value per cell.  The predictor is
piecewise constant on the cells.  (CART greediness, splits, and bootstrap are out
of scope; this is the structural target a tree compiles to.)
-/

namespace Causalean.ML

/-- A piecewise-constant predictor on a finite partition: a finite `cell` type, a
cell-assignment map, and a value per cell. -/
structure FinitePartitionPredictor (X : Type*) where
  /-- The (finite) index type of partition cells. -/
  cell : Type
  /-- Finiteness of the cell index. -/
  [fintypeCell : Fintype cell]
  /-- The cell that an input falls into. -/
  chooseCell : X → cell
  /-- The constant predicted value on each cell. -/
  value : cell → ℝ

attribute [instance] FinitePartitionPredictor.fintypeCell

/-- The tree prediction: the value of the cell the input falls into. -/
def FinitePartitionPredictor.eval {X : Type*} (T : FinitePartitionPredictor X) (x : X) : ℝ :=
  T.value (T.chooseCell x)

/-- The tree is constant — equal to `value c` — on the cell `c`. -/
theorem FinitePartitionPredictor.eval_eqOn_cell {X : Type*}
    (T : FinitePartitionPredictor X) (c : T.cell) :
    Set.EqOn T.eval (fun _ => T.value c) {x | T.chooseCell x = c} := by
  intro x hx
  simp only [FinitePartitionPredictor.eval, Set.mem_setOf_eq] at hx ⊢
  rw [hx]

end Causalean.ML
