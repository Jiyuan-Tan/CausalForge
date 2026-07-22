/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Tree.FinitePartitionPredictor

/-! # Random forests

This file models a random forest as a fixed-size finite ensemble of
`FinitePartitionPredictor`s over an input type `X`.  The public API consists of
`RandomForest`, which stores one tree for each index in `Fin T`, and
`RandomForest.eval`, the uniform average of the tree predictions.

The main structural theorem, `RandomForest.eval_mem_Icc`, states that a nonempty
forest preserves pointwise interval bounds: if every tree prediction lies in
`[a, b]` at every input, then the averaged forest prediction also lies in
`[a, b]`.
-/

namespace Causalean.ML

open BigOperators

/-- A random forest with one finite-partition regression tree for each index in `Fin T`. -/
structure RandomForest (X : Type*) (T : ℕ) where
  /-- The ensemble of trees. -/
  tree : Fin T → FinitePartitionPredictor X

/-- The forest prediction: the average of the tree predictions. -/
noncomputable def RandomForest.eval {X : Type*} {T : ℕ} (F : RandomForest X T) (x : X) : ℝ :=
  (T : ℝ)⁻¹ * ∑ t : Fin T, (F.tree t).eval x

/-- If every tree in a nonempty forest predicts within `[a, b]`, then the forest
average also predicts within `[a, b]`. -/
theorem RandomForest.eval_mem_Icc {X : Type*} {T : ℕ} (F : RandomForest X T) (hT : 0 < T)
    {a b : ℝ} (hb : ∀ (t : Fin T) (x : X), (F.tree t).eval x ∈ Set.Icc a b) (x : X) :
    F.eval x ∈ Set.Icc a b := by
  rw [Set.mem_Icc]
  have hTpos : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
  have hsum_lower : (T : ℝ) * a ≤ ∑ t : Fin T, (F.tree t).eval x := by
    calc
      (T : ℝ) * a = ∑ _t : Fin T, a := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ t : Fin T, (F.tree t).eval x := by
        exact Finset.sum_le_sum (fun t _ => (Set.mem_Icc.mp (hb t x)).1)
  have hsum_upper : ∑ t : Fin T, (F.tree t).eval x ≤ (T : ℝ) * b := by
    calc
      ∑ t : Fin T, (F.tree t).eval x ≤ ∑ _t : Fin T, b := by
        exact Finset.sum_le_sum (fun t _ => (Set.mem_Icc.mp (hb t x)).2)
      _ = (T : ℝ) * b := by
        simp [Finset.sum_const, nsmul_eq_mul]
  constructor
  · have hscale :=
      mul_le_mul_of_nonneg_left hsum_lower (inv_nonneg.mpr (le_of_lt hTpos))
    calc
      a = (T : ℝ)⁻¹ * ((T : ℝ) * a) := by
        field_simp [hTne]
      _ ≤ F.eval x := by
        simpa [RandomForest.eval] using hscale
  · have hscale :=
      mul_le_mul_of_nonneg_left hsum_upper (inv_nonneg.mpr (le_of_lt hTpos))
    calc
      F.eval x ≤ (T : ℝ)⁻¹ * ((T : ℝ) * b) := by
        simpa [RandomForest.eval] using hscale
      _ = b := by
        field_simp [hTne]

end Causalean.ML
