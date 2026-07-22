/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Loss functions for the standalone ML module

This file collects the elementary pointwise loss functions used throughout
`Causalean.ML`: the squared loss for regression, and the sigmoid / softplus /
score-space logistic loss for binary classification.  Everything here is
causal-free real analysis; no probability or causal layer is imported.
-/

namespace Causalean.ML

/-- Squared loss measures prediction error by squaring the difference between the
observed label and the prediction. -/
def squaredLoss (ŷ y : ℝ) : ℝ := (y - ŷ) ^ 2

/-- Boolean labels are encoded as real zero-one outcomes. -/
def bool01 (b : Bool) : ℝ := if b then 1 else 0

/-- The logistic sigmoid maps any real score to a probability-like number between
zero and one. -/
noncomputable def sigmoid (t : ℝ) : ℝ := (1 + Real.exp (-t))⁻¹

/-- Softplus is a smooth positive transformation used to write logistic losses in
score space. -/
noncomputable def softplus (t : ℝ) : ℝ := Real.log (1 + Real.exp t)

/-- Logistic score loss is the binary cross-entropy loss written as a function of
the raw prediction score. -/
noncomputable def logisticScoreLoss (y : Bool) (t : ℝ) : ℝ :=
  softplus t - bool01 y * t

/-- A true Boolean label is encoded as one. -/
@[simp] lemma bool01_true : bool01 true = 1 := rfl

/-- A false Boolean label is encoded as zero. -/
@[simp] lemma bool01_false : bool01 false = 0 := rfl

/-- The zero-one encoding of a Boolean label is always nonnegative. -/
lemma bool01_nonneg (b : Bool) : 0 ≤ bool01 b := by
  cases b <;> simp [bool01]

/-- The zero-one encoding of a Boolean label is always at most one. -/
lemma bool01_le_one (b : Bool) : bool01 b ≤ 1 := by
  cases b <;> simp [bool01]

/-- Squared loss is always nonnegative. -/
lemma squaredLoss_nonneg (ŷ y : ℝ) : 0 ≤ squaredLoss ŷ y := sq_nonneg _

/-- The logistic sigmoid is strictly positive at every score. -/
lemma sigmoid_pos (t : ℝ) : 0 < sigmoid t := by
  have : 0 < 1 + Real.exp (-t) := by positivity
  exact inv_pos.mpr this

/-- The logistic sigmoid is strictly below one at every score. -/
lemma sigmoid_lt_one (t : ℝ) : sigmoid t < 1 := by
  have hpos : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  have h1 : (1 : ℝ) < 1 + Real.exp (-t) := by linarith
  calc sigmoid t = (1 + Real.exp (-t))⁻¹ := rfl
    _ < 1 := by
        rw [inv_lt_one_iff₀]
        right; exact h1

/-- Softplus is strictly positive at every score. -/
lemma softplus_pos (t : ℝ) : 0 < softplus t := by
  have hpos : (0 : ℝ) < Real.exp t := Real.exp_pos _
  have h1 : (1 : ℝ) < 1 + Real.exp t := by linarith
  exact Real.log_pos h1

end Causalean.ML
