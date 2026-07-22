/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bias, mean squared error, and the bias–variance decomposition

For a design-based estimator `est : Ω → ℝ` of a fixed target `μ : ℝ` (a functional of
the finite population's potential-outcome table, hence design-independent), this file
records the two scalar summaries of estimation error under the randomization: the *bias*
`E[est] − μ` and the *mean squared error* `E[(est − μ)²]`.  The central fact is the
**bias–variance decomposition** `mse = Var + bias²`, the algebraic identity that makes the
mean squared error a function of the design alone once the estimator and target are fixed.
This `mse`-as-functional-of-the-design is the object that the design-comparison and
optimality layers minimize.
-/

import Causalean.Experimentation.DesignBased.DesignCore

/-! # Design-based risk summaries

Bias and mean squared error summarize fixed-target estimation error under a finite design.

The definitions `FiniteDesign.bias`, `FiniteDesign.mse`, and `FiniteDesign.Unbiased` describe
estimation error for a fixed target under a finite randomization design.  The central theorem
`FiniteDesign.mse_eq_var_add_bias_sq` proves the bias-variance decomposition, with supporting
lemmas for unbiased estimators, nonnegativity, the lower bound `FiniteDesign.var_le_mse`, and
congruence under pointwise-equal estimators.
-/

open scoped BigOperators

namespace Causalean
namespace Experimentation
namespace DesignBased

namespace FiniteDesign

variable {Ω : Type*} [Fintype Ω] (D : FiniteDesign Ω)

/-- Bias of an estimator `est` for the target `μ` under the design: `E[est] − μ`. -/
def bias (est : Ω → ℝ) (μ : ℝ) : ℝ := D.E est - μ

/-- Mean squared error of `est` for the target `μ` under the design: `E[(est − μ)²]`. -/
def mse (est : Ω → ℝ) (μ : ℝ) : ℝ := D.E (fun z => (est z - μ) ^ 2)

/-- An estimator is **unbiased** for `μ` under the design when its expectation equals `μ`. -/
def Unbiased (est : Ω → ℝ) (μ : ℝ) : Prop := D.E est = μ

/-- **Bias–variance decomposition.** The mean squared error is the variance plus the
squared bias: `mse = Var + bias²`. -/
lemma mse_eq_var_add_bias_sq (est : Ω → ℝ) (μ : ℝ) :
    D.mse est μ = D.Var est + (D.bias est μ) ^ 2 := by
  unfold mse bias
  rw [Var_eq]
  have h : (fun z => (est z - μ) ^ 2)
      = (fun z => (est z) ^ 2 + ((-(2 * μ)) * est z + μ ^ 2)) := by
    funext z; ring
  rw [h, E_add, E_add, E_const_mul, E_const]; ring

/-- For an unbiased estimator the mean squared error equals the variance. -/
lemma mse_eq_var_of_unbiased {est : Ω → ℝ} {μ : ℝ} (h : D.Unbiased est μ) :
    D.mse est μ = D.Var est := by
  rw [mse_eq_var_add_bias_sq]
  unfold bias Unbiased at *
  rw [h]; ring

/-- The bias of an unbiased estimator is zero. -/
@[simp] lemma bias_of_unbiased {est : Ω → ℝ} {μ : ℝ} (h : D.Unbiased est μ) :
    D.bias est μ = 0 := by
  unfold bias Unbiased at *; rw [h]; ring

/-- Mean squared error is nonnegative. -/
lemma mse_nonneg (est : Ω → ℝ) (μ : ℝ) : 0 ≤ D.mse est μ :=
  D.E_nonneg (fun _ => sq_nonneg _)

/-- Variance is nonnegative (it is the mean squared error of the centered estimator). -/
lemma Var_nonneg (X : Ω → ℝ) : 0 ≤ D.Var X := by
  have : D.Var X = D.mse X (D.E X) := by unfold mse Var; rfl
  rw [this]; exact D.mse_nonneg _ _

/-- Mean squared error is bounded below by the variance. -/
lemma var_le_mse (est : Ω → ℝ) (μ : ℝ) : D.Var est ≤ D.mse est μ := by
  rw [mse_eq_var_add_bias_sq]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Congruence: pointwise-equal estimators have equal mean squared error. -/
lemma mse_congr {est est' : Ω → ℝ} {μ : ℝ} (h : ∀ z, est z = est' z) :
    D.mse est μ = D.mse est' μ :=
  D.E_congr (fun z => by rw [h z])

end FiniteDesign

end DesignBased
end Experimentation
end Causalean
