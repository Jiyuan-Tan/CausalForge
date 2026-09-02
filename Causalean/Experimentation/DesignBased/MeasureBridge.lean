/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Descent from a finite design to its probability measure

`FiniteDesignMeasure` builds `D.toMeasure` and the forward dictionary
`∫ ∂D.toMeasure = D.E`, `variance _ D.toMeasure = D.Var`, `D.toMeasure.real {A} = D.Pr`.
This file packages the reverse direction: rewrites that push the lightweight design operations
`D.E` / `D.Var` / `D.Pr` back into their measure-theoretic counterparts, together with the
side-condition dischargers (`MemLp`, a.e.-strong-measurability) that are automatic on a finite
assignment space.  Together they let a measure-theoretic fact from `Causalean.Stat` or Mathlib be
pulled down to a design-based statement in a couple of `simp only [← …]` rewrites, instead of being
re-proved from the finite-sum definitions.
-/

import Causalean.Experimentation.DesignBased.FiniteDesignMeasure
import Causalean.Experimentation.DesignBased.Chebyshev
import Causalean.Mathlib.Probability.CovarianceCauchySchwarz

/-! # Descent bundle: design operations as measure-theoretic operations

For a finite design `D`, `FiniteDesign.E`, `FiniteDesign.Var`, and `FiniteDesign.Pr` are the design
expectation, variance, and event probability.  This file exposes them as the integral, variance, and
event measure of `D.toMeasure`, and proves that every statistic is `Lᵖ` under `D.toMeasure`
(`memLp_toMeasure`) and strongly measurable (`aestronglyMeasurable_toMeasure`).  These are the
obligations that gate the reuse of measure-theoretic inference results, so discharging them once
lets those results transfer to the design layer directly.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Causalean
namespace Experimentation
namespace DesignBased
namespace FiniteDesign

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (D : FiniteDesign Ω)

/-- On a finite assignment space every statistic is strongly measurable, because singletons — hence
all sets — are measurable. -/
@[fun_prop]
lemma aestronglyMeasurable_toMeasure {β : Type*} [MeasurableSpace β] [TopologicalSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] [SecondCountableTopology β]
    [OpensMeasurableSpace β] (g : Ω → β) :
    AEStronglyMeasurable g D.toMeasure :=
  (measurable_of_finite g).aestronglyMeasurable

/-- On a finite assignment space every statistic with a measurable codomain is a.e.-measurable
under the design measure. -/
@[fun_prop]
lemma aemeasurable_toMeasure {β : Type*} [MeasurableSpace β] (g : Ω → β) :
    AEMeasurable g D.toMeasure :=
  (measurable_of_finite g).aemeasurable

/-- Every normed-additive statistic with a suitable measurable second-countable codomain on a finite
assignment space is `Lᵖ` under the design measure: the space is finite so every statistic is
bounded, and the design measure is a probability measure, so every power is integrable. -/
lemma memLp_toMeasure {β : Type*} [NormedAddCommGroup β] [MeasurableSpace β]
    [SecondCountableTopology β] [OpensMeasurableSpace β] (g : Ω → β) (p : ℝ≥0∞) :
    MemLp g p D.toMeasure := by
  refine MemLp.of_bound (D.aestronglyMeasurable_toMeasure g) (∑ z, ‖g z‖) ?_
  filter_upwards with x
  exact Finset.single_le_sum (f := fun z => ‖g z‖) (fun z _ => norm_nonneg _)
    (Finset.mem_univ x)

/-- **Reverse rewrite.** The design expectation is the integral against the design measure. -/
lemma E_eq_integral (g : Ω → ℝ) : D.E g = ∫ x, g x ∂D.toMeasure :=
  (D.integral_toMeasure g).symm

/-- **Reverse rewrite.** The design variance is the measure-theoretic variance under the design
measure. -/
lemma Var_eq_variance (g : Ω → ℝ) : D.Var g = variance g D.toMeasure :=
  (D.variance_toMeasure g).symm

/-- **Reverse rewrite.** The design probability of an event is the real-valued measure of the event
under the design measure. -/
lemma Pr_eq_measureReal (A : Ω → Prop) [DecidablePred A] :
    D.Pr A = D.toMeasure.real {z | A z} :=
  (D.toMeasure_real_setOf A).symm

/-- **Reverse rewrite.** The design covariance is the measure-theoretic covariance under the design
measure. -/
lemma Cov_eq_covariance (X Y : Ω → ℝ) : D.Cov X Y = covariance X Y D.toMeasure := by
  rw [covariance, D.integral_toMeasure X, D.integral_toMeasure Y,
    D.integral_toMeasure (fun z => (X z - D.E X) * (Y z - D.E Y))]
  rfl

/-- **Cauchy–Schwarz for the design covariance.** In any finite design, [the absolute covariance of
two statistics `X` and `Y` is at most the product of their design standard deviations,
`|Cov(X,Y)| ≤ √(Var X) · √(Var Y)`](goal).

Obtained from the general covariance Cauchy–Schwarz inequality via the measure bridge; the design
side has no self-contained proof of it. -/
lemma abs_Cov_le (X Y : Ω → ℝ) :
    |D.Cov X Y| ≤ Real.sqrt (D.Var X) * Real.sqrt (D.Var Y) := by
  rw [D.Cov_eq_covariance X Y, D.Var_eq_variance X, D.Var_eq_variance Y]
  exact Causalean.Mathlib.abs_covariance_le_sqrt_mul (D.memLp_toMeasure X 2) (D.memLp_toMeasure Y 2)

end FiniteDesign
end DesignBased
end Experimentation
end Causalean
