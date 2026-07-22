/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bridge: a finite randomization design as a measure-theoretic probability measure

The lightweight `FiniteDesign` (a pmf `p` on a finite `Ω` with `E`/`Var`/`Cov` finite sums) is
turned into an honest `MeasureTheory.Measure`, `D.toMeasure := ∑_z (p z)·δ_z`, so that the
design-based estimators can be fed to the measure-theoretic Stein CLT.  We prove the dictionary

* `D.toMeasure` is a probability measure;
* `∫ g ∂D.toMeasure = D.E g`;
* `D.toMeasure.real {z | A z} = D.Pr A`;
* `variance g D.toMeasure = D.Var g`.

`Ω` carries the top σ-algebra (every set measurable), so every function is measurable.
-/

import Causalean.Experimentation.DesignBased.DesignCore
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Finite designs as probability measures

Finite randomization designs can be viewed as ordinary probability measures, enabling reuse of
measure-theoretic probability results.

For a design `D`, `FiniteDesign.toMeasure` places mass `D.p z` at each assignment `z`. The induced
measure is registered as an `IsProbabilityMeasure`, and the bridge theorems
`integral_toMeasure`, `toMeasure_real_setOf`, and `variance_toMeasure` identify integrals, event
probabilities, and variances under `D.toMeasure` with the finite-design operations `D.E`, `D.Pr`,
and `D.Var`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Causalean
namespace Experimentation
namespace DesignBased
namespace FiniteDesign

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (D : FiniteDesign Ω)

/-- The probability measure on `Ω` induced by the design: `∑_z (p z)·δ_z`. -/
noncomputable def toMeasure : Measure Ω := ∑ z, ENNReal.ofReal (D.p z) • Measure.dirac z

omit [MeasurableSingletonClass Ω] in
/-- `toMeasure` applied to any set is the design-weighted sum of dirac masses. -/
private lemma toMeasure_apply (s : Set Ω) :
    D.toMeasure s = ∑ z, ENNReal.ofReal (D.p z) * Measure.dirac z s := by
  rw [toMeasure, Measure.finset_sum_apply]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Measure.smul_apply, smul_eq_mul]

/-- The measure induced by a finite randomization design has total mass one. -/
instance : IsProbabilityMeasure D.toMeasure := by
  refine ⟨?_⟩
  rw [toMeasure_apply]
  have h : ∀ z ∈ (Finset.univ : Finset Ω),
      ENNReal.ofReal (D.p z) * Measure.dirac z Set.univ = ENNReal.ofReal (D.p z) := by
    intro z _; rw [Measure.dirac_apply' z MeasurableSet.univ]; simp
  rw [Finset.sum_congr rfl h, ← ENNReal.ofReal_sum_of_nonneg (fun z _ => D.p_nonneg z),
    D.p_sum, ENNReal.ofReal_one]

/-- The measure-theoretic integral against `toMeasure` is the design expectation. -/
theorem integral_toMeasure (g : Ω → ℝ) : ∫ x, g x ∂D.toMeasure = D.E g := by
  rw [toMeasure, integral_finset_sum_measure]
  · have h : ∀ z ∈ (Finset.univ : Finset Ω),
        ∫ x, g x ∂(ENNReal.ofReal (D.p z) • Measure.dirac z) = D.p z * g z := by
      intro z _
      rw [integral_smul_measure, integral_dirac, smul_eq_mul,
        ENNReal.toReal_ofReal (D.p_nonneg z)]
    rw [Finset.sum_congr rfl h]
    rfl
  · intro z _
    exact (integrable_dirac (by simp)).smul_measure (by simp)

/-- The measure of an event matches the design probability. -/
theorem toMeasure_real_setOf (A : Ω → Prop) [DecidablePred A] :
    D.toMeasure.real {z | A z} = D.Pr A := by
  rw [← integral_indicator_one (Set.toFinite {z | A z}).measurableSet,
    Pr, ← integral_toMeasure]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  unfold ind
  by_cases h : A z <;> simp [Set.indicator, h]

/-- The measure-theoretic variance against `toMeasure` is the design variance. -/
theorem variance_toMeasure (g : Ω → ℝ) : variance g D.toMeasure = D.Var g := by
  rw [variance_eq_integral (measurable_of_finite g).aemeasurable, integral_toMeasure,
    integral_toMeasure]
  rfl

end FiniteDesign
end DesignBased
end Experimentation
end Causalean
