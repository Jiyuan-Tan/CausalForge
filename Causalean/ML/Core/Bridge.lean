/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Core.ERM

/-! # Bridge between the parametric and extensional views

The image of a `Predictor` under its prediction map is a `HypothesisClass`, and a
*parametric* minimizer pushes forward to an *extensional* minimizer over that
image class.  These two lemmas are the only glue between the two views of a
method: properties stated in parameter space (convexity, regularization,
optimization) transfer to the function-class statements (best-in-class,
population target).
-/

namespace Causalean.ML

open MeasureTheory

/-- The hypothesis class realized by a predictor: the image of its admissible
parameter set under the prediction map. -/
def imageClass {Θ X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (M : Predictor Θ X Y)
    (hmeas : ∀ θ ∈ M.paramSet, Measurable (M.predict θ)) : HypothesisClass X Y where
  carrier := (fun θ => M.predict θ) '' M.paramSet
  measurable := by
    rintro h ⟨θ, hθ, rfl⟩
    exact hmeas θ hθ

/-- A parametric empirical-risk minimizer pushes forward to an extensional
empirical-risk minimizer over the realized hypothesis class. -/
theorem isERMP_to_extensional {ι Θ X Y : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace X] [MeasurableSpace Y]
    (M : Predictor Θ X Y) (loss : Loss Y) (S : ι → X × Y)
    (hmeas : ∀ θ ∈ M.paramSet, Measurable (M.predict θ)) {θhat : Θ}
    (h : IsERMP (empiricalRiskP M loss S) M.paramSet θhat) :
    IsERM (imageClass M hmeas) loss S (M.predict θhat) where
  mem := ⟨θhat, h.mem, rfl⟩
  isMin := by
    rw [isMinOn_iff]
    rintro g ⟨θ, hθ, rfl⟩
    simpa [empiricalRiskP] using (isMinOn_iff.mp h.isMin) θ hθ

/-- A parametric population-risk minimizer pushes forward to an extensional
population-risk minimizer over the realized hypothesis class. -/
theorem populationTarget_pushforward {Θ X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (M : Predictor Θ X Y) (loss : Loss Y) (P : Measure (X × Y))
    (hmeas : ∀ θ ∈ M.paramSet, Measurable (M.predict θ)) {θhat : Θ}
    (hmem : θhat ∈ M.paramSet)
    (hfinite : ∀ θ ∈ M.paramSet, HasFinitePopulationRisk loss P (M.predict θ))
    (h : IsMinOn (fun θ => populationRiskP M loss P θ) M.paramSet θhat) :
    IsPopulationRiskMinimizer (imageClass M hmeas) loss P (M.predict θhat) where
  mem := ⟨θhat, hmem, rfl⟩
  finite_self := hfinite θhat hmem
  finite_competitor := by
    rintro g ⟨θ, hθ, rfl⟩
    exact hfinite θ hθ
  isMin := by
    rw [isMinOn_iff]
    rintro g ⟨θ, hθ, rfl⟩
    simpa [populationRiskP] using (isMinOn_iff.mp h) θ hθ

end Causalean.ML
