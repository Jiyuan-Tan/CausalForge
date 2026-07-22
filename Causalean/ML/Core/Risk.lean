/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Core.Hypothesis
import Causalean.Stat.Sample
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Empirical and population risk

Risk criteria for the ML spine, in both the parametric and extensional views.
`Loss` is a pointwise prediction-label loss, `empiricalRisk` and
`empiricalRiskP` are nonempty finite-sample averages, `populationRisk` and
`populationRiskP` are Bochner-integral population criteria, and
`iidEmpiricalRisk` expresses empirical risk through `Stat.IIDSample.sampleMean`.
The separate predicate `HasFinitePopulationRisk` records when the population
integral has the usual finite expected-loss interpretation.
-/

namespace Causalean.ML

open MeasureTheory

/-- A pointwise loss: `loss ŷ y` compares a prediction `ŷ` to a label `y`. -/
abbrev Loss (Y : Type*) := Y → Y → ℝ

/-- The empirical risk criterion of a prediction rule is the sample loss sum
scaled by the inverse cardinality of a nonempty finite sample index.  The
nonemptiness assumption rules out the empty-sample convention where the average
would collapse to zero without data. -/
noncomputable def empiricalRisk {ι X Y : Type*} [Fintype ι] [Nonempty ι]
    (loss : Loss Y) (S : ι → X × Y) (h : X → Y) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, loss (h (S i).1) (S i).2

/-- The empirical risk criterion of a model parameter is the finite-sample
criterion over a nonempty sample applied to the prediction rule selected by that
parameter. -/
noncomputable def empiricalRiskP {ι Θ X Y : Type*} [Fintype ι] [Nonempty ι]
    (M : Predictor Θ X Y) (loss : Loss Y) (S : ι → X × Y) (θ : Θ) : ℝ :=
  empiricalRisk loss S (M.predict θ)

/-- The population risk criterion of a prediction rule is the Bochner integral
of its pointwise loss under the joint law.  This definition does not by itself
assert integrability or finite expected loss. -/
noncomputable def populationRisk {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (loss : Loss Y) (P : Measure (X × Y)) (h : X → Y) : ℝ :=
  ∫ z, loss (h z.1) z.2 ∂P

/-- The population risk criterion of a model parameter is the Bochner-integral
criterion applied to the prediction rule selected by that parameter. -/
noncomputable def populationRiskP {Θ X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (M : Predictor Θ X Y) (loss : Loss Y) (P : Measure (X × Y)) (θ : Θ) : ℝ :=
  populationRisk loss P (M.predict θ)

/-- The empirical risk along the first `n` points of an i.i.d. sample, expressed
through `Stat.IIDSample.sampleMean`. -/
noncomputable def iidEmpiricalRisk {Ω X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace (X × Y)]
    {μ : Measure Ω} {P : Measure (X × Y)}
    (S : Causalean.Stat.IIDSample Ω (X × Y) μ P)
    (loss : Loss Y) (h : X → Y) (n : ℕ) : Ω → ℝ :=
  S.sampleMean (fun z => loss (h z.1) z.2) n

/-- The loss-integrand of `h` is integrable, so the population risk is finite. -/
def HasFinitePopulationRisk {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (loss : Loss Y) (P : Measure (X × Y)) (h : X → Y) : Prop :=
  Integrable (fun z => loss (h z.1) z.2) P

end Causalean.ML
