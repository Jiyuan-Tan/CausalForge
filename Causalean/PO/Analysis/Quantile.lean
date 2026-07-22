/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.PO.Core.Variable
import Causalean.Stat.Quantile.Quantile

/-! # Laws and Quantiles of Real Potential Outcomes

This file gives the distributional reading of a real-valued potential outcome:
its law under a measure on the sample space, the associated cumulative
distribution function, and the corresponding quantile.  The main definitions are
`POVar.cfLaw`, `POVar.cfCDF`, and `POVar.cfQuantile`, with the single-intervention
specializations `POVar.cfUnderLaw` and `POVar.cfUnderQuantile` for treatment
effects written as `Y(d)`.  The lemma `POVar.cfCDF_eq_measureReal` records the
probability interpretation of the counterfactual cdf. -/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POVar

variable {P : POSystem} (a : POVar P ℝ)

/-- For a real-valued potential-outcome variable, an intervention regime, and a
measure on the sample space, this is the distribution of the variable's
potential outcome under the regime, obtained by pushing that measure forward
through the counterfactual-value function.

Law of the counterfactual outcome `a(r)`: the pushforward of `μ` under
`a.cf r`. -/
noncomputable def cfLaw (r : Regime P.V P.X) (μ : Measure P.Ω) : Measure ℝ :=
  μ.map (a.cf r)

/-- The law of a real-valued potential outcome is a probability measure
whenever the original sample-space measure is a probability measure. -/
instance instIsProbabilityMeasureCfLaw (r : Regime P.V P.X) (μ : Measure P.Ω)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (a.cfLaw r μ) :=
  Measure.isProbabilityMeasure_map (a.measurable_cf r).aemeasurable

/-- For a real-valued potential-outcome variable, an intervention regime, and a
measure on the sample space, this is the cumulative distribution function of
the variable's potential outcome under that regime with respect to that measure.

The distributional potential outcome: cdf of the law of `a(r)`,
`F_{a(r)}(y) = P(a(r) ≤ y)`. -/
noncomputable def cfCDF (r : Regime P.V P.X) (μ : Measure P.Ω) : StieltjesFunction ℝ :=
  cdf (a.cfLaw r μ)

/-- For a real-valued potential-outcome variable, an intervention regime, a
measure on the sample space, and a real index $\tau$, this is the $\tau$-quantile
of the variable's potential outcome under that regime with respect to that
measure.

The `τ`-quantile of the potential outcome `a(r)`: `F_{a(r)}^{-1}(τ)`. -/
noncomputable def cfQuantile (r : Regime P.V P.X) (μ : Measure P.Ω) (τ : ℝ) : ℝ :=
  Causalean.Stat.quantile (a.cfLaw r μ) τ

/-- The cdf of `a(r)` evaluated at `y` is `μ`-probability that `a(r) ≤ y`. -/
lemma cfCDF_eq_measureReal (r : Regime P.V P.X) (μ : Measure P.Ω)
    [IsProbabilityMeasure μ] (y : ℝ) :
    a.cfCDF r μ y = (a.cfLaw r μ).real (Set.Iic y) :=
  cdf_eq_real (a.cfLaw r μ) y

/-! ### Single-node specialisations (binary-treatment `Y(d)` shape) -/

variable {β : Type*} [MeasurableSpace β]

/-- For a real-valued potential-outcome variable, another potential-outcome
variable, a value of the second variable, and a measure on the sample space,
this is the distribution of the first variable's potential outcome under the
single-variable intervention that sets the second variable to that value.

Law of the single-intervention counterfactual `a` under `{w ← y}`. -/
noncomputable def cfUnderLaw (w : POVar P β) (y : β) (μ : Measure P.Ω) : Measure ℝ :=
  a.cfLaw (Regime.single w.v (w.equiv.symm y)) μ

/-- For a real-valued potential-outcome variable, another potential-outcome
variable, a value of the second variable, a measure on the sample space, and a
real index $\tau$, this is the $\tau$-quantile of the first variable's potential
outcome under the single-variable intervention that sets the second variable to
that value.

The `τ`-quantile of `a` under the single intervention `{w ← y}`; this is the
`τ`-quantile of `Y(d)` when `a := Y`, `w := D`, `y := d`. -/
noncomputable def cfUnderQuantile (w : POVar P β) (y : β) (μ : Measure P.Ω) (τ : ℝ) : ℝ :=
  a.cfQuantile (Regime.single w.v (w.equiv.symm y)) μ τ

/-- The single-intervention quantile is exactly the quantile computed from the
corresponding single-intervention law. -/
lemma cfUnderQuantile_eq (w : POVar P β) (y : β) (μ : Measure P.Ω) (τ : ℝ) :
    a.cfUnderQuantile w y μ τ
      = Causalean.Stat.quantile (a.cfUnderLaw w y μ) τ := rfl

end POVar

end PO
end Causalean
