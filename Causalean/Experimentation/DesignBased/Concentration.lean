/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bernstein concentration for a bounded design statistic

Chebyshev (`FiniteDesign.chebyshev`) controls a design statistic only polynomially.  For a *bounded*
statistic the tail is exponential, and this file records that sharper Bernstein bound for the
finite-design layer by descending to `D.toMeasure` and invoking the single-random-variable
sub-exponential machinery of `Causalean.Stat.Concentration`.  No independence is needed: a single
bounded, mean-zero statistic on the assignment space is sub-exponential under the design measure, so
its right tail — and, two-sidedly, its absolute deviation — decays like `exp(−ε²/·)`.
-/

import Causalean.Experimentation.DesignBased.MeasureBridge
import Causalean.Stat.Concentration.TailBounds.Bernstein

/-! # Bernstein concentration for a bounded design statistic

For a finite design `D` and a statistic `X` bounded by `c`, with design mean `0` and design
variance at most `σ²`, `bernstein_ge` gives the one-sided tail bound
`Pr[ε ≤ X] ≤ exp(−ε² / (2(2σ² + cε)))` and `bernstein_abs_ge` the two-sided bound
`Pr[ε ≤ |X|] ≤ 2·exp(−ε² / (2(2σ² + cε)))`.  These are exponentially sharper than the Chebyshev
bound `Var/ε²`, and are obtained from the measure-theoretic sub-exponential Chernoff bound through
the design-to-measure bridge.
-/

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration

namespace Causalean
namespace Experimentation
namespace DesignBased
namespace FiniteDesign

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (D : FiniteDesign Ω)

/-- A bounded, mean-zero statistic on a finite design is sub-exponential under the design measure,
with variance-proxy `2σ²` and scale `c`.  This is the finite-design instance of the Bernstein
sub-exponential lemma, obtained through the measure bridge. -/
lemma hasSubexponentialMGF_of_bounded (X : Ω → ℝ) {c σ : ℝ} (hc : 0 ≤ c) (hσ : 0 ≤ σ)
    (hmean : D.E X = 0) (hbound : ∀ z, |X z| ≤ c) (hvar : D.Var X ≤ σ ^ 2) :
    HasSubexponentialMGF X ⟨2 * σ ^ 2, by positivity⟩ ⟨c, hc⟩ D.toMeasure := by
  have hmean' : D.toMeasure[X] = 0 := (D.integral_toMeasure X).trans hmean
  have hvar' : D.toMeasure[fun ω => X ω ^ 2] ≤ σ ^ 2 := by
    rw [D.integral_toMeasure (fun z => X z ^ 2)]
    have : D.E (fun z => X z ^ 2) = D.Var X := by rw [D.Var_eq X, hmean]; ring
    rw [this]; exact hvar
  exact bounded_hasSubexponentialMGF hc hσ (D.aemeasurable_toMeasure X) hmean'
    (Filter.Eventually.of_forall hbound) hvar'

/-- **Bernstein tail for a bounded design statistic (one-sided).** If a statistic is bounded by `c`,
has design mean `0`, and has design variance at most `σ²`, then it exceeds a nonnegative threshold
`ε` with probability at most `exp(−ε² / (2(2σ² + cε)))`, far sharper than Chebyshev. -/
theorem bernstein_ge (X : Ω → ℝ) {c σ ε : ℝ} (hc : 0 ≤ c) (hσ : 0 ≤ σ)
    (hmean : D.E X = 0) (hbound : ∀ z, |X z| ≤ c) (hvar : D.Var X ≤ σ ^ 2) (hε : 0 ≤ ε) :
    D.Pr (fun z => ε ≤ X z) ≤ Real.exp (-ε ^ 2 / (2 * (2 * σ ^ 2 + c * ε))) := by
  have hsub := D.hasSubexponentialMGF_of_bounded X hc hσ hmean hbound hvar
  have h := hsub.measure_ge_le hε
  rw [D.toMeasure_real_setOf (fun z => ε ≤ X z)] at h
  simpa only [NNReal.coe_mk] using h

/-- **Bernstein tail for a bounded design statistic (two-sided).** Under the same hypotheses, the
absolute deviation exceeds `ε` with probability at most twice the one-sided bound. -/
theorem bernstein_abs_ge (X : Ω → ℝ) {c σ ε : ℝ} (hc : 0 ≤ c) (hσ : 0 ≤ σ)
    (hmean : D.E X = 0) (hbound : ∀ z, |X z| ≤ c) (hvar : D.Var X ≤ σ ^ 2) (hε : 0 ≤ ε) :
    D.Pr (fun z => ε ≤ |X z|) ≤ 2 * Real.exp (-ε ^ 2 / (2 * (2 * σ ^ 2 + c * ε))) := by
  have hvarneg : D.Var (fun z => -X z) = D.Var X := by
    have he : (fun z => -X z) = (fun z => (-1 : ℝ) * X z) := by funext z; ring
    rw [he, D.Var_const_mul]; ring
  have hsub := D.hasSubexponentialMGF_of_bounded X hc hσ hmean hbound hvar
  have hpos := D.hasSubexponentialMGF_of_bounded (fun z => -X z) hc hσ
    (by rw [D.E_neg, hmean, neg_zero]) (fun z => by simpa [abs_neg] using hbound z)
    (by rw [hvarneg]; exact hvar)
  have hup : D.toMeasure.real {ω | ε ≤ X ω - 0} ≤
      Real.exp (-ε ^ 2 / (2 * (2 * σ ^ 2 + c * ε))) := by
    simpa only [sub_zero, NNReal.coe_mk] using hsub.measure_ge_le hε
  have hlow : D.toMeasure.real {ω | ε ≤ -X ω + 0} ≤
      Real.exp (-ε ^ 2 / (2 * (2 * σ ^ 2 + c * ε))) := by
    simpa only [add_zero, NNReal.coe_mk] using hpos.measure_ge_le hε
  have h := measureReal_abs_dev_le_two_sided (μ := D.toMeasure) X 0
    (Real.exp (-ε ^ 2 / (2 * (2 * σ ^ 2 + c * ε)))) ε hup hlow
  rw [D.Pr_eq_measureReal (fun z => ε ≤ |X z|)]
  simpa only [sub_zero] using h

end FiniteDesign
end DesignBased
end Experimentation
end Causalean
