import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Basic
import Causalean.Mathlib.IndepIntegral
import Causalean.Stat.SampleSplit.OneShot

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory ProbabilityTheory

variable {Ω X B C : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace B] [MeasurableSpace C]
  {μ : Measure Ω} {P : Measure X}

/-- Any measurable pilot statistic is independent of any measurable estimation-fold
statistic.  This is the reusable conditioning interface for freezing the pilot-selected
light-cell set before applying factorial-moment bounds on the estimation fold. -/
lemma oneShot_statistics_indep
    {S : Causalean.Stat.IIDSample Ω X μ P} (split : Causalean.Stat.OneShotSplit S)
    (n : ℕ) (pilot : (split.foldA n → X) → B)
    (estimate : (split.foldB n → X) → C)
    (hpilot : Measurable pilot) (hestimate : Measurable estimate) :
    IndepFun
      (fun ω => pilot (fun i : split.foldA n => S.Z i ω))
      (fun ω => estimate (fun i : split.foldB n => S.Z i ω)) μ := by
  simpa only [Function.comp_apply] using
    (split.folds_indep n).comp hpilot hestimate

/-- Integral factorization after the pilot/estimation split. -/
lemma oneShot_integral_mul_factorization
    {S : Causalean.Stat.IIDSample Ω X μ P} (split : Causalean.Stat.OneShotSplit S)
    (n : ℕ) (pilot : (split.foldA n → X) → ℝ)
    (estimate : (split.foldB n → X) → ℝ)
    (hpilot : Measurable pilot) (hestimate : Measurable estimate) :
    ∫ ω, pilot (fun i : split.foldA n => S.Z i ω) *
        estimate (fun i : split.foldB n => S.Z i ω) ∂μ =
      (∫ ω, pilot (fun i : split.foldA n => S.Z i ω) ∂μ) *
        ∫ ω, estimate (fun i : split.foldB n => S.Z i ω) ∂μ := by
  have hpTuple : Measurable (fun ω => fun i : split.foldA n => S.Z i ω) :=
    measurable_pi_lambda _ (fun i : split.foldA n => S.meas i)
  have heTuple : Measurable (fun ω => fun i : split.foldB n => S.Z i ω) :=
    measurable_pi_lambda _ (fun i : split.foldB n => S.meas i)
  have hind := oneShot_statistics_indep split n pilot estimate hpilot hestimate
  exact hind.integral_fun_mul_eq_mul_integral
    (hpilot.comp hpTuple).aestronglyMeasurable
    (hestimate.comp heTuple).aestronglyMeasurable

/-- Conditioning on a measurable pilot event does not alter an estimation-fold
integral, except for multiplication by the pilot-event probability. -/
lemma oneShot_integral_estimate_restrict_pilot
    {S : Causalean.Stat.IIDSample Ω X μ P} (split : Causalean.Stat.OneShotSplit S)
    (n : ℕ) (pilot : (split.foldA n → X) → B)
    (estimate : (split.foldB n → X) → ℝ)
    (hpilot : Measurable pilot) (hestimate : Measurable estimate)
    (E : Set B) (hE : MeasurableSet E) :
    ∫ ω in (fun ω => pilot (fun i : split.foldA n => S.Z i ω)) ⁻¹' E,
        estimate (fun i : split.foldB n => S.Z i ω) ∂μ =
      (μ ((fun ω => pilot (fun i : split.foldA n => S.Z i ω)) ⁻¹' E)).toReal *
        ∫ ω, estimate (fun i : split.foldB n => S.Z i ω) ∂μ := by
  have hpTuple : Measurable (fun ω => fun i : split.foldA n => S.Z i ω) :=
    measurable_pi_lambda _ (fun i : split.foldA n => S.meas i)
  have heTuple : Measurable (fun ω => fun i : split.foldB n => S.Z i ω) :=
    measurable_pi_lambda _ (fun i : split.foldB n => S.meas i)
  have hind := oneShot_statistics_indep split n pilot estimate hpilot hestimate
  exact hind.integral_restrict_preimage_eq_mul (hpilot.comp hpTuple)
    (hestimate.comp heTuple) hE measurable_id

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
