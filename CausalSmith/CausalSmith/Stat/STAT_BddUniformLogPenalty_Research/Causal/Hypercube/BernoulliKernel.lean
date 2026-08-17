import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Basic
import Causalean.Mathlib.Probability.BernoulliMeasure

/-!
# Pointwise Bernoulli kernels for the causal hard family

This module supplies the bounded selected conditional kernels used by the
potential-outcome angular construction.  Unlike the Gaussian-noise kernels in
the support-boundary family, these kernels obey every finite conditional
moment envelope uniformly in the exponent.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- The real-valued Bernoulli kernel with measurable success-probability
profile `p`. -/
-- @node: causalSelectedBernoulliKernel
noncomputable def causalSelectedBernoulliKernel
    (p : Score → ℝ) (hp : Measurable p) : Kernel Score ℝ where
  toFun x := Causalean.Mathlib.Probability.bernoulliLaw (p x)
  measurable' := by
    unfold Causalean.Mathlib.Probability.bernoulliLaw
    fun_prop

/-- A unit-range success-probability profile makes the selected Bernoulli
kernel Markov. -/
-- @node: causalSelectedBernoulliKernel_isMarkovKernel
lemma causalSelectedBernoulliKernel_isMarkovKernel
    (p : Score → ℝ) (hp : Measurable p)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1) :
    IsMarkovKernel (causalSelectedBernoulliKernel p hp) := by
  constructor
  intro x
  exact Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure
    (hp0 x) (hp1 x)

/-- The selected Bernoulli kernel has pointwise mean equal to its supplied
success-probability profile. -/
-- @node: causalSelectedBernoulliKernel_integral_id
lemma causalSelectedBernoulliKernel_integral_id
    (p : Score → ℝ) (hp : Measurable p)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1) (x : Score) :
    ∫ y, y ∂causalSelectedBernoulliKernel p hp x = p x := by
  change ∫ y, y ∂Causalean.Mathlib.Probability.bernoulliLaw (p x) = p x
  rw [Causalean.Mathlib.Probability.bernoulliLaw_integral
    (hp0 x) (hp1 x)]
  ring

/-- The selected Bernoulli kernel has pointwise variance `p(x)(1-p(x))`. -/
-- @node: causalSelectedBernoulliKernel_variance_id
lemma causalSelectedBernoulliKernel_variance_id
    (p : Score → ℝ) (hp : Measurable p)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1) (x : Score) :
    variance id (causalSelectedBernoulliKernel p hp x) = p x * (1 - p x) := by
  change variance id (Causalean.Mathlib.Probability.bernoulliLaw (p x)) = _
  letI : IsProbabilityMeasure (causalSelectedBernoulliKernel p hp x) :=
    Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure
      (hp0 x) (hp1 x)
  have hmean :
      ∫ y, id y ∂Causalean.Mathlib.Probability.bernoulliLaw (p x) = p x := by
    rw [Causalean.Mathlib.Probability.bernoulliLaw_integral
      (hp0 x) (hp1 x)]
    simp only [id_eq]
    ring
  rw [variance_eq_integral measurable_id.aemeasurable]
  rw [hmean]
  rw [Causalean.Mathlib.Probability.bernoulliLaw_integral
    (hp0 x) (hp1 x)]
  simp only [id_eq]
  ring

/-- Every pointwise absolute moment of order at least four equals the success
probability and is therefore at most one. -/
-- @node: causalSelectedBernoulliKernel_condAbsMoment_le_one
lemma causalSelectedBernoulliKernel_condAbsMoment_le_one
    (p : Score → ℝ) (hp : Measurable p)
    (hp1 : ∀ x, p x ≤ 1)
    {ν : ℝ} (hν : 2 ≤ ν) (x : Score) :
    (∫⁻ y, ENNReal.ofReal (|y| ^ (2 + ν))
        ∂causalSelectedBernoulliKernel p hp x) ≤ 1 := by
  change (∫⁻ y, ENNReal.ofReal (|y| ^ (2 + ν))
    ∂Causalean.Mathlib.Probability.bernoulliLaw (p x)) ≤ 1
  rw [Causalean.Mathlib.Probability.bernoulliLaw_lintegral_ofReal]
  have hexp : 2 + ν ≠ 0 := by linarith
  simp [hexp, hp1 x]

end CausalSmith.Stat.BddUniformLogPenalty
