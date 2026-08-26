import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmDepoissonization
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Analysis.Complex.ExponentialBounds

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal MeasureTheory

/-- A larger Poisson mean has a smaller lower-tail probability. -/
lemma poissonMeasure_lowerTail_antitone {lam mu : ℝ≥0} (h : lam ≤ mu) (n : ℕ) :
    poissonMeasure mu {k | k < n} ≤ poissonMeasure lam {k | k < n} := by
  have hsum : lam + (mu - lam) = mu := by
    rw [add_comm, tsub_add_cancel_of_le h]
  rw [← hsum, ← poissonMeasure_conv_poissonMeasure]
  have hset : MeasurableSet ({k : ℕ | k < n}) := measurableSet_Iio
  rw [Measure.conv, Measure.map_apply (by fun_prop) hset]
  calc
    (poissonMeasure lam).prod (poissonMeasure (mu - lam))
        ((fun z : ℕ × ℕ => z.1 + z.2) ⁻¹' {k | k < n}) ≤
        (poissonMeasure lam).prod (poissonMeasure (mu - lam))
          ({k | k < n} ×ˢ Set.univ) := by
      apply measure_mono
      intro z hz
      change z.1 + z.2 < n at hz
      change z.1 < n ∧ z.2 ∈ Set.univ
      exact ⟨by omega, Set.mem_univ z.2⟩
    _ = poissonMeasure lam {k | k < n} *
        poissonMeasure (mu - lam) Set.univ := by
      rw [Measure.prod_prod]
    _ = poissonMeasure lam {k | k < n} := by simp

/-- The explicit `2n` lower-tail bound also applies to every larger mean. -/
lemma poisson_lower_tail_le_two_n_bound {lam : ℝ≥0} (n : ℕ)
    (h : 2 * n ≤ lam) :
    poissonMeasure lam {k | k < n} ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) * (1 - Real.log 2))) := by
  exact (poissonMeasure_lowerTail_antitone h n).trans
    (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.poisson_two_n_lower_tail n)

/-- A coarse polynomial form of the same tail bound, convenient for the final
scalar D.2 accounting. -/
lemma poisson_lower_tail_le_inv_sq {lam : ℝ≥0} {n : ℕ}
    (hn : 400 ≤ n) (h : 2 * n ≤ lam) :
    poissonMeasure lam {k | k < n} ≤
      ENNReal.ofReal ((n : ℝ)⁻¹ ^ 2) := by
  refine (poisson_lower_tail_le_two_n_bound n h).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hn0 : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by omega)
  have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hn0.le
  have hsqrt20 : 20 ≤ Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 20)]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hlog : Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    calc
      Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
        Real.log_le_rpow_div hn0.le (by norm_num)
      _ = 2 * Real.sqrt (n : ℝ) := by
        rw [← Real.sqrt_eq_rpow]
        ring
  have hc : (3 / 10 : ℝ) < 1 - Real.log 2 := by
    nlinarith [Real.log_two_lt_d9]
  have hbudget : 2 * Real.log (n : ℝ) ≤
      (n : ℝ) * (1 - Real.log 2) := by
    nlinarith
  calc
    Real.exp (-(n : ℝ) * (1 - Real.log 2)) ≤
        Real.exp (-2 * Real.log (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = (n : ℝ)⁻¹ ^ 2 := by
      rw [show -2 * Real.log (n : ℝ) =
          -(Real.log (n : ℝ)) + -(Real.log (n : ℝ)) by ring,
        Real.exp_add, Real.exp_neg, Real.exp_log hn0]
      ring

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
