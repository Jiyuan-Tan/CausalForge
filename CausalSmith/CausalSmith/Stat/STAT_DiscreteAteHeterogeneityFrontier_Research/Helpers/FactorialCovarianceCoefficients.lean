/- Paper-local coefficient envelopes for the marked factorial covariance sum. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.Estimators
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.ChebyshevCertificate

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open scoped BigOperators

-- @node: shiftedCoefficient_eq_gCoefficient
/-- [The signed coefficient in the real-outcome estimator is the same shifted Chebyshev
  coefficient used by the binary factorial construction](goal). -/
lemma shiftedCoefficient_eq_gCoefficient (K j : ℕ) :
    shiftedCoefficient K j =
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.gCoefficient K j := by
  simp [shiftedCoefficient,
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.gCoefficient]

-- @node: shiftedCoefficientEnvelope
/-- Absolute shifted-coefficient series evaluated at a nonnegative intensity. -/
noncomputable def shiftedCoefficientEnvelope (K : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (K - 1), |shiftedCoefficient K j| * x ^ j

-- @node: shiftedCoefficientEnvelope_eq_gpos
/-- [The marked-statistic coefficient envelope is the previously audited shifted-Chebyshev
  absolute series](goal). -/
lemma shiftedCoefficientEnvelope_eq_gpos (K : ℕ) (x : ℝ) :
    shiftedCoefficientEnvelope K x =
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.gpos K x := by
  unfold shiftedCoefficientEnvelope
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.gpos
  simp_rw [shiftedCoefficient_eq_gCoefficient]

-- @node: shiftedCoefficientEnvelope_le
/-- If [the polynomial or elbow parameter satisfies its stated bound](hyp:hK) and [the scalar
  satisfies the stated range condition](hyp:hx), [for nonnegative intensity, the absolute
  coefficient sum has the paper's `6^K max(1,x^(K-2))` envelope](goal). -/
lemma shiftedCoefficientEnvelope_le {K : ℕ} (hK : 0 < K) {x : ℝ}
    (hx : 0 ≤ x) :
    shiftedCoefficientEnvelope K x ≤
      (6 : ℝ) ^ K * max 1 (x ^ (K - 2)) := by
  rw [shiftedCoefficientEnvelope_eq_gpos]
  exact CausalSmith.Stat.DiscreteAteMinimaxLoggap.gpos_bound hK hx

-- @node: shiftedCoefficientEnvelope_le_six_pow
/-- If [the polynomial or elbow parameter satisfies its stated bound](hyp:hK) and [the scalar is
  nonnegative](hyp:hx0) and [the scalar is at most one](hyp:hx1), [on the unit intensity range,
  the absolute coefficient sum is at most `6^K`](goal). -/
lemma shiftedCoefficientEnvelope_le_six_pow {K : ℕ} (hK : 0 < K) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    shiftedCoefficientEnvelope K x ≤ (6 : ℝ) ^ K := by
  refine (shiftedCoefficientEnvelope_le hK hx0).trans ?_
  rw [max_eq_left]
  · simp
  · exact pow_le_one₀ hx0 hx1

-- @node: shiftedCoefficient_weighted_cellMass_sum_le
/-- If [the polynomial or elbow parameter satisfies its stated bound](hyp:hK) and [the outcome
  bound is positive](hyp:hB) and [the cell probability is nonnegative](hyp:hp0) and [the scaled
  cell probability satisfies the budget bound](hyp:hpB), [on a light cell, the
  coefficient-weighted factorial mean series is at most `B * 6^K`. This is the one-dimensional
  factor in the cross-cell sum](goal). -/
lemma shiftedCoefficient_weighted_cellMass_sum_le
    {K : ℕ} (hK : 0 < K) {B p : ℝ} (hB : 0 < B)
    (hp0 : 0 ≤ p) (hpB : p ≤ B / 4) :
    ∑ j ∈ Finset.range (K - 1),
        |shiftedCoefficient K j / B ^ (j + 1)| * p ^ (j + 2) ≤
      B * (6 : ℝ) ^ K := by
  have hB0 : 0 ≤ B := hB.le
  have hp_le_B : p ≤ B := by linarith
  have hratio0 : 0 ≤ p / B := div_nonneg hp0 hB0
  have hratio1 : p / B ≤ 1 := (div_le_one hB).2 hp_le_B
  have hrewrite :
      (∑ j ∈ Finset.range (K - 1),
          |shiftedCoefficient K j / B ^ (j + 1)| * p ^ (j + 2)) =
        (p ^ 2 / B) * shiftedCoefficientEnvelope K (p / B) := by
    unfold shiftedCoefficientEnvelope
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [abs_div, abs_pow, abs_of_pos hB]
    have hBne : B ≠ 0 := ne_of_gt hB
    rw [div_pow]
    field_simp
    ring
  rw [hrewrite]
  have henv := shiftedCoefficientEnvelope_le_six_pow hK hratio0 hratio1
  have hp2 : p ^ 2 / B ≤ B := by
    apply (div_le_iff₀ hB).2
    nlinarith
  exact (mul_le_mul_of_nonneg_left henv (div_nonneg (sq_nonneg p) hB0)).trans
    (mul_le_mul_of_nonneg_right hp2 (by positivity))

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
