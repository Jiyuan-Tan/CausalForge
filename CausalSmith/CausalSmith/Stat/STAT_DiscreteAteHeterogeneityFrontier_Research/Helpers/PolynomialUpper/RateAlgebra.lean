/- Deterministic completion-of-squares algebra for the polynomial upper rate. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.Calibration

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

-- @node: polynomial_linear_dimension_term_le_rate
/-- If [the sample is nonempty](hyp:hn) and [the logarithmic scale satisfies its stated
  bound](hyp:hL) and [the stated growth condition holds](hyp:hgrowth), [the first
  coefficient-growth term is absorbed by the parametric and quadratic-alphabet rates once its
  scalar logarithmic factor is at most the square-root sample scale](goal). -/
lemma polynomial_linear_dimension_term_le_rate
    {A n d L : ℝ} (hn : 0 < n) (hL : 0 < L)
    (hgrowth : A ^ 2 * L ^ 6 ≤ n) :
    A * d * L ^ 2 / n ^ 2 ≤
      1 / n + d ^ 2 / (n ^ 2 * L ^ 2) := by
  have hL0 : 0 ≤ L := hL.le
  have hAL : (A * L ^ 4) ^ 2 ≤ n * L ^ 2 := by
    calc
      (A * L ^ 4) ^ 2 = (A ^ 2 * L ^ 6) * L ^ 2 := by ring
      _ ≤ n * L ^ 2 := mul_le_mul_of_nonneg_right hgrowth (sq_nonneg L)
  have hyoung : A * d * L ^ 4 ≤ n * L ^ 2 + d ^ 2 := by
    have hsquare := sq_nonneg (A * L ^ 4 - d)
    nlinarith [mul_nonneg hn.le (sq_nonneg L)]
  have hden : 0 < n ^ 2 * L ^ 2 := mul_pos (sq_pos_of_pos hn) (sq_pos_of_pos hL)
  calc
    A * d * L ^ 2 / n ^ 2 = (A * d * L ^ 4) / (n ^ 2 * L ^ 2) := by
      field_simp [hn.ne', hL.ne']
    _ ≤ (n * L ^ 2 + d ^ 2) / (n ^ 2 * L ^ 2) :=
      (div_le_div_iff_of_pos_right hden).2 hyoung
    _ = 1 / n + d ^ 2 / (n ^ 2 * L ^ 2) := by
      field_simp [hn.ne', hL.ne']

-- @node: polynomial_quadratic_dimension_term_le_rate
/-- If [the sample is nonempty](hyp:hn) and [the logarithmic scale satisfies its stated
  bound](hyp:hL) and [the stated growth condition holds](hyp:hgrowth), [the second
  coefficient-growth term is absorbed directly by the quadratic-alphabet rate under the
  corresponding logarithmic growth bound](goal). -/
lemma polynomial_quadratic_dimension_term_le_rate
    {A n d L : ℝ} (hn : 0 < n) (hL : 0 < L)
    (hgrowth : A * L ^ 6 ≤ n) :
    A * d ^ 2 * L ^ 4 / n ^ 3 ≤ d ^ 2 / (n ^ 2 * L ^ 2) := by
  have hden : 0 < n ^ 3 * L ^ 2 := mul_pos (pow_pos hn 3) (sq_pos_of_pos hL)
  have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
  have hnum : A * d ^ 2 * L ^ 6 ≤ n * d ^ 2 := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right hgrowth hd2
  calc
    A * d ^ 2 * L ^ 4 / n ^ 3 =
        (A * d ^ 2 * L ^ 6) / (n ^ 3 * L ^ 2) := by
      field_simp [hn.ne', hL.ne']
    _ ≤ (n * d ^ 2) / (n ^ 3 * L ^ 2) :=
      (div_le_div_iff_of_pos_right hden).2 hnum
    _ = d ^ 2 / (n ^ 2 * L ^ 2) := by
      field_simp [hn.ne', hL.ne']

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
