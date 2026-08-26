/- Endpoint and shrinking-radius rate algebra. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.T_TwoSidedMinimaxBracket

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open Filter MeasureTheory Set

/-- The parametric-plus-exact-homogeneity benchmark `b`. -/
noncomputable def baseRate (n d : ℕ) : ℝ :=
  1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2

-- @node: logEN_sq_le_nine_mul
/-- If [the sample is nonempty](hyp:hn), [the squared logarithmic scale is bounded by nine times
  the sample size](goal). -/
lemma logEN_sq_le_nine_mul (n : ℕ) (hn : 0 < n) :
    logEN n ^ 2 ≤ 9 * (n : ℝ) := by
  have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn_one : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    calc
      Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
        Real.log_le_rpow_div (le_of_lt hn_real) (by norm_num)
      _ = 2 * Real.sqrt (n : ℝ) := by
        rw [← Real.sqrt_eq_rpow]
        ring
  have hsqrt_one : 1 ≤ Real.sqrt (n : ℝ) := by
    simpa using Real.sqrt_le_sqrt hn_one
  have hsqrt_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (le_of_lt hn_real)
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn_one
  rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hn_real.ne', Real.log_exp]
  nlinarith

set_option maxHeartbeats 800000 in
-- The explicit eight-way endpoint comparison requires several nonlinear normalizations.
-- @node: prop:endpoint-reductions-all-d
/-- [At radii zero and two, the all-alphabet upper and lower rate expressions are uniformly
  comparable, radius two gives the unrestricted model class, and the radius-two frontier is
  exactly the unrestricted endpoint formula](goal). -/
theorem endpoint_reductions_all_d :
    (∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ n d : ℕ, 0 < n → 0 < d →
        c * (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)) ≤
          frontierRate n d 0 ∧
        frontierRate n d 0 ≤
          C * (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)) ∧
        c * (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)) ≤
          converseRate n d 0 ∧
        converseRate n d 0 ≤
          C * (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2)) ∧
        c * (1 / (n : ℝ) + min 1 (polynomialComponent n d)) ≤
          frontierRate n d 2 ∧
        frontierRate n d 2 ≤
          C * (1 / (n : ℝ) + min 1 (polynomialComponent n d)) ∧
        c * (1 / (n : ℝ) + min 1 (polynomialComponent n d)) ≤
          converseRate n d 2 ∧
        converseRate n d 2 ≤
          C * (1 / (n : ℝ) + min 1 (polynomialComponent n d))) ∧
    (∀ d : ℕ, ∀ epsilon M : ℝ,
      (∀ P : UnrestrictedClass d epsilon M,
        ∃ Q : ModelClass d epsilon M 2, Q.law = P.law) ∧
      (∀ Q : ModelClass d epsilon M 2,
        ∃ P : UnrestrictedClass d epsilon M, P.law = Q.law)) ∧
    (∀ n d : ℕ, 0 < n → 0 < d →
      frontierRate n d 2 = 1 / (n : ℝ) + min 1 (polynomialComponent n d)) := by
  have hfront_two : ∀ n d : ℕ, 0 < n → 0 < d →
      frontierRate n d 2 = 1 / (n : ℝ) + min 1 (polynomialComponent n d) := by
    intro n d hn hd
    have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
    have hd_real : 0 < (d : ℝ) := by exact_mod_cast hd
    have hn_sq : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hn_real
    have ht : 0 ≤ (d : ℝ) / (n : ℝ) ^ 2 :=
      div_nonneg (le_of_lt hd_real) (le_of_lt hn_sq)
    have hcollision_two : 1 ≤ collisionComponent n d 2 := by
      unfold collisionComponent
      nlinarith
    unfold frontierRate
    rw [← min_assoc, min_eq_left (le_trans (min_le_left _ _) hcollision_two)]
  refine ⟨⟨1 / 10, 10, by norm_num, by norm_num, ?_⟩,
    fun d epsilon M => (scale_sanity (d := d) (epsilon := epsilon) (M := M)).2,
    hfront_two⟩
  intro n d hn hd
  have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
  have hd_real : 0 < (d : ℝ) := by exact_mod_cast hd
  have hn_sq : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hn_real
  have hlog_one : 1 ≤ logEN n := by
    rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hn_real.ne', Real.log_exp]
    exact le_add_of_nonneg_right (Real.log_nonneg (by exact_mod_cast hn))
  have hlog_sq : 0 < logEN n ^ 2 := sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hlog_one)
  have ht : 0 ≤ (d : ℝ) / (n : ℝ) ^ 2 := div_nonneg (le_of_lt hd_real) (le_of_lt hn_sq)
  have hu : 0 ≤ polynomialComponent n d := by
    unfold polynomialComponent
    positivity
  have hfront_zero_upper :
      frontierRate n d 0 ≤
        1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2) := by
    unfold frontierRate collisionComponent
    gcongr
    simpa using min_le_right (polynomialComponent n d)
      ((d : ℝ) / (n : ℝ) ^ 2)
  have hconverse_zero : converseRate n d 0 =
      1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2) := by
    simp [converseRate]
  have hfront_two := hfront_two n d hn hd
  have htarget_zero_nonneg :
      0 ≤ 1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2) := by positivity
  have htarget_two_nonneg :
      0 ≤ 1 / (n : ℝ) + min 1 (polynomialComponent n d) := by positivity
  have hone_over_nonneg : 0 ≤ 1 / (n : ℝ) := by positivity
  by_cases hlarge : logEN n ^ 2 ≤ (d : ℝ)
  · have htu : (d : ℝ) / (n : ℝ) ^ 2 ≤ polynomialComponent n d := by
      unfold polynomialComponent
      rw [div_le_div_iff₀ hn_sq (mul_pos hn_sq hlog_sq)]
      have hmul := mul_le_mul_of_nonneg_left hlarge
        (mul_nonneg (le_of_lt hd_real) (le_of_lt hn_sq))
      nlinarith
    have hfront_zero : frontierRate n d 0 =
        1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2) := by
      unfold frontierRate collisionComponent
      have hz : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [hz, zero_add]
      change 1 / (n : ℝ) +
        min 1 (min (polynomialComponent n d) ((d : ℝ) / (n : ℝ) ^ 2)) = _
      rw [min_eq_right htu]
    have htmin_le_u : min 1 ((d : ℝ) / (n : ℝ) ^ 2) ≤
        min 1 (polynomialComponent n d) := min_le_min_left 1 htu
    have hconv_two_lower :
        1 / (n : ℝ) + min 1 (polynomialComponent n d) ≤ converseRate n d 2 := by
      unfold converseRate
      nlinarith [le_min zero_le_one ht, le_min zero_le_one hu]
    have hconv_two_upper : converseRate n d 2 ≤
        5 * (1 / (n : ℝ) + min 1 (polynomialComponent n d)) := by
      unfold converseRate
      nlinarith [htmin_le_u, le_min zero_le_one hu]
    rw [hfront_zero, hconverse_zero, hfront_two]
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
      by nlinarith, by nlinarith, by nlinarith, ?_⟩
    nlinarith
  · have hd_log : (d : ℝ) < logEN n ^ 2 := lt_of_not_ge hlarge
    have hd_nine : (d : ℝ) ≤ 9 * (n : ℝ) :=
      le_trans (le_of_lt hd_log) (logEN_sq_le_nine_mul n hn)
    have ht_le : (d : ℝ) / (n : ℝ) ^ 2 ≤ 9 * (1 / (n : ℝ)) := by
      calc
        (d : ℝ) / (n : ℝ) ^ 2 ≤ (9 * (n : ℝ)) / (n : ℝ) ^ 2 := by
          gcongr
        _ = 9 * (1 / (n : ℝ)) := by field_simp
    have hfront_zero_lower : 1 / (n : ℝ) ≤ frontierRate n d 0 := by
      unfold frontierRate collisionComponent
      have hz : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [hz, zero_add]
      change 1 / (n : ℝ) ≤ 1 / (n : ℝ) +
        min 1 (min (polynomialComponent n d) ((d : ℝ) / (n : ℝ) ^ 2))
      exact le_add_of_nonneg_right (le_min zero_le_one (le_min hu ht))
    have htarget_zero_upper :
        1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2) ≤
          10 * (1 / (n : ℝ)) := by
      calc
        1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2) ≤
            1 / (n : ℝ) + 9 * (1 / (n : ℝ)) :=
          add_le_add (le_refl _) (min_le_of_right_le ht_le)
        _ = 10 * (1 / (n : ℝ)) := by ring
    have htmin_le : min 1 ((d : ℝ) / (n : ℝ) ^ 2) ≤ 9 * (1 / (n : ℝ)) :=
      min_le_of_right_le ht_le
    have hconv_two_lower :
        1 / (n : ℝ) + min 1 (polynomialComponent n d) ≤ converseRate n d 2 := by
      unfold converseRate
      nlinarith [le_min zero_le_one ht, le_min zero_le_one hu]
    have hconv_two_upper : converseRate n d 2 ≤
        10 * (1 / (n : ℝ) + min 1 (polynomialComponent n d)) := by
      unfold converseRate
      nlinarith [htmin_le, le_min zero_le_one hu]
    rw [hconverse_zero, hfront_two]
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
      by nlinarith, by nlinarith, by nlinarith, hconv_two_upper⟩

-- @node: prop:endpoint-reductions
/-- [Restricted-range exact-homogeneity reduction together with the unrestricted radius-two
  identity and converse comparison for every positive alphabet size](goal). -/
theorem endpoint_reductions :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ c_epsilon c C : ℝ,
      0 < c_epsilon ∧ c_epsilon ≤ 1 ∧
      0 < c ∧ c ≤ C ∧
      (
      ∀ n d : ℕ, 0 < n → 0 < d →
        (d : ℝ) ≤ c_epsilon * (n : ℝ) ^ 2 / logEN n →
        c * (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2) ≤
          frontierRate n d 0 ∧
        frontierRate n d 0 ≤
          C * (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2) ∧
        c * (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2) ≤
          converseRate n d 0 ∧
        converseRate n d 0 ≤
          C * (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2) ∧
        c * (1 / (n : ℝ) + min 1 (polynomialComponent n d)) ≤
          frontierRate n d 2 ∧
        frontierRate n d 2 ≤
          C * (1 / (n : ℝ) + min 1 (polynomialComponent n d)) ∧
        c * (1 / (n : ℝ) + min 1 (polynomialComponent n d)) ≤
          converseRate n d 2 ∧
        converseRate n d 2 ≤
          C * (1 / (n : ℝ) + min 1 (polynomialComponent n d))) ∧
      (∀ d : ℕ, ∀ M : ℝ,
        (∀ P : UnrestrictedClass d epsilon M,
          ∃ Q : ModelClass d epsilon M 2, Q.law = P.law) ∧
        (∀ Q : ModelClass d epsilon M 2,
          ∃ P : UnrestrictedClass d epsilon M, P.law = Q.law)) ∧
      (∀ n d : ℕ, 0 < n → 0 < d →
        frontierRate n d 2 =
            1 / (n : ℝ) + min 1 (polynomialComponent n d) ∧
        c * (1 / (n : ℝ) + min 1 (polynomialComponent n d)) ≤
            converseRate n d 2 ∧
        converseRate n d 2 ≤
            C * (1 / (n : ℝ) + min 1 (polynomialComponent n d))) := by
  intro epsilon _ _
  obtain ⟨⟨c, C, hc, hcC, hall⟩, hclasses, hfront_two⟩ :=
    endpoint_reductions_all_d
  refine ⟨1, c, C, zero_lt_one, le_rfl, hc, hcC, ?_, ?_, ?_⟩
  · intro n d hn hd hd_range
    have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
    have hn_one : (1 : ℝ) ≤ n := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
    have hlog : 1 ≤ logEN n := by
      rw [logEN, Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hn_real), Real.log_exp]
      exact le_add_of_nonneg_right (Real.log_nonneg hn_one)
    have hcap : (d : ℝ) ≤ (n : ℝ) ^ 2 := calc
      (d : ℝ) ≤ 1 * (n : ℝ) ^ 2 / logEN n := hd_range
      _ ≤ 1 * (n : ℝ) ^ 2 :=
        div_le_self (by positivity) hlog
      _ = (n : ℝ) ^ 2 := one_mul _
    have hratio : (d : ℝ) / (n : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one (sq_pos_of_pos hn_real)]
      exact hcap
    simpa [min_eq_right hratio] using hall n d hn hd
  · intro d M
    exact hclasses d epsilon M
  · intro n d hn hd
    have h := hall n d hn hd
    exact ⟨hfront_two n d hn hd, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

/-- A sequence lies in the residual shrinking-radius wedge. -/
def ResidualWedge (dseq : ℕ → ℕ) (sseq : ℕ → ℝ) : Prop :=
  (∀ᶠ t in atTop, 1 ≤ dseq t ∧ 0 ≤ sseq t ∧ sseq t ≤ 2) ∧
  Tendsto (fun n => baseRate n (dseq n) / polynomialComponent n (dseq n))
      atTop (nhds 0) ∧
  Tendsto (fun n => polynomialComponent n (dseq n)) atTop (nhds 0) ∧
  Tendsto (fun n => baseRate n (dseq n) / (sseq n) ^ 2) atTop (nhds 0) ∧
  Tendsto (fun n => (sseq n) ^ 2) atTop (nhds 0)

-- @node: oeq:shrinking-radius-frontier
/-- Descriptive, never-proved open question.  Put `L = log(en)`,
`b = n⁻¹ + d/n²`, and `u = d²/(n²L²)`.  In the residual wedge
`b ≪ u ≪ 1` and `b ≪ sigma² ≪ 1`, ask for either a realization-wise
radius-constrained paired-cell moment-matching fuzzy experiment in the model
class with ATE separation of order `M * min(sigma, d/(nL))` and sample-mixture total
variation bounded away from one, or an explicit total estimator with risk
strictly smaller than the selector benchmark `M² * (b + min(u,sigma²))`.
The ideal desideratum is an estimator ideally attaining the proved product
benchmark `M² * (b + sigma²*u)`.
The existing hypothesis-independent channel yields only product separation
`M * sigma * min(1,d/(nL))` and therefore does not answer the question. -/
def ShrinkingRadiusFrontierQuestion : String :=
  "Put L := log(en), b := n^-1 + d/n^2, and u := d^2/(n^2 L^2). " ++
  "In the residual wedge b << u << 1 and b << sigma^2 << 1, equivalently " ++
  "up to boundary constants sqrt(n)L << d << nL and sigma^2 >> b, ask " ++
  "whether one can construct a realization-wise radius-constrained paired-cell " ++
  "moment-matching fuzzy experiment in P_{d,epsilon,M,sigma} with ATE " ++
  "separation of order M*min(sigma,d/(nL)) and sample-mixture total variation bounded " ++
  "away from one, or instead construct an explicit total estimator whose risk " ++
  "is strictly smaller in order than the selector benchmark " ++
  "M^2*(b+min(u,sigma^2)), ideally attaining the proved product benchmark " ++
  "M^2*(b+sigma^2*u). The existing hypothesis-independent channel gives only " ++
  "the product separation M*sigma*min(1,d/(nL)) and does not answer this question."

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
