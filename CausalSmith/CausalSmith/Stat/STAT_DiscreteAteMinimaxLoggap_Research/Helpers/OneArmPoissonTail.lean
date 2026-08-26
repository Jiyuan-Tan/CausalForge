import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmPoissonTaylor
import Mathlib.Data.Nat.Choose.Sum

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open scoped BigOperators

/-!
# Poisson tail collapse for the one-arm lower bound

This file collects the scalar analytic part of the C.5 argument: the
count-dependent Taylor remainder and the high-count complement are the upper
tail of the Cauchy product of two exponential series.  A dyadic Chernoff bound
then gives the logarithmic calibration used downstream.
-/

/-- The nonnegative coefficient of degree `k` in the exponential series. -/
noncomputable def expSeriesCoeff (x : ℝ) (k : ℕ) : ℝ :=
  x ^ k / (Nat.factorial k : ℝ)

/-- Convolution of two exponential-series coefficients is the coefficient at
the sum of their arguments. -/
lemma sum_expSeriesCoeff_mul_eq (x y : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        expSeriesCoeff x k * expSeriesCoeff y (n - k) =
      expSeriesCoeff (x + y) n := by
  unfold expSeriesCoeff
  rw [show (x + y) ^ n = ∑ k ∈ Finset.range (n + 1),
      x ^ k * y ^ (n - k) * (n.choose k : ℝ) by exact add_pow x y n]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hfac : (n.choose k : ℝ) * (Nat.factorial k : ℝ) *
      (Nat.factorial (n - k) : ℝ) = (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  field_simp
  rw [← hfac]
  ring

/-- Sum of the three sufficient-count coefficients at a fixed total count. -/
noncomputable def triplePoissonTotalCoefficient
    (sampleScale p pi mu : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    ∑ j ∈ Finset.range (k - i + 1),
      triplePoissonCoefficient sampleScale p pi mu ![i, j, k - i - j]

/-- The three independent Poisson coordinates have total mean
`sampleScale*p`; summing their coefficients over a fixed total count gives
the corresponding scalar exponential-series coefficient. -/
lemma triplePoissonTotalCoefficient_eq
    (sampleScale p pi mu : ℝ) (k : ℕ) :
    triplePoissonTotalCoefficient sampleScale p pi mu k =
      expSeriesCoeff (sampleScale * p) k := by
  let x11 := sampleScale * p * pi * mu
  let x10 := sampleScale * p * pi * (1 - mu)
  let x0 := sampleScale * p * (1 - pi)
  have hsum : x11 + x10 + x0 = sampleScale * p := by
    dsimp [x11, x10, x0]
    ring
  unfold triplePoissonTotalCoefficient
  have hpoint (i : ℕ) (hi : i ∈ Finset.range (k + 1)) :
      ∑ j ∈ Finset.range (k - i + 1),
          triplePoissonCoefficient sampleScale p pi mu ![i, j, k - i - j] =
        expSeriesCoeff x11 i * expSeriesCoeff (x10 + x0) (k - i) := by
    have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    rw [← sum_expSeriesCoeff_mul_eq x10 x0 (k - i)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjik : j ≤ k - i := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    unfold triplePoissonCoefficient expSeriesCoeff
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_succ, Function.comp_apply]
    have hsub : k - i - j = k - (i + j) := by omega
    rw [hsub]
    ring
  rw [Finset.sum_congr rfl hpoint]
  rw [sum_expSeriesCoeff_mul_eq]
  rw [show x11 + (x10 + x0) = sampleScale * p by linarith [hsum]]

/-- The exponential-series tail is the ordinary exponential minus its first
`L` coefficients. -/
lemma expSeriesTail_eq_exp_sub_sum (x : ℝ) (L : ℕ) :
    expSeriesTail x L = Real.exp x -
      ∑ k ∈ Finset.range L, expSeriesCoeff x k := by
  let f : ℕ → ℝ := fun k => expSeriesCoeff x k
  have hf : Summable f := by
    simpa [f, expSeriesCoeff] using NormedSpace.expSeries_div_summable x
  have hsplit := hf.sum_add_tsum_nat_add L
  have hexp : Real.exp x = ∑' k, f k := by
    rw [Real.exp_eq_exp_ℝ]
    simpa [f, expSeriesCoeff] using
      (NormedSpace.expSeries_div_hasSum_exp x).tsum_eq.symm
  unfold expSeriesTail
  change (∑' k : ℕ, f (k + L)) = _
  rw [hexp]
  linarith

private lemma sum_triangle_eq_sum_convolution (f g : ℕ → ℝ) (D : ℕ) :
    ∑ k ∈ Finset.range (D + 1), f k *
        ∑ t ∈ Finset.range (D + 1 - k), g t =
      ∑ n ∈ Finset.range (D + 1),
        ∑ k ∈ Finset.range (n + 1), f k * g (n - k) := by
  induction D with
  | zero => simp
  | succ D ih =>
      rw [show D + 1 + 1 = (D + 1) + 1 by omega]
      conv_lhs => rw [Finset.sum_range_succ]
      conv_rhs => rw [Finset.sum_range_succ]
      rw [← ih]
      have hinner :
          ∑ k ∈ Finset.range (D + 1), f k *
              ∑ t ∈ Finset.range (D + 1 + 1 - k), g t =
            (∑ k ∈ Finset.range (D + 1), f k *
              ∑ t ∈ Finset.range (D + 1 - k), g t) +
              ∑ k ∈ Finset.range (D + 1), f k * g (D + 1 - k) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        have hkD : k ≤ D := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        rw [show D + 1 + 1 - k = (D + 1 - k) + 1 by omega,
          Finset.sum_range_succ]
        ring
      rw [hinner]
      have hconv :
          ∑ k ∈ Finset.range (D + 1 + 1), f k * g (D + 1 - k) =
            (∑ k ∈ Finset.range (D + 1), f k * g (D + 1 - k)) +
              f (D + 1) * g 0 := by
        rw [Finset.sum_range_succ]
        simp
      rw [hconv]
      simp only [show D + 1 + 1 - (D + 1) = 1 by omega,
        Finset.range_one, Finset.sum_singleton]
      ring

/-- Scalar form of the low-count Taylor remainder plus the high-count
complement. -/
noncomputable def countTaylorRemainder (x : ℝ) (D : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (D + 1),
      expSeriesCoeff x k * expSeriesTail x (D + 1 - k)) +
    expSeriesTail x (D + 1) * Real.exp x

/-- The actual three-count remainder, grouped by the total sufficient count. -/
noncomputable def tripleCountTaylorRemainder
    (sampleScale p pi mu : ℝ) (D : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (D + 1),
      (∑ i ∈ Finset.range (k + 1),
        ∑ j ∈ Finset.range (k - i + 1),
          triplePoissonCoefficient sampleScale p pi mu ![i, j, k - i - j]) *
        expSeriesTail (sampleScale * p) (D + 1 - k)) +
    expSeriesTail (sampleScale * p) (D + 1) * Real.exp (sampleScale * p)

lemma tripleCountTaylorRemainder_eq_countTaylorRemainder
    (sampleScale p pi mu : ℝ) (D : ℕ) :
    tripleCountTaylorRemainder sampleScale p pi mu D =
      countTaylorRemainder (sampleScale * p) D := by
  unfold tripleCountTaylorRemainder countTaylorRemainder
  apply congrArg (fun z => z +
    expSeriesTail (sampleScale * p) (D + 1) * Real.exp (sampleScale * p))
  apply Finset.sum_congr rfl
  intro k _
  rw [← triplePoissonTotalCoefficient, triplePoissonTotalCoefficient_eq]

/-- Exact Cauchy-product collapse: the count-dependent Taylor remainder on
counts at most `D`, together with the high-count complement, is the tail of
the exponential series at parameter `2*x`. -/
lemma countTaylorRemainder_eq_expSeriesTail_two_mul (x : ℝ) (D : ℕ) :
    countTaylorRemainder x D = expSeriesTail (2 * x) (D + 1) := by
  rw [countTaylorRemainder, expSeriesTail_eq_exp_sub_sum,
    expSeriesTail_eq_exp_sub_sum]
  simp_rw [expSeriesTail_eq_exp_sub_sum]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, sum_triangle_eq_sum_convolution]
  rw [← Finset.sum_mul]
  simp_rw [sum_expSeriesCoeff_mul_eq]
  have hexp_sq : Real.exp x * Real.exp x = Real.exp (2 * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  ring_nf at hexp_sq ⊢
  linarith

/-- Exact collapse for the actual triple sufficient counts. -/
lemma tripleCountTaylorRemainder_eq_expSeriesTail_two_mul
    (sampleScale p pi mu : ℝ) (D : ℕ) :
    tripleCountTaylorRemainder sampleScale p pi mu D =
      expSeriesTail (2 * (sampleScale * p)) (D + 1) := by
  rw [tripleCountTaylorRemainder_eq_countTaylorRemainder,
    countTaylorRemainder_eq_expSeriesTail_two_mul]

/-- A dyadic Chernoff bound for the normalized exponential-series tail. -/
lemma exp_neg_mul_expSeriesTail_le_exp_div_two_pow
    (x : ℝ) (hx : 0 ≤ x) (L : ℕ) :
    Real.exp (-x) * expSeriesTail x L ≤ Real.exp x / (2 : ℝ) ^ L := by
  unfold expSeriesTail
  have hsx : Summable (fun t : ℕ => x ^ (t + L) /
      (Nat.factorial (t + L) : ℝ)) := by
    exact (NormedSpace.expSeries_div_summable x).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  have hs2x : Summable (fun t : ℕ => (2 * x) ^ (t + L) /
      (Nat.factorial (t + L) : ℝ)) := by
    exact (NormedSpace.expSeries_div_summable (2 * x)).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  have hterm (t : ℕ) :
      x ^ (t + L) / (Nat.factorial (t + L) : ℝ) ≤
        ((2 : ℝ) ^ L)⁻¹ *
          ((2 * x) ^ (t + L) / (Nat.factorial (t + L) : ℝ)) := by
    rw [mul_pow]
    have hpow : (2 : ℝ) ^ L ≤ (2 : ℝ) ^ (t + L) := by
      exact pow_le_pow_right₀ (by norm_num) (Nat.le_add_left L t)
    have hxpow : 0 ≤ x ^ (t + L) := pow_nonneg hx _
    field_simp
    nlinarith
  calc
    Real.exp (-x) * ∑' t : ℕ,
        x ^ (t + L) / (Nat.factorial (t + L) : ℝ)
        ≤ Real.exp (-x) * ∑' t : ℕ, ((2 : ℝ) ^ L)⁻¹ *
            ((2 * x) ^ (t + L) / (Nat.factorial (t + L) : ℝ)) := by
          exact mul_le_mul_of_nonneg_left
            (hsx.tsum_le_tsum hterm (hs2x.mul_left _)) (Real.exp_pos _).le
    _ = Real.exp (-x) * ((2 : ℝ) ^ L)⁻¹ *
          expSeriesTail (2 * x) L := by
          rw [tsum_mul_left]
          unfold expSeriesTail
          ring
    _ ≤ Real.exp (-x) * ((2 : ℝ) ^ L)⁻¹ * Real.exp (2 * x) := by
          gcongr
          rw [expSeriesTail_eq_exp_sub_sum]
          exact sub_le_self _ (Finset.sum_nonneg fun k _ => by
            exact div_nonneg (pow_nonneg (mul_nonneg (by norm_num) hx) _)
              (Nat.cast_nonneg _))
    _ = Real.exp x / (2 : ℝ) ^ L := by
          calc
            _ = ((2 : ℝ) ^ L)⁻¹ *
                (Real.exp (-x) * Real.exp (2 * x)) := by ring
            _ = ((2 : ℝ) ^ L)⁻¹ * Real.exp x := by
              rw [← Real.exp_add]
              congr 2
              ring
            _ = _ := by rw [div_eq_mul_inv]; ring

/-- Logarithmic calibration of the dyadic tail bound. -/
lemma exp_neg_mul_expSeriesTail_le_of_log
    {x delta : ℝ} (hx : 0 ≤ x) (hdelta : 0 < delta) (L : ℕ)
    (hcal : x ≤ (L : ℝ) * Real.log 2 + Real.log delta) :
    Real.exp (-x) * expSeriesTail x L ≤ delta := by
  refine (exp_neg_mul_expSeriesTail_le_exp_div_two_pow x hx L).trans ?_
  rw [div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ L)]
  have hexp := Real.exp_le_exp.mpr hcal
  rw [Real.exp_add, Real.exp_log hdelta, Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hexp
  simpa [mul_comm] using hexp

/-- A form ready for the usual logarithmic cutoff: if the cutoff pays for the
Poisson mean plus `2 log n`, then the normalized tail is at most `n⁻²`. -/
lemma exp_neg_mul_expSeriesTail_le_inv_sq_of_log_budget
    {x n : ℝ} (hx : 0 ≤ x) (hn : 0 < n) (L : ℕ)
    (hbudget : x + 2 * Real.log n ≤ (L : ℝ) * Real.log 2) :
    Real.exp (-x) * expSeriesTail x L ≤ n⁻¹ ^ 2 := by
  apply exp_neg_mul_expSeriesTail_le_of_log hx (sq_pos_of_pos (inv_pos.mpr hn)) L
  have hlog : Real.log (n⁻¹ ^ 2) = -2 * Real.log n := by
    rw [Real.log_pow, Real.log_inv]
    ring
  rw [hlog]
  linarith

/-- Log-budget bound in the normalization arising from the triple-count
predictive mass: the count/Taylor collapse has parameter `2*x` but only one
factor `exp (-x)` from the original Poisson atom. -/
lemma exp_neg_mul_expSeriesTail_two_mul_le_inv_sq_of_log_budget
    {x n : ℝ} (hx : 0 ≤ x) (hn : 0 < n) (L : ℕ)
    (hbudget : 3 * x + 2 * Real.log n ≤ (L : ℝ) * Real.log 2) :
    Real.exp (-x) * expSeriesTail (2 * x) L ≤ n⁻¹ ^ 2 := by
  have hbase := exp_neg_mul_expSeriesTail_le_exp_div_two_pow
    (2 * x) (mul_nonneg (by norm_num) hx) L
  have hscaled : Real.exp x *
      (Real.exp (-(2 * x)) * expSeriesTail (2 * x) L) ≤
      Real.exp x * (Real.exp (2 * x) / (2 : ℝ) ^ L) :=
    mul_le_mul_of_nonneg_left hbase (Real.exp_pos _).le
  have hleft : Real.exp x *
      (Real.exp (-(2 * x)) * expSeriesTail (2 * x) L) =
      Real.exp (-x) * expSeriesTail (2 * x) L := by
    calc
      _ = (Real.exp x * Real.exp (-(2 * x))) *
          expSeriesTail (2 * x) L := by ring
      _ = Real.exp (x + -(2 * x)) * expSeriesTail (2 * x) L := by
        rw [Real.exp_add]
      _ = _ := by congr 2 <;> ring
  rw [hleft] at hscaled
  refine hscaled.trans ?_
  have hright : Real.exp x * (Real.exp (2 * x) / (2 : ℝ) ^ L) =
      Real.exp (3 * x) / (2 : ℝ) ^ L := by
    calc
      _ = (Real.exp x * Real.exp (2 * x)) / (2 : ℝ) ^ L := by ring
      _ = Real.exp (x + 2 * x) / (2 : ℝ) ^ L := by rw [Real.exp_add]
      _ = _ := by congr 2 <;> ring
  rw [hright]
  rw [div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ L)]
  have hexp := Real.exp_le_exp.mpr hbudget
  rw [Real.exp_add, Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hexp
  have hninv : 0 < n⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hn)
  have hcancel : n⁻¹ ^ 2 * Real.exp (2 * Real.log n) = 1 := by
    rw [show 2 * Real.log n = Real.log n + Real.log n by ring,
      Real.exp_add, Real.exp_log hn]
    field_simp
  calc
    Real.exp (3 * x) = n⁻¹ ^ 2 *
        (Real.exp (3 * x) * Real.exp (2 * Real.log n)) := by
      symm
      calc
        n⁻¹ ^ 2 * (Real.exp (3 * x) * Real.exp (2 * Real.log n)) =
            Real.exp (3 * x) *
              (n⁻¹ ^ 2 * Real.exp (2 * Real.log n)) := by ring
        _ = Real.exp (3 * x) := by rw [hcancel, mul_one]
    _ ≤ n⁻¹ ^ 2 * (2 : ℝ) ^ L :=
      mul_le_mul_of_nonneg_left hexp hninv.le

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
