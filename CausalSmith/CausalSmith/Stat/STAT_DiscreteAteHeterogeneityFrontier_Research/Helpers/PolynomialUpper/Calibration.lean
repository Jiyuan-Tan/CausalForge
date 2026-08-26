/- Calibration and totality certificates for the polynomial estimator. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.Estimators

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open Set

-- @node: polynomialAlpha0_pos
/-- [The explicit shifted-Chebyshev degree constant is strictly positive](goal). -/
lemma polynomialAlpha0_pos : 0 < polynomialAlpha0 := by
  unfold polynomialAlpha0
  have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hlog274 : 0 < Real.log (27 / 4) := Real.log_pos (by norm_num)
  positivity

/-- [the polynomial calibration constant is at most one](goal). -/
lemma polynomialAlpha0_le_one : polynomialAlpha0 ≤ 1 := by
  unfold polynomialAlpha0
  exact min_le_left _ _

-- @node: polynomialAlpha0_le_log_six_budget
/-- [The declared degree constant fits the coefficient-growth budget used by the shifted-Chebyshev
  variance bound](goal). -/
lemma polynomialAlpha0_le_log_six_budget :
    polynomialAlpha0 ≤ 1 / (64 * Real.log 6) := by
  unfold polynomialAlpha0
  exact (min_le_right _ _).trans (min_le_left _ _)

-- @node: polynomialAlpha0_le_covariance_budget
/-- [The same degree constant fits the stronger covariance calibration budget](goal). -/
lemma polynomialAlpha0_le_covariance_budget :
    polynomialAlpha0 ≤ 1 / (512 * (8 * Real.log (27 / 4))) := by
  unfold polynomialAlpha0
  exact (min_le_right _ _).trans (min_le_right _ _)

-- @node: polynomialDegree_cast_le
/-- [Removing the floor can only increase the calibrated real-valued degree](goal). -/
lemma polynomialDegree_cast_le (n : ℕ) :
    (polynomialDegree n : ℝ) ≤ polynomialAlpha0 * logEN n := by
  unfold polynomialDegree
  apply Nat.floor_le
  apply mul_nonneg polynomialAlpha0_pos.le
  by_cases hn : n = 0
  · subst n
    simp [logEN]
  · have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    unfold logEN
    exact Real.log_nonneg (by
      have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
      nlinarith)

/-- [the effective logarithmic sample size is nonnegative](goal). -/
lemma logEN_nonneg_poly (n : ℕ) : 0 ≤ logEN n := by
  by_cases hn : n = 0
  · subst n
    simp [logEN]
  · have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    unfold logEN
    exact Real.log_nonneg (by
      have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
      nlinarith)

/-- If [the sample is nonempty](hyp:hn), [the effective logarithmic sample size is at least
  one](goal). -/
lemma one_le_logEN {n : ℕ} (hn : 0 < n) : 1 ≤ logEN n := by
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  rw [logEN, Real.log_mul (Real.exp_ne_zero 1)
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hnR)), Real.log_exp]
  linarith [Real.log_nonneg hnR]

/-- If [the sample is nonempty](hyp:hn), [the polynomial degree is at most the effective
  logarithmic sample size](goal). -/
lemma polynomialDegree_cast_le_logEN {n : ℕ} (hn : 0 < n) :
    (polynomialDegree n : ℝ) ≤ logEN n := by
  exact (polynomialDegree_cast_le n).trans
    (mul_le_of_le_one_left (logEN_nonneg_poly n) polynomialAlpha0_le_one)

/-- If [the polynomial or elbow parameter satisfies its stated bound](hyp:hK), [the polynomial
  degree satisfies its stated lower bound in terms of the effective logarithmic sample
  size](goal). -/
lemma polynomialDegree_cast_lower {n : ℕ} (hK : 2 ≤ polynomialDegree n) :
    polynomialAlpha0 * logEN n / 2 ≤ (polynomialDegree n : ℝ) := by
  have hfloor := Nat.lt_floor_add_one (polynomialAlpha0 * logEN n)
  change polynomialAlpha0 * logEN n <
      (polynomialDegree n : ℝ) + 1 at hfloor
  have hKreal : (2 : ℝ) ≤ polynomialDegree n := by exact_mod_cast hK
  nlinarith

-- @node: six_pow_two_degree_le_exp
/-- [The squared coefficient-growth factor is dominated by a small exponential power of the
  effective logarithmic sample size](goal). -/
lemma six_pow_two_degree_le_exp (n : ℕ) :
    (6 : ℝ) ^ (2 * polynomialDegree n) ≤
      Real.exp (logEN n / 32) := by
  rw [Real.pow_le_iff_le_log (by norm_num) (Real.exp_pos _), Real.log_exp]
  have hK := polynomialDegree_cast_le n
  have ha := polynomialAlpha0_le_log_six_budget
  have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hL := logEN_nonneg_poly n
  have ha' : 2 * polynomialAlpha0 * Real.log 6 ≤ 1 / 32 := by
    calc
      2 * polynomialAlpha0 * Real.log 6 =
          (2 * Real.log 6) * polynomialAlpha0 := by ring
      _ ≤ (2 * Real.log 6) * (1 / (64 * Real.log 6)) :=
        mul_le_mul_of_nonneg_left ha (by positivity)
      _ = 1 / 32 := by field_simp [hlog6.ne']; ring
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    2 * (polynomialDegree n : ℝ) * Real.log 6 =
        (2 * Real.log 6) * (polynomialDegree n : ℝ) := by ring
    _ ≤ (2 * Real.log 6) * (polynomialAlpha0 * logEN n) :=
      mul_le_mul_of_nonneg_left hK (by positivity)
    _ = (2 * polynomialAlpha0 * Real.log 6) * logEN n := by ring
    _ ≤ (1 / 32) * logEN n := mul_le_mul_of_nonneg_right ha' hL
    _ = logEN n / 32 := by ring

-- @node: six_pow_four_degree_le_exp
/-- [The fourth-power coefficient factor obeys the matching doubled exponent budget](goal). -/
lemma six_pow_four_degree_le_exp (n : ℕ) :
    (6 : ℝ) ^ (4 * polynomialDegree n) ≤
      Real.exp (logEN n / 16) := by
  have h := six_pow_two_degree_le_exp n
  have h0 : 0 ≤ (6 : ℝ) ^ (2 * polynomialDegree n) := by positivity
  have he0 : 0 ≤ Real.exp (logEN n / 32) := (Real.exp_pos _).le
  calc
    (6 : ℝ) ^ (4 * polynomialDegree n) =
        ((6 : ℝ) ^ (2 * polynomialDegree n)) ^ 2 := by
      rw [show 4 * polynomialDegree n =
        (2 * polynomialDegree n) * 2 by omega, pow_mul]
    _ ≤ (Real.exp (logEN n / 32)) ^ 2 :=
      pow_le_pow_left₀ h0 h 2
    _ = Real.exp (logEN n / 16) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- If [the sample is nonempty](hyp:hn), [the polynomial estimation block is nonempty](goal). -/
lemma polynomial_estimationBlock_pos {n : ℕ} (hn : 0 < n) :
    0 < n - n / 2 := by
  omega

/-- If [the sample is nonempty](hyp:hn), [the polynomial light-cell scale is positive](goal). -/
lemma polynomial_lightScale_pos {n : ℕ} (hn : 0 < n) :
    0 < 4096 * logEN n / (n - n / 2 : ℕ) := by
  have hm := polynomial_estimationBlock_pos hn
  have hL := one_le_logEN hn
  positivity

/-- If [the sample is nonempty](hyp:hn), [the polynomial light-cell scale satisfies its stated
  upper bound](goal). -/
lemma polynomial_lightScale_le {n : ℕ} (hn : 0 < n) :
    4096 * logEN n / (n - n / 2 : ℕ) ≤
      8192 * logEN n / (n : ℝ) := by
  have hm : 0 < ((n - n / 2 : ℕ) : ℝ) := by
    exact_mod_cast polynomial_estimationBlock_pos hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hL : 0 ≤ logEN n := logEN_nonneg_poly n
  have htwice : n ≤ 2 * (n - n / 2) := by omega
  have htwiceR : (n : ℝ) ≤ 2 * ((n - n / 2 : ℕ) : ℝ) := by
    exact_mod_cast htwice
  apply (div_le_div_iff₀ hm hnR).2
  nlinarith

/-- If [the sample size satisfies the stated lower bound](hyp:hn) and [the overlap constant is
  positive](hyp:hepsilon), [the pilot denominator satisfies the stated lower bound](goal). -/
lemma polynomial_pilot_denominator_ge {n : ℕ} {epsilon : ℝ}
    (hn : 8 ≤ n) (hepsilon : 0 < epsilon) :
    4 * (n : ℝ) * epsilon ^ 2 * logEN n ≤
      (((((n - n / 2 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) *
        (128 * logEN n / (n / 2 : ℕ))) := by
  have hnpos : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hpNat : 0 < n / 2 := Nat.div_pos (by omega) (by norm_num)
  have hp : 0 < ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hpNat
  have hL : 0 < logEN n := zero_lt_one.trans_le (one_le_logEN hnpos)
  have hblockNat : n ≤ 4 * (n - n / 2 - 2) := by omega
  have hblock : (n : ℝ) / 8 ≤ ((n - n / 2 - 2 : ℕ) : ℝ) / 2 := by
    have hc : (n : ℝ) ≤ 4 * ((n - n / 2 - 2 : ℕ) : ℝ) := by
      exact_mod_cast hblockNat
    linarith
  have hlower : 256 * logEN n / (n : ℝ) ≤
      128 * logEN n / (n / 2 : ℕ) := by
    apply (div_le_div_iff₀ hnR hp).2
    have hhalf : 2 * (n / 2) ≤ n := by omega
    have hhalfR : 2 * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hhalf
    nlinarith
  have hsq : ((n : ℝ) / 8 * epsilon) ^ 2 ≤
      (((n - n / 2 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hblock hepsilon.le
    nlinarith [sq_nonneg
      ((((n - n / 2 - 2 : ℕ) : ℝ) / 2 * epsilon) -
        ((n : ℝ) / 8 * epsilon))]
  calc
    4 * (n : ℝ) * epsilon ^ 2 * logEN n =
        (((n : ℝ) / 8 * epsilon) ^ 2) *
          (256 * logEN n / (n : ℝ)) := by field_simp [hnR.ne']; ring
    _ ≤ ((((n - n / 2 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) *
        (128 * logEN n / (n / 2 : ℕ)) :=
      mul_le_mul hsq hlower (by positivity) (by positivity)

/-- If [the sample is nonempty](hyp:hn), [the calibrated polynomial shift satisfies the required
  approximation condition](goal). -/
lemma polynomial_shift_condition {n : ℕ} (hn : 0 < n) :
    (4 : ℝ) * (polynomialDegree n + 2) / (n - n / 2 : ℕ) ≤
      3 * (4096 * logEN n / (n - n / 2 : ℕ)) / 4 := by
  have hm : 0 < ((n - n / 2 : ℕ) : ℝ) := by
    exact_mod_cast polynomial_estimationBlock_pos hn
  have hK := polynomialDegree_cast_le_logEN hn
  have hL := one_le_logEN hn
  rw [show 3 * (4096 * logEN n / ((n - n / 2 : ℕ) : ℝ)) / 4 =
    (3072 * logEN n) / ((n - n / 2 : ℕ) : ℝ) by ring]
  apply (div_le_div_iff_of_pos_right hm).2
  push_cast
  nlinarith

/-- If [the sample is nonempty](hyp:hn) and [the stated llarge condition holds](hyp:hLlarge), [the
  fourth-power logarithmic growth term satisfies the stated sample-size bound](goal). -/
lemma polynomial_log_growth_four {n : ℕ} (hn : 0 < n)
    (hLlarge : 240 ≤ logEN n) :
    (6 : ℝ) ^ (4 * polynomialDegree n) * logEN n ^ 6 ≤ n := by
  have hL : 0 < logEN n := by linarith
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlogn : logEN n = 1 + Real.log (n : ℝ) := by
    rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnR.ne', Real.log_exp]
  have hlog12 : Real.log (12 : ℝ) ≤ 11 :=
    (Real.log_le_sub_one_of_pos (by norm_num)).trans_eq (by norm_num)
  have hlogL : Real.log (logEN n) ≤ logEN n / 8 := by
    have hsplit : Real.log (logEN n) =
        Real.log 12 + Real.log (logEN n / 12) := by
      rw [← Real.log_mul (by norm_num : (12 : ℝ) ≠ 0) (by positivity)]
      congr 1
      field_simp
    rw [hsplit]
    have hsmall := Real.log_le_sub_one_of_pos (by positivity : 0 < logEN n / 12)
    nlinarith
  have hLpow : logEN n ^ 6 ≤ Real.exp (3 * logEN n / 4) := by
    rw [show logEN n ^ 6 = Real.exp (6 * Real.log (logEN n)) by
      calc
        logEN n ^ 6 = (Real.exp (Real.log (logEN n))) ^ 6 := by
          rw [Real.exp_log hL]
        _ = Real.exp ((6 : ℕ) * Real.log (logEN n)) := by
          rw [Real.exp_nat_mul]
        _ = _ := by norm_num]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc
    (6 : ℝ) ^ (4 * polynomialDegree n) * logEN n ^ 6 ≤
        Real.exp (logEN n / 16) * Real.exp (3 * logEN n / 4) := by
      gcongr
      exact six_pow_four_degree_le_exp n
    _ = Real.exp (13 * logEN n / 16) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (logEN n - 1) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = n := by
      rw [hlogn]
      simp [Real.exp_log hnR]

/-- If [the sample is nonempty](hyp:hn) and [the stated llarge condition holds](hyp:hLlarge), [the
  squared logarithmic growth term satisfies the stated sample-size bound](goal). -/
lemma polynomial_log_growth_two {n : ℕ} (hn : 0 < n)
    (hLlarge : 240 ≤ logEN n) :
    (6 : ℝ) ^ (2 * polynomialDegree n) * logEN n ^ 6 ≤ n := by
  have hpow : (6 : ℝ) ^ (2 * polynomialDegree n) ≤
      (6 : ℝ) ^ (4 * polynomialDegree n) := by
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  exact (mul_le_mul_of_nonneg_right hpow (by positivity)).trans
    (polynomial_log_growth_four hn hLlarge)

/-- If [the sample is nonempty](hyp:hn) and [the stated llarge condition holds](hyp:hLlarge), [the
  calibrated fixed branch satisfies the required degree-versus-block-size condition](goal). -/
lemma polynomial_fixedBranch_size_condition {n : ℕ} (hn : 0 < n)
    (hLlarge : 240 ≤ logEN n) :
    4 * (polynomialDegree n + 2) ^ 2 ≤ n - n / 2 := by
  have hK := polynomialDegree_cast_le_logEN hn
  have hgrowth := polynomial_log_growth_four hn hLlarge
  have hsix : 1 ≤ (6 : ℝ) ^ (4 * polynomialDegree n) :=
    one_le_pow₀ (by norm_num)
  have hL : 0 ≤ logEN n := by linarith
  have hL6 : logEN n ^ 6 ≤ (n : ℝ) := by
    calc
      logEN n ^ 6 = 1 * logEN n ^ 6 := by ring
      _ ≤ (6 : ℝ) ^ (4 * polynomialDegree n) * logEN n ^ 6 := by gcongr
      _ ≤ n := hgrowth
  have hnum : (8 : ℝ) * (polynomialDegree n + 2) ^ 2 ≤ n := by
    have hK2 : (polynomialDegree n : ℝ) + 2 ≤ 2 * logEN n := by
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
      nlinarith
    have hsq : ((polynomialDegree n : ℝ) + 2) ^ 2 ≤
        (2 * logEN n) ^ 2 := by
      have hp : 0 ≤
          (2 * logEN n - ((polynomialDegree n : ℝ) + 2)) *
            (2 * logEN n + ((polynomialDegree n : ℝ) + 2)) := by
        positivity
      nlinarith
    have h32 : 32 * logEN n ^ 2 ≤ logEN n ^ 6 := by
      have hp : (240 : ℝ) ^ 4 ≤ logEN n ^ 4 :=
        pow_le_pow_left₀ (by norm_num) hLlarge 4
      have hc : (32 : ℝ) ≤ logEN n ^ 4 := by norm_num at hp ⊢; linarith
      calc
        32 * logEN n ^ 2 ≤ logEN n ^ 4 * logEN n ^ 2 :=
          mul_le_mul_of_nonneg_right hc (sq_nonneg _)
        _ = logEN n ^ 6 := by ring
    calc
      (8 : ℝ) * (polynomialDegree n + 2) ^ 2 ≤
          8 * (2 * logEN n) ^ 2 := by gcongr
      _ = 32 * logEN n ^ 2 := by ring
      _ ≤ logEN n ^ 6 := h32
      _ ≤ n := hL6
  have hhalf : (n : ℝ) / 2 ≤ ((n - n / 2 : ℕ) : ℝ) := by
    have htwice : n ≤ 2 * (n - n / 2) := by omega
    have htwiceR : (n : ℝ) ≤ 2 * ((n - n / 2 : ℕ) : ℝ) := by
      exact_mod_cast htwice
    linarith
  exact_mod_cast (show (4 : ℝ) * (polynomialDegree n + 2) ^ 2 ≤
      ((n - n / 2 : ℕ) : ℝ) by nlinarith)

/-- [the effective logarithmic sample size is eventually at least 240](goal). -/
lemma logEN_eventually_ge_240 :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 240 ≤ logEN n := by
  let N : ℕ := Nat.ceil (Real.exp 239)
  refine ⟨N, ?_⟩
  intro n hn
  have hceil : Real.exp 239 ≤ N := Nat.le_ceil _
  have hnreal : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) :=
    lt_of_lt_of_le (Real.exp_pos _) (hceil.trans hnreal)
  have hlog : (239 : ℝ) ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hnpos]
    exact hceil.trans hnreal
  rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnpos.ne', Real.log_exp]
  linarith

/-- If [the sample is nonempty](hyp:hn) and [the stated llarge condition holds](hyp:hLlarge) and
  [the alphabet size satisfies the stated condition](hyp:hd), [the pilot bad-event term is
  absorbed by the target polynomial rate](goal). -/
lemma polynomial_bad_event_absorption {n d : ℕ} (hn : 0 < n)
    (hLlarge : 240 ≤ logEN n)
    (hd : (d : ℝ) ≤ (n : ℝ) * logEN n) :
    8 * (d : ℝ) * Real.exp (-32 * logEN n) ≤ 1 / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hL : 0 < logEN n := by linarith
  have hnid : Real.exp (logEN n - 1) = (n : ℝ) := by
    rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnR.ne', Real.log_exp]
    ring_nf
    rw [Real.exp_log hnR]
  have hLexp : logEN n ≤ Real.exp (logEN n) := by
    exact (show logEN n ≤ logEN n + 1 by linarith).trans
      (Real.add_one_le_exp (logEN n))
  have h8exp : (8 : ℝ) ≤ Real.exp (logEN n) := by
    calc
      (8 : ℝ) ≤ 1 + logEN n := by linarith
      _ ≤ Real.exp (logEN n) := by
        simpa [add_comm] using Real.add_one_le_exp (logEN n)
  have hpolyexp : 8 * logEN n ≤ Real.exp (2 * logEN n) := by
    calc
      8 * logEN n ≤ Real.exp (logEN n) * Real.exp (logEN n) :=
        mul_le_mul h8exp hLexp hL.le (Real.exp_pos _).le
      _ = Real.exp (2 * logEN n) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hmajor : 8 * (n : ℝ) ^ 2 * logEN n ≤
      Real.exp (32 * logEN n) := by
    rw [← hnid, ← Real.exp_nat_mul]
    calc
      8 * Real.exp (2 * (logEN n - 1)) * logEN n =
          (8 * logEN n) * Real.exp (2 * (logEN n - 1)) := by ring
      _ ≤ Real.exp (2 * logEN n) * Real.exp (2 * (logEN n - 1)) := by
        gcongr
      _ = Real.exp (4 * logEN n - 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (32 * logEN n) := by
        apply Real.exp_le_exp.mpr
        nlinarith
  apply (le_div_iff₀ hnR).2
  calc
    8 * (d : ℝ) * Real.exp (-32 * logEN n) * n ≤
        8 * ((n : ℝ) * logEN n) * Real.exp (-32 * logEN n) * n := by
      gcongr
    _ = (8 * (n : ℝ) ^ 2 * logEN n) * Real.exp (-32 * logEN n) := by ring
    _ ≤ Real.exp (32 * logEN n) * Real.exp (-32 * logEN n) := by
      gcongr
    _ = 1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero

-- @node: polynomialDegree_eventually_two
/-- [Beyond an explicit finite cutoff, the calibrated polynomial degree is at least two](goal). -/
lemma polynomialDegree_eventually_two :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 2 ≤ polynomialDegree n := by
  let N : ℕ := Nat.ceil (Real.exp (2 / polynomialAlpha0))
  refine ⟨N, ?_⟩
  intro n hn
  unfold polynomialDegree
  apply Nat.le_floor
  have hceil : Real.exp (2 / polynomialAlpha0) ≤ N := Nat.le_ceil _
  have hnreal : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) :=
    lt_of_lt_of_le (Real.exp_pos _) (hceil.trans hnreal)
  have hlog : 2 / polynomialAlpha0 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hnpos]
    exact hceil.trans hnreal
  have hlogEN : Real.log n ≤ logEN n := by
    rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnpos.ne', Real.log_exp]
    linarith
  have hscaled := mul_le_mul_of_nonneg_left
    (hlog.trans hlogEN) polynomialAlpha0_pos.le
  have hcancel : polynomialAlpha0 * (2 / polynomialAlpha0) = 2 := by
    field_simp [polynomialAlpha0_pos.ne']
  rw [hcancel] at hscaled
  exact hscaled

/-- If [the outcome scale satisfies its stated bound](hyp:hM), [for every cutoff choice, the
  concrete estimator is measurable, uses its declared zero fallback, and is clipped to the
  required range](goal). -/
lemma polyEstimator_total_and_clipped {n d N : ℕ} {M rho : ℝ} (hM : 0 ≤ M) :
    Measurable (rawPolyEstimator (n := n) (d := d) N rho M) ∧
      ∀ s : Fin n → Obs d,
        rawPolyEstimator (n := n) (d := d) N rho M s ∈ Icc (-M) M := by
  exact polyEstimator_admissible hM

/-- [One finite cutoff simultaneously supplies the degree side condition and, for every alphabet
  and scale, the total clipped estimator certificate used in the all-alphabet assembly](goal). -/
lemma polynomialCalibrationPackage :
    ∃ N : ℕ, ∀ n d : ℕ, ∀ M rho : ℝ,
      0 ≤ M →
      (N ≤ n ∧ (d : ℝ) ≤ rho * n * logEN n → 2 ≤ polynomialDegree n) ∧
      Measurable (rawPolyEstimator (n := n) (d := d) N rho M) ∧
      (∀ s : Fin n → Obs d,
        rawPolyEstimator (n := n) (d := d) N rho M s ∈ Icc (-M) M) := by
  obtain ⟨N, hN⟩ := polynomialDegree_eventually_two
  refine ⟨N, ?_⟩
  intro n d M rho hM
  obtain ⟨hmeas, hrange⟩ :=
    polyEstimator_total_and_clipped (n := n) (d := d) (N := N)
      (M := M) (rho := rho) hM
  exact ⟨fun hcalibrated => hN n hcalibrated.1, hmeas, hrange⟩

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
