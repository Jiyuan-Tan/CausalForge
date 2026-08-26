/- Fallback-risk and clipping facts for the polynomial estimator. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.Calibration

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory Set

/-- If [the indicated calibration branch applies](hyp:hbranch), [outside the calibrated
  sample-size/alphabet branch, the declared zero fallback has squared risk at most `M²`](goal). -/
lemma polyEstimator_fallback_mse_le {n d N : ℕ} {epsilon M sigma rho : ℝ}
    (P : ModelClass d epsilon M sigma)
    (hbranch : ¬(N ≤ n ∧ (d : ℝ) ≤ rho * n * logEN n)) :
    mse P.law (rawPolyEstimator (n := n) (d := d) N rho M) ≤ M ^ 2 := by
  have hraw : |rawAteFormula P.law| ≤ M := by
    let Q : UnrestrictedClass d epsilon M :=
      { law := P.law
        epsilon_pos := P.epsilon_pos
        epsilon_lt_half := P.epsilon_lt_half
        M_ge_one := P.M_ge_one
        consistency := P.consistency
        exchangeability := P.exchangeability
        overlap := P.overlap
        mean_normalization := P.mean_normalization
        second_moment := P.second_moment }
    exact scale_sanity.1 Q |>.2.1
  have hsqAbs : |rawAteFormula P.law| ^ 2 ≤ M ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (le_trans zero_le_one P.M_ge_one)).2 hraw
  have hsq : (rawAteFormula P.law) ^ 2 ≤ M ^ 2 := by
    simpa [sq_abs] using hsqAbs
  unfold mse rawPolyEstimator
  simp_rw [if_neg hbranch]
  simp only [zero_sub, neg_sq]
  simpa using hsq

/-- If [the tuning radius satisfies the stated restriction](hyp:hrho), [for fixed positive
  alphabet cutoff, the zero fallback already satisfies the paper's capped polynomial rate on every
  uncalibrated branch](goal). -/
lemma polyEstimator_uncalibrated_rate {N : ℕ} {rho : ℝ} (hrho : 0 < rho) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n d : ℕ} {epsilon M sigma : ℝ},
        0 < n → 0 < d →
        ¬(N ≤ n ∧ (d : ℝ) ≤ rho * n * logEN n) →
        ∀ P : ModelClass d epsilon M sigma,
          mse P.law (rawPolyEstimator (n := n) (d := d) N rho M) ≤
            C * M ^ 2 *
              (1 / (n : ℝ) + min 1 (polynomialComponent n d)) := by
  let q : ℝ := min 1 (rho ^ 2)
  have hq : 0 < q := lt_min zero_lt_one (sq_pos_of_pos hrho)
  let C : ℝ := (N : ℝ) + 1 + 1 / q
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro n d epsilon M sigma hn hd hbranch P
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hlog : 0 < logEN n := by
    rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnR.ne', Real.log_exp]
    have hn_one : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn_one
    linarith
  have hpoly : 0 ≤ polynomialComponent n d := by
    unfold polynomialComponent
    positivity
  have hrate : 0 ≤ 1 / (n : ℝ) + min 1 (polynomialComponent n d) := by
    positivity
  have hfallback := polyEstimator_fallback_mse_le P hbranch
  apply hfallback.trans
  have hC0 : 0 ≤ C := hC.le
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  suffices hone : 1 ≤ C *
      (1 / (n : ℝ) + min 1 (polynomialComponent n d)) by
    calc
      M ^ 2 = M ^ 2 * 1 := by ring
      _ ≤ M ^ 2 * (C *
          (1 / (n : ℝ) + min 1 (polynomialComponent n d))) :=
        mul_le_mul_of_nonneg_left hone hM2
      _ = C * M ^ 2 *
          (1 / (n : ℝ) + min 1 (polynomialComponent n d)) := by ring
  rcases not_and_or.mp hbranch with hsmall | hlarge
  · have hnN : n < N := Nat.lt_of_not_ge hsmall
    have hnC : (n : ℝ) ≤ C := by
      have hnNreal : (n : ℝ) < N := by exact_mod_cast hnN
      dsimp [C]
      have hqinv : 0 < 1 / q := by positivity
      linarith
    have hone' : 1 ≤ C * (1 / (n : ℝ)) := by
      rw [mul_one_div]
      exact (le_div_iff₀ hnR).2 (by simpa [one_mul] using hnC)
    have hmin0 : 0 ≤ min 1 (polynomialComponent n d) :=
      le_min zero_le_one hpoly
    nlinarith
  · have hlarge' : rho * (n : ℝ) * logEN n < (d : ℝ) :=
      lt_of_not_ge hlarge
    have hleft : 0 < rho * (n : ℝ) * logEN n :=
      mul_pos (mul_pos hrho hnR) hlog
    have hfactor : 0 <
        ((d : ℝ) - rho * (n : ℝ) * logEN n) *
          ((d : ℝ) + rho * (n : ℝ) * logEN n) :=
      mul_pos (sub_pos.mpr hlarge') (add_pos hdR hleft)
    have hsquare : rho ^ 2 * (n : ℝ) ^ 2 * logEN n ^ 2 < (d : ℝ) ^ 2 := by
      nlinarith
    have hden : 0 < (n : ℝ) ^ 2 * logEN n ^ 2 := mul_pos (sq_pos_of_pos hnR)
      (sq_pos_of_pos hlog)
    have hrho_poly : rho ^ 2 < polynomialComponent n d := by
      unfold polynomialComponent
      rw [lt_div_iff₀ hden]
      nlinarith
    have hqpoly : q ≤ min 1 (polynomialComponent n d) := by
      exact min_le_min (le_refl 1) hrho_poly.le
    have hCq : 1 / q ≤ C := by
      dsimp [C]
      have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    have hone' : 1 ≤ C * min 1 (polynomialComponent n d) := by
      calc
        1 = (1 / q) * q := by field_simp [hq.ne']
        _ ≤ C * min 1 (polynomialComponent n d) :=
          mul_le_mul hCq hqpoly hq.le (by positivity)
    have hninv0 : 0 ≤ 1 / (n : ℝ) := by positivity
    nlinarith

-- @node: clip_normalized_sq_error_le
/-- If [the target lies in the clipping interval](hyp:ht), [clipping a normalized estimate to
  `[-1,1]` cannot increase squared loss against a normalized target already in that
  interval](goal). -/
lemma clip_normalized_sq_error_le (x t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
    (clip (-1) 1 x - t) ^ 2 ≤ (x - t) ^ 2 := by
  rcases ht with ⟨htl, htu⟩
  unfold clip
  by_cases hxlow : x ≤ -1
  · rw [min_eq_right (hxlow.trans (by norm_num : (-1 : ℝ) ≤ 1)),
      max_eq_left hxlow]
    nlinarith [sq_nonneg (x - t)]
  · have hxlow' : -1 ≤ x := le_of_not_ge hxlow
    rw [max_eq_right (le_min (by norm_num) hxlow')]
    by_cases hxhigh : x ≤ 1
    · rw [min_eq_right hxhigh]
    · rw [min_eq_left (le_of_not_ge hxhigh)]
      nlinarith [sq_nonneg (x - t)]

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
