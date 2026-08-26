/- Scalar closure of the explicit deterministic-branch terms. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.FixedBranchRate
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.RateAlgebra

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

/-- If [the sample size satisfies the stated lower bound](hyp:hn) and [the overlap constant is
  positive](hyp:hepsilon), [the missing-mass term is bounded by the polynomial rate
  component](goal). -/
lemma polynomial_missing_term_le_component {n d : ℕ} {epsilon : ℝ}
    (hn : 8 ≤ n) (hepsilon : 0 < epsilon) :
    ((d : ℝ) /
      (((((n - n / 2 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) *
        polynomialPilotLowerBand n)) ^ 2 ≤
      (1 / (16 * epsilon ^ 4)) * polynomialComponent n d := by
  have hnpos : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hL : 0 < logEN n := zero_lt_one.trans_le (one_le_logEN hnpos)
  have hD := polynomial_pilot_denominator_ge (epsilon := epsilon) hn hepsilon
  change 4 * (n : ℝ) * epsilon ^ 2 * logEN n ≤
      (((((n - n / 2 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) *
        polynomialPilotLowerBand n) at hD
  have hDpos : 0 < (((((n - n / 2 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) *
      polynomialPilotLowerBand n) := lt_of_lt_of_le (by positivity) hD
  have hfrac : (d : ℝ) /
      (((((n - n / 2 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) *
        polynomialPilotLowerBand n) ≤
      (d : ℝ) / (4 * (n : ℝ) * epsilon ^ 2 * logEN n) := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hD
  have hfrac0 : 0 ≤ (d : ℝ) /
      (((((n - n / 2 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) *
        polynomialPilotLowerBand n) := by positivity
  have hsquare := sq_le_sq₀ hfrac0 (by positivity) |>.2 hfrac
  apply hsquare.trans_eq
  unfold polynomialComponent
  field_simp [hnR.ne', hL.ne', hepsilon.ne']
  ring

/-- If [the sample is nonempty](hyp:hn) and [the overlap constant is positive](hyp:hepsilon) and
  [the polynomial or elbow parameter satisfies its stated bound](hyp:hK), [the polynomial
  approximation bias term is bounded by the polynomial rate component](goal). -/
lemma polynomial_bias_term_le_component {n d : ℕ} {epsilon : ℝ}
    (hn : 0 < n) (hepsilon : 0 < epsilon)
    (hK : 2 ≤ polynomialDegree n) :
    ((d : ℝ) * ((4096 * logEN n / (n - n / 2 : ℕ)) /
      (epsilon * (polynomialDegree n : ℝ) ^ 2))) ^ 2 ≤
      (32768 / (epsilon * polynomialAlpha0 ^ 2)) ^ 2 *
        polynomialComponent n d := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hL : 0 < logEN n := zero_lt_one.trans_le (one_le_logEN hn)
  have ha := polynomialAlpha0_pos
  have hB := polynomial_lightScale_le hn
  have hKlower := polynomialDegree_cast_lower hK
  have hKsq : (polynomialAlpha0 * logEN n / 2) ^ 2 ≤
      (polynomialDegree n : ℝ) ^ 2 := by
    have hleft : 0 ≤ polynomialAlpha0 * logEN n / 2 := by positivity
    exact (sq_le_sq₀ hleft (by positivity)).2 hKlower
  have hden : 0 < epsilon * (polynomialDegree n : ℝ) ^ 2 := by
    have : 0 < (polynomialDegree n : ℝ) := by exact_mod_cast (by omega : 0 < polynomialDegree n)
    positivity
  have hq : 4096 * logEN n / (n - n / 2 : ℕ) /
      (epsilon * (polynomialDegree n : ℝ) ^ 2) ≤
      32768 / (epsilon * polynomialAlpha0 ^ 2 * (n : ℝ) * logEN n) := by
    apply (div_le_iff₀ hden).2
    calc
      4096 * logEN n / (n - n / 2 : ℕ) ≤
          8192 * logEN n / (n : ℝ) := hB
      _ = (32768 / (epsilon * polynomialAlpha0 ^ 2 * (n : ℝ) * logEN n)) *
          (epsilon * (polynomialAlpha0 * logEN n / 2) ^ 2) := by
        field_simp [hnR.ne', hL.ne', hepsilon.ne', ha.ne']
        ring
      _ ≤ (32768 / (epsilon * polynomialAlpha0 ^ 2 * (n : ℝ) * logEN n)) *
          (epsilon * (polynomialDegree n : ℝ) ^ 2) := by
        gcongr
  have hmul := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ d)
  have hsquare := (sq_le_sq₀ (by positivity) (by positivity)).2 hmul
  apply hsquare.trans_eq
  unfold polynomialComponent
  field_simp [hnR.ne', hL.ne', hepsilon.ne', ha.ne']

/-- If [the sample is nonempty](hyp:hn) and [the stated llarge condition holds](hyp:hLlarge), [the
  linear light-cell variance term is bounded by the target polynomial rate](goal). -/
lemma polynomial_linear_light_term_le_rate {n d : ℕ} (hn : 0 < n)
    (hLlarge : 240 ≤ logEN n) :
    (6 : ℝ) ^ (2 * polynomialDegree n) * (d : ℝ) *
        (4096 * logEN n / (n - n / 2 : ℕ)) ^ 2 ≤
      8192 ^ 2 * (1 / (n : ℝ) + polynomialComponent n d) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hL : 0 < logEN n := by linarith
  have hB := polynomial_lightScale_le hn
  have hB0 : 0 ≤ 4096 * logEN n / (n - n / 2 : ℕ) := by positivity
  have hBsq := (sq_le_sq₀ hB0 (by positivity)).2 hB
  have hgrowth : ((6 : ℝ) ^ (2 * polynomialDegree n)) ^ 2 *
      logEN n ^ 6 ≤ n := by
    rw [show ((6 : ℝ) ^ (2 * polynomialDegree n)) ^ 2 =
        (6 : ℝ) ^ (4 * polynomialDegree n) by
      calc
        ((6 : ℝ) ^ (2 * polynomialDegree n)) ^ 2 =
            (6 : ℝ) ^ ((2 * polynomialDegree n) * 2) :=
          (pow_mul _ _ _).symm
        _ = (6 : ℝ) ^ (4 * polynomialDegree n) := by
          congr 1
          omega]
    exact polynomial_log_growth_four hn hLlarge
  have hcore := polynomial_linear_dimension_term_le_rate
    (A := (6 : ℝ) ^ (2 * polynomialDegree n))
    (n := (n : ℝ)) (d := (d : ℝ)) (L := logEN n) hnR hL hgrowth
  calc
    (6 : ℝ) ^ (2 * polynomialDegree n) * (d : ℝ) *
        (4096 * logEN n / (n - n / 2 : ℕ)) ^ 2 ≤
      (6 : ℝ) ^ (2 * polynomialDegree n) * (d : ℝ) *
        (8192 * logEN n / (n : ℝ)) ^ 2 := by gcongr
    _ = 8192 ^ 2 * ((6 : ℝ) ^ (2 * polynomialDegree n) *
        (d : ℝ) * logEN n ^ 2 / (n : ℝ) ^ 2) := by
      field_simp [hnR.ne']
    _ ≤ 8192 ^ 2 * (1 / (n : ℝ) +
        (d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * logEN n ^ 2)) := by gcongr
    _ = 8192 ^ 2 * (1 / (n : ℝ) + polynomialComponent n d) := by
      rfl

/-- If [the sample is nonempty](hyp:hn) and [the stated llarge condition holds](hyp:hLlarge), [the
  quadratic light-cell variance term is bounded by the polynomial rate component](goal). -/
lemma polynomial_quadratic_light_term_le_component {n d : ℕ} (hn : 0 < n)
    (hLlarge : 240 ≤ logEN n) :
    (6 : ℝ) ^ (2 * polynomialDegree n) * (d : ℝ) ^ 2 *
        polynomialDegree n ^ 2 *
        (4096 * logEN n / (n - n / 2 : ℕ)) ^ 2 /
          (n - n / 2 : ℕ) ≤
      (2 * 8192 ^ 2) * polynomialComponent n d := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hL : 0 < logEN n := by linarith
  have hmR : 0 < ((n - n / 2 : ℕ) : ℝ) := by
    exact_mod_cast polynomial_estimationBlock_pos hn
  have hK := polynomialDegree_cast_le_logEN hn
  have hKsq : (polynomialDegree n : ℝ) ^ 2 ≤ logEN n ^ 2 := by
    exact (sq_le_sq₀ (by positivity) hL.le).2 hK
  have hB := polynomial_lightScale_le hn
  have hBsq := (sq_le_sq₀ (by positivity) (by positivity)).2 hB
  have hinv : (1 : ℝ) / (n - n / 2 : ℕ) ≤ 2 / (n : ℝ) := by
    apply (div_le_div_iff₀ hmR hnR).2
    have htwice : n ≤ 2 * (n - n / 2) := by omega
    have htwiceR : (n : ℝ) ≤ 2 * ((n - n / 2 : ℕ) : ℝ) := by
      exact_mod_cast htwice
    nlinarith
  have hgrowth := polynomial_log_growth_two hn hLlarge
  have hcore := polynomial_quadratic_dimension_term_le_rate
    (A := (6 : ℝ) ^ (2 * polynomialDegree n))
    (n := (n : ℝ)) (d := (d : ℝ)) (L := logEN n) hnR hL hgrowth
  calc
    (6 : ℝ) ^ (2 * polynomialDegree n) * (d : ℝ) ^ 2 *
        polynomialDegree n ^ 2 *
        (4096 * logEN n / (n - n / 2 : ℕ)) ^ 2 /
          (n - n / 2 : ℕ) ≤
      (6 : ℝ) ^ (2 * polynomialDegree n) * (d : ℝ) ^ 2 *
        logEN n ^ 2 * (8192 * logEN n / (n : ℝ)) ^ 2 *
          (2 / (n : ℝ)) := by
      rw [div_eq_mul_inv]
      gcongr
      simpa [one_div] using hinv
    _ = (2 * 8192 ^ 2) *
        ((6 : ℝ) ^ (2 * polynomialDegree n) * (d : ℝ) ^ 2 *
          logEN n ^ 4 / (n : ℝ) ^ 3) := by
      field_simp [hnR.ne']
    _ ≤ (2 * 8192 ^ 2) *
        ((d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * logEN n ^ 2)) := by gcongr
    _ = (2 * 8192 ^ 2) * polynomialComponent n d := by rfl

-- @node: polynomial_uniformBranch_expression_le_rate
/-- If [the sample size satisfies the stated lower bound](hyp:hn) and [the overlap constant is
  positive](hyp:hepsilon) and [the stated c condition holds](hyp:hC) and [the polynomial or elbow
  parameter satisfies its stated bound](hyp:hK) and [the stated llarge condition
  holds](hyp:hLlarge), [the complete uniform branchwise error expression is bounded by the target
  polynomial rate](goal). -/
lemma polynomial_uniformBranch_expression_le_rate {n d : ℕ} {epsilon C : ℝ}
    (hn : 8 ≤ n) (hepsilon : 0 < epsilon) (hC : 0 < C)
    (hK : 2 ≤ polynomialDegree n) (hLlarge : 240 ≤ logEN n) :
    8 * (8 / (((n - n / 2 : ℕ) : ℝ) * epsilon) +
      6 / (n - n / 2 : ℕ) +
      4 * ((d : ℝ) /
        (((((n - n / 2 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) *
          polynomialPilotLowerBand n)) ^ 2) +
    2 * (C / (n - n / 2 : ℕ) +
      C * 6 ^ (2 * polynomialDegree n) *
        ((d : ℝ) * (4096 * logEN n / (n - n / 2 : ℕ)) ^ 2 +
          (d : ℝ) ^ 2 * polynomialDegree n ^ 2 *
            (4096 * logEN n / (n - n / 2 : ℕ)) ^ 2 /
              (n - n / 2 : ℕ)) +
      ((d : ℝ) * ((4096 * logEN n / (n - n / 2 : ℕ)) /
        (epsilon * (polynomialDegree n : ℝ) ^ 2))) ^ 2) ≤
      (128 / epsilon + 96 + 2 / epsilon ^ 4 + 4 * C +
        6 * C * 8192 ^ 2 +
        2 * (32768 / (epsilon * polynomialAlpha0 ^ 2)) ^ 2) *
          (1 / (n : ℝ) + polynomialComponent n d) := by
  have hnpos : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hmR : 0 < ((n - n / 2 : ℕ) : ℝ) := by
    exact_mod_cast polynomial_estimationBlock_pos hnpos
  have htwice : n ≤ 2 * (n - n / 2) := by omega
  have htwiceR : (n : ℝ) ≤ 2 * ((n - n / 2 : ℕ) : ℝ) := by
    exact_mod_cast htwice
  have hinv : (1 : ℝ) / (n - n / 2 : ℕ) ≤ 2 / (n : ℝ) := by
    apply (div_le_div_iff₀ hmR hnR).2
    nlinarith
  have hrate0 : 0 ≤ 1 / (n : ℝ) + polynomialComponent n d := by
    unfold polynomialComponent
    positivity
  have hinvRate : (1 : ℝ) / (n - n / 2 : ℕ) ≤
      2 * (1 / (n : ℝ) + polynomialComponent n d) := by
    have hc : 0 ≤ polynomialComponent n d := by
      unfold polynomialComponent
      positivity
    have hb : 1 / (n : ℝ) ≤
        1 / (n : ℝ) + polynomialComponent n d :=
      le_add_of_nonneg_right hc
    have hs : (2 : ℝ) * (1 / (n : ℝ)) ≤
        2 * (1 / (n : ℝ) + polynomialComponent n d) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    calc
      (1 : ℝ) / (n - n / 2 : ℕ) ≤ 2 / (n : ℝ) := hinv
      _ = 2 * (1 / (n : ℝ)) := by ring
      _ ≤ 2 * (1 / (n : ℝ) + polynomialComponent n d) := hs
  have hinvEps : 1 / (((n - n / 2 : ℕ) : ℝ) * epsilon) ≤
      (2 / epsilon) * (1 / (n : ℝ) + polynomialComponent n d) := by
    have he : 0 < ((n - n / 2 : ℕ) : ℝ) * epsilon := mul_pos hmR hepsilon
    have heq : 1 / (((n - n / 2 : ℕ) : ℝ) * epsilon) =
        (1 / epsilon) * (1 / ((n - n / 2 : ℕ) : ℝ)) := by
      field_simp [hmR.ne', hepsilon.ne']
    rw [heq]
    have hmul : (1 / epsilon) * (1 / ((n - n / 2 : ℕ) : ℝ)) ≤
        (1 / epsilon) *
          (2 * (1 / (n : ℝ) + polynomialComponent n d)) :=
      mul_le_mul_of_nonneg_left hinvRate (by positivity)
    calc
      (1 / epsilon) * (1 / ((n - n / 2 : ℕ) : ℝ)) ≤
          (1 / epsilon) *
            (2 * (1 / (n : ℝ) + polynomialComponent n d)) :=
        hmul
      _ = (2 / epsilon) *
          (1 / (n : ℝ) + polynomialComponent n d) := by ring
  have hmissing := polynomial_missing_term_le_component
    (n := n) (d := d) hn hepsilon
  have hlinear := polynomial_linear_light_term_le_rate
    (n := n) (d := d) hnpos hLlarge
  have hquad := polynomial_quadratic_light_term_le_component
    (n := n) (d := d) hnpos hLlarge
  have hbias := polynomial_bias_term_le_component
    (n := n) (d := d) hnpos hepsilon hK
  have hparam1 : 8 * (8 / (((n - n / 2 : ℕ) : ℝ) * epsilon)) ≤
      (128 / epsilon) * (1 / (n : ℝ) + polynomialComponent n d) := by
    calc
      8 * (8 / (((n - n / 2 : ℕ) : ℝ) * epsilon)) =
          64 * (1 / (((n - n / 2 : ℕ) : ℝ) * epsilon)) := by ring
      _ ≤ 64 * ((2 / epsilon) *
          (1 / (n : ℝ) + polynomialComponent n d)) :=
        mul_le_mul_of_nonneg_left hinvEps (by norm_num)
      _ = _ := by ring
  have hparam2 : 8 * (6 / ((n - n / 2 : ℕ) : ℝ)) ≤
      96 * (1 / (n : ℝ) + polynomialComponent n d) := by
    calc
      8 * (6 / ((n - n / 2 : ℕ) : ℝ)) =
          48 * (1 / ((n - n / 2 : ℕ) : ℝ)) := by ring
      _ ≤ 48 * (2 * (1 / (n : ℝ) + polynomialComponent n d)) :=
        mul_le_mul_of_nonneg_left hinvRate (by norm_num)
      _ = _ := by ring
  have hmissing' : 8 * 4 * ((d : ℝ) /
      (((((n - n / 2 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) *
        polynomialPilotLowerBand n)) ^ 2 ≤
      (2 / epsilon ^ 4) * (1 / (n : ℝ) + polynomialComponent n d) := by
    have he4 : 0 < epsilon ^ 4 := pow_pos hepsilon 4
    have hc : 0 ≤ polynomialComponent n d := by
      unfold polynomialComponent
      positivity
    calc
      8 * 4 * ((d : ℝ) /
          (((((n - n / 2 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) *
            polynomialPilotLowerBand n)) ^ 2 =
          32 * ((d : ℝ) /
          (((((n - n / 2 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) *
            polynomialPilotLowerBand n)) ^ 2 := by ring
      _ ≤ 32 * ((1 / (16 * epsilon ^ 4)) * polynomialComponent n d) :=
        mul_le_mul_of_nonneg_left hmissing (by norm_num)
      _ = (2 / epsilon ^ 4) * polynomialComponent n d := by
        field_simp [he4.ne']
        ring
      _ ≤ (2 / epsilon ^ 4) *
          (1 / (n : ℝ) + polynomialComponent n d) := by
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (by positivity : 0 ≤ 1 / (n : ℝ)))
          (by positivity)
  have hCparam : 2 * (C / ((n - n / 2 : ℕ) : ℝ)) ≤
      (4 * C) * (1 / (n : ℝ) + polynomialComponent n d) := by
    have := mul_le_mul_of_nonneg_left hinvRate hC.le
    rw [show C / ((n - n / 2 : ℕ) : ℝ) =
      C * (1 / ((n - n / 2 : ℕ) : ℝ)) by ring]
    nlinarith
  have hlinear' : 2 * C *
      ((6 : ℝ) ^ (2 * polynomialDegree n) * (d : ℝ) *
        (4096 * logEN n / (n - n / 2 : ℕ)) ^ 2) ≤
      (2 * C * 8192 ^ 2) *
        (1 / (n : ℝ) + polynomialComponent n d) := by
    calc
      _ ≤ (2 * C) * (8192 ^ 2 *
          (1 / (n : ℝ) + polynomialComponent n d)) :=
        mul_le_mul_of_nonneg_left hlinear (mul_nonneg (by norm_num) hC.le)
      _ = _ := by ring
  have hquad' : 2 * C *
      ((6 : ℝ) ^ (2 * polynomialDegree n) * (d : ℝ) ^ 2 *
        polynomialDegree n ^ 2 *
        (4096 * logEN n / (n - n / 2 : ℕ)) ^ 2 /
          (n - n / 2 : ℕ)) ≤
      (4 * C * 8192 ^ 2) *
        (1 / (n : ℝ) + polynomialComponent n d) := by
    calc
      _ ≤ (2 * C) * ((2 * 8192 ^ 2) * polynomialComponent n d) :=
        mul_le_mul_of_nonneg_left hquad (mul_nonneg (by norm_num) hC.le)
      _ ≤ (4 * C * 8192 ^ 2) *
          (1 / (n : ℝ) + polynomialComponent n d) := by
        have hp : 0 ≤ 1 / (n : ℝ) := by positivity
        nlinarith
  have hbias' : 2 * ((d : ℝ) *
      ((4096 * logEN n / (n - n / 2 : ℕ)) /
        (epsilon * (polynomialDegree n : ℝ) ^ 2))) ^ 2 ≤
      (2 * (32768 / (epsilon * polynomialAlpha0 ^ 2)) ^ 2) *
        (1 / (n : ℝ) + polynomialComponent n d) := by
    have hc := mul_le_mul_of_nonneg_left hbias (by norm_num : (0 : ℝ) ≤ 2)
    have hp : 0 ≤ 1 / (n : ℝ) := by positivity
    nlinarith
  calc
    8 * (8 / (((n - n / 2 : ℕ) : ℝ) * epsilon) +
        6 / (n - n / 2 : ℕ) +
        4 * ((d : ℝ) /
          (((((n - n / 2 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) *
            polynomialPilotLowerBand n)) ^ 2) +
      2 * (C / (n - n / 2 : ℕ) +
        C * 6 ^ (2 * polynomialDegree n) *
          ((d : ℝ) * (4096 * logEN n / (n - n / 2 : ℕ)) ^ 2 +
            (d : ℝ) ^ 2 * polynomialDegree n ^ 2 *
              (4096 * logEN n / (n - n / 2 : ℕ)) ^ 2 /
                (n - n / 2 : ℕ)) +
        ((d : ℝ) * ((4096 * logEN n / (n - n / 2 : ℕ)) /
          (epsilon * (polynomialDegree n : ℝ) ^ 2))) ^ 2) =
      8 * (8 / (((n - n / 2 : ℕ) : ℝ) * epsilon)) +
      8 * (6 / ((n - n / 2 : ℕ) : ℝ)) +
      8 * 4 * ((d : ℝ) /
        (((((n - n / 2 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) *
          polynomialPilotLowerBand n)) ^ 2 +
      2 * (C / ((n - n / 2 : ℕ) : ℝ)) +
      2 * C * ((6 : ℝ) ^ (2 * polynomialDegree n) * (d : ℝ) *
        (4096 * logEN n / (n - n / 2 : ℕ)) ^ 2) +
      2 * C * ((6 : ℝ) ^ (2 * polynomialDegree n) * (d : ℝ) ^ 2 *
        polynomialDegree n ^ 2 *
        (4096 * logEN n / (n - n / 2 : ℕ)) ^ 2 /
          (n - n / 2 : ℕ)) +
      2 * ((d : ℝ) * ((4096 * logEN n / (n - n / 2 : ℕ)) /
        (epsilon * (polynomialDegree n : ℝ) ^ 2))) ^ 2 := by ring
    _ ≤ (128 / epsilon) * (1 / (n : ℝ) + polynomialComponent n d) +
        96 * (1 / (n : ℝ) + polynomialComponent n d) +
        (2 / epsilon ^ 4) * (1 / (n : ℝ) + polynomialComponent n d) +
        (4 * C) * (1 / (n : ℝ) + polynomialComponent n d) +
        (2 * C * 8192 ^ 2) * (1 / (n : ℝ) + polynomialComponent n d) +
        (4 * C * 8192 ^ 2) * (1 / (n : ℝ) + polynomialComponent n d) +
        (2 * (32768 / (epsilon * polynomialAlpha0 ^ 2)) ^ 2) *
          (1 / (n : ℝ) + polynomialComponent n d) := by
      exact add_le_add (add_le_add (add_le_add (add_le_add
        (add_le_add (add_le_add hparam1 hparam2) hmissing') hCparam)
        hlinear') hquad') hbias'
    _ = _ := by ring

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
