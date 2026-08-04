import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Localization.BoundedLinearLocalization.Projection
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Localization.BoundedLinearLocalization.Zhao

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Arithmetic for the frozen localization constant
-/

namespace CausalSmith.Stat.ReverseKLTwoCoverage.BoundedLinearLocalizationArithmetic

open MeasureTheory
open scoped BigOperators

open CausalSmith.Stat.ReverseKLTwoCoverage.BoundedLinearLocalizationProjection
open CausalSmith.Stat.ReverseKLTwoCoverage.BoundedLinearLocalizationEntropy

variable {d n : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [LinearOrder 𝒳] [LinearOrder 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]

noncomputable def localizationRate (d n : ℕ) : ℝ :=
  d * Real.log (Real.exp 1 * n) + Real.log (2 * (n : ℝ) ^ 2)

noncomputable def localizationU (n : ℕ) : ℝ :=
  1 / (2 * n)

noncomputable def localizationDelta (n : ℕ) (hn : 0 < n) : ℝ :=
  failureProbability n hn / 4

lemma log_rate_identities (hn : 0 < n) :
    Real.log (Real.exp 1 * n) = 1 + Real.log n ∧
    Real.log (2 * (n : ℝ) ^ 2) =
      Real.log 2 + 2 * Real.log n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  constructor
  · rw [Real.log_mul (Real.exp_ne_zero 1) hn0, Real.log_exp]
  · rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (pow_ne_zero 2 hn0), Real.log_pow]
    ring

lemma localizationRate_pos
    (E : CommonExperiment d 𝒳 𝒜) (hn : 0 < n) :
    0 < localizationRate d n := by
  rcases log_rate_identities hn with ⟨hL, hQ⟩
  have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hd : (4 : ℝ) ≤ d := by exact_mod_cast E.dim_ge_four
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold localizationRate
  rw [hL, hQ]
  nlinarith

lemma localizationU_pos (hn : 0 < n) :
    0 < localizationU n := by
  unfold localizationU
  positivity

lemma localizationU_lt_one (hn : 0 < n) :
    localizationU n < 1 := by
  unfold localizationU
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply (div_lt_one (by positivity : (0 : ℝ) < 2 * n)).2
  nlinarith

lemma localizationDelta_pos (hn : 0 < n) :
    0 < localizationDelta n hn := by
  unfold localizationDelta failureProbability
  positivity

lemma localizationDelta_lt_one (hn : 0 < n) :
    localizationDelta n hn < 1 := by
  unfold localizationDelta failureProbability
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsquare : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hinv : ((n : ℝ) ^ 2)⁻¹ ≤ 1 :=
    (inv_le_one₀ (show 0 < (n : ℝ) ^ 2 by positivity)).2 hsquare
  linarith

lemma log_five_le_nine_fifths :
    Real.log 5 ≤ (9 : ℝ) / 5 := by
  have h08 := Real.sum_le_exp_of_nonneg
    (x := (4 : ℝ) / 5) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h08
  have he : (5 : ℝ) < Real.exp ((9 : ℝ) / 5) := by
    rw [show (9 : ℝ) / 5 = 1 + 4 / 5 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_gt_d9, Real.exp_pos ((4 : ℝ) / 5)]
  exact (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 5)).2 he.le

lemma projectionThreshold_le_rate
    (E : CommonExperiment d 𝒳 𝒜) (hn : 0 < n) :
    projectionThreshold d (localizationDelta n hn) ≤
      16 * localizationRate d n := by
  rcases log_rate_identities hn with ⟨hL, hQ⟩
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hd : (4 : ℝ) ≤ d := by exact_mod_cast E.dim_ge_four
  have hlog2hi : Real.log 2 < (7 : ℝ) / 10 := by
    exact Real.log_two_lt_d9.trans_le (by norm_num)
  have hdelta :
      2 / localizationDelta n hn = 8 * (n : ℝ) ^ 2 := by
    unfold localizationDelta failureProbability
    field_simp
    norm_num
  have hlog8 :
      Real.log (8 * (n : ℝ) ^ 2) =
        3 * Real.log 2 + 2 * Real.log n := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_mul
      (pow_ne_zero 3 (by norm_num : (2 : ℝ) ≠ 0))
      (pow_ne_zero 2 hn0), Real.log_pow, Real.log_pow]
    norm_num
  unfold projectionThreshold localizationRate
  rw [hdelta, hlog8, hL, hQ]
  nlinarith [mul_nonneg (sub_nonneg.mpr hd) hlogn,
    log_five_le_nine_fifths]

lemma projection_selected_le_rate
    (E : CommonExperiment d 𝒳 𝒜) (hn : 0 < n) :
    4 * ((n : ℝ)⁻¹ *
        projectionThreshold d (localizationDelta n hn)) ≤
      64 * localizationRate d n / n := by
  have hninv : 0 ≤ (n : ℝ)⁻¹ := by positivity
  have h := mul_le_mul_of_nonneg_left
    (projectionThreshold_le_rate E hn) hninv
  calc
    4 * ((n : ℝ)⁻¹ *
        projectionThreshold d (localizationDelta n hn)) ≤
      4 * ((n : ℝ)⁻¹ * (16 * localizationRate d n)) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 64 * localizationRate d n / n := by
      field_simp
      ring

lemma log_one_add_four_n_le
    (hn : 0 < n) :
    Real.log (1 + 4 * (n : ℝ)) ≤
      2 * Real.log (Real.exp 1 * n) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by positivity
  have harg : (0 : ℝ) < 1 + 4 * n := by positivity
  have hbase : (0 : ℝ) < Real.exp 1 * n := mul_pos (Real.exp_pos 1) hnpos
  have hnum :
      1 + 4 * (n : ℝ) ≤ (Real.exp 1 * n) ^ 2 := by
    have he : (5 : ℝ) ≤ (Real.exp 1) ^ 2 := by
      nlinarith [Real.exp_one_gt_d9]
    have hn2 : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg (n : ℝ)
    calc
      1 + 4 * (n : ℝ) ≤ 5 * (n : ℝ) ^ 2 := by nlinarith
      _ ≤ (Real.exp 1) ^ 2 * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right he hn2
      _ = (Real.exp 1 * n) ^ 2 := by ring
  calc
    Real.log (1 + 4 * (n : ℝ)) ≤
        Real.log ((Real.exp 1 * n) ^ 2) :=
      Real.log_le_log harg hnum
    _ = 2 * Real.log (Real.exp 1 * n) := by
      rw [Real.log_pow]
      norm_num

lemma zhaoLog_le
    (E : CommonExperiment d 𝒳 𝒜) (hn : 0 < n) :
    Real.log
        (2 * supCoveringNumber (predictionPolytope E) (localizationU n) /
          localizationDelta n hn) ≤
      2 * d * Real.log (Real.exp 1 * n) +
        3 * Real.log (2 * (n : ℝ) ^ 2) := by
  have hu := localizationU_pos hn
  have hcover := supCoveringNumber_le E (localizationU n) hu
  have hcoverPos := supCoveringNumber_pos E (localizationU n) hu
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hbase : 0 < (1 + 2 / localizationU n) ^ d := by
    positivity
  have hlogCover :
      Real.log (supCoveringNumber (predictionPolytope E) (localizationU n)) ≤
        d * Real.log (1 + 4 * (n : ℝ)) := by
    have hid : 1 + 2 / localizationU n = 1 + 4 * (n : ℝ) := by
      unfold localizationU
      field_simp
      ring
    have hlog := Real.log_le_log
      (by exact_mod_cast hcoverPos) hcover
    rw [Real.log_pow] at hlog
    simpa [hid] using hlog
  have hdelta :
      2 / localizationDelta n hn = 8 * (n : ℝ) ^ 2 := by
    unfold localizationDelta failureProbability
    field_simp
    norm_num
  have hlog8 :
      Real.log (8 * (n : ℝ) ^ 2) =
        3 * Real.log 2 + 2 * Real.log n := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_mul
      (pow_ne_zero 3 (by norm_num : (2 : ℝ) ≠ 0))
      (pow_ne_zero 2 hn0), Real.log_pow, Real.log_pow]
    norm_num
  have hQ := (log_rate_identities hn).2
  have hQnonneg : 0 ≤ Real.log (2 * (n : ℝ) ^ 2) :=
    Real.log_nonneg (by
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [sq_nonneg ((n : ℝ) - 1)])
  calc
    Real.log
        (2 * supCoveringNumber (predictionPolytope E) (localizationU n) /
          localizationDelta n hn) =
      Real.log (supCoveringNumber
        (predictionPolytope E) (localizationU n)) +
        Real.log (2 / localizationDelta n hn) := by
      rw [← Real.log_mul
        (Nat.cast_ne_zero.mpr hcoverPos.ne')
        (ne_of_gt (div_pos (by norm_num) (localizationDelta_pos hn)))]
      congr 1
      field_simp
    _ ≤ d * Real.log (1 + 4 * (n : ℝ)) +
        Real.log (8 * (n : ℝ) ^ 2) := by
      rw [hdelta]
      gcongr
    _ ≤ d * (2 * Real.log (Real.exp 1 * n)) +
        3 * Real.log (2 * (n : ℝ) ^ 2) := by
      have hone := log_one_add_four_n_le hn
      rw [hlog8, hQ]
      have hlogn := Real.log_natCast_nonneg n
      have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      nlinarith [mul_nonneg (Nat.cast_nonneg d)
        (sub_nonneg.mpr hone)]
    _ = 2 * d * Real.log (Real.exp 1 * n) +
        3 * Real.log (2 * (n : ℝ) ^ 2) := by ring

lemma zhaoRemainder_le_rate
    (E : CommonExperiment d 𝒳 𝒜) (hn : 0 < n) :
    32 / (3 * n) *
        Real.log
          (2 * supCoveringNumber (predictionPolytope E) (localizationU n) /
            localizationDelta n hn) +
        10 * localizationU n ≤
      35 * localizationRate d n / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog := zhaoLog_le E hn
  have hL : 1 ≤ Real.log (Real.exp 1 * n) := by
    rw [(log_rate_identities hn).1]
    exact le_add_of_nonneg_right (Real.log_natCast_nonneg n)
  have hQ : 0 ≤ Real.log (2 * (n : ℝ) ^ 2) :=
    Real.log_nonneg (by
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [sq_nonneg ((n : ℝ) - 1)])
  have hd : (4 : ℝ) ≤ d := by exact_mod_cast E.dim_ge_four
  unfold localizationU localizationRate
  have hscaled := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ (32 : ℝ) / 3 by norm_num)
  have hnum :
      (32 / 3) *
          Real.log
            (2 * supCoveringNumber
              (predictionPolytope E) (localizationU n) /
              localizationDelta n hn) + 5 ≤
        35 * localizationRate d n := by
    unfold localizationRate
    nlinarith [hscaled,
      mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hL)]
  calc
    32 / (3 * n) *
        Real.log
          (2 * supCoveringNumber (predictionPolytope E) (1 / (2 * n)) /
            localizationDelta n hn) +
        10 * (1 / (2 * n)) =
      ((32 / 3) *
          Real.log
            (2 * supCoveringNumber
              (predictionPolytope E) (localizationU n) /
              localizationDelta n hn) + 5) / n := by
        unfold localizationU
        field_simp
        ring
    _ ≤ (35 * localizationRate d n) / n :=
      div_le_div_of_nonneg_right hnum hnpos.le

end CausalSmith.Stat.ReverseKLTwoCoverage.BoundedLinearLocalizationArithmetic
