import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmHighDimensionalAssembly
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmParametric

/-!
# Scalar final assembly for the one-arm converse

This module combines a high-dimensional lower bound above a logarithmic
threshold with the parametric lower bound below that threshold.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

/-- A high-dimensional bound above `K (log n)^4`, together with the universal
parametric bound, implies the unchanged public Zeng one-arm gate. -/
theorem zengOneArmMinimaxLower_of_highDimensional
    {epsilon A K b : ℝ} {N₀ : ℕ}
    (hA : 0 < A) (hK : 0 < K) (hb : 0 < b)
    (hhigh : ∀ n d : ℕ, 0 < d → N₀ ≤ n →
      K * Real.log (n : ℝ) ^ 4 ≤ (d : ℝ) →
      (d : ℝ) ≤ b * n * Real.log n →
      A * ((d : ℝ) ^ 2 /
          ((n : ℝ) ^ 2 * Real.log (n : ℝ) ^ 2)) ≤
        oneArmMinimaxRisk n d epsilon) :
    ZengOneArmMinimaxLower epsilon := by
  rintro ⟨he0, hehalf⟩
  have heps : 0 < (1 / (K ^ 2 + 1) : ℝ) := by positivity
  have hlogReal :=
    (Real.isLittleO_pow_log_id_atTop (n := 6)).bound heps
  have hlogNat : ∀ᶠ n : ℕ in Filter.atTop,
      |Real.log (n : ℝ) ^ 6| ≤
        (1 / (K ^ 2 + 1) : ℝ) * |(n : ℝ)| :=
    tendsto_natCast_atTop_atTop.eventually hlogReal
  have hall : ∀ᶠ n : ℕ in Filter.atTop,
      max N₀ 3 ≤ n ∧
        |Real.log (n : ℝ) ^ 6| ≤
          (1 / (K ^ 2 + 1) : ℝ) * |(n : ℝ)| :=
    (Filter.eventually_ge_atTop (max N₀ 3)).and hlogNat
  rw [Filter.eventually_atTop] at hall
  obtain ⟨N, hN⟩ := hall
  refine ⟨min (1 / 200 : ℝ) (A / 2), b, N, ?_, hb, ?_⟩
  · exact lt_min (by norm_num) (by positivity)
  intro n d hd hn hcap
  obtain ⟨hnbase, hlogSmall⟩ := hN n hn
  have hnN₀ : N₀ ≤ n := (le_max_left N₀ 3).trans hnbase
  have hn3 : 3 ≤ n := (le_max_right N₀ 3).trans hnbase
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hparam := oneArm_parametric_lower he0 hehalf n d hnpos hd
  let a : ℝ := min (1 / 200 : ℝ) (A / 2)
  have ha0 : 0 ≤ a := (lt_min (by norm_num) (by positivity)).le
  have haParam : a ≤ 1 / 200 := min_le_left _ _
  have haHigh : a ≤ A / 2 := min_le_right _ _
  by_cases hdim : K * Real.log (n : ℝ) ^ 4 ≤ (d : ℝ)
  · have hhighRisk := hhigh n d hd hnN₀ hdim hcap
    have hparamHalf :
        a * (1 / (n : ℝ)) ≤
          (1 / (100 * (n : ℝ))) / 2 := by
      calc
        a * (1 / (n : ℝ)) ≤
            (1 / 200 : ℝ) * (1 / (n : ℝ)) := by gcongr
        _ = (1 / (100 * (n : ℝ))) / 2 := by field_simp; ring
    have hhighHalf :
        a * ((d : ℝ) ^ 2 /
            ((n : ℝ) ^ 2 * Real.log (n : ℝ) ^ 2)) ≤
          (A * ((d : ℝ) ^ 2 /
            ((n : ℝ) ^ 2 * Real.log (n : ℝ) ^ 2))) / 2 := by
      have hrate0 : 0 ≤ (d : ℝ) ^ 2 /
          ((n : ℝ) ^ 2 * Real.log (n : ℝ) ^ 2) := by positivity
      nlinarith
    unfold minimaxRate
    nlinarith
  · have hdim' : (d : ℝ) < K * Real.log (n : ℝ) ^ 4 :=
      lt_of_not_ge hdim
    have hlogSmall' : Real.log (n : ℝ) ^ 6 ≤
        (1 / (K ^ 2 + 1) : ℝ) * (n : ℝ) := by
      simpa [abs_of_nonneg (pow_nonneg hlogpos.le 6), abs_of_pos hnR] using
        hlogSmall
    have hfrac : K ^ 2 / (K ^ 2 + 1) ≤ (1 : ℝ) := by
      exact (div_le_one (by positivity)).2 (by linarith [sq_nonneg K])
    have hKlog : K ^ 2 * Real.log (n : ℝ) ^ 6 ≤ (n : ℝ) := by
      calc
        K ^ 2 * Real.log (n : ℝ) ^ 6 ≤
            K ^ 2 * ((1 / (K ^ 2 + 1)) * (n : ℝ)) := by
          gcongr
        _ = (K ^ 2 / (K ^ 2 + 1)) * (n : ℝ) := by ring
        _ ≤ n := mul_le_of_le_one_left hnR.le hfrac
    have hd0 : (0 : ℝ) ≤ d := by positivity
    have hthreshold0 : 0 ≤ K * Real.log (n : ℝ) ^ 4 := by positivity
    have hdsq : (d : ℝ) ^ 2 ≤
        K ^ 2 * Real.log (n : ℝ) ^ 8 := by
      nlinarith [sq_nonneg (K * Real.log (n : ℝ) ^ 4 - (d : ℝ))]
    have hdsq' : (d : ℝ) ^ 2 ≤
        (n : ℝ) * Real.log (n : ℝ) ^ 2 := by
      calc
        (d : ℝ) ^ 2 ≤ K ^ 2 * Real.log (n : ℝ) ^ 8 := hdsq
        _ = (K ^ 2 * Real.log (n : ℝ) ^ 6) *
            Real.log (n : ℝ) ^ 2 := by ring
        _ ≤ (n : ℝ) * Real.log (n : ℝ) ^ 2 := by gcongr
    have hrate : (d : ℝ) ^ 2 /
          ((n : ℝ) ^ 2 * Real.log (n : ℝ) ^ 2) ≤
        1 / (n : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hnR]
      nlinarith
    have htotal : minimaxRate n d ≤ 2 / (n : ℝ) := by
      calc
        minimaxRate n d = 1 / (n : ℝ) + (d : ℝ) ^ 2 /
            ((n : ℝ) ^ 2 * Real.log (n : ℝ) ^ 2) := rfl
        _ ≤ 1 / (n : ℝ) + 1 / (n : ℝ) := add_le_add_right hrate _
        _ = 2 / (n : ℝ) := by ring
    have hrateTotal0 : 0 ≤ minimaxRate n d := by
      unfold minimaxRate
      positivity
    have haRate : a * minimaxRate n d ≤ 1 / (100 * (n : ℝ)) := by
      calc
        a * minimaxRate n d ≤
            (1 / 200 : ℝ) * minimaxRate n d :=
          mul_le_mul_of_nonneg_right haParam hrateTotal0
        _ ≤ (1 / 200 : ℝ) * (2 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left htotal (by norm_num)
        _ = 1 / (100 * (n : ℝ)) := by field_simp; ring
    simpa [a] using haRate.trans hparam

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
