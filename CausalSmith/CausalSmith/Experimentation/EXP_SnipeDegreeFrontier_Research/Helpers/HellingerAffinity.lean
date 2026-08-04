import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LeastFavourable
import Causalean.Stat.Minimax.HellingerAffinity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Affinity defect of the cosine-squared least-favourable pair

The general common-density affinity interface (`densityAffinity`, `hellingerSqDensity`,
their identity, the total-variation comparison, and product tensorization) now lives in
`Causalean/Stat/Minimax/HellingerAffinity.lean`; this file re-exports it and adds the
computation specific to this run's least-favourable prior: the exact affinity of two
translates of the cosine-squared bump `cosSqDensity`, and the resulting quadratic bound on
its affinity defect.
-/

open scoped BigOperators ENNReal
open MeasureTheory
open Causalean.Stat

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

/-- Establishes the stated mathematical result for cos sq density affinity formula. -/
lemma cosSqDensity_affinity_formula
    (s a b : ℝ) (hs : 0 < s) (hab : a ≤ b) (hgap : b - a < s) :
    ∫ u, Real.sqrt
        (cosSqDensity s (u - a) * cosSqDensity s (u - b)) =
      (1 - (b - a) / (2 * s)) *
          Real.cos (Real.pi * (b - a) / (2 * s)) +
        Real.sin (Real.pi * (b - a) / (2 * s)) / Real.pi := by
  let k : ℝ := Real.pi / (2 * s)
  have hk : 0 < k := by dsimp [k]; positivity
  have hk0 : k ≠ 0 := ne_of_gt hk
  have hks : k * s = Real.pi / 2 := by
    dsimp [k]
    field_simp
  let F : ℝ → ℝ := fun u =>
    s⁻¹ * Real.cos (k * (u - a)) * Real.cos (k * (u - b))
  have hfun :
      (fun u => Real.sqrt
        (cosSqDensity s (u - a) * cosSqDensity s (u - b))) =
      Set.indicator (Set.Icc (b - s) (a + s)) F := by
    funext u
    by_cases hu : u ∈ Set.Icc (b - s) (a + s)
    · have hua : |u - a| ≤ s := by
        rw [abs_le]
        constructor <;> linarith [hu.1, hu.2]
      have hub : |u - b| ≤ s := by
        rw [abs_le]
        constructor <;> linarith [hu.1, hu.2]
      rw [Set.indicator_of_mem hu, cosSqDensity, if_pos hua,
        cosSqDensity, if_pos hub]
      have hanga : -(Real.pi / 2) ≤ k * (u - a) ∧
          k * (u - a) ≤ Real.pi / 2 := by
        rw [abs_le] at hua
        constructor
        · calc
            -(Real.pi / 2) = k * (-s) := by rw [mul_neg, hks]
            _ ≤ k * (u - a) :=
              mul_le_mul_of_nonneg_left hua.1 (le_of_lt hk)
        · calc
            k * (u - a) ≤ k * s :=
              mul_le_mul_of_nonneg_left hua.2 (le_of_lt hk)
            _ = Real.pi / 2 := hks
      have hangb : -(Real.pi / 2) ≤ k * (u - b) ∧
          k * (u - b) ≤ Real.pi / 2 := by
        rw [abs_le] at hub
        constructor
        · calc
            -(Real.pi / 2) = k * (-s) := by rw [mul_neg, hks]
            _ ≤ k * (u - b) :=
              mul_le_mul_of_nonneg_left hub.1 (le_of_lt hk)
        · calc
            k * (u - b) ≤ k * s :=
              mul_le_mul_of_nonneg_left hub.2 (le_of_lt hk)
            _ = Real.pi / 2 := hks
      have hcosa : 0 ≤ Real.cos (k * (u - a)) :=
        Real.cos_nonneg_of_mem_Icc hanga
      have hcosb : 0 ≤ Real.cos (k * (u - b)) :=
        Real.cos_nonneg_of_mem_Icc hangb
      dsimp [F]
      rw [show
        s⁻¹ * Real.cos (Real.pi * (u - a) / (2 * s)) ^ 2 *
            (s⁻¹ * Real.cos (Real.pi * (u - b) / (2 * s)) ^ 2) =
          (s⁻¹ * Real.cos (k * (u - a)) *
            Real.cos (k * (u - b))) ^ 2 by
        dsimp [k]
        ring]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
      exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (le_of_lt hs)) hcosa) hcosb
    · rw [Set.indicator_of_notMem hu]
      by_cases hua : |u - a| ≤ s
      · by_cases hub : |u - b| ≤ s
        · exfalso
          apply hu
          rw [abs_le] at hua hub
          exact ⟨by linarith, by linarith⟩
        · rw [cosSqDensity, if_pos hua, cosSqDensity, if_neg hub]
          simp
      · rw [cosSqDensity, if_neg hua]
        simp
  rw [hfun, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : b - s ≤ a + s)]
  dsimp [F]
  rw [show
    (fun u => s⁻¹ * Real.cos (k * (u - a)) * Real.cos (k * (u - b))) =
      (fun u => s⁻¹ *
        (Real.cos (k * (u - a)) * Real.cos (k * (u - b)))) by
    funext u
    ring]
  rw [intervalIntegral.integral_const_mul]
  have htrig :
      (fun u => Real.cos (k * (u - a)) * Real.cos (k * (u - b))) =
      (fun u => (Real.cos (k * (b - a)) +
        Real.cos ((2 * k) * u - k * (a + b))) / 2) := by
    funext u
    apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
    rw [show
      Real.cos (k * (u - a)) * Real.cos (k * (u - b)) * 2 =
        2 * Real.cos (k * (u - a)) * Real.cos (k * (u - b)) by ring,
      Real.two_mul_cos_mul_cos]
    congr 1 <;> congr 1 <;> ring
  rw [htrig]
  rw [show
      (fun u => (Real.cos (k * (b - a)) +
        Real.cos ((2 * k) * u - k * (a + b))) / 2) =
      (fun u => (1 / 2 : ℝ) * Real.cos (k * (b - a)) +
        (1 / 2 : ℝ) * Real.cos ((2 * k) * u - k * (a + b))) by
    funext u
    ring]
  rw [intervalIntegral.integral_add
      ((by fun_prop : Continuous fun u =>
        (1 / 2 : ℝ) * Real.cos (k * (b - a))).continuousOn.intervalIntegrable)
      ((by fun_prop : Continuous fun u =>
        (1 / 2 : ℝ) * Real.cos ((2 * k) * u - k * (a + b))
        ).continuousOn.intervalIntegrable),
    intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul]
  have h2k : 2 * k ≠ 0 := mul_ne_zero two_ne_zero hk0
  rw [intervalIntegral.integral_comp_mul_sub Real.cos h2k (k * (a + b))]
  rw [integral_cos]
  have huarg :
      2 * k * (a + s) - k * (a + b) =
        Real.pi - k * (b - a) := by
    have hpi_eq : Real.pi = 2 * k * s := by nlinarith [hks]
    rw [hpi_eq]
    ring
  have hlarg :
      2 * k * (b - s) - k * (a + b) =
        k * (b - a) - Real.pi := by
    have hpi_eq : Real.pi = 2 * k * s := by nlinarith [hks]
    rw [hpi_eq]
    ring
  rw [huarg, hlarg]
  rw [show Real.sin (Real.pi - k * (b - a)) =
      Real.sin (k * (b - a)) by
    rw [Real.sin_sub]
    simp,
    show Real.sin (k * (b - a) - Real.pi) =
      -Real.sin (k * (b - a)) by
    rw [Real.sin_sub]
    simp]
  dsimp [k]
  field_simp
  ring

/-- The cosine-squared translate has quadratic affinity defect. -/
lemma cosSqDensity_affinity_defect
    (s a b : ℝ) (hs : 0 < s) :
    1 - ∫ u, Real.sqrt
        (cosSqDensity s (u - a) * cosSqDensity s (u - b)) ≤
      Real.pi ^ 2 * (a - b) ^ 2 / (4 * s ^ 2) := by
  let A : ℝ := ∫ u, Real.sqrt
    (cosSqDensity s (u - a) * cosSqDensity s (u - b))
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun u => Real.sqrt_nonneg _)
  by_cases hlarge : s ≤ |a - b|
  · have hs_sq : 0 < s ^ 2 := sq_pos_of_pos hs
    have hdiff_sq : s ^ 2 ≤ (a - b) ^ 2 := by
      simpa [sq_abs] using
        ((sq_le_sq₀ (le_of_lt hs) (abs_nonneg (a - b))).2
          (by simpa [abs_of_pos hs] using hlarge))
    have hpi : 3 < Real.pi := Real.pi_gt_three
    have hpi_sq : (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
    have hscale :
        4 * s ^ 2 ≤ Real.pi ^ 2 * (a - b) ^ 2 := calc
      4 * s ^ 2 ≤ 4 * (a - b) ^ 2 :=
        mul_le_mul_of_nonneg_left hdiff_sq (by norm_num)
      _ ≤ Real.pi ^ 2 * (a - b) ^ 2 :=
        mul_le_mul_of_nonneg_right hpi_sq (sq_nonneg (a - b))
    have hone :
        (1 : ℝ) ≤ Real.pi ^ 2 * (a - b) ^ 2 / (4 * s ^ 2) := by
      rw [le_div_iff₀ (by positivity : 0 < 4 * s ^ 2)]
      simpa using hscale
    exact (by linarith : 1 - A ≤ 1) |>.trans hone
  · have hsmall : |a - b| < s := lt_of_not_ge hlarge
    have hordered (x y : ℝ) (hxy : x ≤ y) (hgap : y - x < s) :
        1 - ∫ u, Real.sqrt
            (cosSqDensity s (u - x) * cosSqDensity s (u - y)) ≤
          Real.pi ^ 2 * (x - y) ^ 2 / (4 * s ^ 2) := by
      let t : ℝ := y - x
      let q : ℝ := Real.pi * t / (2 * s)
      have ht0 : 0 ≤ t := by dsimp [t]; linarith
      have ht : t < s := by simpa [t] using hgap
      have hq0 : 0 ≤ q := by dsimp [q]; positivity
      have hqlt : q < Real.pi / 2 := by
        dsimp [q]
        rw [div_lt_iff₀ (by positivity : 0 < 2 * s)]
        nlinarith [Real.pi_pos]
      have hcospos : 0 < Real.cos q :=
        Real.cos_pos_of_mem_Ioo ⟨by
          nlinarith [Real.pi_pos], hqlt⟩
      have hqtan : q ≤ Real.tan q := Real.le_tan hq0 hqlt
      rw [Real.tan_eq_sin_div_cos] at hqtan
      have hqcos : q * Real.cos q ≤ Real.sin q :=
        (le_div_iff₀ hcospos).mp hqtan
      have hformula := cosSqDensity_affinity_formula
        s x y hs hxy hgap
      have hdefect_nonneg :
          0 ≤ Real.sin q / Real.pi -
            t / (2 * s) * Real.cos q := by
        have heq :
            t / (2 * s) * Real.cos q =
              (q * Real.cos q) / Real.pi := by
          dsimp [q]
          field_simp
        rw [heq]
        exact sub_nonneg.mpr
          (div_le_div_of_nonneg_right hqcos (le_of_lt Real.pi_pos))
      have hAgecos :
          Real.cos q ≤ ∫ u, Real.sqrt
            (cosSqDensity s (u - x) * cosSqDensity s (u - y)) := by
        rw [hformula]
        change Real.cos q ≤
          (1 - t / (2 * s)) * Real.cos q +
            Real.sin q / Real.pi
        nlinarith
      have hcoslower : 1 - q ^ 2 / 2 ≤ Real.cos q :=
        Real.one_sub_sq_div_two_le_cos (x := q)
      have hq_sq : 0 ≤ q ^ 2 := sq_nonneg q
      calc
        1 - ∫ u, Real.sqrt
            (cosSqDensity s (u - x) * cosSqDensity s (u - y)) ≤
            1 - Real.cos q := sub_le_sub_left hAgecos 1
        _ ≤ q ^ 2 / 2 := by linarith
        _ ≤ q ^ 2 := by linarith
        _ = Real.pi ^ 2 * (x - y) ^ 2 / (4 * s ^ 2) := by
          dsimp [q, t]
          field_simp
          ring
    rcases le_total a b with hab | hba
    · exact hordered a b hab (by
        have := hsmall
        rw [abs_of_nonpos (sub_nonpos.mpr hab)] at this
        linarith)
    · have h := hordered b a hba (by
          have := hsmall
          rw [abs_of_nonneg (sub_nonneg.mpr hba)] at this
          linarith)
      have h' :
          1 - ∫ u, Real.sqrt
              (cosSqDensity s (u - a) * cosSqDensity s (u - b)) ≤
            Real.pi ^ 2 * (b - a) ^ 2 / (4 * s ^ 2) := by
        simpa only [mul_comm] using h
      calc
        1 - ∫ u, Real.sqrt
            (cosSqDensity s (u - a) * cosSqDensity s (u - b)) ≤
            Real.pi ^ 2 * (b - a) ^ 2 / (4 * s ^ 2) := h'
        _ = Real.pi ^ 2 * (a - b) ^ 2 / (4 * s ^ 2) := by
          congr 2
          ring

/-- The sharper constant needed when affinity defect is converted to the
unhalved squared-Hellinger convention used in this development. -/
lemma cosSqDensity_affinity_defect_sharp
    (s a b : ℝ) (hs : 0 < s) :
    1 - ∫ u, Real.sqrt
        (cosSqDensity s (u - a) * cosSqDensity s (u - b)) ≤
      Real.pi ^ 2 * (a - b) ^ 2 / (8 * s ^ 2) := by
  let A : ℝ := ∫ u, Real.sqrt
    (cosSqDensity s (u - a) * cosSqDensity s (u - b))
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun u => Real.sqrt_nonneg _)
  by_cases hlarge : s ≤ |a - b|
  · have hs_sq : 0 < s ^ 2 := sq_pos_of_pos hs
    have hdiff_sq : s ^ 2 ≤ (a - b) ^ 2 := by
      simpa [sq_abs] using
        ((sq_le_sq₀ (le_of_lt hs) (abs_nonneg (a - b))).2
          (by simpa [abs_of_pos hs] using hlarge))
    have hpi_sq : (8 : ℝ) < Real.pi ^ 2 := by
      nlinarith [Real.pi_gt_three]
    have hscale :
        8 * s ^ 2 ≤ Real.pi ^ 2 * (a - b) ^ 2 := calc
      8 * s ^ 2 ≤ 8 * (a - b) ^ 2 :=
        mul_le_mul_of_nonneg_left hdiff_sq (by norm_num)
      _ ≤ Real.pi ^ 2 * (a - b) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_of_lt hpi_sq) (sq_nonneg (a - b))
    have hone :
        (1 : ℝ) ≤ Real.pi ^ 2 * (a - b) ^ 2 / (8 * s ^ 2) := by
      rw [le_div_iff₀ (by positivity : 0 < 8 * s ^ 2)]
      simpa using hscale
    exact (by linarith : 1 - A ≤ 1) |>.trans hone
  · have hsmall : |a - b| < s := lt_of_not_ge hlarge
    have hordered (x y : ℝ) (hxy : x ≤ y) (hgap : y - x < s) :
        1 - ∫ u, Real.sqrt
            (cosSqDensity s (u - x) * cosSqDensity s (u - y)) ≤
          Real.pi ^ 2 * (x - y) ^ 2 / (8 * s ^ 2) := by
      let t : ℝ := y - x
      let q : ℝ := Real.pi * t / (2 * s)
      have ht0 : 0 ≤ t := by dsimp [t]; linarith
      have ht : t < s := by simpa [t] using hgap
      have hq0 : 0 ≤ q := by dsimp [q]; positivity
      have hqlt : q < Real.pi / 2 := by
        dsimp [q]
        rw [div_lt_iff₀ (by positivity : 0 < 2 * s)]
        nlinarith [Real.pi_pos]
      have hcospos : 0 < Real.cos q :=
        Real.cos_pos_of_mem_Ioo ⟨by
          nlinarith [Real.pi_pos], hqlt⟩
      have hqtan : q ≤ Real.tan q := Real.le_tan hq0 hqlt
      rw [Real.tan_eq_sin_div_cos] at hqtan
      have hqcos : q * Real.cos q ≤ Real.sin q :=
        (le_div_iff₀ hcospos).mp hqtan
      have hformula := cosSqDensity_affinity_formula
        s x y hs hxy hgap
      have hdefect_nonneg :
          0 ≤ Real.sin q / Real.pi -
            t / (2 * s) * Real.cos q := by
        have heq :
            t / (2 * s) * Real.cos q =
              (q * Real.cos q) / Real.pi := by
          dsimp [q]
          field_simp
        rw [heq]
        exact sub_nonneg.mpr
          (div_le_div_of_nonneg_right hqcos (le_of_lt Real.pi_pos))
      have hAgecos :
          Real.cos q ≤ ∫ u, Real.sqrt
            (cosSqDensity s (u - x) * cosSqDensity s (u - y)) := by
        rw [hformula]
        change Real.cos q ≤
          (1 - t / (2 * s)) * Real.cos q +
            Real.sin q / Real.pi
        nlinarith
      have hcoslower : 1 - q ^ 2 / 2 ≤ Real.cos q :=
        Real.one_sub_sq_div_two_le_cos (x := q)
      calc
        1 - ∫ u, Real.sqrt
            (cosSqDensity s (u - x) * cosSqDensity s (u - y)) ≤
            1 - Real.cos q := sub_le_sub_left hAgecos 1
        _ ≤ q ^ 2 / 2 := by linarith
        _ = Real.pi ^ 2 * (x - y) ^ 2 / (8 * s ^ 2) := by
          dsimp [q, t]
          field_simp
          ring
    rcases le_total a b with hab | hba
    · exact hordered a b hab (by
        have := hsmall
        rw [abs_of_nonpos (sub_nonpos.mpr hab)] at this
        linarith)
    · have h := hordered b a hba (by
          have := hsmall
          rw [abs_of_nonneg (sub_nonneg.mpr hba)] at this
          linarith)
      have h' :
          1 - ∫ u, Real.sqrt
              (cosSqDensity s (u - a) * cosSqDensity s (u - b)) ≤
            Real.pi ^ 2 * (b - a) ^ 2 / (8 * s ^ 2) := by
        simpa only [mul_comm] using h
      calc
        1 - ∫ u, Real.sqrt
            (cosSqDensity s (u - a) * cosSqDensity s (u - b)) ≤
            Real.pi ^ 2 * (b - a) ^ 2 / (8 * s ^ 2) := h'
        _ = Real.pi ^ 2 * (a - b) ^ 2 / (8 * s ^ 2) := by
          congr 2
          ring

end CausalSmith.Experimentation.SnipeDegreeFrontier
