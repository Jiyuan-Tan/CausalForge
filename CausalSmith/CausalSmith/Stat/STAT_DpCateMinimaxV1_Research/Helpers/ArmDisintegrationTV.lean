/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Minimax.TotalVariation
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.ArmDisintegration
import Mathlib.MeasureTheory.Order.Group.Lattice

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory
open Causalean.Stat

noncomputable section

/-- **Arm-disintegration total-variation lower bound.** -/
theorem arm_disintegration_tv_lower {d : ℕ}
    (alpha beta gamma L e0 f0 f1 r0 : ℝ) (x0 : Fin d → ℝ)
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (P Q : CateLaw d)
    (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P)
    (hQ : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 Q)
    (hIidP : IidSampling P) (hIidQ : IidSampling Q) :
    e0 * f0 / 4 * ∫ x in supBall x0 (rStar r0 x0),
        |(P.mu1 x - P.mu0 x) - (Q.mu1 x - Q.mu0 x)|
      ≤ tvDist P.dataMeasure Q.dataMeasure := by
  classical
  let S : Set (Fin d → ℝ) := supBall x0 (rStar r0 x0)
  let D : ℝ → (Fin d → ℝ) → ℝ := fun a x =>
    S.indicator (armReg P a) x - S.indicator (armReg Q a) x
  let g : ℝ → (Fin d → ℝ) → ℝ := fun a x =>
    if x ∈ S then (if 0 ≤ D a x then (1 : ℝ) else -1) else 0
  let c : ℝ → (Fin d → ℝ) → ℝ := fun a x =>
    max (-1) (min 1 (S.indicator (armReg Q a) x))
  let T : ℝ → CateObs d → ℝ := fun a O =>
    (if O.A = a then (1 : ℝ) else 0) * g a O.X * (O.Y - c a O.X)
  let F : CateObs d → ℝ := fun O => T 1 O + T 0 O
  have hS : MeasurableSet S := measurableSet_supBall _ _
  have hDmeas (a : ℝ) (ha : a = 0 ∨ a = 1) : Measurable (D a) :=
    (measurable_indicator_armReg hreg P hP ha).sub
      (measurable_indicator_armReg hreg Q hQ ha)
  have hgmeas (a : ℝ) (ha : a = 0 ∨ a = 1) : Measurable (g a) := by
    exact Measurable.ite hS
      (Measurable.ite (measurableSet_le measurable_const (hDmeas a ha))
        measurable_const measurable_const) measurable_const
  have hgbd (a : ℝ) : ∀ x, |g a x| ≤ 1 := by
    intro x
    by_cases hx : x ∈ S
    · simp only [g, if_pos hx]
      split <;> norm_num
    · simp only [g, if_neg hx, abs_zero]
      norm_num
  have hgsupp (a : ℝ) : ∀ x, x ∉ S → g a x = 0 := by
    intro x hx
    simp only [g, if_neg hx]
  have hcmeas (a : ℝ) (ha : a = 0 ∨ a = 1) : Measurable (c a) :=
    measurable_const.max (measurable_const.min
      (measurable_indicator_armReg hreg Q hQ ha))
  have hcbd (a : ℝ) : ∀ x, |c a x| ≤ 1 := by
    intro x
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hcvol (a : ℝ) (ha : a = 0 ∨ a = 1) :
      ∀ᵐ x ∂volume, x ∈ S → c a x = armReg Q a x := by
    have hb := armReg_abs_le_one_ae hreg Q hQ hIidQ ha
    have hb' : ∀ᵐ x ∂volume, x ∈ S → |armReg Q a x| ≤ 1 :=
      (ae_restrict_iff' hS).mp hb
    filter_upwards [hb'] with x hx
    intro hxS
    have hle := (abs_le.mp (hx hxS)).2
    have hge := (abs_le.mp (hx hxS)).1
    simp only [c, Set.indicator_of_mem hxS, min_eq_right hle, max_eq_right hge]
  have hcP (a : ℝ) (ha : a = 0 ∨ a = 1) :
      ∀ᵐ x ∂xMarginal P, x ∈ S → c a x = armReg Q a x :=
    (xMarginal_absolutelyContinuous hreg P hP) (hcvol a ha)
  have hcQ (a : ℝ) (ha : a = 0 ∨ a = 1) :
      ∀ᵐ x ∂xMarginal Q, x ∈ S → c a x = armReg Q a x :=
    (xMarginal_absolutelyContinuous hreg Q hQ) (hcvol a ha)
  have hTmeas (a : ℝ) (ha : a = 0 ∨ a = 1) : Measurable (T a) := by
    exact ((Measurable.ite
      (measurableSet_eq_fun measurable_CateObs_A measurable_const)
      measurable_const measurable_const).mul
      ((hgmeas a ha).comp measurable_CateObs_X)).mul
      (measurable_CateObs_Y.sub ((hcmeas a ha).comp measurable_CateObs_X))
  have hFmeas : Measurable F := (hTmeas 1 (Or.inr rfl)).add (hTmeas 0 (Or.inl rfl))
  have hterm_bd (a : ℝ) (O : CateObs d) (hY : |O.Y| ≤ 1) : |T a O| ≤ 2 := by
    by_cases hA : O.A = a
    · simp only [T, if_pos hA, one_mul, abs_mul]
      have hsub : |O.Y - c a O.X| ≤ 2 :=
        (abs_sub _ _).trans (by linarith [hcbd a O.X])
      nlinarith [abs_nonneg (g a O.X), hgbd a O.X]
    · simp only [T, if_neg hA, zero_mul, abs_zero]
      norm_num
  have hFbd (R : CateLaw d) (hIid : IidSampling R) :
      ∀ᵐ O ∂(R.dataMeasure), |F O| ≤ 2 := by
    filter_upwards [hIid.2.1] with O hY
    have hY' : |O.Y| ≤ 1 := by simpa [abs_le] using hY
    by_cases h1 : O.A = (1 : ℝ)
    · have h0 : O.A ≠ (0 : ℝ) := by intro h; linarith
      have heq : F O = T 1 O := by
        simp only [F, T, if_pos h1, if_neg h0, zero_mul, add_zero]
      rw [heq]
      exact hterm_bd 1 O hY'
    · by_cases h0 : O.A = (0 : ℝ)
      · have heq : F O = T 0 O := by
          simp only [F, T, if_neg h1, if_pos h0, zero_mul, zero_add]
        rw [heq]
        exact hterm_bd 0 O hY'
      · simp only [F, T, if_neg h1, if_neg h0, zero_mul, add_zero, abs_zero]
        norm_num
  have hTint (R : CateLaw d) (hIid : IidSampling R)
      (a : ℝ) (ha : a = 0 ∨ a = 1) : Integrable (T a) R.dataMeasure := by
    letI : IsProbabilityMeasure R.dataMeasure := hIid.1
    apply Integrable.of_bound (hTmeas a ha).aestronglyMeasurable 2
    filter_upwards [hIid.2.1] with O hY
    rw [Real.norm_eq_abs]
    apply hterm_bd a O
    simpa [abs_le] using hY
  have hpair (R : CateLaw d)
      (hR : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 R)
      (hIid : IidSampling R) :
      ∫ O, F O ∂(R.dataMeasure) =
        (∫ x, g 1 x * (armReg R 1 x - c 1 x) * armPi R 1 x ∂xMarginal R) +
        ∫ x, g 0 x * (armReg R 0 x - c 0 x) * armPi R 0 x ∂xMarginal R := by
    rw [show F = fun O => T 1 O + T 0 O from rfl,
      integral_add (hTint R hIid 1 (Or.inr rfl)) (hTint R hIid 0 (Or.inl rfl))]
    rw [integral_arm_pairing hreg R hR hIid (Or.inr rfl) (g 1) (c 1)
      (hgmeas 1 (Or.inr rfl)) (hcmeas 1 (Or.inr rfl)) (hgbd 1) (hcbd 1) (hgsupp 1)]
    rw [integral_arm_pairing hreg R hR hIid (Or.inl rfl) (g 0) (c 0)
      (hgmeas 0 (Or.inl rfl)) (hcmeas 0 (Or.inl rfl)) (hgbd 0) (hcbd 0) (hgsupp 0)]
  have hQarm (a : ℝ) (ha : a = 0 ∨ a = 1) :
      ∫ x, g a x * (armReg Q a x - c a x) * armPi Q a x ∂xMarginal Q = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hcQ a ha] with x hx
    change g a x * (armReg Q a x - c a x) * armPi Q a x = (0 : ℝ)
    by_cases hxS : x ∈ S
    · simp only [hx hxS, sub_self, mul_zero, zero_mul]
    · simp only [hgsupp a x hxS, zero_mul]
  have hQzero : ∫ O, F O ∂Q.dataMeasure = 0 := by
    rw [hpair Q hQ hIidQ, hQarm 1 (Or.inr rfl), hQarm 0 (Or.inl rfl), add_zero]
  have hParm (a : ℝ) (ha : a = 0 ∨ a = 1) :
      ∫ x, g a x * (armReg P a x - c a x) * armPi P a x ∂xMarginal P =
        ∫ x in S, |D a x| * armPi P a x ∂xMarginal P := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards [hcP a ha] with x hx
    by_cases hxS : x ∈ S
    · have hDx : D a x = armReg P a x - armReg Q a x := by
        simp only [D, Set.indicator_of_mem hxS]
      rw [Set.indicator_of_mem hxS, hx hxS, ← hDx]
      by_cases hd : 0 ≤ D a x
      · simp only [g, if_pos hxS, if_pos hd, one_mul, abs_of_nonneg hd]
      · have hd'' : D a x ≤ 0 := le_of_not_ge hd
        simp only [g, if_pos hxS, if_neg hd, neg_one_mul, abs_of_nonpos hd'']
    · simp only [hgsupp a x hxS, zero_mul, Set.indicator, Set.piecewise, if_neg hxS]
  let W : ℝ → (Fin d → ℝ) → ℝ := fun a x =>
    |D a x| * S.indicator (armPi P a) x
  have hWmeas (a : ℝ) (ha : a = 0 ∨ a = 1) : Measurable (W a) :=
    (hDmeas a ha).abs.mul (measurable_indicator_armPi hreg P hP ha)
  have hDbd (a : ℝ) (ha : a = 0 ∨ a = 1) : ∀ x, |D a x| ≤ 2 * L := by
    intro x
    by_cases hx : x ∈ S
    · have hcube := supBall_rStar_subset_cube r0 x0 hreg.2.2.2.2.2.2.2.1.1
        hreg.2.2.2.2.2.2.2.2 hx
      simp only [D, Set.indicator_of_mem hx]
      exact (abs_sub _ _).trans (by
        linarith [armReg_abs_le_L hreg P hP ha x hcube,
          armReg_abs_le_L hreg Q hQ ha x hcube])
    · simp only [D, Set.indicator, Set.piecewise, if_neg hx, sub_self, abs_zero]
      exact mul_nonneg (by norm_num) hreg.2.2.2.1.le
  have hWbd (a : ℝ) (ha : a = 0 ∨ a = 1) : ∀ x, |W a x| ≤ 2 * L := by
    intro x
    by_cases hx : x ∈ S
    · have hp0 := armPi_ge hreg P hP ha x hx
      have hp1 := armPi_le_one hreg P hP ha x hx
      simp only [W, Set.indicator_of_mem hx]
      rw [abs_mul, abs_abs,
        abs_of_nonneg (hreg.2.2.2.2.1.1.le.trans hp0)]
      nlinarith [abs_nonneg (D a x), hDbd a ha x, hreg.2.2.2.1]
    · simp only [W, Set.indicator, Set.piecewise, if_neg hx, mul_zero, abs_zero]
      exact mul_nonneg (by norm_num) hreg.2.2.2.1.le
  have hWint (a : ℝ) (ha : a = 0 ∨ a = 1) : Integrable (W a) (xMarginal P) := by
    letI : IsProbabilityMeasure P.dataMeasure := hIidP.1
    letI : IsProbabilityMeasure (xMarginal P) := by
      unfold xMarginal
      exact Measure.isProbabilityMeasure_map measurable_CateObs_X.aemeasurable
    apply Integrable.of_bound (hWmeas a ha).aestronglyMeasurable (2 * L)
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact hWbd a ha x
  have hsetW (a : ℝ) :
      (∫ x in S, |D a x| * armPi P a x ∂xMarginal P) = ∫ x, W a x ∂xMarginal P := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ S
    · simp only [W, Set.indicator_of_mem hx]
    · simp only [W, Set.indicator, Set.piecewise, if_neg hx, mul_zero]
  let H : (Fin d → ℝ) → ℝ := fun x => |D 1 x - D 0 x|
  have hHmeas : Measurable H := ((hDmeas 1 (Or.inr rfl)).sub
    (hDmeas 0 (Or.inl rfl))).abs
  have hHbd : ∀ x, H x ≤ 4 * L := by
    intro x
    exact (abs_sub _ _).trans (by
      linarith [hDbd 1 (Or.inr rfl) x, hDbd 0 (Or.inl rfl) x])
  have hHnn : ∀ x, 0 ≤ H x := fun x => abs_nonneg _
  have hHint : Integrable H (xMarginal P) := by
    letI : IsProbabilityMeasure P.dataMeasure := hIidP.1
    letI : IsProbabilityMeasure (xMarginal P) := by
      unfold xMarginal
      exact Measure.isProbabilityMeasure_map measurable_CateObs_X.aemeasurable
    apply Integrable.of_bound hHmeas.aestronglyMeasurable (4 * L)
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hHnn x)]
    exact hHbd x
  have hpoint : ∀ x, e0 * H x ≤ W 1 x + W 0 x := by
    intro x
    by_cases hx : x ∈ S
    · have hp1 := armPi_ge hreg P hP (Or.inr rfl) x hx
      have hp0 := armPi_ge hreg P hP (Or.inl rfl) x hx
      simp only [W, Set.indicator_of_mem hx]
      have htri : H x ≤ |D 1 x| + |D 0 x| := abs_sub _ _
      nlinarith [abs_nonneg (D 1 x), abs_nonneg (D 0 x), hreg.2.2.2.2.1.1]
    · simp only [H, D, W, Set.indicator, Set.piecewise, if_neg hx, sub_self,
        abs_zero, mul_zero, zero_add]
      norm_num
  have hPlower : e0 * (∫ x, H x ∂xMarginal P) ≤ ∫ O, F O ∂P.dataMeasure := by
    rw [hpair P hP hIidP, hParm 1 (Or.inr rfl), hParm 0 (Or.inl rfl),
      hsetW 1, hsetW 0, ← integral_add (hWint 1 (Or.inr rfl)) (hWint 0 (Or.inl rfl)),
      ← integral_const_mul]
    exact integral_mono_ae (hHint.const_mul e0)
      ((hWint 1 (Or.inr rfl)).add (hWint 0 (Or.inl rfl))) (ae_of_all _ hpoint)
  have hmass := mul_setIntegral_volume_le_setIntegral_xMarginal hreg P hP hIidP H
    hHmeas hHnn (4 * L) hHbd
  have hHsupport : ∀ x, x ∉ S → H x = 0 := by
    intro x hx
    simp only [H, D, Set.indicator, Set.piecewise, if_neg hx, sub_self, abs_zero]
  have hglobal_set (mu : Measure (Fin d → ℝ)) :
      (∫ x, H x ∂mu) = ∫ x in S, H x ∂mu := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator, Set.piecewise, if_neg hx, hHsupport x hx]
  rw [← hglobal_set (xMarginal P)] at hmass
  have hvol_to_P : e0 * f0 * (∫ x in S, H x ∂volume) ≤ ∫ O, F O ∂P.dataMeasure := by
    calc
      e0 * f0 * (∫ x in S, H x ∂volume) =
          e0 * (f0 * (∫ x in S, H x ∂volume)) := by ring
      _ ≤ e0 * (∫ x, H x ∂xMarginal P) :=
        mul_le_mul_of_nonneg_left hmass hreg.2.2.2.2.1.1.le
      _ ≤ _ := hPlower
  have htarget :
      (∫ x in S, H x ∂volume) = ∫ x in S,
        |(P.mu1 x - P.mu0 x) - (Q.mu1 x - Q.mu0 x)| ∂volume := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hS] with x hx
    have hP1 : armReg P 1 x = P.mu1 x := by rw [armReg, if_pos rfl]
    have hQ1 : armReg Q 1 x = Q.mu1 x := by rw [armReg, if_pos rfl]
    have hP0 : armReg P 0 x = P.mu0 x := by rw [armReg, if_neg (by norm_num)]
    have hQ0 : armReg Q 0 x = Q.mu0 x := by rw [armReg, if_neg (by norm_num)]
    simp only [H, D, Set.indicator_of_mem hx, hP1, hQ1, hP0, hQ0]
    ring
  haveI : IsProbabilityMeasure P.dataMeasure := hIidP.1
  haveI : IsProbabilityMeasure Q.dataMeasure := hIidQ.1
  have hTV := Causalean.Stat.tvDist_integral_le_of_abs_le_ae
    P.dataMeasure Q.dataMeasure F hFmeas 2 (by norm_num) (hFbd P hIidP) (hFbd Q hIidQ)
  rw [hQzero, sub_zero] at hTV
  rw [htarget] at hvol_to_P
  have hnonneg : 0 ≤ ∫ x in S,
      |(P.mu1 x - P.mu0 x) - (Q.mu1 x - Q.mu0 x)| ∂volume :=
    integral_nonneg_of_ae (ae_of_all _ fun x => abs_nonneg _)
  have hchain : e0 * f0 * (∫ x in S,
      |(P.mu1 x - P.mu0 x) - (Q.mu1 x - Q.mu0 x)| ∂volume) ≤
      4 * tvDist P.dataMeasure Q.dataMeasure := by
    calc
      _ ≤ ∫ O, F O ∂P.dataMeasure := hvol_to_P
      _ ≤ |∫ O, F O ∂P.dataMeasure| := le_abs_self _
      _ ≤ 4 * tvDist P.dataMeasure Q.dataMeasure := by
        calc
          _ ≤ 2 * 2 * tvDist P.dataMeasure Q.dataMeasure := hTV
          _ = 4 * tvDist P.dataMeasure Q.dataMeasure := by ring
  calc
    e0 * f0 / 4 * (∫ x in S,
        |(P.mu1 x - P.mu0 x) - (Q.mu1 x - Q.mu0 x)| ∂volume) =
        (e0 * f0 * (∫ x in S,
          |(P.mu1 x - P.mu0 x) - (Q.mu1 x - Q.mu0 x)| ∂volume)) / 4 := by ring
    _ ≤ (4 * tvDist P.dataMeasure Q.dataMeasure) / 4 :=
      div_le_div_of_nonneg_right hchain (by norm_num)
    _ = tvDist P.dataMeasure Q.dataMeasure := by ring

end

end CausalSmith.Stat.DpCateMinimax
