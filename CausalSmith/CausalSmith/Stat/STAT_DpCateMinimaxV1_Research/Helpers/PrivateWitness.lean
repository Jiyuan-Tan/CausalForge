/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PrivateRiskBound
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.RegressionCalibrationBounds

/-!
# Explicit private local-polynomial witness

This file assembles the uniform population bounds, the clipped bandwidth choice, and the
private local-polynomial mechanism into the achievability witness for the central-DP CATE rate.
-/

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory Set Matrix
open scoped BigOperators ENNReal
open Causalean.Mathlib.Analysis
open Causalean.Stat.Nonparametric

noncomputable section

private lemma rStar_pos_of_pos_dim {d : ℕ} (hd : 0 < d)
    {alpha beta gamma L e0 f0 f1 r0 : ℝ} {x0 : Fin d → ℝ}
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0) :
    0 < rStar r0 x0 := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨i, hi⟩ := Finite.exists_min
    (fun j : Fin d => min (x0 j) (1 - x0 j))
  have hinf : (⨅ j : Fin d, min (x0 j) (1 - x0 j)) =
      min (x0 i) (1 - x0 i) := by
    apply le_antisymm
    · exact ciInf_le (Finite.bddBelow_range _) i
    · exact le_ciInf hi
  rw [rStar, hinf]
  have hi0 := hreg.2.2.2.2.2.2.2.2 i
  have hr0 := hreg.2.2.2.2.2.2.2.1.1
  have : 0 < min r0 (min (x0 i) (1 - x0 i)) :=
    lt_min hr0 (lt_min hi0.1 (sub_pos.mpr hi0.2))
  positivity

private lemma rStar_le_r0 {d : ℕ} (r0 : ℝ) (x0 : Fin d → ℝ) (hr0 : 0 < r0) :
    rStar r0 x0 ≤ r0 := by
  unfold rStar
  have h := min_le_left r0 (⨅ i : Fin d, min (x0 i) (1 - x0 i))
  nlinarith

private lemma witness_measurable_uCoord_obs {d : ℕ} (h : ℝ) (x0 : Fin d → ℝ) :
    Measurable (fun O : CateObs d ↦ uCoord h x0 O.X) := by
  rw [measurable_pi_iff]
  intro j
  exact (((measurable_pi_apply j).comp measurable_CateObs_X).sub measurable_const).div_const h

private lemma witness_measurable_momSummand {d p : ℕ} (h : ℝ) (x0 : Fin d → ℝ)
    (expo : Fin p → (Fin d → ℕ)) (a : Fin 2) (k : Fin p) :
    Measurable (fun O : CateObs d ↦
      momSummand h x0 expo (unifKernel d) a O k) := by
  unfold momSummand
  have hi : Measurable (fun O : CateObs d ↦
      if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0) := Measurable.ite
    (measurableSet_eq_fun measurable_CateObs_A measurable_const)
    measurable_const measurable_const
  have hK := (measurable_unifKernel d).comp (witness_measurable_uCoord_obs h x0)
  have hk : Measurable (fun O : CateObs d ↦ monomial (expo k) (uCoord h x0 O.X)) := by
    unfold monomial
    apply Finset.measurable_prod
    intro j _
    exact ((measurable_pi_iff.mp (witness_measurable_uCoord_obs h x0)) j).pow_const _
  exact ((((hi.mul measurable_const).mul hK).mul
    (measurable_const.max (measurable_const.min measurable_CateObs_Y))).mul hk)

private lemma witness_abs_integral_le_ball_mass {d : ℕ} (P : CateLaw d)
    (hiid : IidSampling P) {h B : ℝ} {x0 : Fin d → ℝ} {q : CateObs d → ℝ}
    (hq : Measurable q) (hqB : ∀ O, |q O| ≤ B)
    (hqsupp : ∀ O, O.X ∉ supBall x0 h → q O = 0) :
    |∫ O, q O ∂P.dataMeasure| ≤
      B * (P.dataMeasure.map (fun O ↦ O.X)).real (supBall x0 h) := by
  letI : IsProbabilityMeasure P.dataMeasure := hiid.1
  let S : Set (CateObs d) := {O | O.X ∈ supBall x0 h}
  have hball : MeasurableSet (supBall x0 h) := by
    rw [show supBall x0 h = ⋂ i : Fin d, {x | |x i - x0 i| ≤ h} by
      ext x
      simp [supBall]]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le
      (continuous_abs.measurable.comp ((measurable_pi_apply i).sub measurable_const))
      measurable_const
  have hS : MeasurableSet S := hball.preimage measurable_CateObs_X
  have hqint : Integrable q P.dataMeasure :=
    Integrable.of_bound hq.aestronglyMeasurable B (Filter.Eventually.of_forall fun O ↦ by
      simpa [Real.norm_eq_abs] using hqB O)
  calc
    |∫ O, q O ∂P.dataMeasure| ≤ ∫ O, |q O| ∂P.dataMeasure := abs_integral_le_integral_abs
    _ ≤ ∫ O, S.indicator (fun _ ↦ B) O ∂P.dataMeasure := by
      apply integral_mono (hqint.abs) ((integrable_const B).indicator hS)
      intro O
      by_cases hO : O ∈ S
      · simpa [Set.indicator_of_mem hO] using hqB O
      · simp [S, hO, hqsupp O hO]
    _ = B * P.dataMeasure.real S := by
      rw [integral_indicator hS]
      simp [Measure.real, mul_comm]
    _ = B * (P.dataMeasure.map (fun O ↦ O.X)).real (supBall x0 h) := by
      congr 1
      rw [Measure.real, Measure.real, Measure.map_apply measurable_CateObs_X hball]
      rfl

private lemma witness_bandwidth_mass_cancel {d : ℕ} {h : ℝ} (hh : 0 < h) :
    h ^ (-(d : ℝ)) * (2 * h) ^ d = (2 : ℝ) ^ d := by
  rw [mul_pow, ← Real.rpow_natCast 2 d, ← Real.rpow_natCast h d]
  rw [show h ^ (-(d : ℝ)) * (2 ^ (d : ℝ) * h ^ (d : ℝ)) =
    2 ^ (d : ℝ) * (h ^ (-(d : ℝ)) * h ^ (d : ℝ)) by ring,
    ← Real.rpow_add hh]
  simp

private lemma witness_norm_popMom_le {d p : ℕ}
    {alpha beta gamma L e0 f0 f1 r0 h : ℝ} {x0 : Fin d → ℝ} {P : CateLaw d}
    {expo : Fin p → (Fin d → ℕ)} (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P)
    (hiid : IidSampling P) (hh : 0 < h) (hhr : h ≤ r0) (a : Fin 2) :
    Real.sqrt (∑ k, (popMom P h x0 expo (unifKernel d) a k) ^ 2) ≤
      Real.sqrt (p : ℝ) * (f1 * 2 ^ d) := by
  have hf10 : 0 ≤ f1 := hreg.2.2.2.2.2.1.le.trans hreg.2.2.2.2.2.2.1
  have hcoord : ∀ k : Fin p,
      |popMom P h x0 expo (unifKernel d) a k| ≤ f1 * 2 ^ d := by
    intro k
    have hqbound : ∀ O, |momSummand h x0 expo (unifKernel d) a O k| ≤
        h ^ (-(d : ℝ)) := by
      intro O
      simpa using abs_momSummand_le hh (unifKernel_nonneg d)
        (unifKernel_le_one d) (unifKernel_eq_zero d) a O k
    have hb := witness_abs_integral_le_ball_mass P hiid
      (witness_measurable_momSummand h x0 expo a k)
      hqbound
      (fun O hO => momSummand_eq_zero_of_not_mem hh (unifKernel_eq_zero d) a O k hO)
    have hm := design_mass_le P f0 f1 r0 x0 hiid hP.pxDens hP.localDensity hf10 hh hhr
    calc
      _ ≤ h ^ (-(d : ℝ)) *
          (P.dataMeasure.map (fun O ↦ O.X)).real (supBall x0 h) := by simpa using hb
      _ ≤ h ^ (-(d : ℝ)) * (f1 * (2 * h) ^ d) := by gcongr
      _ = f1 * 2 ^ d := by
        rw [show h ^ (-(d : ℝ)) * (f1 * (2 * h) ^ d) =
          f1 * (h ^ (-(d : ℝ)) * (2 * h) ^ d) by ring,
          witness_bandwidth_mass_cancel hh]
  have hs : ∑ k, (popMom P h x0 expo (unifKernel d) a k) ^ 2 ≤
      (p : ℝ) * (f1 * 2 ^ d) ^ 2 := by
    calc
      _ ≤ ∑ _k : Fin p, (f1 * 2 ^ d) ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hf10 (pow_nonneg (by norm_num) _))).mpr
          (hcoord k)
      _ = _ := by simp
  calc
    _ ≤ Real.sqrt ((p : ℝ) * (f1 * 2 ^ d) ^ 2) := Real.sqrt_le_sqrt hs
    _ = _ := by
      rw [Real.sqrt_mul (Nat.cast_nonneg p), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (mul_nonneg hf10 (pow_nonneg (by norm_num) _))]

/-- A clipped maximum of the sampling- and privacy-optimal bandwidths controls all three
terms in the private risk decomposition by one uniform multiple of the target rate. -/
private lemma clipped_bandwidth_bounds (d : ℕ) {beta rho x y : ℝ}
    (hbeta : 0 < beta) (hrho : 0 < rho) (hx1 : 1 ≤ x) (hy1 : 1 ≤ y) :
    let A := x ^ (-(1 / (2 * beta + (d : ℝ))))
    let B := y ^ (-(1 / (beta + (d : ℝ))))
    let H := max A B
    let h := min H (rho / 2)
    let R := max (x ^ (-(beta / (2 * beta + (d : ℝ)))))
      (y ^ (-(beta / (beta + (d : ℝ)))))
    let K := max 3 (max (((rho / 2) ^ (d : ℝ)) ^ (-(1 / 2 : ℝ)))
      (1 / (rho / 2) ^ (d : ℝ)))
    0 < K ∧ 0 < h ∧ h < rho ∧
      h ^ beta ≤ K * R ∧
      Real.sqrt (1 / (x * h ^ (d : ℝ))) ≤ K * R ∧
      1 / (y * h ^ (d : ℝ)) ≤ K * R := by
  dsimp
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hy : 0 < y := zero_lt_one.trans_le hy1
  let A := x ^ (-(1 / (2 * beta + (d : ℝ))))
  let B := y ^ (-(1 / (beta + (d : ℝ))))
  let H := max A B
  let a := rho / 2
  let h := min H a
  let R := max (x ^ (-(beta / (2 * beta + (d : ℝ)))))
    (y ^ (-(beta / (beta + (d : ℝ)))))
  let Ks := (a ^ (d : ℝ)) ^ (-(1 / 2 : ℝ))
  let Kp := 1 / a ^ (d : ℝ)
  let K := max 3 (max Ks Kp)
  have hA : 0 < A := Real.rpow_pos_of_pos hx _
  have hB : 0 < B := Real.rpow_pos_of_pos hy _
  have hH : 0 < H := hA.trans_le (le_max_left _ _)
  have ha : 0 < a := by dsimp [a]; positivity
  have hh : 0 < h := lt_min hH ha
  have hR0 : 0 ≤ R := (Real.rpow_nonneg hx.le _).trans (le_max_left _ _)
  have hKs0 : 0 ≤ Ks := Real.rpow_nonneg (Real.rpow_nonneg ha.le _ ) _
  have hKp0 : 0 ≤ Kp := one_div_nonneg.mpr (Real.rpow_nonneg ha.le _)
  have hK : 0 < K := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) (le_max_left _ _)
  have hmax := private_regression_max_bandwidth_bound x y beta d hx hy hbeta
  have hHpow : H ^ beta = R := by simpa [A, B, H, R] using hmax.1
  have hpow : h ^ beta ≤ K * R := by
    have hhH : h ≤ H := min_le_left _ _
    have hleR : h ^ beta ≤ R := by
      rw [← hHpow]
      exact Real.rpow_le_rpow hh.le hhH hbeta.le
    exact hleR.trans (by
      calc
        R = 1 * R := by ring
        _ ≤ K * R := mul_le_mul_of_nonneg_right
          ((by norm_num : (1 : ℝ) ≤ 3).trans (le_max_left _ _)) hR0)
  have hsqrt_rpow (t : ℝ) (ht : 0 < t) :
      Real.sqrt (1 / t) = t ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg_one,
      ← Real.rpow_mul ht.le]
    congr 1
    ring
  have hsamp : Real.sqrt (1 / (x * h ^ (d : ℝ))) ≤ K * R := by
    by_cases hHa : H ≤ a
    · have heq : h = H := min_eq_left hHa
      have hterm : Real.sqrt (1 / (x * H ^ (d : ℝ))) ≤ 3 * R := by
        rw [hsqrt_rpow _ (mul_pos hx (Real.rpow_pos_of_pos hH _))]
        have hsnonneg : 0 ≤ H ^ beta := Real.rpow_nonneg hH.le _
        have hpnonneg : 0 ≤ 1 / (y * H ^ (d : ℝ)) := by positivity
        have := hmax.2
        dsimp [A, B, H, R] at this ⊢
        linarith
      rw [heq]
      exact hterm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hR0)
    · have heq : h = a := min_eq_right (le_of_not_ge hHa)
      rw [heq, hsqrt_rpow _ (mul_pos hx (Real.rpow_pos_of_pos ha _))]
      have hfac : (x * a ^ (d : ℝ)) ^ (-(1 / 2 : ℝ)) =
          x ^ (-(1 / 2 : ℝ)) * Ks := by
        dsimp [Ks]
        rw [Real.mul_rpow hx.le (Real.rpow_nonneg ha.le _),
          ← Real.rpow_mul ha.le]
      rw [hfac]
      have hexp : -(1 / 2 : ℝ) ≤ -(beta / (2 * beta + (d : ℝ))) := by
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        have hden : 0 < 2 * beta + (d : ℝ) := by positivity
        apply neg_le_neg
        apply (div_le_iff₀ hden).2
        nlinarith
      have hxrate : x ^ (-(1 / 2 : ℝ)) ≤ R :=
        (Real.rpow_le_rpow_of_exponent_le hx1 hexp).trans (le_max_left _ _)
      calc
        x ^ (-(1 / 2 : ℝ)) * Ks ≤ R * Ks :=
          mul_le_mul_of_nonneg_right hxrate hKs0
        _ = Ks * R := by ring
        _ ≤ K * R := mul_le_mul_of_nonneg_right
          ((le_max_left Ks Kp).trans (le_max_right 3 (max Ks Kp))) hR0
  have hpriv : 1 / (y * h ^ (d : ℝ)) ≤ K * R := by
    by_cases hHa : H ≤ a
    · have heq : h = H := min_eq_left hHa
      have hterm : 1 / (y * H ^ (d : ℝ)) ≤ 3 * R := by
        have hsnonneg : 0 ≤ H ^ beta := Real.rpow_nonneg hH.le _
        have hvnonneg : 0 ≤ (x * H ^ (d : ℝ)) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_nonneg (mul_nonneg hx.le (Real.rpow_nonneg hH.le _)) _
        have := hmax.2
        dsimp [A, B, H, R] at this ⊢
        linarith
      rw [heq]
      exact hterm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hR0)
    · have heq : h = a := min_eq_right (le_of_not_ge hHa)
      rw [heq]
      have hfac : 1 / (y * a ^ (d : ℝ)) = Kp * y⁻¹ := by
        dsimp [Kp]
        field_simp
      rw [hfac, ← Real.rpow_neg_one]
      have hden : 0 < beta + (d : ℝ) := by positivity
      have hexp : (-1 : ℝ) ≤ -(beta / (beta + (d : ℝ))) := by
        apply neg_le_neg
        apply (div_le_one hden).2
        exact le_add_of_nonneg_right (Nat.cast_nonneg d)
      have hyrate : y ^ (-1 : ℝ) ≤ R :=
        (Real.rpow_le_rpow_of_exponent_le hy1 hexp).trans (le_max_right _ _)
      calc
        Kp * y ^ (-1 : ℝ) ≤ Kp * R := mul_le_mul_of_nonneg_left hyrate hKp0
        _ ≤ K * R := mul_le_mul_of_nonneg_right
          ((le_max_right Ks Kp).trans (le_max_right 3 (max Ks Kp))) hR0
  refine ⟨hK, hh, ?_, hpow, hsamp, hpriv⟩
  exact (min_le_right H a).trans_lt (by dsimp [a]; linarith)

set_option maxHeartbeats 1000000 in
/-- The explicit clipped, centrally private local-polynomial mechanism attains the uniform
two-branch minimax rate over the positive-density Hölder CATE class. -/
theorem explicit_private_local_poly_witness {d : ℕ}
    (alpha beta gamma L e0 f0 f1 r0 : ℝ) (x0 : Fin d → ℝ)
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (eps del : ℕ → ℝ), PrivacyBudget eps del →
      ∀ᶠ n : ℕ in Filter.atTop,
      ∃ M : (Fin n → CateObs d) → Measure ℝ,
        IsArmwisePrivatizedLocalPoly n beta r0 (eps n) x0 M ∧
        CentralDP n (eps n) (del n) M ∧
        (∀ s, (M s) (Set.Icc (-2 : ℝ) 2)ᶜ = 0) ∧
        (⨆ P : {P : CateLaw d //
              HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P
                ∧ IidSampling P ∧ |P.mu1 x0 - P.mu0 x0| ≤ 2},
            ∫ s, (∫ z, |z - (P.1.mu1 x0 - P.1.mu0 x0)| ∂(M s))
              ∂(Measure.pi fun _ : Fin n => (P.1).dataMeasure))
          ≤ C * max ((n : ℝ) ^ (-(beta / (2 * beta + (d : ℝ)))))
              (((n : ℝ) * eps n) ^ (-(beta / (beta + (d : ℝ))))) := by
  let m := ⌈beta⌉₊ - 1
  let p := pDim d m
  let expo := expoOf d m
  have hexpo : Function.Injective expo := expoOf_injective d m
  obtain ⟨cmin, hcmin, hcoer⟩ :=
    exists_monomialGram_coercive expo (r := (1 / 2 : ℝ)) (by norm_num) hexpo
  let cstar := e0 * f0 * 1 * cmin
  let Cstar := 1 * (p : ℝ) * f1 * 2 ^ d + cstar
  let Bg := Real.sqrt (p : ℝ) * (1 * f1 * 2 ^ d)
  have hrho : 0 < rStar r0 x0 := rStar_pos_of_pos_dim hd hreg
  have hsubset : supBall x0 (rStar r0 x0) ⊆ cube d :=
    (supBall_subset_of_lt_rStar hreg hrho le_rfl).1
  obtain ⟨Cb, hCb, hCbApprox0⟩ := holder_taylor_monomial_approx
    hreg.2.1 hreg.2.2.2.1 hrho hsubset expo (expoOf_surj d m)
  have hCbApprox : ∀ f : (Fin d → ℝ) → ℝ, HolderBallStd f beta L (cube d) →
      ∀ h : ℝ, 0 < h → h < rStar r0 x0 → ∃ theta : Fin p → ℝ,
        ∀ u : Fin d → ℝ, (∀ j, |u j| ≤ 1) →
          |f (x0 + h • u) - ∑ k, theta k * monomial (expo k) u| ≤
            Cb * L * h ^ beta := by
    simpa [monomial] using hCbApprox0
  let Cbias := Real.sqrt (p : ℝ) * Cb * L * 1 * f1 * 2 ^ d / cstar + Cb * L
  obtain ⟨Cv1, Cv2, Cw, hCv1, hCv2, hCw, hrisk⟩ := mechOf_risk_bound d beta f1
  have hcstar : 0 < cstar := by
    dsimp [cstar]
    have he0 := hreg.2.2.2.2.1.1
    have hf0 := hreg.2.2.2.2.2.1
    positivity
  have hcC : cstar ≤ Cstar := by
    dsimp [Cstar]
    have hf1 : 0 ≤ f1 := hreg.2.2.2.2.2.1.le.trans hreg.2.2.2.2.2.2.1
    have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
    have hpow2 : 0 ≤ (2 : ℝ) ^ d := pow_nonneg (by norm_num) d
    nlinarith [mul_nonneg (mul_nonneg hp0 hf1) hpow2]
  have hBg : 0 ≤ Bg := by
    dsimp [Bg]
    have hf1 : 0 ≤ f1 := hreg.2.2.2.2.2.1.le.trans hreg.2.2.2.2.2.2.1
    positivity
  have hCbias : 0 ≤ Cbias := by
    dsimp [Cbias]
    have hf1 : 0 ≤ f1 := hreg.2.2.2.2.2.1.le.trans hreg.2.2.2.2.2.2.1
    have hL : 0 ≤ L := hreg.2.2.2.1.le
    apply add_nonneg
    · apply div_nonneg
      · positivity
      · exact hcstar.le
    · positivity
  let Krate := max 3
    (max (((rStar r0 x0 / 2) ^ (d : ℝ)) ^ (-(1 / 2 : ℝ)))
      (1 / (rStar r0 x0 / 2) ^ (d : ℝ)))
  have hKrate : 0 < Krate :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) (le_max_left _ _)
  let V := Cv1 / cstar + Cv2 * Bg / cstar ^ 2
  let W := Cw * (1 / cstar + Bg / cstar ^ 2)
  let C0 := Krate * (2 * Cbias + V + W)
  let C := max C0 1
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hC : 0 < C := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro eps del hbudget
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hx : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hbn := hbudget n hn
  have hy1 : 1 ≤ (n : ℝ) * eps n := by
    calc
      1 = (n : ℝ) * (n : ℝ)⁻¹ := (mul_inv_cancel₀ hx.ne').symm
      _ ≤ (n : ℝ) * eps n := mul_le_mul_of_nonneg_left hbn.1 hx.le
  have heps : 0 < eps n := lt_of_lt_of_le (inv_pos.mpr hx) hbn.1
  let A := (n : ℝ) ^ (-(1 / (2 * beta + (d : ℝ))))
  let B := ((n : ℝ) * eps n) ^ (-(1 / (beta + (d : ℝ))))
  let H := max A B
  let h := min H (rStar r0 x0 / 2)
  let R := max ((n : ℝ) ^ (-(beta / (2 * beta + (d : ℝ)))))
    (((n : ℝ) * eps n) ^ (-(beta / (beta + (d : ℝ)))))
  obtain ⟨hK, hh, hhr, hbiasRate, hvarRate, hprivRate⟩ :=
    clipped_bandwidth_bounds d hreg.2.1 hrho hnreal hy1
  have hhr_le : h ≤ rStar r0 x0 := hhr.le
  have hhr0 : h ≤ r0 := hhr_le.trans
    (rStar_le_r0 r0 x0 hreg.2.2.2.2.2.2.2.1.1)
  let M : (Fin n → CateObs d) → Measure ℝ :=
    mechOf (n := n) m h cstar Cstar (eps n) x0
  refine ⟨M, ?_, ?_, mechOf_clipped m h cstar Cstar (eps n) x0, ?_⟩
  · exact mechOf_isArmwise beta r0 (eps n) h cstar Cstar x0 hreg.2.1 hh hhr0
      hcstar hcC hnpos
  · exact mechOf_centralDP m h cstar Cstar (eps n) (del n) x0 hnpos hh heps hbn.2.2.1.le
  · have hR0 : 0 ≤ R := (Real.rpow_nonneg hx.le _).trans (le_max_left _ _)
    refine Real.iSup_le ?_ (mul_nonneg hC.le hR0)
    intro P
    have hloew (a : Fin 2) :
        popGram P.1 h x0 expo (unifKernel d) a ∈ loewnerSet p cstar Cstar := by
      simpa [h, A, B, H, expo, p, cstar, Cstar] using popGram_mem_loewnerSet
        hreg P.2.1 P.2.2.1 hexpo (unifKernel_nonneg d) (unifKernel_le_one d)
        (unifKernel_eq_zero d) (one_le_unifKernel d) (measurable_unifKernel d)
        (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) (pDim_pos d m) hh hhr_le hcmin hcoer
    have hmom (a : Fin 2) :
        Real.sqrt (∑ k, (popMom P.1 h x0 expo (unifKernel d) a k) ^ 2) ≤ Bg := by
      simpa [h, A, B, H, expo, p, Bg] using
        witness_norm_popMom_le (expo := expo) hreg P.2.1 P.2.2.1 hh hhr0 a
    have hbias (a : Fin 2) :
        |((popGram P.1 h x0 expo (unifKernel d) a)⁻¹.mulVec
            (popMom P.1 h x0 expo (unifKernel d) a)) (icptOf d m) -
              armMu P.1 a x0| ≤ Cbias * h ^ beta := by
      simpa [h, A, B, H, expo, p, Cbias] using popGram_inv_popMom_bias
        (Kmin := 1) (rinner := (1 / 2 : ℝ)) hreg P.2.1 P.2.2.1
        hexpo (expoOf_icptOf d m) (expoOf_surj d m) (unifKernel_nonneg d)
        (unifKernel_le_one d) (unifKernel_eq_zero d) (measurable_unifKernel d)
        hh hhr hcstar hcC (hloew a) hCb hCbApprox
    have hraw := hrisk hreg P.2.1 P.2.2.1 hnpos hh hhr heps hcstar hcC
      hloew hmom hBg hbias P.2.2.2
    have hsum :
        2 * Cbias * h ^ beta + V * Real.sqrt (1 / ((n : ℝ) * h ^ (d : ℝ))) +
            W * (1 / ((n : ℝ) * eps n * h ^ (d : ℝ))) ≤ C0 * R := by
      dsimp [V, W, C0]
      calc
        _ ≤ 2 * Cbias * (Krate * R) + V * (Krate * R) + W * (Krate * R) := by
          gcongr
        _ = C0 * R := by dsimp [C0, V, W]; ring
    calc
      _ ≤ 2 * Cbias * h ^ beta + V * Real.sqrt (1 / ((n : ℝ) * h ^ (d : ℝ))) +
          W * (1 / ((n : ℝ) * eps n * h ^ (d : ℝ))) := by
        simpa [M, h, A, B, H, m, expo, p, V, W] using hraw
      _ ≤ C0 * R := hsum
      _ ≤ C * R := mul_le_mul_of_nonneg_right (le_max_left _ _) hR0
      _ = _ := by rfl

end

end CausalSmith.Stat.DpCateMinimax
