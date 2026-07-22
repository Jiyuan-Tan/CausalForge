/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PopulationGram

/-!
# Bias of the population local-polynomial normal equations

This module bounds the intercept bias of the population local-polynomial fit.  The bound is
uniform over the model class and the bandwidth; the Gram-matrix conditioning is supplied as an
explicit hypothesis.
-/

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory Set Matrix
open scoped BigOperators ENNReal
open Causalean.Mathlib.Analysis

private lemma uCoord_reconstruct {d : ℕ} {h : ℝ} (hh : 0 < h)
    (x0 x : Fin d → ℝ) : x0 + h • uCoord h x0 x = x := by
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, uCoord]
  rw [mul_div_cancel₀ _ hh.ne']
  ring

private lemma monomial_zero_eq {d : ℕ} (e : Fin d → ℕ) :
    monomial e (0 : Fin d → ℝ) = if e = 0 then 1 else 0 := by
  classical
  by_cases he : e = 0
  · simp [he, monomial]
  · have hex : ∃ j, e j ≠ 0 := by
      contrapose! he
      funext j
      exact he j
    obtain ⟨j, hj⟩ := hex
    rw [if_neg he, monomial, Finset.prod_eq_zero (Finset.mem_univ j)]
    simp [hj]

private lemma polynomial_at_zero {d p : ℕ} {expo : Fin p → (Fin d → ℕ)}
    (hexpo : Function.Injective expo) {icpt : Fin p} (hicpt : expo icpt = 0)
    (theta : Fin p → ℝ) :
    ∑ k, theta k * monomial (expo k) (0 : Fin d → ℝ) = theta icpt := by
  classical
  rw [Finset.sum_eq_single icpt]
  · simp [monomial_zero_eq, hicpt]
  · intro k _ hki
    have hne : expo k ≠ 0 := by
      intro hk0
      apply hki
      apply hexpo
      simpa [hicpt] using hk0
    simp [monomial_zero_eq, hne]
  · simp

private lemma armMu_holder {d : ℕ} {P : CateLaw d} {beta L : ℝ}
    (hmu : MuHolder P beta L) (a : Fin 2) :
    HolderBallStd (armMu P a) beta L (cube d) := by
  by_cases ha : a = 1
  · simpa [armMu, ha] using hmu.2
  · rw [show armMu P a = P.mu0 by
      funext x
      simp [armMu, ha]]
    exact hmu.1

private lemma bandwidth_mass_cancel' {d : ℕ} {h : ℝ} (hh : 0 < h) :
    h ^ (-(d : ℝ)) * (2 * h) ^ d = (2 : ℝ) ^ d := by
  rw [mul_pow, ← Real.rpow_natCast 2 d, ← Real.rpow_natCast h d]
  rw [show h ^ (-(d : ℝ)) * (2 ^ (d : ℝ) * h ^ (d : ℝ)) =
    2 ^ (d : ℝ) * (h ^ (-(d : ℝ)) * h ^ (d : ℝ)) by ring,
    ← Real.rpow_add hh]
  simp

private lemma feature_measurable {d p : ℕ} {h : ℝ} {x0 : Fin d → ℝ}
    {expo : Fin p → (Fin d → ℕ)} {K : (Fin d → ℝ) → ℝ}
    (hKmeas : Measurable K) (k : Fin p) :
    Measurable (fun x : Fin d → ℝ ↦
      h ^ (-(d : ℝ)) * K (uCoord h x0 x) * monomial (expo k) (uCoord h x0 x)) := by
  unfold monomial uCoord
  fun_prop

private lemma abs_feature_le {d p : ℕ} {h Kmax : ℝ} {x0 : Fin d → ℝ}
    {expo : Fin p → (Fin d → ℕ)} {K : (Fin d → ℝ) → ℝ}
    (hh : 0 < h) (hK0 : ∀ u, 0 ≤ K u) (hKmax : ∀ u, K u ≤ Kmax)
    (hKsupp : ∀ u, (∃ j, 1 < |u j|) → K u = 0) (k : Fin p) (x : Fin d → ℝ) :
    |h ^ (-(d : ℝ)) * K (uCoord h x0 x) * monomial (expo k) (uCoord h x0 x)|
      ≤ h ^ (-(d : ℝ)) * Kmax := by
  by_cases hx : x ∈ supBall x0 h
  · rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hh.le _),
      abs_of_nonneg (hK0 _)]
    have hm := abs_monomial_uCoord_le_one hh hx (expo k)
    have hKm : 0 ≤ Kmax := (hK0 0).trans (hKmax 0)
    calc
      h ^ (-(d : ℝ)) * K (uCoord h x0 x) * |monomial (expo k) (uCoord h x0 x)|
          ≤ h ^ (-(d : ℝ)) * Kmax * 1 := by
            gcongr
            exact hKmax _
      _ = h ^ (-(d : ℝ)) * Kmax := by ring
  · have hex : ∃ j, 1 < |uCoord h x0 x j| := by
      have : ∃ j, h < |x j - x0 j| := by
        simpa [supBall, not_forall, not_le] using hx
      obtain ⟨j, hj⟩ := this
      refine ⟨j, ?_⟩
      rw [uCoord, abs_div, abs_of_pos hh]
      exact (lt_div_iff₀ hh).2 (by simpa using hj)
    rw [hKsupp _ hex, mul_zero, zero_mul, abs_zero]
    exact mul_nonneg (Real.rpow_nonneg hh.le _) ((hK0 0).trans (hKmax 0))

private lemma abs_gram_feature_le {d p : ℕ} {h Kmax : ℝ} {x0 : Fin d → ℝ}
    {expo : Fin p → (Fin d → ℕ)} {K : (Fin d → ℝ) → ℝ}
    (hh : 0 < h) (hK0 : ∀ u, 0 ≤ K u) (hKmax : ∀ u, K u ≤ Kmax)
    (hKsupp : ∀ u, (∃ j, 1 < |u j|) → K u = 0) (k l : Fin p) (x : Fin d → ℝ) :
    |h ^ (-(d : ℝ)) * K (uCoord h x0 x) * monomial (expo k) (uCoord h x0 x) *
        monomial (expo l) (uCoord h x0 x)| ≤ h ^ (-(d : ℝ)) * Kmax := by
  by_cases hx : x ∈ supBall x0 h
  · have hk := abs_monomial_uCoord_le_one hh hx (expo k)
    have hl := abs_monomial_uCoord_le_one hh hx (expo l)
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hh.le _),
      abs_of_nonneg (hK0 _)]
    have hKm : 0 ≤ Kmax := (hK0 0).trans (hKmax 0)
    calc
      h ^ (-(d : ℝ)) * K (uCoord h x0 x) *
          |monomial (expo k) (uCoord h x0 x)| * |monomial (expo l) (uCoord h x0 x)|
          ≤ h ^ (-(d : ℝ)) * Kmax * 1 * 1 := by
            gcongr
            exact hKmax _
      _ = h ^ (-(d : ℝ)) * Kmax := by ring
  · have hex : ∃ j, 1 < |uCoord h x0 x j| := by
      have : ∃ j, h < |x j - x0 j| := by
        simpa [supBall, not_forall, not_le] using hx
      obtain ⟨j, hj⟩ := this
      refine ⟨j, ?_⟩
      rw [uCoord, abs_div, abs_of_pos hh]
      exact (lt_div_iff₀ hh).2 (by simpa using hj)
    rw [hKsupp _ hex, mul_zero, zero_mul, zero_mul, abs_zero]
    exact mul_nonneg (Real.rpow_nonneg hh.le _) ((hK0 0).trans (hKmax 0))

private lemma measurableSet_supBall_bias {d : ℕ} (x0 : Fin d → ℝ) (h : ℝ) :
    MeasurableSet (supBall x0 h) := by
  rw [show supBall x0 h = ⋂ i : Fin d, {x | |x i - x0 i| ≤ h} by
    ext x
    simp [supBall]]
  apply MeasurableSet.iInter
  intro i
  change MeasurableSet ((fun x : Fin d → ℝ ↦ |x i - x0 i|) ⁻¹' Set.Iic h)
  apply measurableSet_Iic.preimage
  simpa only [Real.norm_eq_abs] using
    (((measurable_pi_apply i).sub measurable_const).norm)

private lemma armProb_aemeasurable {d : ℕ} {P : CateLaw d} {alpha L : ℝ}
    (hiid : IidSampling P) (hpi : PiHolder P alpha L) (a : Fin 2) :
    AEMeasurable (armProb P a) (P.dataMeasure.map (fun O ↦ O.X)) := by
  have hcontPi : ContinuousOn P.pi (cube d) := hpi.1.continuousOn
  have hcont : ContinuousOn (armProb P a) (cube d) := by
    by_cases ha : a = 1
    · simpa [armProb, ha] using hcontPi
    · have heq : armProb P a = fun x ↦ 1 - P.pi x := by
        funext x
        simp [armProb, ha]
      rw [heq]
      exact continuousOn_const.sub hcontPi
  have hcubemeas : MeasurableSet (cube d) := by
    rw [show cube d = Set.univ.pi (fun _ : Fin d ↦ Set.Icc (0 : ℝ) 1) by
      ext x
      change (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) ↔
        ∀ i, i ∈ (Set.univ : Set (Fin d)) → x i ∈ Set.Icc (0 : ℝ) 1
      simp]
    exact MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc
  have hr : AEMeasurable (armProb P a)
      ((P.dataMeasure.map (fun O ↦ O.X)).restrict (cube d)) :=
    hcont.aemeasurable hcubemeas
  suffices hsupp : P.dataMeasure.map (fun O ↦ O.X) =
      (P.dataMeasure.map (fun O ↦ O.X)).restrict (cube d) by
    rw [hsupp]
    exact hr
  symm
  apply Measure.restrict_eq_self_of_ae_mem
  exact (ae_map_iff measurable_CateObs_X.aemeasurable hcubemeas).2 hiid.2.2.2.1

private lemma integrable_of_ae_bound_probability {d : ℕ} (P : CateLaw d)
    (hiid : IidSampling P) {f : CateObs d → ℝ} (hf : AEStronglyMeasurable f P.dataMeasure)
    {B : ℝ} (hB : ∀ᵐ O ∂P.dataMeasure, |f O| ≤ B) : Integrable f P.dataMeasure := by
  letI : IsProbabilityMeasure P.dataMeasure := hiid.1
  apply Integrable.of_bound hf B
  filter_upwards [hB] with O hO
  simpa [Real.norm_eq_abs] using hO

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
/-- The intercept of the population normal-equation solution has uniform local-polynomial bias
of order `h^β`, conditional on a uniform Loewner lower bound for the population Gram matrix. -/
theorem popGram_inv_popMom_bias {d p : ℕ}
    {alpha beta gamma L e0 f0 f1 r0 h Kmax Kmin rinner cstar Cstar : ℝ}
    {x0 : Fin d → ℝ} {P : CateLaw d} {expo : Fin p → (Fin d → ℕ)}
    {K : (Fin d → ℝ) → ℝ} {icpt : Fin p} {a : Fin 2}
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P)
    (hiid : IidSampling P) (hexpo : Function.Injective expo)
    (hicpt : expo icpt = fun _ ↦ 0)
    (hcover : ∀ e : Fin d → ℕ, (∑ j, e j) ≤ ⌈beta⌉₊ - 1 → ∃ k, expo k = e)
    (hK0 : ∀ u, 0 ≤ K u) (hKmax : ∀ u, K u ≤ Kmax)
    (hKsupp : ∀ u, (∃ j, 1 < |u j|) → K u = 0) (hKmeas : Measurable K)
    (hh : 0 < h) (hhr : h < rStar r0 x0)
    (hcstar : 0 < cstar) (hcC : cstar ≤ Cstar)
    (hloew : popGram P h x0 expo K a ∈ loewnerSet p cstar Cstar)
    {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hCbApprox : ∀ f : (Fin d → ℝ) → ℝ, HolderBallStd f beta L (cube d) →
      ∀ hh' : ℝ, 0 < hh' → hh' < rStar r0 x0 → ∃ theta : Fin p → ℝ,
        ∀ u : Fin d → ℝ, (∀ j, |u j| ≤ 1) →
          |f (x0 + hh' • u) - ∑ k, theta k * monomial (expo k) u|
            ≤ Cb * L * hh' ^ beta) :
    |((popGram P h x0 expo K a)⁻¹.mulVec (popMom P h x0 expo K a)) icpt -
        armMu P a x0| ≤
      (Real.sqrt (p : ℝ) * Cb * L * Kmax * f1 * 2 ^ d / cstar + Cb * L) *
        h ^ beta := by
  classical
  letI : IsProbabilityMeasure P.dataMeasure := hiid.1
  have hbeta : 0 < beta := hreg.2.1
  have hL : 0 < L := hreg.2.2.2.1
  have hf1 : 0 ≤ f1 := hreg.2.2.2.2.2.1.le.trans hreg.2.2.2.2.2.2.1
  have hKmax0 : 0 ≤ Kmax := (hK0 0).trans (hKmax 0)
  obtain ⟨theta, htheta⟩ := hCbApprox (armMu P a) (armMu_holder hP.muH a) h hh hhr
  let feat : Fin p → (Fin d → ℝ) → ℝ := fun k x ↦
    h ^ (-(d : ℝ)) * K (uCoord h x0 x) * monomial (expo k) (uCoord h x0 x)
  let poly : (Fin d → ℝ) → ℝ := fun x ↦
    ∑ l, theta l * monomial (expo l) (uCoord h x0 x)
  have hfeatMeas (k : Fin p) : Measurable (feat k) := feature_measurable hKmeas k
  have hfeatB (k : Fin p) (x : Fin d → ℝ) :
      |feat k x| ≤ h ^ (-(d : ℝ)) * Kmax := abs_feature_le hh hK0 hKmax hKsupp k x
  have hmuAE := armMu_aemeasurable P beta L hbeta hiid hP.muH a
  have hmuB := armMu_ae_bound P beta L hbeta hiid hP.muH a
  have hpiAE := armProb_aemeasurable hiid hP.piH a
  have hpiB := armProb_ae_bounds P e0 hreg.2.2.2.2.1.1 hiid hP.overlap a
  have hMom (k : Fin p) : popMom P h x0 expo K a k =
      ∫ O, armProb P a O.X * armMu P a O.X * feat k O.X ∂P.dataMeasure := by
    calc
      popMom P h x0 expo K a k =
          ∫ O, (if O.A = ((a : ℕ) : ℝ) then 1 else 0) * feat k O.X * O.Y
            ∂P.dataMeasure := by
        unfold popMom momSummand
        apply integral_congr_ae
        filter_upwards [clip_outcome_ae P hiid] with O hclip
        simp only [feat, hclip]
        ring
      _ = _ := integral_arm_outcome_mul P hiid hP.piProp hP.muReg a (feat k)
        (hfeatMeas k).aemeasurable (h ^ (-(d : ℝ)) * Kmax) (hfeatB k)
        hmuAE L hmuB
  have hGram (k l : Fin p) : popGram P h x0 expo K a k l =
      ∫ O, armProb P a O.X *
        (feat k O.X * monomial (expo l) (uCoord h x0 O.X)) ∂P.dataMeasure := by
    calc
      popGram P h x0 expo K a k l =
          ∫ O, (if O.A = ((a : ℕ) : ℝ) then 1 else 0) *
            (feat k O.X * monomial (expo l) (uCoord h x0 O.X)) ∂P.dataMeasure := by
        unfold popGram gramSummand
        apply integral_congr_ae
        filter_upwards with O
        simp only [feat]
        ring
      _ = _ := integral_arm_indicator_mul P hiid hP.piProp a
        (fun x ↦ feat k x * monomial (expo l) (uCoord h x0 x))
        (by
          apply Measurable.aemeasurable
          unfold feat monomial uCoord
          fun_prop)
        (h ^ (-(d : ℝ)) * Kmax)
        (abs_gram_feature_le hh hK0 hKmax hKsupp k l)
  have hGramInt (k l : Fin p) : Integrable (fun O : CateObs d ↦
      armProb P a O.X * (feat k O.X * monomial (expo l) (uCoord h x0 O.X)))
      P.dataMeasure := by
    apply integrable_of_ae_bound_probability P hiid
      (B := h ^ (-(d : ℝ)) * Kmax)
    · apply AEStronglyMeasurable.mul
      · exact (hpiAE.comp_aemeasurable
          measurable_CateObs_X.aemeasurable).aestronglyMeasurable
      · apply Measurable.aestronglyMeasurable
        unfold feat monomial uCoord
        fun_prop
    · filter_upwards [hpiB] with O hp
      rw [abs_mul, abs_of_nonneg (hreg.2.2.2.2.1.1.le.trans hp.1)]
      calc
        armProb P a O.X * |feat k O.X * monomial (expo l) (uCoord h x0 O.X)|
            ≤ 1 * |feat k O.X * monomial (expo l) (uCoord h x0 O.X)| := by
              gcongr
              exact hp.2
        _ ≤ _ := by
          dsimp only [feat]
          simpa only [one_mul] using
            (abs_gram_feature_le hh hK0 hKmax hKsupp k l O.X)
  have hGtheta (k : Fin p) : (popGram P h x0 expo K a).mulVec theta k =
      ∫ O, armProb P a O.X * feat k O.X * poly O.X ∂P.dataMeasure := by
    rw [Matrix.mulVec]
    unfold dotProduct
    simp_rw [hGram]
    simp_rw [← integral_mul_const]
    rw [← integral_finset_sum]
    · apply integral_congr_ae
      filter_upwards with O
      simp only [poly, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    · intro l _
      exact (hGramInt k l).mul_const (theta l)
  have hresPoint (k : Fin p) (x : Fin d → ℝ) :
      |feat k x * (armMu P a x - poly x)| ≤
        h ^ (-(d : ℝ)) * Kmax * (Cb * L * h ^ beta) := by
    by_cases hx : x ∈ supBall x0 h
    · have hu : ∀ j, |uCoord h x0 x j| ≤ 1 := by
        intro j
        rw [uCoord, abs_div, abs_of_pos hh]
        exact (div_le_one hh).2 (hx j)
      have ha := htheta (uCoord h x0 x) hu
      rw [uCoord_reconstruct hh x0 x] at ha
      change |feat k x * (armMu P a x - poly x)| ≤ _
      rw [abs_mul]
      exact mul_le_mul (hfeatB k x) ha (abs_nonneg _) (mul_nonneg
        (Real.rpow_nonneg hh.le _) hKmax0)
    · have hz : feat k x = 0 := by
        have hex : ∃ j, 1 < |uCoord h x0 x j| := by
          have : ∃ j, h < |x j - x0 j| := by
            simpa [supBall, not_forall, not_le] using hx
          obtain ⟨j, hj⟩ := this
          refine ⟨j, ?_⟩
          rw [uCoord, abs_div, abs_of_pos hh]
          exact (lt_div_iff₀ hh).2 (by simpa using hj)
        simp [feat, hKsupp _ hex]
      rw [hz, zero_mul, abs_zero]
      positivity
  have hcoord (k : Fin p) :
      |popMom P h x0 expo K a k - (popGram P h x0 expo K a).mulVec theta k| ≤
        Cb * L * Kmax * f1 * 2 ^ d * h ^ beta := by
    rw [hMom, hGtheta]
    have hmuInt : Integrable (fun O ↦
        armProb P a O.X * armMu P a O.X * feat k O.X) P.dataMeasure := by
      apply integrable_of_ae_bound_probability P hiid
      · exact ((hpiAE.comp_aemeasurable measurable_CateObs_X.aemeasurable).mul
          (hmuAE.comp_aemeasurable measurable_CateObs_X.aemeasurable)).mul
            ((hfeatMeas k).comp measurable_CateObs_X).aemeasurable |>.aestronglyMeasurable
      · filter_upwards [hpiB, hmuB] with O hp hm
        rw [abs_mul, abs_mul]
        have hp0 : 0 ≤ armProb P a O.X := hreg.2.2.2.2.1.1.le.trans hp.1
        rw [abs_of_nonneg hp0]
        calc
          armProb P a O.X * |armMu P a O.X| * |feat k O.X|
              ≤ 1 * L * (h ^ (-(d : ℝ)) * Kmax) := by
                gcongr
                · exact hp.2
                · exact hfeatB k O.X
          _ = L * (h ^ (-(d : ℝ)) * Kmax) := by ring
    have hgramInt : Integrable (fun O ↦
        armProb P a O.X * feat k O.X * poly O.X) P.dataMeasure := by
      have hsumint : Integrable (∑ l, fun O : CateObs d ↦ theta l *
          (armProb P a O.X * (feat k O.X *
            monomial (expo l) (uCoord h x0 O.X)))) P.dataMeasure := by
        have hs := integrable_finset_sum (Finset.univ : Finset (Fin p))
          (fun l _ ↦ (hGramInt k l).const_mul (theta l))
        convert hs using 1
        funext O
        simp only [Finset.sum_apply]
      rw [show (fun O : CateObs d ↦ armProb P a O.X * feat k O.X * poly O.X) =
          ∑ l, fun O : CateObs d ↦ theta l * (armProb P a O.X *
            (feat k O.X * monomial (expo l) (uCoord h x0 O.X))) by
        funext O
        simp only [poly, Finset.sum_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring]
      exact hsumint
    rw [← integral_sub hmuInt hgramInt]
    have hqint := hmuInt.sub hgramInt
    have hS : MeasurableSet {O : CateObs d | O.X ∈ supBall x0 h} :=
      (measurableSet_supBall_bias x0 h).preimage measurable_CateObs_X
    calc
      |∫ O, armProb P a O.X * armMu P a O.X * feat k O.X -
          armProb P a O.X * feat k O.X * poly O.X ∂P.dataMeasure|
          ≤ ∫ O, |armProb P a O.X * armMu P a O.X * feat k O.X -
              armProb P a O.X * feat k O.X * poly O.X| ∂P.dataMeasure :=
        abs_integral_le_integral_abs
      _ ≤ ∫ O, ({O : CateObs d | O.X ∈ supBall x0 h}.indicator
          (fun _ ↦ h ^ (-(d : ℝ)) * Kmax * (Cb * L * h ^ beta))) O
          ∂P.dataMeasure := by
        apply integral_mono_ae hqint.abs ((integrable_const _).indicator hS)
        filter_upwards [hpiB] with O hp
        by_cases hO : O.X ∈ supBall x0 h
        · rw [Set.indicator_of_mem (show O ∈ {O : CateObs d | O.X ∈ supBall x0 h}
              from hO)]
          change |armProb P a O.X * armMu P a O.X * feat k O.X -
            armProb P a O.X * feat k O.X * poly O.X| ≤ _
          rw [show armProb P a O.X * armMu P a O.X * feat k O.X -
              armProb P a O.X * feat k O.X * poly O.X =
              armProb P a O.X * (feat k O.X * (armMu P a O.X - poly O.X)) by ring,
            abs_mul, abs_of_nonneg (hreg.2.2.2.2.1.1.le.trans hp.1)]
          calc
            armProb P a O.X * |feat k O.X * (armMu P a O.X - poly O.X)|
                ≤ 1 * |feat k O.X * (armMu P a O.X - poly O.X)| := by
                  gcongr
                  exact hp.2
            _ ≤ _ := by simpa using hresPoint k O.X
        · simp [hO,
            show feat k O.X = 0 by
              have hex : ∃ j, 1 < |uCoord h x0 O.X j| := by
                have : ∃ j, h < |O.X j - x0 j| := by
                  simpa [supBall, not_forall, not_le] using hO
                obtain ⟨j, hj⟩ := this
                refine ⟨j, ?_⟩
                rw [uCoord, abs_div, abs_of_pos hh]
                exact (lt_div_iff₀ hh).2 (by simpa using hj)
              simp [feat, hKsupp _ hex]]
      _ = h ^ (-(d : ℝ)) * Kmax * (Cb * L * h ^ beta) *
          (P.dataMeasure.map (fun O ↦ O.X)).real (supBall x0 h) := by
        rw [integral_indicator hS]
        simp only [integral_const, Measure.real, smul_eq_mul]
        rw [Measure.map_apply measurable_CateObs_X
          (measurableSet_supBall_bias x0 h), Measure.restrict_apply_univ]
        rw [show {O : CateObs d | O.X ∈ supBall x0 h} =
          (fun O ↦ O.X) ⁻¹' supBall x0 h by rfl]
        ring
      _ ≤ h ^ (-(d : ℝ)) * Kmax * (Cb * L * h ^ beta) *
          (f1 * (2 * h) ^ d) := by
        gcongr
        exact design_mass_le P f0 f1 r0 x0 hiid hP.pxDens hP.localDensity hf1 hh
          (hhr.le.trans (by
            unfold rStar
            have := min_le_left r0 (⨅ i : Fin d, min (x0 i) (1 - x0 i))
            have hr0 : 0 < r0 := hreg.2.2.2.2.2.2.2.1.1
            linarith))
      _ = Cb * L * Kmax * f1 * 2 ^ d * h ^ beta := by
        rw [show h ^ (-(d : ℝ)) * Kmax * (Cb * L * h ^ beta) *
            (f1 * (2 * h) ^ d) =
          (Cb * L * Kmax * f1 * h ^ beta) *
            (h ^ (-(d : ℝ)) * (2 * h) ^ d) by ring,
          bandwidth_mass_cancel' hh]
        ring
  let G := popGram P h x0 expo K a
  let m := popMom P h x0 expo K a
  let r : Fin p → ℝ := fun k ↦ m k - G.mulVec theta k
  let B : ℝ := Cb * L * Kmax * f1 * 2 ^ d * h ^ beta
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hrcoord (k : Fin p) : |r k| ≤ B := by
    simpa [r, m, G, B] using hcoord k
  have hrsum : ∑ k, (r k) ^ 2 ≤ (p : ℝ) * B ^ 2 := by
    calc
      ∑ k, (r k) ^ 2 ≤ ∑ _k : Fin p, B ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        have hlo : -B ≤ r k := neg_le_of_abs_le (hrcoord k)
        have hhi : r k ≤ B := le_of_abs_le (hrcoord k)
        nlinarith
      _ = (p : ℝ) * B ^ 2 := by simp
  have hrnorm : Real.sqrt (∑ k, (r k) ^ 2) ≤ Real.sqrt (p : ℝ) * B := by
    calc
      Real.sqrt (∑ k, (r k) ^ 2) ≤ Real.sqrt ((p : ℝ) * B ^ 2) :=
        Real.sqrt_le_sqrt hrsum
      _ = Real.sqrt (p : ℝ) * B := by
        rw [Real.sqrt_mul (Nat.cast_nonneg p), Real.sqrt_sq_eq_abs, abs_of_nonneg hB0]
  have hpd : G.PosDef := loewnerSet_posDef hcstar hcC hloew
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hpd.isUnit
  have hinvtheta : G⁻¹.mulVec (G.mulVec theta) = theta := by
    calc
      G⁻¹.mulVec (G.mulVec theta) = (G⁻¹ * G).mulVec theta :=
        Matrix.mulVec_mulVec theta G⁻¹ G
      _ = theta := by rw [Matrix.nonsing_inv_mul G hdet, Matrix.one_mulVec]
  have hz : (fun k ↦ G⁻¹.mulVec m k - theta k) = G⁻¹.mulVec r := by
    funext k
    rw [← hinvtheta]
    change G⁻¹.mulVec m k - G⁻¹.mulVec (G.mulVec theta) k =
      G⁻¹.mulVec (m - G.mulVec theta) k
    exact congrFun (Matrix.mulVec_sub G⁻¹ m (G.mulVec theta)) k |>.symm
  have hzinv : Real.sqrt (∑ k, (G⁻¹.mulVec r k) ^ 2) ≤
      Real.sqrt (∑ k, (r k) ^ 2) / cstar :=
    loewnerSet_inv_mulVec_norm_le hcstar hcC hloew r
  have hznorm : Real.sqrt (∑ k, (G⁻¹.mulVec m k - theta k) ^ 2) ≤
      Real.sqrt (p : ℝ) * B / cstar := by
    simp_rw [congrFun hz]
    exact hzinv.trans (div_le_div_of_nonneg_right hrnorm hcstar.le)
  have hcoordnorm : |G⁻¹.mulVec m icpt - theta icpt| ≤
      Real.sqrt (∑ k, (G⁻¹.mulVec m k - theta k) ^ 2) := by
    have hsquare : (G⁻¹.mulVec m icpt - theta icpt) ^ 2 ≤
        ∑ k, (G⁻¹.mulVec m k - theta k) ^ 2 := by
      exact Finset.single_le_sum (fun k _ ↦ sq_nonneg (G⁻¹.mulVec m k - theta k))
        (Finset.mem_univ icpt)
    calc
      |G⁻¹.mulVec m icpt - theta icpt| =
          Real.sqrt ((G⁻¹.mulVec m icpt - theta icpt) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt (∑ k, (G⁻¹.mulVec m k - theta k) ^ 2) :=
        Real.sqrt_le_sqrt hsquare
  have hintercept : |theta icpt - armMu P a x0| ≤ Cb * L * h ^ beta := by
    have hz := htheta (0 : Fin d → ℝ) (by simp)
    rw [abs_sub_comm]
    simpa [polynomial_at_zero hexpo hicpt theta] using hz
  calc
    |G⁻¹.mulVec m icpt - armMu P a x0| ≤
        |G⁻¹.mulVec m icpt - theta icpt| + |theta icpt - armMu P a x0| := by
      calc
        |G⁻¹.mulVec m icpt - armMu P a x0| =
            |(G⁻¹.mulVec m icpt - theta icpt) +
              (theta icpt - armMu P a x0)| := by
                congr 1
                ring
        _ ≤ _ := abs_add_le _ _
    _ ≤ Real.sqrt (p : ℝ) * B / cstar + Cb * L * h ^ beta :=
      add_le_add (hcoordnorm.trans hznorm) hintercept
    _ = (Real.sqrt (p : ℝ) * Cb * L * Kmax * f1 * 2 ^ d / cstar + Cb * L) *
        h ^ beta := by
      simp only [B]
      ring

end CausalSmith.Stat.DpCateMinimax
