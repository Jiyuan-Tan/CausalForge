/- Copyright (c) 2026 Jiyuan Tan. All rights reserved. -/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.BumpHolder
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.TwoPointDivergence

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory ProbabilityTheory
open scoped ENNReal

lemma measurableSet_supBall {d : ℕ} (x0 : Fin d → ℝ) (h : ℝ) :
    MeasurableSet (supBall x0 h) := by
  rw [show supBall x0 h = Set.Icc (fun i => x0 i - h) (fun i => x0 i + h) by
    ext x
    simp only [supBall, Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def]
    constructor
    · intro hx
      constructor <;> intro i
      · linarith [(abs_le.mp (hx i)).1]
      · linarith [(abs_le.mp (hx i)).2]
    · rintro ⟨hxlo, hxhi⟩ i
      exact abs_le.mpr ⟨by linarith [hxlo i], by linarith [hxhi i]⟩]
  exact measurableSet_Icc

lemma volume_supBall {d : ℕ} (x0 : Fin d → ℝ) {h : ℝ} (hh : 0 ≤ h) :
    volume (supBall x0 h) = ENNReal.ofReal (2 * h) ^ d := by
  rw [show supBall x0 h = Set.Icc (fun i => x0 i - h) (fun i => x0 i + h) by
    ext x
    simp only [supBall, Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def]
    constructor
    · intro hx
      exact ⟨fun i => by linarith [(abs_le.mp (hx i)).1],
        fun i => by linarith [(abs_le.mp (hx i)).2]⟩
    · rintro ⟨hxlo, hxhi⟩ i
      exact abs_le.mpr ⟨by linarith [hxlo i], by linarith [hxhi i]⟩,
    Real.volume_Icc_pi]
  simp_rw [show ∀ i : Fin d, x0 i + h - (x0 i - h) = 2 * h by
    intro i; ring]
  simp [Finset.prod_const]

lemma localDensity_PX_supBall_le {d : ℕ} (Q : CateLaw d) (f0 f1 r0 h : ℝ)
    (x0 : Fin d → ℝ) (hQ : LocalDensity Q f0 f1 r0 x0)
    (hQdens : PxIsXDensity Q) (hQmarg : PXIsXMarginal Q)
    (hf1 : 0 ≤ f1) (hh : 0 ≤ h) (hhr : h ≤ r0) :
    Q.PX (supBall x0 h) ≤ ENNReal.ofReal f1 * ENNReal.ofReal (2 * h) ^ d := by
  rw [hQmarg, hQdens, withDensity_apply _ (measurableSet_supBall x0 h)]
  calc
    ∫⁻ x in supBall x0 h, ENNReal.ofReal (Q.px x) ∂volume.restrict (cube d)
        ≤ ∫⁻ _x in supBall x0 h, ENNReal.ofReal f1 ∂volume.restrict (cube d) := by
      refine setLIntegral_mono_ae measurable_const.aemeasurable ?_
      have hcube : ∀ᵐ x ∂volume.restrict (cube d), x ∈ cube d :=
        ae_restrict_mem (CausalSmith.Stat.DoseResponseMinimax.measurableSet_cube d)
      filter_upwards [hcube] with x hxc
      intro hx
      apply ENNReal.ofReal_le_ofReal
      exact (hQ x (fun i => (hx i).trans hhr) hxc).2
    _ ≤ ENNReal.ofReal f1 * volume (supBall x0 h) := by
      rw [setLIntegral_const]
      gcongr
      exact Measure.restrict_le_self
    _ = _ := by rw [volume_supBall x0 hh]

lemma localized_bump_kl_single_le {d : ℕ}
    (Q : CateLaw d) (e0 f0 f1 r0 gamma cB h : ℝ) (x0 : Fin d → ℝ)
    (hQ : LocalDensity Q f0 f1 r0 x0) (hQdens : PxIsXDensity Q)
    (hQmarg : PXIsXMarginal Q) (hQiid : IidSampling Q)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) (hf1 : 0 ≤ f1)
    (hcB : 0 ≤ cB) (hcB1 : cB ≤ 1 / 2) (hgamma : 0 < gamma) (hh : 0 < h) (hhr : h ≤ r0)
    (hh1 : h ≤ 1) :
    InformationTheory.klDiv
      (cateWitnessLaw Q e0 (fun x => cB * h ^ gamma *
        causalCubeBump (fun i => (x i - x0 i) / h))).dataMeasure
      (cateWitnessLaw Q e0 0).dataMeasure ≤
      ENNReal.ofReal (2 * cB ^ 2 * h ^ (2 * gamma) * f1) *
        ENNReal.ofReal (2 * h) ^ d := by
  classical
  let b : (Fin d → ℝ) → ℝ := fun x => cB * h ^ gamma *
    causalCubeBump (fun i => (x i - x0 i) / h)
  have hbmeas : Measurable b := by
    exact (((causalCubeBump_contDiff (d := d)).continuous.measurable.comp
      (by fun_prop)).const_mul (cB * h ^ gamma))
  have hb : ∀ x, |b x| ≤ 1 / 2 := by
    intro x
    have hp := Real.rpow_le_one hh.le hh1 hgamma.le
    have hB := causalCubeBump_bounds (fun i => (x i - x0 i) / h)
    rw [abs_mul, abs_mul, abs_of_nonneg hcB,
      abs_of_nonneg (Real.rpow_nonneg hh.le gamma), abs_of_nonneg hB.1]
    calc
      cB * h ^ gamma * causalCubeBump (fun i => (x i - x0 i) / h)
          ≤ (1 / 2) * 1 * 1 := by
            gcongr
            · exact hB.1
            · exact hB.2
      _ = 1 / 2 := by norm_num
  haveI : IsProbabilityMeasure Q.dataMeasure := hQiid.1
  haveI : IsProbabilityMeasure Q.PX := by
    rw [hQmarg]
    exact Measure.isProbabilityMeasure_map measurable_CateObs_X.aemeasurable
  have hsqmeas : Measurable (fun x => ENNReal.ofReal (2 * (b x) ^ 2)) :=
    ((hbmeas.pow_const 2).const_mul 2).ennreal_ofReal
  calc
    InformationTheory.klDiv (cateWitnessLaw Q e0 b).dataMeasure
        (cateWitnessLaw Q e0 0).dataMeasure
        ≤ ∫⁻ p, ENNReal.ofReal (2 * (b p.1) ^ 2) ∂cateWitnessAXMeasure Q e0 :=
      cateWitness_kl_single_le Q e0 b hbmeas hb he0 he1
    _ = ∫⁻ x, ENNReal.ofReal (2 * (b x) ^ 2) ∂Q.PX :=
      lintegral_cateWitnessAX_fst Q e0 _ hsqmeas he0 he1
    _ ≤ ENNReal.ofReal (2 * cB ^ 2 * h ^ (2 * gamma) * f1) *
        ENNReal.ofReal (2 * h) ^ d := by
      rw [hQmarg, hQdens]
      let S := supBall x0 h
      let C := 2 * cB ^ 2 * h ^ (2 * gamma)
      have hC : 0 ≤ C := by dsimp [C]; positivity
      have hpoint : (fun x => ENNReal.ofReal (2 * (b x) ^ 2)) ≤
          fun x => S.indicator (fun _ => ENNReal.ofReal C) x := by
        intro x
        by_cases hx : x ∈ S
        · change ENNReal.ofReal (2 * b x ^ 2) ≤ S.indicator (fun _ => ENNReal.ofReal C) x
          rw [Set.indicator_of_mem hx]
          apply ENNReal.ofReal_le_ofReal
          dsimp [b, C]
          have hB := causalCubeBump_bounds (fun i => (x i - x0 i) / h)
          have hp : (h ^ gamma) ^ 2 = h ^ (2 * gamma) := by
            rw [← Real.rpow_mul_natCast hh.le]
            congr 1; ring
          rw [mul_pow, mul_pow, hp]
          have hsquare : (causalCubeBump (fun i => (x i - x0 i) / h)) ^ 2 ≤ 1 := by
            nlinarith [sq_nonneg
              (1 - causalCubeBump (fun i => (x i - x0 i) / h))]
          have hcoef : 0 ≤ 2 * cB ^ 2 * h ^ (2 * gamma) := by positivity
          nlinarith [mul_nonneg hcoef (sub_nonneg.mpr hsquare)]
        · have hout : b x = 0 := by
            dsimp [b]
            rw [mul_eq_zero]
            right
            apply causalCubeBump_support
            by_contra hn
            push_neg at hn
            apply hx
            intro i
            have hni := hn i
            rw [abs_div, abs_of_pos hh] at hni
            simpa using (div_le_iff₀ hh).mp hni
          simp [Set.indicator_of_notMem hx, hout]
      calc
        ∫⁻ x, ENNReal.ofReal (2 * b x ^ 2)
            ∂((volume.restrict (cube d)).withDensity fun x => ENNReal.ofReal (Q.px x))
            ≤ ∫⁻ x, S.indicator (fun _ => ENNReal.ofReal C) x
                ∂((volume.restrict (cube d)).withDensity fun x => ENNReal.ofReal (Q.px x)) :=
          lintegral_mono hpoint
        _ = ENNReal.ofReal C *
            ((volume.restrict (cube d)).withDensity fun x => ENNReal.ofReal (Q.px x)) S := by
          rw [lintegral_indicator (measurableSet_supBall x0 h), lintegral_const]
          rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        _ ≤ ENNReal.ofReal C * (ENNReal.ofReal f1 * volume S) := by
          gcongr
          rw [withDensity_apply _ (measurableSet_supBall x0 h)]
          calc
            ∫⁻ x in S, ENNReal.ofReal (Q.px x) ∂volume.restrict (cube d)
                ≤ ∫⁻ _x in S, ENNReal.ofReal f1 ∂volume.restrict (cube d) := by
              refine setLIntegral_mono_ae measurable_const.aemeasurable ?_
              have hcube : ∀ᵐ x ∂volume.restrict (cube d), x ∈ cube d :=
                ae_restrict_mem
                  (CausalSmith.Stat.DoseResponseMinimax.measurableSet_cube d)
              filter_upwards [hcube] with x hxc
              intro hx
              apply ENNReal.ofReal_le_ofReal
              apply (hQ x ?_ hxc).2
              intro i
              exact le_trans (hx i) hhr
            _ ≤ ENNReal.ofReal f1 * volume S := by
              rw [setLIntegral_const]
              gcongr
              exact Measure.restrict_le_self
        _ = ENNReal.ofReal (C * f1) * ENNReal.ofReal (2 * h) ^ d := by
          rw [volume_supBall x0 hh.le, ENNReal.ofReal_mul hC]
          ring
        _ = _ := by simp [C]

end CausalSmith.Stat.DpCateMinimax
