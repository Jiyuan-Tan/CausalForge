/- Copyright (c) 2026 Jiyuan Tan. All rights reserved. -/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.DivergenceLocalized
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.DpContractionAux
import Causalean.Stat.Minimax.TotalVariation

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory ProbabilityTheory
open Causalean.Stat
open Causalean.Mathlib.Probability
open scoped ENNReal

private lemma twoPointMean_event_gap {u : ℝ} (hu : |u| ≤ 1)
    {S : Set ℝ} (hS : MeasurableSet S) :
    |(twoPointMean 1 u).real S - (twoPointMean 1 0).real S| ≤ |u| / 2 := by
  rcases abs_le.mp hu with ⟨hu0, hu1⟩
  have hplus : 0 ≤ (1 + u) / 2 := by linarith
  have hminus : 0 ≤ (1 - u) / 2 := by linarith
  unfold twoPointMean
  simp only [Measure.real, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hS]
  by_cases hp : (1 : ℝ) ∈ S <;> by_cases hm : (-1 : ℝ) ∈ S <;>
    simp [hp, hm, ENNReal.toReal_add, ENNReal.toReal_ofReal hplus,
      ENNReal.toReal_ofReal hminus] <;> ring_nf <;>
      try simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
        abs_of_nonpos (by norm_num : (-1 / 2 : ℝ) ≤ 0)]
  all_goals first | positivity | nlinarith [abs_nonneg u, le_abs_self u, neg_abs_le u]

/-- A shared-base mixture inherits any measurable pointwise event-gap envelope. -/
private lemma tvDist_bind_le_integral {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (m : Measure X) (κ η : Kernel X Y)
    [IsProbabilityMeasure m] [IsMarkovKernel κ] [IsMarkovKernel η]
    (g : X → ℝ) (hgint : Integrable g m)
    (hgap : ∀ x (S : Set Y), MeasurableSet S →
      |(κ x).real S - (η x).real S| ≤ g x) :
    tvDist (m.bind κ) (m.bind η) ≤ ∫ x, g x ∂m := by
  refine ciSup_le fun S => ?_
  have hκint : Integrable (fun x => (κ x).real S.1) m :=
    Integrable.of_bound
      ((Measure.measurable_coe S.2).ennreal_toReal.comp κ.measurable).aestronglyMeasurable 1
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
        exact measureReal_le_one)
  have hηint : Integrable (fun x => (η x).real S.1) m :=
    Integrable.of_bound
      ((Measure.measurable_coe S.2).ennreal_toReal.comp η.measurable).aestronglyMeasurable 1
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
        exact measureReal_le_one)
  rw [measureReal_bind_eq_integral m κ κ.measurable (fun x => inferInstance) S.1 S.2,
    measureReal_bind_eq_integral m η η.measurable (fun x => inferInstance) S.1 S.2,
    ← integral_sub hκint hηint]
  calc
    |∫ x, ((κ x).real S.1 - (η x).real S.1) ∂m|
        ≤ ∫ x, |(κ x).real S.1 - (η x).real S.1| ∂m :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, g x ∂m :=
      integral_mono_ae (hκint.sub hηint).abs hgint
        (ae_of_all _ fun x => hgap x S.1 S.2)

private lemma integral_cateWitnessAX_fst {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) (C : ℝ)
    (hfb : ∀ x, ‖f x‖ ≤ C)
    [IsProbabilityMeasure Q.PX]
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) :
    ∫ p, f p.1 ∂cateWitnessAXMeasure Q e0 = ∫ x, f x ∂Q.PX := by
  letI : IsProbabilityMeasure (cateWitnessTreatmentMeasure e0) :=
    cateWitnessTreatmentMeasure_isProbabilityMeasure he0 he1
  haveI : IsProbabilityMeasure (cateWitnessAXMeasure Q e0) :=
    cateWitnessAXMeasure_isProbabilityMeasure Q e0 he0 he1
  have hfint : Integrable (fun p : (Fin d → ℝ) × Bool => f p.1)
      (cateWitnessAXMeasure Q e0) :=
    Integrable.of_bound (hf.comp measurable_fst).aestronglyMeasurable C
      (ae_of_all _ fun p => hfb p.1)
  unfold cateWitnessAXMeasure
  rw [Causalean.Mathlib.MeasureTheory.integral_bind
    (Measurable.map_prodMk_left
      (ν := cateWitnessTreatmentMeasure e0)) hfint]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [integral_map (μ := cateWitnessTreatmentMeasure e0)
    (φ := fun a : Bool => (x, a)) (f := fun p : (Fin d → ℝ) × Bool => f p.1)
    measurable_prodMk_left.aemeasurable
    (hf.comp measurable_fst).aestronglyMeasurable]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    one_smul]

/-- The one-draw TV of the witness is controlled linearly (rather than through
Pinsker) by the localized contrast mass. -/
lemma cateWitness_tv_single_le {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    (b : (Fin d → ℝ) → ℝ) [IsProbabilityMeasure Q.PX]
    (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1 / 2)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) :
    tvDist (cateWitnessLaw Q e0 b).dataMeasure
        (cateWitnessLaw Q e0 0).dataMeasure ≤ ∫ x, |b x| / 2 ∂Q.PX := by
  let m := cateWitnessAXMeasure Q e0
  let κ := cateWitnessChannel e0 b hbmeas
  let η := cateWitnessChannel e0 (0 : (Fin d → ℝ) → ℝ) measurable_const
  letI : IsProbabilityMeasure m := cateWitnessAXMeasure_isProbabilityMeasure Q e0 he0 he1
  letI : IsMarkovKernel κ := cateWitnessChannel_isMarkov e0 b hbmeas hb
  letI : IsMarkovKernel η := cateWitnessChannel_isMarkov e0 0 measurable_const (by simp)
  have habsmeas : Measurable (fun x => |b x| / 2) := by fun_prop
  have hgint : Integrable (fun p : (Fin d → ℝ) × Bool => |b p.1| / 2) m :=
    Integrable.of_bound (habsmeas.comp measurable_fst).aestronglyMeasurable 1
      (ae_of_all _ fun p => by
        rw [Real.norm_eq_abs, abs_div, abs_abs]
        norm_num
        linarith [hb p.1, abs_nonneg (b p.1)])
  have hgap (p : (Fin d → ℝ) × Bool) (S : Set (CateObs d)) (hS : MeasurableSet S) :
      |(κ p).real S - (η p).real S| ≤ |b p.1| / 2 := by
    let pack := cateWitnessPack (d := d) p.1 p.2
    have hpack : Measurable pack := by dsimp [pack]; rw [measurable_comap_iff]; fun_prop
    have hpre : MeasurableSet (pack ⁻¹' S) := hS.preimage hpack
    rw [cateWitnessChannel_apply, cateWitnessChannel_apply]
    simp only [Pi.zero_apply, ite_self]
    change |((twoPointMean 1 (if p.2 then b p.1 else 0)).map pack).real S -
      ((twoPointMean 1 0).map pack).real S| ≤ |b p.1| / 2
    change |(((twoPointMean 1 (if p.2 then b p.1 else 0)).map pack) S).toReal -
      (((twoPointMean 1 0).map pack) S).toReal| ≤ |b p.1| / 2
    rw [Measure.map_apply hpack hS, Measure.map_apply hpack hS]
    have hmean : |if p.2 then b p.1 else 0| ≤ 1 := by
      split
      · exact (hb p.1).trans (by norm_num)
      · norm_num
    have h := twoPointMean_event_gap hmean hpre
    change |((twoPointMean 1 (if p.2 then b p.1 else 0))
      (pack ⁻¹' S)).toReal - ((twoPointMean 1 0) (pack ⁻¹' S)).toReal| ≤
        |if p.2 then b p.1 else 0| / 2 at h
    split at *
    all_goals simp_all only [Bool.true_eq, Bool.false_eq_true, ↓reduceIte, abs_div, abs_neg]
    all_goals norm_num at h hmean ⊢
    all_goals nlinarith [abs_nonneg (b p.1)]
  change tvDist (cateWitnessDataMeasure Q e0 b) (cateWitnessDataMeasure Q e0 0) ≤ _
  rw [
    cateWitnessDataMeasure_eq_AXbind Q e0 b hbmeas,
    cateWitnessDataMeasure_eq_AXbind Q e0 0 measurable_const]
  change tvDist (m.bind κ) (m.bind η) ≤ _
  calc
    tvDist (m.bind κ) (m.bind η) ≤ ∫ p, |b p.1| / 2 ∂m :=
      tvDist_bind_le_integral m κ η _ hgint hgap
    _ = ∫ x, |b x| / 2 ∂Q.PX := integral_cateWitnessAX_fst Q e0 _ habsmeas 1
      (fun x => by rw [Real.norm_eq_abs, abs_div, abs_abs]; norm_num
                   linarith [hb x, abs_nonneg (b x)]) he0 he1

lemma cateWitness_tv_single_le_mass {d : ℕ} (Q : CateLaw d) (e0 a : ℝ)
    (b : (Fin d → ℝ) → ℝ) (S : Set (Fin d → ℝ)) [IsProbabilityMeasure Q.PX]
    (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1 / 2)
    (hS : MeasurableSet S) (ha : 0 ≤ a)
    (hlocal : ∀ x, x ∈ S → |b x| ≤ a) (hsupp : ∀ x, x ∉ S → b x = 0)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) :
    tvDist (cateWitnessLaw Q e0 b).dataMeasure
        (cateWitnessLaw Q e0 0).dataMeasure ≤ (a / 2) * (Q.PX S).toReal := by
  calc
    tvDist (cateWitnessLaw Q e0 b).dataMeasure
        (cateWitnessLaw Q e0 0).dataMeasure ≤ ∫ x, |b x| / 2 ∂Q.PX :=
      cateWitness_tv_single_le Q e0 b hbmeas hb he0 he1
    _ ≤ ∫ x, S.indicator (fun _ => a / 2) x ∂Q.PX := by
      apply integral_mono_ae
      · exact Integrable.of_bound (by fun_prop) 1
          (ae_of_all _ fun x => by
            rw [Real.norm_eq_abs, abs_div, abs_abs]
            norm_num
            linarith [hb x, abs_nonneg (b x)])
      · exact (integrable_const (a / 2)).indicator hS
      · exact ae_of_all _ fun x => by
          by_cases hx : x ∈ S
          · simp only [Set.indicator_of_mem hx]
            exact div_le_div_of_nonneg_right (hlocal x hx) (by norm_num)
          · simp [Set.indicator_of_notMem hx, hsupp x hx]
    _ = (a / 2) * (Q.PX S).toReal := by
      rw [integral_indicator hS, setIntegral_const, smul_eq_mul]
      rw [measureReal_def]
      ring

lemma localized_bump_tv_single_le {d : ℕ}
    (Q : CateLaw d) (e0 f0 f1 r0 gamma cB h : ℝ) (x0 : Fin d → ℝ)
    (hQ : LocalDensity Q f0 f1 r0 x0) (hQdens : PxIsXDensity Q)
    (hQmarg : PXIsXMarginal Q) (hQiid : IidSampling Q)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) (hf1 : 0 ≤ f1)
    (hcB : 0 ≤ cB) (hcB1 : cB ≤ 1 / 2) (hgamma : 0 < gamma)
    (hh : 0 < h) (hhr : h ≤ r0) (hh1 : h ≤ 1) :
    tvDist
      (cateWitnessLaw Q e0 (fun x => cB * h ^ gamma *
        causalCubeBump (fun i => (x i - x0 i) / h))).dataMeasure
      (cateWitnessLaw Q e0 0).dataMeasure ≤
      (cB * h ^ gamma / 2) * f1 * (2 * h) ^ d := by
  let b : (Fin d → ℝ) → ℝ := fun x => cB * h ^ gamma *
    causalCubeBump (fun i => (x i - x0 i) / h)
  let S := supBall x0 h
  haveI : IsProbabilityMeasure Q.dataMeasure := hQiid.1
  haveI : IsProbabilityMeasure Q.PX := by
    rw [hQmarg]
    exact Measure.isProbabilityMeasure_map measurable_CateObs_X.aemeasurable
  have hbmeas : Measurable b := by
    exact (((causalCubeBump_contDiff (d := d)).continuous.measurable.comp
      (by fun_prop)).const_mul (cB * h ^ gamma))
  have hp := Real.rpow_le_one hh.le hh1 hgamma.le
  have hb : ∀ x, |b x| ≤ 1 / 2 := by
    intro x
    have hB := causalCubeBump_bounds (fun i => (x i - x0 i) / h)
    rw [abs_mul, abs_mul, abs_of_nonneg hcB,
      abs_of_nonneg (Real.rpow_nonneg hh.le gamma), abs_of_nonneg hB.1]
    calc
      cB * h ^ gamma * causalCubeBump (fun i => (x i - x0 i) / h)
          ≤ (1 / 2) * 1 * 1 := by gcongr <;> tauto
      _ = 1 / 2 := by norm_num
  have hlocal : ∀ x, x ∈ S → |b x| ≤ cB * h ^ gamma := by
    intro x hx
    have hB := causalCubeBump_bounds (fun i => (x i - x0 i) / h)
    rw [abs_mul, abs_mul, abs_of_nonneg hcB,
      abs_of_nonneg (Real.rpow_nonneg hh.le gamma), abs_of_nonneg hB.1]
    exact mul_le_of_le_one_right
      (mul_nonneg hcB (Real.rpow_nonneg hh.le gamma)) hB.2
  have hsupp : ∀ x, x ∉ S → b x = 0 := by
    intro x hx
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
  have htv := cateWitness_tv_single_le_mass Q e0 (cB * h ^ gamma) b S
    hbmeas hb (measurableSet_supBall x0 h) (mul_nonneg hcB (Real.rpow_nonneg hh.le _))
    hlocal hsupp he0 he1
  change tvDist (cateWitnessLaw Q e0 b).dataMeasure
      (cateWitnessLaw Q e0 0).dataMeasure ≤ _
  have hmass := localDensity_PX_supBall_le Q f0 f1 r0 h x0 hQ hQdens hQmarg
    hf1 hh.le hhr
  have hmassReal : (Q.PX S).toReal ≤ f1 * (2 * h) ^ d := by
    have hm := ENNReal.toReal_mono (by finiteness) hmass
    simpa [S, ENNReal.toReal_mul, ENNReal.toReal_ofReal hf1,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hh.le,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * h)] using hm
  exact htv.trans (by
    calc
      (cB * h ^ gamma / 2) * (Q.PX S).toReal
          ≤ (cB * h ^ gamma / 2) * (f1 * (2 * h) ^ d) := by gcongr
      _ = _ := by ring)

end CausalSmith.Stat.DpCateMinimax
