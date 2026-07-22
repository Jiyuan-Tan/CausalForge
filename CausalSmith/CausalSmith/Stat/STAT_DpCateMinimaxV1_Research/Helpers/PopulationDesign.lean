/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Population identities and local design comparisons

This file proves the population tower identities used for arm-specific CATE
quantities, derives measurable and bounded representatives of the nuisance
regressions on the covariate support, and compares the design distribution with
Lebesgue measure under the local density bounds.  No measurability of the
law-side density field is assumed.
-/

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory
open scoped ENNReal

/-- The arm-`a` selection probability is the propensity in arm one and its complement in arm zero. -/
def armProb {d : ℕ} (P : CateLaw d) (a : Fin 2) (x : Fin d → ℝ) : ℝ :=
  if a = 1 then P.pi x else 1 - P.pi x

/-- The arm-`a` regression is `μ₁` in arm one and `μ₀` in arm zero. -/
def armMu {d : ℕ} (P : CateLaw d) (a : Fin 2) (x : Fin d → ℝ) : ℝ :=
  if a = 1 then P.mu1 x else P.mu0 x

private lemma integrable_armIndicator {d : ℕ} (P : CateLaw d) (hiid : IidSampling P)
    (a : Fin 2) : Integrable (fun O : CateObs d =>
      if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0) P.dataMeasure := by
  letI : IsProbabilityMeasure P.dataMeasure := hiid.1
  apply Integrable.of_bound (C := 1)
  · exact Measurable.ite (measurableSet_eq_fun measurable_CateObs_A measurable_const)
      measurable_const measurable_const |>.aestronglyMeasurable
  · filter_upwards with O
    split <;> simp

private lemma condExp_armIndicator {d : ℕ} (P : CateLaw d) (hiid : IidSampling P)
    (hpi : PiIsPropensity P) (a : Fin 2) :
    P.dataMeasure[(fun O => if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0) |
        MeasurableSpace.comap (fun O : CateObs d => O.X) inferInstance]
      =ᵐ[P.dataMeasure] (fun O => armProb P a O.X) := by
  letI : IsProbabilityMeasure P.dataMeasure := hiid.1
  fin_cases a
  · have hind : (fun O : CateObs d => if O.A = (0 : ℝ) then (1 : ℝ) else 0) =ᵐ[P.dataMeasure]
        (fun O => 1 - (if O.A = (1 : ℝ) then (1 : ℝ) else 0)) := by
      filter_upwards [hiid.2.2.1] with O hA
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
      rcases hA with hA | hA <;> simp [hA]
    calc
      P.dataMeasure[(fun O => if O.A = ((0 : Fin 2) : ℕ) then (1 : ℝ) else 0) |
          MeasurableSpace.comap (fun O : CateObs d => O.X) inferInstance]
          =ᵐ[P.dataMeasure]
          P.dataMeasure[(fun O => 1 - (if O.A = (1 : ℝ) then (1 : ℝ) else 0)) |
            MeasurableSpace.comap (fun O : CateObs d => O.X) inferInstance] :=
        condExp_congr_ae (by simpa using hind)
      _ =ᵐ[P.dataMeasure] (fun O => 1 -
          P.dataMeasure[(fun O => if O.A = 1 then (1 : ℝ) else 0) |
            MeasurableSpace.comap (fun O : CateObs d => O.X) inferInstance] O) := by
        have hone : (((1 : Fin 2) : ℕ) : ℝ) = 1 := by norm_num
        change P.dataMeasure[((fun _ => (1 : ℝ)) - fun O =>
            if O.A = (1 : ℝ) then (1 : ℝ) else 0) |
              MeasurableSpace.comap (fun O : CateObs d => O.X) inferInstance]
            =ᵐ[P.dataMeasure] (fun O => 1 -
              P.dataMeasure[(fun O => if O.A = 1 then (1 : ℝ) else 0) |
                MeasurableSpace.comap (fun O : CateObs d => O.X) inferInstance] O)
        simpa only [hone, Pi.sub_apply, Pi.one_apply,
          condExp_const measurable_CateObs_X.comap_le (1 : ℝ)] using
          condExp_sub (integrable_const (μ := P.dataMeasure) (1 : ℝ))
            (integrable_armIndicator P hiid 1)
            (MeasurableSpace.comap (fun O : CateObs d => O.X) inferInstance)
      _ =ᵐ[P.dataMeasure] (fun O => armProb P 0 O.X) := by
        filter_upwards [hpi] with O hO
        simp [armProb, hO]
  · simpa [armProb] using hpi

/-- Integrating a bounded covariate function in arm `a` equals weighting it by the arm probability. -/
theorem integral_arm_indicator_mul {d : ℕ} (P : CateLaw d) (hiid : IidSampling P)
    (hpi : PiIsPropensity P) (a : Fin 2)
    (g : (Fin d → ℝ) → ℝ) (hg : AEMeasurable g (P.dataMeasure.map (fun O => O.X)))
    (Bg : ℝ) (hgB : ∀ x, |g x| ≤ Bg) :
    ∫ O, (if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0) * g O.X ∂P.dataMeasure
      = ∫ O, armProb P a O.X * g O.X ∂P.dataMeasure := by
  letI : IsProbabilityMeasure P.dataMeasure := hiid.1
  have hBg : 0 ≤ Bg := (abs_nonneg (g (fun _ => 0))).trans (hgB _)
  have hgX : AEStronglyMeasurable[
      MeasurableSpace.comap (fun O : CateObs d => O.X) inferInstance]
      (fun O : CateObs d => g O.X) P.dataMeasure :=
    hg.aestronglyMeasurable.comp_ae_measurable' measurable_CateObs_X.aemeasurable
  have hgInt : Integrable (fun O : CateObs d => g O.X) P.dataMeasure := by
    apply Integrable.of_bound (hgX.mono measurable_CateObs_X.comap_le) Bg
    filter_upwards with O
    simpa [Real.norm_eq_abs] using hgB O.X
  have hprodInt : Integrable (fun O : CateObs d =>
      (if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0) * g O.X) P.dataMeasure := by
    apply Integrable.of_bound (C := Bg)
    · exact (Measurable.ite (measurableSet_eq_fun measurable_CateObs_A measurable_const)
        measurable_const measurable_const |>.aestronglyMeasurable.mul
          (hgX.mono measurable_CateObs_X.comap_le))
    · filter_upwards with O
      split
      · simpa [Real.norm_eq_abs] using hgB O.X
      · simpa using hBg
  have hpull := condExp_mul_of_aestronglyMeasurable_right
    (μ := P.dataMeasure)
    (m := MeasurableSpace.comap (fun O : CateObs d => O.X) inferInstance)
    hgX hprodInt (integrable_armIndicator P hiid a)
  calc
    ∫ O, (if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0) * g O.X ∂P.dataMeasure
        = ∫ O, P.dataMeasure[(fun O =>
          (if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0) * g O.X) |
          MeasurableSpace.comap (fun O : CateObs d => O.X) inferInstance] O ∂P.dataMeasure :=
      (integral_condExp measurable_CateObs_X.comap_le).symm
    _ = ∫ O, P.dataMeasure[(fun O =>
          if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0) |
          MeasurableSpace.comap (fun O : CateObs d => O.X) inferInstance] O * g O.X
          ∂P.dataMeasure := integral_congr_ae hpull
    _ = ∫ O, armProb P a O.X * g O.X ∂P.dataMeasure :=
      integral_congr_ae ((condExp_armIndicator P hiid hpi a).mul
        (Filter.EventuallyEq.rfl : (fun O : CateObs d => g O.X) =ᵐ[P.dataMeasure]
          (fun O => g O.X)))

/-- Integrating an arm-selected, covariate-weighted outcome equals weighting the arm regression by its selection probability. -/
theorem integral_arm_outcome_mul {d : ℕ} (P : CateLaw d) (hiid : IidSampling P)
    (hpi : PiIsPropensity P) (hmu : MuIsRegression P) (a : Fin 2)
    (g : (Fin d → ℝ) → ℝ) (hg : AEMeasurable g (P.dataMeasure.map (fun O => O.X)))
    (Bg : ℝ) (hgB : ∀ x, |g x| ≤ Bg)
    (hmuAE : AEMeasurable (armMu P a) (P.dataMeasure.map (fun O => O.X)))
    (Bm : ℝ) (hmuB : ∀ᵐ O ∂P.dataMeasure, |armMu P a O.X| ≤ Bm) :
    ∫ O, (if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0) * g O.X * O.Y
        ∂P.dataMeasure
      = ∫ O, armProb P a O.X * armMu P a O.X * g O.X ∂P.dataMeasure := by
  letI : IsProbabilityMeasure P.dataMeasure := hiid.1
  let gm := hg.mk g
  have hgm : Measurable gm := hg.measurable_mk
  have hgeq : (fun O : CateObs d => g O.X) =ᵐ[P.dataMeasure] (fun O => gm O.X) := by
    exact ae_of_ae_map measurable_CateObs_X.aemeasurable hg.ae_eq_mk
  have hgmb : ∀ᵐ O ∂P.dataMeasure, ‖gm O.X‖ ≤ Bg := by
    filter_upwards [hgeq] with O hO
    simpa [← hO, Real.norm_eq_abs] using hgB O.X
  have hYint : Integrable (fun O : CateObs d => O.Y) P.dataMeasure := by
    apply Integrable.of_bound measurable_CateObs_Y.aestronglyMeasurable 1
    filter_upwards [hiid.2.1] with O hO
    simpa [Real.norm_eq_abs, abs_le] using hO
  let k : CateObs d → ℝ := fun O =>
    (if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0) * gm O.X
  have hkmeas : Measurable k := by
    dsimp [k]
    exact (Measurable.ite (measurableSet_eq_fun measurable_CateObs_A measurable_const)
      measurable_const measurable_const).mul (hgm.comp measurable_CateObs_X)
  have hkAX : StronglyMeasurable[
      MeasurableSpace.comap (fun O : CateObs d => (O.A, O.X)) inferInstance] k := by
    apply Measurable.stronglyMeasurable
    exact ((Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
      measurable_const measurable_const).mul (hgm.comp measurable_snd)).comp
        (comap_measurable fun O : CateObs d => (O.A, O.X))
  have hkbound : ∀ᵐ O ∂P.dataMeasure, ‖k O‖ ≤ |Bg| := by
    filter_upwards [hgmb] with O hO
    dsimp [k]
    split
    · simpa using hO.trans (le_abs_self Bg)
    · simp
  have hkYint : Integrable (fun O => k O * O.Y) P.dataMeasure :=
    hYint.bdd_mul hkmeas.aestronglyMeasurable hkbound
  have hpullY := condExp_mul_of_stronglyMeasurable_left
    (μ := P.dataMeasure)
    (m := MeasurableSpace.comap (fun O : CateObs d => (O.A, O.X)) inferInstance)
    hkAX hkYint hYint
  have hmueq : (fun O : CateObs d => armMu P a O.X) =ᵐ[P.dataMeasure]
      (fun O => hmuAE.mk (armMu P a) O.X) := by
    exact ae_of_ae_map measurable_CateObs_X.aemeasurable hmuAE.ae_eq_mk
  have hmugAE : AEStronglyMeasurable[
      MeasurableSpace.comap (fun O : CateObs d => O.X) inferInstance]
      (fun O : CateObs d => armMu P a O.X * gm O.X) P.dataMeasure := by
    refine ⟨fun O => hmuAE.mk (armMu P a) O.X * gm O.X, ?_, ?_⟩
    · exact (hmuAE.measurable_mk.mul hgm).stronglyMeasurable.comp_measurable
        (comap_measurable fun O : CateObs d => O.X)
    · exact hmueq.mul (Filter.EventuallyEq.rfl :
        (fun O : CateObs d => gm O.X) =ᵐ[P.dataMeasure] fun O => gm O.X)
  have hmugBound : ∀ᵐ O ∂P.dataMeasure,
      ‖armMu P a O.X * gm O.X‖ ≤ |Bm| * |Bg| := by
    filter_upwards [hmuB, hgmb] with O hm hg'
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (hm.trans (le_abs_self Bm)) (hg'.trans (le_abs_self Bg))
      (abs_nonneg _) (abs_nonneg _)
  have hmugInt : Integrable (fun O : CateObs d => armMu P a O.X * gm O.X)
      P.dataMeasure := by
    exact Integrable.of_bound (hmugAE.mono measurable_CateObs_X.comap_le)
      (|Bm| * |Bg|) hmugBound
  have hpullA := condExp_mul_of_aestronglyMeasurable_right
    (μ := P.dataMeasure)
    (m := MeasurableSpace.comap (fun O : CateObs d => O.X) inferInstance)
    hmugAE
    ((hmugInt.bdd_mul
      (Measurable.ite (measurableSet_eq_fun measurable_CateObs_A measurable_const)
        measurable_const measurable_const |>.aestronglyMeasurable)
      (by
        filter_upwards with O
        show ‖(if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0)‖ ≤ (1 : ℝ)
        split <;> simp)))
    (integrable_armIndicator P hiid a)
  have hselect : (fun O : CateObs d => k O *
      (if O.A = 1 then P.mu1 O.X else P.mu0 O.X)) =ᵐ[P.dataMeasure]
      (fun O => (if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0) *
        (armMu P a O.X * gm O.X)) := by
    filter_upwards [hiid.2.2.1] with O hA
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    fin_cases a <;> rcases hA with hA | hA <;> simp [k, armMu, hA] <;> ring
  calc
    ∫ O, (if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0) * g O.X * O.Y
        ∂P.dataMeasure
        = ∫ O, k O * O.Y ∂P.dataMeasure := by
          apply integral_congr_ae
          filter_upwards [hgeq] with O hO
          simp [k, hO]
    _ = ∫ O, P.dataMeasure[(fun O => k O * O.Y) |
          MeasurableSpace.comap (fun O : CateObs d => (O.A, O.X)) inferInstance] O
          ∂P.dataMeasure := (integral_condExp
            (measurable_CateObs_A.prodMk measurable_CateObs_X).comap_le).symm
    _ = ∫ O, k O * P.dataMeasure[(fun O => O.Y) |
          MeasurableSpace.comap (fun O : CateObs d => (O.A, O.X)) inferInstance] O
          ∂P.dataMeasure := integral_congr_ae hpullY
    _ = ∫ O, k O * (if O.A = 1 then P.mu1 O.X else P.mu0 O.X)
          ∂P.dataMeasure := integral_congr_ae ((Filter.EventuallyEq.rfl :
            k =ᵐ[P.dataMeasure] k).mul hmu)
    _ = ∫ O, (if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0) *
          (armMu P a O.X * gm O.X) ∂P.dataMeasure := integral_congr_ae hselect
    _ = ∫ O, P.dataMeasure[(fun O =>
          (if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0) *
            (armMu P a O.X * gm O.X)) |
          MeasurableSpace.comap (fun O : CateObs d => O.X) inferInstance] O
          ∂P.dataMeasure := (integral_condExp measurable_CateObs_X.comap_le).symm
    _ = ∫ O, P.dataMeasure[(fun O =>
          if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0) |
          MeasurableSpace.comap (fun O : CateObs d => O.X) inferInstance] O *
          (armMu P a O.X * gm O.X) ∂P.dataMeasure := integral_congr_ae hpullA
    _ = ∫ O, armProb P a O.X * (armMu P a O.X * gm O.X) ∂P.dataMeasure :=
      integral_congr_ae ((condExp_armIndicator P hiid hpi a).mul
        (Filter.EventuallyEq.rfl :
          (fun O : CateObs d => armMu P a O.X * gm O.X) =ᵐ[P.dataMeasure]
            fun O => armMu P a O.X * gm O.X))
    _ = ∫ O, armProb P a O.X * armMu P a O.X * g O.X ∂P.dataMeasure := by
      apply integral_congr_ae
      filter_upwards [hgeq] with O hO
      rw [hO]
      ring

/-- The covariate cube is a measurable closed set. -/
private lemma measurableSet_cube' (d : ℕ) : MeasurableSet (cube d) := by
  rw [show cube d = Set.univ.pi (fun _ : Fin d => Set.Icc (0 : ℝ) 1) by
    ext x
    change (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) ↔
      ∀ i, i ∈ (Set.univ : Set (Fin d)) → x i ∈ Set.Icc (0 : ℝ) 1
    simp]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Icc

/-- Clipping an outcome to `[-1,1]` changes it only on a null set. -/
theorem clip_outcome_ae {d : ℕ} (P : CateLaw d) (hiid : IidSampling P) :
    ∀ᵐ O ∂P.dataMeasure, max (-1 : ℝ) (min 1 O.Y) = O.Y := by
  filter_upwards [hiid.2.1] with O hO
  rw [min_eq_right hO.2, max_eq_right hO.1]

/-- A Hölder arm regression is almost everywhere measurable under the covariate marginal. -/
theorem armMu_aemeasurable {d : ℕ} (P : CateLaw d) (beta L : ℝ) (hbeta : 0 < beta)
    (hiid : IidSampling P) (hmuH : MuHolder P beta L) (a : Fin 2) :
    AEMeasurable (armMu P a) (P.dataMeasure.map (fun O => O.X)) := by
  have _hbeta : 0 < beta := hbeta
  have hcont0 : ContinuousOn P.mu0 (cube d) :=
    hmuH.1.1.continuousOn
  have hcont1 : ContinuousOn P.mu1 (cube d) :=
    hmuH.2.1.continuousOn
  have hcont : ContinuousOn (armMu P a) (cube d) := by
    by_cases ha : a = 1
    · subst a
      simpa [armMu] using hcont1
    · have hf : armMu P a = P.mu0 := by
        funext x
        exact if_neg ha
      rw [hf]
      exact hcont0
  have hr : AEMeasurable (armMu P a)
      ((P.dataMeasure.map (fun O => O.X)).restrict (cube d)) :=
    hcont.aemeasurable (measurableSet_cube' d)
  suffices hsupp : P.dataMeasure.map (fun O => O.X) =
      (P.dataMeasure.map (fun O => O.X)).restrict (cube d) by
    rw [hsupp]
    exact hr
  symm
  apply Measure.restrict_eq_self_of_ae_mem
  exact (ae_map_iff measurable_CateObs_X.aemeasurable (measurableSet_cube' d)).2
    hiid.2.2.2.1

/-- A Hölder arm regression has absolute value at most its Hölder radius almost surely. -/
theorem armMu_ae_bound {d : ℕ} (P : CateLaw d) (beta L : ℝ) (hbeta : 0 < beta)
    (hiid : IidSampling P) (hmuH : MuHolder P beta L) (a : Fin 2) :
    ∀ᵐ O ∂P.dataMeasure, |armMu P a O.X| ≤ L := by
  have _hbeta : 0 < beta := hbeta
  filter_upwards [hiid.2.2.2.1] with O hX
  by_cases ha : a = 1
  · rw [armMu, if_pos ha, ← Real.norm_eq_abs,
      ← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact hmuH.2.2.1 0 (Nat.zero_le _) O.X hX
  · rw [armMu, if_neg ha, ← Real.norm_eq_abs,
      ← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact hmuH.1.2.1 0 (Nat.zero_le _) O.X hX

/-- Strong overlap bounds every arm probability between `e₀` and one almost surely. -/
theorem armProb_ae_bounds {d : ℕ} (P : CateLaw d) (e0 : ℝ) (he0 : 0 < e0)
    (hiid : IidSampling P)
    (hov : StrongOverlap P e0) (a : Fin 2) :
    ∀ᵐ O ∂P.dataMeasure, e0 ≤ armProb P a O.X ∧ armProb P a O.X ≤ 1 := by
  filter_upwards [hiid.2.2.2.1] with O hX
  obtain ⟨hl, hu⟩ := hov O.X hX
  by_cases ha : a = 1
  · simp only [armProb, ha, if_pos]
    exact ⟨hl, by linarith⟩
  · simp only [armProb, if_neg ha]
    exact ⟨by linarith, by linarith⟩

private lemma design_restrict_bounds {d : ℕ} (P : CateLaw d) (f0 f1 r0 : ℝ)
    (x0 : Fin d → ℝ) (hpx : PxIsXDensity P) (hld : LocalDensity P f0 f1 r0 x0)
    {S : Set (Fin d → ℝ)} (hS : MeasurableSet S) (hSsub : S ⊆ supBall x0 r0) :
    ENNReal.ofReal f0 • volume.restrict (S ∩ cube d) ≤
        (P.dataMeasure.map (fun O => O.X)).restrict S ∧
      (P.dataMeasure.map (fun O => O.X)).restrict S ≤
        ENNReal.ofReal f1 • volume.restrict S := by
  let ν : Measure (Fin d → ℝ) := volume.restrict (S ∩ cube d)
  have hSC : MeasurableSet (S ∩ cube d) := hS.inter (measurableSet_cube' d)
  have hbase : (volume.restrict (cube d)).restrict S = ν := by
    rw [Measure.restrict_restrict hS]
  have hlo : (fun _ : Fin d → ℝ => ENNReal.ofReal f0) ≤ᵐ[ν]
      (fun x => ENNReal.ofReal (P.px x)) := by
    filter_upwards [ae_restrict_mem hSC] with x hx
    exact ENNReal.ofReal_le_ofReal (hld x (hSsub hx.1) hx.2).1
  have hhi : (fun x => ENNReal.ofReal (P.px x)) ≤ᵐ[ν]
      (fun _ : Fin d → ℝ => ENNReal.ofReal f1) := by
    filter_upwards [ae_restrict_mem hSC] with x hx
    exact ENNReal.ofReal_le_ofReal (hld x (hSsub hx.1) hx.2).2
  have hνS : ν ≤ volume.restrict S := by
    exact Measure.restrict_mono Set.inter_subset_left le_rfl
  constructor
  · calc
      ENNReal.ofReal f0 • volume.restrict (S ∩ cube d)
          = ν.withDensity (fun _ => ENNReal.ofReal f0) :=
            (withDensity_const (μ := ν) _).symm
      _ ≤ ν.withDensity (fun x => ENNReal.ofReal (P.px x)) := withDensity_mono hlo
      _ = (P.dataMeasure.map (fun O => O.X)).restrict S := by
        rw [hpx, restrict_withDensity hS, hbase]
  · calc
      (P.dataMeasure.map (fun O => O.X)).restrict S
          = ν.withDensity (fun x => ENNReal.ofReal (P.px x)) := by
            rw [hpx, restrict_withDensity hS, hbase]
      _ ≤ ν.withDensity (fun _ => ENNReal.ofReal f1) := withDensity_mono hhi
      _ = ENNReal.ofReal f1 • ν := withDensity_const _
      _ ≤ ENNReal.ofReal f1 • volume.restrict S := by
        intro T
        simp only [Measure.smul_apply]
        exact mul_le_mul_of_nonneg_left (hνS T) (zero_le _)

/-- On a measurable local set inside the cube, the design integral dominates `f₀` times its Lebesgue integral. -/
theorem design_lower_bound {d : ℕ} (P : CateLaw d) (f0 f1 r0 : ℝ) (x0 : Fin d → ℝ)
    (hpx : PxIsXDensity P) (hld : LocalDensity P f0 f1 r0 x0) (hf0 : 0 < f0)
    {S : Set (Fin d → ℝ)} (hS : MeasurableSet S)
    (hSsub : S ⊆ supBall x0 r0) (hScube : S ⊆ cube d)
    (φ : (Fin d → ℝ) → ℝ) (hφ : Measurable φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hφsupp : ∀ x, x ∉ S → φ x = 0)
    (hφint : Integrable φ (volume.restrict S)) :
    f0 * (∫ x in S, φ x) ≤ ∫ O, φ O.X ∂P.dataMeasure := by
  have hb := (design_restrict_bounds P f0 f1 r0 x0 hpx hld hS hSsub).1
  have hSC : S ∩ cube d = S := Set.inter_eq_left.mpr hScube
  rw [hSC] at hb
  have hφscalar : Integrable φ (ENNReal.ofReal f0 • volume.restrict S) :=
    hφint.smul_measure ENNReal.ofReal_ne_top
  have hφdesign : Integrable φ ((P.dataMeasure.map (fun O => O.X)).restrict S) := by
    have hu := (design_restrict_bounds P f0 f1 r0 x0 hpx hld hS hSsub).2
    exact (hφint.smul_measure ENNReal.ofReal_ne_top).mono_measure hu
  calc
    f0 * (∫ x in S, φ x)
        = ∫ x, φ x ∂(ENNReal.ofReal f0 • volume.restrict S) := by
          rw [integral_smul_measure, ENNReal.toReal_ofReal hf0.le]
          rfl
    _ ≤ ∫ x, φ x ∂((P.dataMeasure.map (fun O => O.X)).restrict S) :=
      integral_mono_measure hb (Filter.Eventually.of_forall hφ0) hφdesign
    _ = ∫ x, φ x ∂(P.dataMeasure.map (fun O => O.X)) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hφsupp
    _ = ∫ O, φ O.X ∂P.dataMeasure :=
      integral_map measurable_CateObs_X.aemeasurable hφ.aestronglyMeasurable

/-- On a measurable local set, the design integral is at most `f₁` times its Lebesgue integral. -/
theorem design_upper_bound {d : ℕ} (P : CateLaw d) (f0 f1 r0 : ℝ) (x0 : Fin d → ℝ)
    (hiid : IidSampling P) (hpx : PxIsXDensity P) (hld : LocalDensity P f0 f1 r0 x0)
    (hf1 : 0 ≤ f1)
    {S : Set (Fin d → ℝ)} (hS : MeasurableSet S) (hSsub : S ⊆ supBall x0 r0)
    (φ : (Fin d → ℝ) → ℝ) (hφ : Measurable φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hφsupp : ∀ x, x ∉ S → φ x = 0)
    (hφint : Integrable φ (volume.restrict S)) :
    ∫ O, φ O.X ∂P.dataMeasure ≤ f1 * (∫ x in S, φ x) := by
  have _hiid : IidSampling P := hiid
  have hu := (design_restrict_bounds P f0 f1 r0 x0 hpx hld hS hSsub).2
  have hφscalar : Integrable φ (ENNReal.ofReal f1 • volume.restrict S) :=
    hφint.smul_measure ENNReal.ofReal_ne_top
  calc
    ∫ O, φ O.X ∂P.dataMeasure
        = ∫ x, φ x ∂(P.dataMeasure.map (fun O => O.X)) :=
          (integral_map measurable_CateObs_X.aemeasurable hφ.aestronglyMeasurable).symm
    _ = ∫ x, φ x ∂((P.dataMeasure.map (fun O => O.X)).restrict S) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hφsupp).symm
    _ ≤ ∫ x, φ x ∂(ENNReal.ofReal f1 • volume.restrict S) :=
      integral_mono_measure hu (Filter.Eventually.of_forall hφ0) hφscalar
    _ = f1 * (∫ x in S, φ x) := by
      rw [integral_smul_measure, ENNReal.toReal_ofReal hf1]
      rfl

/-- The design mass of a sup-norm ball of radius `h` is at most `f₁ (2h)^d`. -/
theorem design_mass_le {d : ℕ} (P : CateLaw d) (f0 f1 r0 : ℝ) (x0 : Fin d → ℝ)
    (hiid : IidSampling P) (hpx : PxIsXDensity P) (hld : LocalDensity P f0 f1 r0 x0)
    (hf1 : 0 ≤ f1) {h : ℝ} (hh : 0 < h) (hhr : h ≤ r0) :
    (P.dataMeasure.map (fun O => O.X)).real (supBall x0 h) ≤ f1 * (2 * h) ^ d := by
  have _hiid : IidSampling P := hiid
  have hball : supBall x0 h = Metric.closedBall x0 h := by
    ext x
    simp only [supBall, Set.mem_setOf_eq, Metric.mem_closedBall]
    rw [dist_pi_le_iff hh.le]
    simp only [Real.dist_eq]
  have hS : MeasurableSet (supBall x0 h) := hball ▸ Metric.isClosed_closedBall.measurableSet
  have hsub : supBall x0 h ⊆ supBall x0 r0 := by
    intro x hx i
    exact (hx i).trans hhr
  have hu := (design_restrict_bounds P f0 f1 r0 x0 hpx hld hS hsub).2
  have hm := Measure.le_iff'.1 hu Set.univ
  rw [Measure.restrict_apply_univ, Measure.smul_apply, Measure.restrict_apply_univ] at hm
  have hvol : volume (supBall x0 h) = ENNReal.ofReal ((2 * h) ^ d) := by
    rw [hball, Real.volume_pi_closedBall x0 hh.le]
    simp
  have hright : ENNReal.ofReal f1 * volume (supBall x0 h) ≠ ∞ := by
    rw [hvol]
    finiteness
  have hreal := ENNReal.toReal_mono hright hm
  change ((P.dataMeasure.map (fun O => O.X)) (supBall x0 h)).toReal ≤
    f1 * (2 * h) ^ d
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hf1, hvol,
    ENNReal.toReal_ofReal (pow_nonneg (mul_nonneg zero_le_two hh.le) _)] at hreal
  exact hreal

end CausalSmith.Stat.DpCateMinimax
