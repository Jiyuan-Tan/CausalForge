/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.CateWitness
import Causalean.Mathlib.InformationTheory.KLBind

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability
open scoped ENNReal

noncomputable def cateWitnessAXMeasure {d : ℕ} (Q : CateLaw d) (e0 : ℝ) :
    Measure ((Fin d → ℝ) × Bool) :=
  Q.PX.bind fun x => (cateWitnessTreatmentMeasure e0).map fun a => (x, a)

noncomputable def cateWitnessChannel {d : ℕ} (_e0 : ℝ)
    (b : (Fin d → ℝ) → ℝ) (hb : Measurable b) :
    Kernel ((Fin d → ℝ) × Bool) (CateObs d) where
  toFun := fun p =>
    (twoPointMean 1 (if p.2 then b p.1 else 0)).map
      (cateWitnessPack p.1 p.2)
  measurable' := measurable_cateWitnessOutcomeKernel hb

@[simp] lemma cateWitnessChannel_apply {d : ℕ} (e0 : ℝ)
    (b : (Fin d → ℝ) → ℝ) (hb : Measurable b) (p : (Fin d → ℝ) × Bool) :
    cateWitnessChannel e0 b hb p =
      (twoPointMean 1 (if p.2 then b p.1 else 0)).map
        (cateWitnessPack p.1 p.2) := rfl

lemma cateWitnessAXMeasure_isProbabilityMeasure {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    [IsProbabilityMeasure Q.PX] (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) :
    IsProbabilityMeasure (cateWitnessAXMeasure Q e0) := by
  letI : IsProbabilityMeasure (cateWitnessTreatmentMeasure e0) :=
    cateWitnessTreatmentMeasure_isProbabilityMeasure he0 he1
  unfold cateWitnessAXMeasure
  apply isProbabilityMeasure_bind
  · exact (Measurable.map_prodMk_left (ν := cateWitnessTreatmentMeasure e0)).aemeasurable
  · filter_upwards [] with x
    exact Measure.isProbabilityMeasure_map measurable_prodMk_left.aemeasurable

lemma lintegral_cateWitnessAX_fst {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    (f : (Fin d → ℝ) → ℝ≥0∞) (hf : Measurable f)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) :
    ∫⁻ p, f p.1 ∂cateWitnessAXMeasure Q e0 = ∫⁻ x, f x ∂Q.PX := by
  letI : IsProbabilityMeasure (cateWitnessTreatmentMeasure e0) :=
    cateWitnessTreatmentMeasure_isProbabilityMeasure he0 he1
  unfold cateWitnessAXMeasure
  rw [Measure.lintegral_bind
    (m := Q.PX)
    (μ := fun x : Fin d → ℝ =>
      (cateWitnessTreatmentMeasure e0).map fun a => (x, a))
    (f := fun p : (Fin d → ℝ) × Bool => f p.1)
    (Measurable.map_prodMk_left
      (ν := cateWitnessTreatmentMeasure e0)).aemeasurable
    (hf.comp measurable_fst).aemeasurable]
  apply lintegral_congr
  intro x
  rw [lintegral_map' (f := fun p : (Fin d → ℝ) × Bool => f p.1)
    (g := fun a : Bool => (x, a))
    (hf.comp measurable_fst).aemeasurable measurable_prodMk_left.aemeasurable]
  simp only [Prod.fst, lintegral_const]
  rw [measure_univ, mul_one]

lemma cateWitnessChannel_isMarkov {d : ℕ} (e0 : ℝ)
    (b : (Fin d → ℝ) → ℝ) (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1 / 2) :
    IsMarkovKernel (cateWitnessChannel e0 b hbmeas) := by
  refine ⟨fun p => ?_⟩
  rw [cateWitnessChannel_apply]
  have hm : |if p.2 then b p.1 else 0| ≤ 1 := by
    split
    · exact (hb p.1).trans (by norm_num)
    · norm_num
  letI : IsProbabilityMeasure
      (twoPointMean 1 (if p.2 then b p.1 else 0)) :=
    twoPointMean_isProbabilityMeasure (by norm_num) hm
  have hp : Measurable (cateWitnessPack (d := d) p.1 p.2) := by
    rw [measurable_comap_iff]
    fun_prop
  exact Measure.isProbabilityMeasure_map hp.aemeasurable

lemma cateWitnessDataMeasure_eq_AXbind {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    (b : (Fin d → ℝ) → ℝ) (hb : Measurable b) :
    cateWitnessDataMeasure Q e0 b =
      (cateWitnessAXMeasure Q e0).bind (cateWitnessChannel e0 b hb) := by
  classical
  let mA := cateWitnessTreatmentMeasure e0
  let κ := cateWitnessChannel e0 b hb
  haveI : SFinite mA := by dsimp [mA]; infer_instance
  have hAX : Measurable fun x : Fin d → ℝ => mA.map fun a => (x, a) :=
    Measurable.map_prodMk_left
  have hκ : Measurable (κ : ((Fin d → ℝ) × Bool) → Measure (CateObs d)) := κ.measurable
  have hinner (x : Fin d → ℝ) :
      (mA.map fun a => (x, a)).bind κ = mA.bind fun a => κ (x, a) := by
    ext s hs
    have hcomp : AEMeasurable (fun a : Bool => κ (x, a)) mA := by
      simpa [Function.comp_def] using
        hκ.aemeasurable.comp_measurable (measurable_prodMk_left (x := x))
    have hκs : AEMeasurable (fun p => κ p s) (mA.map fun a => (x, a)) :=
      (Measure.measurable_coe hs).comp_aemeasurable hκ.aemeasurable
    rw [Measure.bind_apply hs hκ.aemeasurable]
    rw [Measure.bind_apply hs hcomp]
    rw [lintegral_map' hκs measurable_prodMk_left.aemeasurable]
  unfold cateWitnessDataMeasure cateWitnessAXMeasure
  change Q.PX.bind (fun x => mA.bind fun a => κ (x, a)) =
    (Q.PX.bind fun x => mA.map fun a => (x, a)).bind κ
  rw [Measure.bind_bind hAX.aemeasurable hκ.aemeasurable]
  apply congrArg (Measure.bind Q.PX)
  funext x
  exact (hinner x).symm

noncomputable def cateWitnessProj {d : ℕ} (O : CateObs d) : (Fin d → ℝ) × Bool :=
  (O.X, if O.A = 1 then true else false)

lemma measurable_cateWitnessProj {d : ℕ} : Measurable (cateWitnessProj (d := d)) := by
  unfold cateWitnessProj
  exact measurable_CateObs_X.prod
    (Measurable.ite (measurableSet_eq_fun measurable_CateObs_A measurable_const)
      measurable_const measurable_const)

lemma cateWitnessChannel_fibre_support {d : ℕ} (e0 : ℝ)
    (b : (Fin d → ℝ) → ℝ) (hb : Measurable b) (p : (Fin d → ℝ) × Bool) :
    cateWitnessChannel e0 b hb p {O | cateWitnessProj O = p}ᶜ = 0 := by
  classical
  rw [cateWitnessChannel_apply]
  have hs : MeasurableSet ({O : CateObs d | cateWitnessProj O = p}ᶜ) :=
    (measurableSet_eq_fun measurable_cateWitnessProj measurable_const).compl
  have hp : Measurable (cateWitnessPack (d := d) p.1 p.2) := by
    rw [measurable_comap_iff]
    fun_prop
  rw [Measure.map_apply hp hs]
  have he : (cateWitnessPack p.1 p.2 ⁻¹' {O | cateWitnessProj O = p}ᶜ) = ∅ := by
    rcases p with ⟨x, a⟩
    ext y
    cases a <;> simp [cateWitnessPack, cateWitnessProj]
  rw [he, measure_empty]

lemma measurableEmbedding_cateWitnessPack {d : ℕ} (x : Fin d → ℝ) (a : Bool) :
    MeasurableEmbedding (cateWitnessPack (d := d) x a) := by
  have hf : Measurable (cateWitnessPack (d := d) x a) := by
    rw [measurable_comap_iff]
    fun_prop
  refine MeasurableEmbedding.of_measurable_inverse hf ?_ measurable_CateObs_Y ?_
  · have hr : Set.range (cateWitnessPack (d := d) x a) =
        {O : CateObs d | O.A = (if a then 1 else 0) ∧ O.X = x} := by
      ext O
      constructor
      · rintro ⟨y, rfl⟩
        simp [cateWitnessPack]
      · intro h
        rcases O with ⟨y, A, X⟩
        exact ⟨y, by cases h.1; cases h.2; rfl⟩
    rw [hr]
    exact (measurableSet_eq_fun measurable_CateObs_A measurable_const).inter
      (measurableSet_eq_fun measurable_CateObs_X measurable_const)
  · intro y
    rfl

lemma twoPointMean_ac_zero {u : ℝ} (hu : |u| ≤ 1 / 2) :
    twoPointMean 1 u ≪ twoPointMean 1 0 := by
  classical
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s hs hs0
  have h1 : (1 : ℝ) ∉ s := by
    intro h
    have hp : (twoPointMean 1 0) s ≠ 0 := by
      unfold twoPointMean
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
      simp [h]
    exact hp hs0
  have hn1 : (-1 : ℝ) ∉ s := by
    intro h
    have hp : (twoPointMean 1 0) s ≠ 0 := by
      unfold twoPointMean
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
      simp [h]
    exact hp hs0
  unfold twoPointMean
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp [h1, hn1]

end CausalSmith.Stat.DpCateMinimax
