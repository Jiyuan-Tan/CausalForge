/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Basic
import Causalean.Mathlib.Probability.SignedTwoPoint
import Causalean.Mathlib.MeasureTheory.IntegralBind
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! # Latent two-point witnesses for the private CATE converse

Conditional on `X = x`, this file draws `Y(0)` and `Y(1)` independently on
`{-1,1}`, with respective means `0` and `b x`, and independently draws treatment
with probability `e0`.  The observed record is the consistency image `Y = Y(A)`.
Thus the counterfactual remains latent and the arm regressions are `mu0 = 0` and
`mu1 = b`, with contrast exactly `b`.
-/

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory
open Causalean.Stat
open ProbabilityTheory
open Causalean.Mathlib.Probability
open scoped ENNReal

private lemma integrable_of_measurable_ae_bounded {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hfmeas : Measurable f) (C : ℝ) (hC : ∀ᵐ x ∂μ, |f x| ≤ C) :
    Integrable f μ := by
  refine Integrable.of_bound hfmeas.aestronglyMeasurable (max C 0) ?_
  filter_upwards [hC] with x hx
  simpa [Real.norm_eq_abs] using hx.trans (le_max_left C 0)

/-- The witness treatment law is a Bernoulli draw represented on booleans, later
packed as the real treatment values zero and one. -/
noncomputable def cateWitnessTreatmentMeasure (e0 : ℝ) : Measure Bool :=
  ENNReal.ofReal e0 • Measure.dirac true +
    ENNReal.ofReal (1 - e0) • Measure.dirac false

/-- The witness packing map turns an outcome, Boolean treatment, and covariate
vector into an observed CATE triple. -/
def cateWitnessPack {d : ℕ} (x : Fin d → ℝ) (a : Bool) (y : ℝ) : CateObs d :=
  ⟨y, if a then 1 else 0, x⟩

/-- The packing map is measurable jointly in its outcome and covariates for each
fixed Boolean treatment value. -/
lemma measurable_cateWitnessPack {d : ℕ} (a : Bool) :
    Measurable (fun p : (Fin d → ℝ) × ℝ => cateWitnessPack p.1 a p.2) := by
  rw [measurable_comap_iff]
  fun_prop

private lemma measurable_cateWitness_indicator {d : ℕ} (y : ℝ)
    (S : Set (CateObs d)) (hS : MeasurableSet S) :
    Measurable (fun p : (Fin d → ℝ) × Bool =>
      ((fun y' : ℝ => cateWitnessPack p.1 p.2 y') ⁻¹' S).indicator
        (fun _ : ℝ => (1 : ℝ≥0∞)) y) := by
  have hmk : Measurable (fun p : (Fin d → ℝ) × Bool =>
      cateWitnessPack p.1 p.2 y) := by
    rw [measurable_comap_iff]
    change Measurable (fun p : (Fin d → ℝ) × Bool =>
      (y, (if p.2 then (1 : ℝ) else 0), p.1))
    exact measurable_const.prodMk
      ((Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
        measurable_const measurable_const).prodMk measurable_fst)
  have hset : MeasurableSet
      ((fun p : (Fin d → ℝ) × Bool => cateWitnessPack p.1 p.2 y) ⁻¹' S) :=
    hS.preimage hmk
  convert measurable_const.indicator hset using 1

/-- The pushed-forward two-point outcome kernel is measurable jointly in the
covariate and Boolean treatment arguments. -/
lemma measurable_cateWitnessOutcomeKernel {d : ℕ}
    {b : (Fin d → ℝ) → ℝ} (hb : Measurable b) :
    Measurable (fun p : (Fin d → ℝ) × Bool =>
      (twoPointMean 1 (if p.2 then b p.1 else 0)).map
        (cateWitnessPack p.1 p.2)) := by
  refine Measure.measurable_of_measurable_coe _ ?_
  intro S hS
  have hmap (p : (Fin d → ℝ) × Bool) :
      Measurable (cateWitnessPack (d := d) p.1 p.2) := by
    rw [measurable_comap_iff]
    fun_prop
  simp_rw [Measure.map_apply (hmap _) hS]
  have hmean : Measurable (fun p : (Fin d → ℝ) × Bool =>
      if p.2 then b p.1 else 0) := by
    exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
      (hb.comp measurable_fst) measurable_const
  unfold twoPointMean
  simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  simpa only [div_one] using
    ((by fun_prop (disch := assumption) : Measurable fun p : (Fin d → ℝ) × Bool =>
      ENNReal.ofReal ((1 + (if p.2 then b p.1 else 0)) / 2)).mul
      (measurable_cateWitness_indicator (d := d) 1 S hS)).add
    ((by fun_prop (disch := assumption) : Measurable fun p : (Fin d → ℝ) × Bool =>
      ENNReal.ofReal ((1 - (if p.2 then b p.1 else 0)) / 2)).mul
      (measurable_cateWitness_indicator (d := d) (-1) S hS))

/-- Integrating the Bernoulli treatment law against the outcome channel gives a
measurable observation kernel as the covariate value varies. -/
lemma measurable_cateWitnessObservationKernel {d : ℕ} (e0 : ℝ)
    {b : (Fin d → ℝ) → ℝ} (hb : Measurable b) :
    Measurable (fun x : Fin d → ℝ =>
      (cateWitnessTreatmentMeasure e0).bind fun a =>
        (twoPointMean 1 (if a then b x else 0)).map
          (cateWitnessPack x a)) := by
  refine Measure.measurable_of_measurable_coe _ ?_
  intro S hS
  have hxa (x : Fin d → ℝ) : Measurable (fun a : Bool => (x, a)) :=
    measurable_const.prodMk measurable_id
  have hout (x : Fin d → ℝ) : Measurable (fun a : Bool =>
      (twoPointMean 1 (if a then b x else 0)).map
        (cateWitnessPack x a)) :=
    (measurable_cateWitnessOutcomeKernel hb).comp (hxa x)
  rw [show (fun x : Fin d → ℝ =>
      ((cateWitnessTreatmentMeasure e0).bind fun a =>
        (twoPointMean 1 (if a then b x else 0)).map
          (cateWitnessPack x a)) S) =
      fun x => ∫⁻ a, ((twoPointMean 1
        (if a then b x else 0)).map
          (cateWitnessPack x a)) S ∂cateWitnessTreatmentMeasure e0 by
    funext x
    rw [Measure.bind_apply hS (hout x).aemeasurable]]
  haveI : SFinite (cateWitnessTreatmentMeasure e0) := by
    unfold cateWitnessTreatmentMeasure
    infer_instance
  exact Measurable.lintegral_prod_right'
    (Measure.measurable_coe hS |>.comp (measurable_cateWitnessOutcomeKernel hb))

/-- The witness data law samples covariates from the supplied model member,
treatment independently from a Bernoulli law, and then a signed two-point outcome. -/
noncomputable def cateWitnessDataMeasure {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    (b : (Fin d → ℝ) → ℝ) : Measure (CateObs d) :=
  Q.PX.bind fun x =>
    (cateWitnessTreatmentMeasure e0).bind fun a =>
      (twoPointMean 1 (if a then b x else 0)).map
        (cateWitnessPack x a)

/-- Pack latent potential outcomes, treatment, and covariates. -/
def cateWitnessFullPack {d : ℕ} (x : Fin d → ℝ) (a : Bool) (y0 y1 : ℝ) : CateFull d :=
  ⟨y0, y1, if a then 1 else 0, x⟩

/-- Conditional on `x`, independently draw treatment, `Y(0)`, and `Y(1)`. -/
noncomputable def cateWitnessFullKernel {d : ℕ} (e0 : ℝ)
    (b : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : Measure (CateFull d) :=
  (cateWitnessTreatmentMeasure e0).bind fun a =>
    (twoPointMean 1 0).bind fun y0 =>
      (twoPointMean 1 (b x)).map (cateWitnessFullPack x a y0)

/-- The latent joint law, with the covariate design retained from `Q`. -/
noncomputable def cateWitnessFullMeasure {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    (b : (Fin d → ℝ) → ℝ) : Measure (CateFull d) :=
  Q.PX.bind (cateWitnessFullKernel e0 b)

private lemma measurable_cateWitnessFull_indicator {d : ℕ} (y1 : ℝ)
    (S : Set (CateFull d)) (hS : MeasurableSet S) :
    Measurable (fun q : ((Fin d → ℝ) × Bool) × ℝ =>
      ((fun z : ℝ => cateWitnessFullPack q.1.1 q.1.2 q.2 z) ⁻¹' S).indicator
        (fun _ : ℝ => (1 : ℝ≥0∞)) y1) := by
  have hmk : Measurable (fun q : ((Fin d → ℝ) × Bool) × ℝ =>
      cateWitnessFullPack q.1.1 q.1.2 q.2 y1) := by
    rw [measurable_comap_iff]
    change Measurable fun q : ((Fin d → ℝ) × Bool) × ℝ =>
      (q.2, y1, (if q.1.2 then (1 : ℝ) else 0), q.1.1)
    exact measurable_snd.prodMk <| measurable_const.prodMk <|
      (Measurable.ite
        (measurableSet_eq_fun (measurable_snd.comp measurable_fst) measurable_const)
        measurable_const measurable_const).prodMk (measurable_fst.comp measurable_fst)
  exact measurable_const.indicator (hS.preimage hmk)

private lemma measurable_cateWitnessFullOutcomeKernel {d : ℕ}
    {b : (Fin d → ℝ) → ℝ} (hb : Measurable b) :
    Measurable (fun q : ((Fin d → ℝ) × Bool) × ℝ =>
      (twoPointMean 1 (b q.1.1)).map
        (cateWitnessFullPack q.1.1 q.1.2 q.2)) := by
  refine Measure.measurable_of_measurable_coe _ ?_
  intro S hS
  have hmap (q : ((Fin d → ℝ) × Bool) × ℝ) :
      Measurable (cateWitnessFullPack (d := d) q.1.1 q.1.2 q.2) := by
    rw [measurable_comap_iff]
    fun_prop
  simp_rw [Measure.map_apply (hmap _) hS]
  unfold twoPointMean
  simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  simpa only [div_one] using
    ((by fun_prop (disch := assumption) : Measurable fun q :
        ((Fin d → ℝ) × Bool) × ℝ => ENNReal.ofReal ((1 + b q.1.1) / 2)).mul
      (measurable_cateWitnessFull_indicator (d := d) 1 S hS)).add
    ((by fun_prop (disch := assumption) : Measurable fun q :
        ((Fin d → ℝ) × Bool) × ℝ => ENNReal.ofReal ((1 - b q.1.1) / 2)).mul
      (measurable_cateWitnessFull_indicator (d := d) (-1) S hS))

private lemma measurable_cateWitnessFullYKernel {d : ℕ}
    {b : (Fin d → ℝ) → ℝ} (hb : Measurable b) :
    Measurable (fun p : (Fin d → ℝ) × Bool =>
      (twoPointMean 1 0).bind fun y0 =>
        (twoPointMean 1 (b p.1)).map (cateWitnessFullPack p.1 p.2 y0)) := by
  refine Measure.measurable_of_measurable_coe _ ?_
  intro S hS
  haveI : SFinite (twoPointMean 1 0) := by
    unfold twoPointMean
    infer_instance
  have hk (p : (Fin d → ℝ) × Bool) : Measurable (fun y0 : ℝ =>
      (twoPointMean 1 (b p.1)).map (cateWitnessFullPack p.1 p.2 y0)) :=
    measurable_cateWitnessFullOutcomeKernel hb |>.comp
      (measurable_const.prodMk measurable_id)
  simp_rw [Measure.bind_apply hS (hk _).aemeasurable]
  exact Measurable.lintegral_prod_right'
    (Measure.measurable_coe hS |>.comp (measurable_cateWitnessFullOutcomeKernel hb))

lemma measurable_cateWitnessFullKernel {d : ℕ} (e0 : ℝ)
    {b : (Fin d → ℝ) → ℝ} (hb : Measurable b) :
    Measurable (cateWitnessFullKernel (d := d) e0 b) := by
  refine Measure.measurable_of_measurable_coe _ ?_
  intro S hS
  let k : (Fin d → ℝ) → Bool → Measure (CateFull d) := fun x a =>
    (twoPointMean 1 0).bind fun y0 =>
      (twoPointMean 1 (b x)).map (cateWitnessFullPack x a y0)
  have hk : Measurable (fun p : (Fin d → ℝ) × Bool => k p.1 p.2) := by
    simpa [k] using measurable_cateWitnessFullYKernel hb
  have hform : (fun x : Fin d → ℝ => cateWitnessFullKernel e0 b x S) =
      fun x => ENNReal.ofReal e0 * k x true S +
        ENNReal.ofReal (1 - e0) * k x false S := by
    funext x
    change ((cateWitnessTreatmentMeasure e0).bind (k x)) S = _
    rw [Measure.bind_apply hS (measurable_of_finite _).aemeasurable]
    unfold cateWitnessTreatmentMeasure
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
    simp
  rw [hform]
  exact ((Measure.measurable_coe hS |>.comp hk |>.comp
    (measurable_id.prodMk measurable_const)).const_mul _).add
    ((Measure.measurable_coe hS |>.comp hk |>.comp
      (measurable_id.prodMk measurable_const)).const_mul _)

/-- The witness retains the covariate design and density, has arm means `0` and
`b`, and carries the independent potential outcomes on its latent law. -/
noncomputable def cateWitnessLaw {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    (b : (Fin d → ℝ) → ℝ) : CateLaw d where
  fullMeasure := cateWitnessFullMeasure Q e0 b
  dataMeasure := cateWitnessDataMeasure Q e0 b
  PX := Q.PX
  pi := fun _ => e0
  mu0 := fun _ => 0
  mu1 := b
  px := Q.px

/-- A valid Bernoulli parameter makes the Boolean treatment measure a probability
measure. -/
lemma cateWitnessTreatmentMeasure_isProbabilityMeasure {e0 : ℝ}
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) :
    IsProbabilityMeasure (cateWitnessTreatmentMeasure e0) := by
  rw [isProbabilityMeasure_iff]
  unfold cateWitnessTreatmentMeasure
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [Measure.dirac_apply, Set.mem_univ, Set.indicator_of_mem, Pi.one_apply,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add he0 (sub_nonneg.mpr he1)]
  norm_num

/-- Under a measurable unit-bounded contrast and a probability covariate design,
the complete witness data measure is a probability measure. -/
lemma cateWitnessLaw_isProbabilityMeasure {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    (b : (Fin d → ℝ) → ℝ) [IsProbabilityMeasure Q.PX]
    (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) :
    IsProbabilityMeasure (cateWitnessLaw Q e0 b).dataMeasure := by
  letI : IsProbabilityMeasure (cateWitnessTreatmentMeasure e0) :=
    cateWitnessTreatmentMeasure_isProbabilityMeasure he0 he1
  unfold cateWitnessLaw cateWitnessDataMeasure
  apply isProbabilityMeasure_bind (measurable_cateWitnessObservationKernel e0 hbmeas).aemeasurable
  exact Filter.Eventually.of_forall fun x => by
    have hxa : Measurable (fun a : Bool => (x, a)) :=
      measurable_const.prodMk measurable_id
    apply isProbabilityMeasure_bind
      ((measurable_cateWitnessOutcomeKernel hbmeas).comp hxa).aemeasurable
    exact Filter.Eventually.of_forall fun a => by
      have hmean : |if a then b x else 0| ≤ 1 := by
        cases a <;> simp [hb x]
      letI : IsProbabilityMeasure
          (twoPointMean 1 (if a then b x else 0)) :=
        twoPointMean_isProbabilityMeasure (by norm_num) hmean
      have hpack : Measurable (cateWitnessPack (d := d) x a) := by
        rw [measurable_comap_iff]
        change Measurable (fun y : ℝ => (y, (if a then (1 : ℝ) else 0), x))
        fun_prop
      exact Measure.isProbabilityMeasure_map hpack.aemeasurable

/-- The two arm regressions of the witness differ by exactly the requested
contrast profile. -/
lemma cateWitnessLaw_tau {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    (b : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    (cateWitnessLaw Q e0 b).tau x = b x := by
  simp [CateLaw.tau, cateWitnessLaw]

private lemma cateWitnessFullKernel_isProbabilityMeasure {d : ℕ} (e0 : ℝ)
    {b : (Fin d → ℝ) → ℝ} (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) (x : Fin d → ℝ) :
    IsProbabilityMeasure (cateWitnessFullKernel (d := d) e0 b x) := by
  letI : IsProbabilityMeasure (cateWitnessTreatmentMeasure e0) :=
    cateWitnessTreatmentMeasure_isProbabilityMeasure he0 he1
  letI : IsProbabilityMeasure (twoPointMean 1 0) :=
    twoPointMean_isProbabilityMeasure (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure (twoPointMean 1 (b x)) :=
    twoPointMean_isProbabilityMeasure (by norm_num) (hb x)
  unfold cateWitnessFullKernel
  apply isProbabilityMeasure_bind
  · exact (measurable_cateWitnessFullYKernel hbmeas).comp
      (measurable_const.prodMk measurable_id) |>.aemeasurable
  · exact Filter.Eventually.of_forall fun a => by
      apply isProbabilityMeasure_bind
      · exact (measurable_cateWitnessFullOutcomeKernel hbmeas).comp
          ((measurable_const.prodMk measurable_const).prodMk measurable_id) |>.aemeasurable
      · exact Filter.Eventually.of_forall fun y0 => by
          letI : IsProbabilityMeasure (twoPointMean 1 (b x)) :=
            twoPointMean_isProbabilityMeasure (by norm_num) (hb x)
          have hp : Measurable (cateWitnessFullPack (d := d) x a y0) := by
            rw [measurable_comap_iff]
            fun_prop
          exact Measure.isProbabilityMeasure_map hp.aemeasurable

private lemma cateWitnessFullMeasure_isProbabilityMeasure {d : ℕ}
    (Q : CateLaw d) (e0 : ℝ) {b : (Fin d → ℝ) → ℝ}
    [IsProbabilityMeasure Q.PX] (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) :
    IsProbabilityMeasure (cateWitnessFullMeasure Q e0 b) := by
  unfold cateWitnessFullMeasure
  apply isProbabilityMeasure_bind (measurable_cateWitnessFullKernel e0 hbmeas).aemeasurable
  exact Filter.Eventually.of_forall
    (cateWitnessFullKernel_isProbabilityMeasure e0 hbmeas hb he0 he1)

private lemma cateWitnessFullKernel_map_toObs {d : ℕ} (e0 : ℝ)
    {b : (Fin d → ℝ) → ℝ} (hbmeas : Measurable b)
    (hb : ∀ x, |b x| ≤ 1) (he0 : 0 ≤ e0) (he1 : e0 ≤ 1)
    (x : Fin d → ℝ) :
    (cateWitnessFullKernel e0 b x).map CateFull.toObs =
      (cateWitnessTreatmentMeasure e0).bind fun a =>
        (twoPointMean 1 (if a then b x else 0)).map (cateWitnessPack x a) := by
  classical
  letI : IsProbabilityMeasure (cateWitnessTreatmentMeasure e0) :=
    cateWitnessTreatmentMeasure_isProbabilityMeasure he0 he1
  letI : IsProbabilityMeasure (twoPointMean 1 0) :=
    twoPointMean_isProbabilityMeasure (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure (twoPointMean 1 (b x)) :=
    twoPointMean_isProbabilityMeasure (by norm_num) (hb x)
  ext S hS
  have hto : Measurable (CateFull.toObs (d := d)) := measurable_CateFull_toObs
  have hpre : MeasurableSet (CateFull.toObs ⁻¹' S) := hS.preimage hto
  have hY (a : Bool) : Measurable (fun y0 : ℝ =>
      (twoPointMean 1 (b x)).map (cateWitnessFullPack x a y0)) :=
    (measurable_cateWitnessFullOutcomeKernel hbmeas).comp
      ((measurable_const.prodMk measurable_const).prodMk measurable_id)
  have hobs : Measurable (fun a : Bool =>
      (twoPointMean 1 (if a then b x else 0)).map (cateWitnessPack x a)) :=
    (measurable_cateWitnessOutcomeKernel hbmeas).comp
      (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply hto hS]
  change ((cateWitnessTreatmentMeasure e0).bind fun a =>
    (twoPointMean 1 0).bind fun y0 =>
      (twoPointMean 1 (b x)).map (cateWitnessFullPack x a y0))
      (CateFull.toObs ⁻¹' S) = _
  have houter : AEMeasurable (fun a : Bool =>
      (twoPointMean 1 0).bind fun y0 =>
        (twoPointMean 1 (b x)).map (cateWitnessFullPack x a y0))
      (cateWitnessTreatmentMeasure e0) := (measurable_of_finite _).aemeasurable
  rw [Measure.bind_apply hpre houter]
  rw [Measure.bind_apply hS hobs.aemeasurable]
  apply lintegral_congr
  intro a
  rw [Measure.bind_apply hpre (hY a).aemeasurable]
  cases a
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hp0 (y0 : ℝ) : Measurable (cateWitnessFullPack (d := d) x false y0) := by
      rw [measurable_comap_iff]
      fun_prop
    have hpo : Measurable (cateWitnessPack (d := d) x false) := by
      rw [measurable_comap_iff]
      fun_prop
    simp_rw [Measure.map_apply (hp0 _) hpre, Measure.map_apply hpo hS]
    have hinner (y0 : ℝ) :
        (twoPointMean 1 (b x)) ((cateWitnessFullPack x false y0) ⁻¹'
          (CateFull.toObs ⁻¹' S)) =
        Set.indicator ((cateWitnessPack x false) ⁻¹' S) (fun _ => (1 : ℝ≥0∞)) y0 := by
      by_cases hy : cateWitnessPack x false y0 ∈ S
      · have hs : (cateWitnessFullPack x false y0) ⁻¹'
        (CateFull.toObs ⁻¹' S) = Set.univ := by
          ext y1
          change CateFull.toObs (cateWitnessFullPack x false y0 y1) ∈ S ↔ True
          rw [show CateFull.toObs (cateWitnessFullPack x false y0 y1) =
            cateWitnessPack x false y0 by
              simp [cateWitnessFullPack, CateFull.toObs, cateWitnessPack]]
          simp [hy]
        rw [hs]
        simp [hy]
      · have hs : (cateWitnessFullPack x false y0) ⁻¹'
            (CateFull.toObs ⁻¹' S) = ∅ := by
          ext y1
          change CateFull.toObs (cateWitnessFullPack x false y0 y1) ∈ S ↔ False
          rw [show CateFull.toObs (cateWitnessFullPack x false y0 y1) =
            cateWitnessPack x false y0 by
              simp [cateWitnessFullPack, CateFull.toObs, cateWitnessPack]]
          simp [hy]
        simp [hs, hy]
    simp_rw [hinner]
    rw [lintegral_indicator (hS.preimage hpo), lintegral_const]
    simp
  · simp only [Bool.true_eq, ↓reduceIte]
    have hp1 (y0 : ℝ) : Measurable (cateWitnessFullPack (d := d) x true y0) := by
      rw [measurable_comap_iff]
      fun_prop
    have hpo : Measurable (cateWitnessPack (d := d) x true) := by
      rw [measurable_comap_iff]
      fun_prop
    simp_rw [Measure.map_apply (hp1 _) hpre, Measure.map_apply hpo hS]
    have heq (y0 : ℝ) :
        (cateWitnessFullPack x true y0) ⁻¹' (CateFull.toObs ⁻¹' S) =
          (cateWitnessPack x true) ⁻¹' S := by
      ext y1
      simp [cateWitnessFullPack, CateFull.toObs, cateWitnessPack]
    simp_rw [heq]
    rw [lintegral_const]
    simp

/-- The observed law is exactly the consistency pushforward of the latent law. -/
lemma cateWitnessLaw_consistency {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    {b : (Fin d → ℝ) → ℝ} [IsProbabilityMeasure Q.PX]
    (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) : Consistency (cateWitnessLaw Q e0 b) := by
  constructor
  · simpa [cateWitnessLaw] using
      cateWitnessFullMeasure_isProbabilityMeasure Q e0 hbmeas hb he0 he1
  · ext S hS
    rw [cateWitnessLaw, cateWitnessDataMeasure, cateWitnessFullMeasure]
    rw [Measure.map_apply measurable_CateFull_toObs hS]
    rw [Measure.bind_apply (hS.preimage measurable_CateFull_toObs)
      (measurable_cateWitnessFullKernel e0 hbmeas).aemeasurable]
    rw [Measure.bind_apply hS
      (measurable_cateWitnessObservationKernel e0 hbmeas).aemeasurable]
    apply lintegral_congr
    intro x
    rw [← Measure.map_apply measurable_CateFull_toObs hS]
    exact congrArg (fun μ : Measure (CateObs d) => μ S)
      (cateWitnessFullKernel_map_toObs e0 hbmeas hb he0 he1 x).symm

private lemma cateWitness_setIntegral_potential_eq {d : ℕ}
    (Q : CateLaw d) (e0 : ℝ) {b : (Fin d → ℝ) → ℝ}
    [IsProbabilityMeasure Q.PX] (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1)
    (f : ℝ × ℝ → ℝ) (hf : Measurable f) (Mf : ℝ) (hMf : ∀ p, |f p| ≤ Mf)
    {Z : Type*} [MeasurableSpace Z] (r : CateFull d → Z) (hr : Measurable r)
    (hrpack : ∀ x a y0 y1, r (cateWitnessFullPack x a y0 y1) =
      r (cateWitnessFullPack x a 0 0)) (S : Set Z) (hS : MeasurableSet S) :
    ∫ U in r ⁻¹' S, f (U.Y0, U.Y1) ∂(cateWitnessLaw Q e0 b).fullMeasure =
      ∫ U in r ⁻¹' S,
        (∫ y0, ∫ y1, f (y0, y1) ∂twoPointMean 1 (b U.X) ∂twoPointMean 1 0)
        ∂(cateWitnessLaw Q e0 b).fullMeasure := by
  classical
  let μ : Measure (CateFull d) := (cateWitnessLaw Q e0 b).fullMeasure
  let g0 : (Fin d → ℝ) → ℝ := fun x =>
    ∫ y0, ∫ y1, f (y0, y1) ∂twoPointMean 1 (b x) ∂twoPointMean 1 0
  let F : CateFull d → ℝ := fun U => f (U.Y0, U.Y1)
  let g : CateFull d → ℝ := fun U => g0 U.X
  let H := (r ⁻¹' S).indicator F
  let K := (r ⁻¹' S).indicator g
  letI : IsProbabilityMeasure μ := by
    simpa [μ, cateWitnessLaw] using
      cateWitnessFullMeasure_isProbabilityMeasure Q e0 hbmeas hb he0 he1
  have hg0 : Measurable g0 := by
    have hform : g0 = fun x =>
        ((1 + b x) / 2) * (((f (1, 1) + f (-1, 1)) / 2)) +
        ((1 - b x) / 2) * (((f (1, -1) + f (-1, -1)) / 2)) := by
      funext x
      dsimp [g0]
      rw [twoPointMean_integral (by norm_num) (by norm_num)]
      rw [twoPointMean_integral (by norm_num) (hb x)]
      rw [twoPointMean_integral (by norm_num) (hb x)]
      ring
    rw [hform]
    fun_prop
  have hpre : MeasurableSet (r ⁻¹' S) := hS.preimage hr
  have hF : Measurable F := hf.comp (measurable_CateFull_Y0.prodMk measurable_CateFull_Y1)
  have hg : Measurable g := hg0.comp measurable_CateFull_X
  have hM : 0 ≤ max Mf 0 := le_max_right _ _
  have hgbd (x : Fin d → ℝ) : |g0 x| ≤ max Mf 0 := by
    letI : IsProbabilityMeasure (twoPointMean 1 0) :=
      twoPointMean_isProbabilityMeasure (by norm_num) (by norm_num)
    letI : IsProbabilityMeasure (twoPointMean 1 (b x)) :=
      twoPointMean_isProbabilityMeasure (by norm_num) (hb x)
    have hi (y0 : ℝ) :
        |∫ y1, f (y0, y1) ∂twoPointMean 1 (b x)| ≤ max Mf 0 := by
      simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one,
        mul_one] using norm_integral_le_of_norm_le_const
          (μ := twoPointMean 1 (b x)) (f := fun y1 => f (y0, y1))
          (C := max Mf 0) (Filter.Eventually.of_forall fun y1 => by
            simpa only [Real.norm_eq_abs] using
              (hMf (y0, y1)).trans (le_max_left Mf 0))
    simpa only [g0, Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one,
      mul_one] using norm_integral_le_of_norm_le_const
        (μ := twoPointMean 1 0)
        (f := fun y0 => ∫ y1, f (y0, y1) ∂twoPointMean 1 (b x))
        (C := max Mf 0) (Filter.Eventually.of_forall fun y0 => by
          simpa only [Real.norm_eq_abs] using hi y0)
  have hHbd (U : CateFull d) : |H U| ≤ max Mf 0 := by
    by_cases h : r U ∈ S
    · simpa [H, F, h] using (hMf (U.Y0, U.Y1)).trans (le_max_left Mf 0)
    · simp [H, h, hM]
  have hKbd (U : CateFull d) : |K U| ≤ max Mf 0 := by
    by_cases h : r U ∈ S
    · simpa [K, g, h] using hgbd U.X
    · simp [K, h, hM]
  have hHint : Integrable H μ := integrable_of_measurable_ae_bounded
    (hF.indicator hpre) _ (Filter.Eventually.of_forall hHbd)
  have hKint : Integrable K μ := integrable_of_measurable_ae_bounded
    (hg.indicator hpre) _ (Filter.Eventually.of_forall hKbd)
  have hinner (x : Fin d → ℝ) :
      ∫ U, H U ∂cateWitnessFullKernel e0 b x =
        ∫ U, K U ∂cateWitnessFullKernel e0 b x := by
    letI : IsProbabilityMeasure (cateWitnessFullKernel e0 b x) :=
      cateWitnessFullKernel_isProbabilityMeasure e0 hbmeas hb he0 he1 x
    have hHi : Integrable H (cateWitnessFullKernel e0 b x) :=
      integrable_of_measurable_ae_bounded (hF.indicator hpre) _
        (Filter.Eventually.of_forall hHbd)
    have hKi : Integrable K (cateWitnessFullKernel e0 b x) :=
      integrable_of_measurable_ae_bounded (hg.indicator hpre) _
        (Filter.Eventually.of_forall hKbd)
    change (∫ U, H U ∂(cateWitnessTreatmentMeasure e0).bind fun a =>
      (twoPointMean 1 0).bind fun y0 =>
        (twoPointMean 1 (b x)).map (cateWitnessFullPack x a y0)) =
      (∫ U, K U ∂(cateWitnessTreatmentMeasure e0).bind fun a =>
        (twoPointMean 1 0).bind fun y0 =>
          (twoPointMean 1 (b x)).map (cateWitnessFullPack x a y0))
    rw [Causalean.Mathlib.MeasureTheory.integral_bind
      (measurable_of_finite _) hHi]
    rw [Causalean.Mathlib.MeasureTheory.integral_bind
      (measurable_of_finite _) hKi]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun a => by
      letI : IsProbabilityMeasure (twoPointMean 1 0) :=
        twoPointMean_isProbabilityMeasure (by norm_num) (by norm_num)
      letI : IsProbabilityMeasure (twoPointMean 1 (b x)) :=
        twoPointMean_isProbabilityMeasure (by norm_num) (hb x)
      have hp (y0 : ℝ) : Measurable (cateWitnessFullPack (d := d) x a y0) := by
        rw [measurable_comap_iff]
        fun_prop
      have hm : Measurable (fun y0 : ℝ =>
          (twoPointMean 1 (b x)).map (cateWitnessFullPack x a y0)) :=
        (measurable_cateWitnessFullOutcomeKernel hbmeas).comp
          ((measurable_const.prodMk measurable_const).prodMk measurable_id)
      letI : IsProbabilityMeasure ((twoPointMean 1 0).bind fun y0 =>
          (twoPointMean 1 (b x)).map (cateWitnessFullPack x a y0)) := by
        apply isProbabilityMeasure_bind hm.aemeasurable
        exact Filter.Eventually.of_forall fun y0 =>
          Measure.isProbabilityMeasure_map (hp y0).aemeasurable
      have hHia : Integrable H ((twoPointMean 1 0).bind fun y0 =>
          (twoPointMean 1 (b x)).map (cateWitnessFullPack x a y0)) :=
        integrable_of_measurable_ae_bounded (hF.indicator hpre) _
          (Filter.Eventually.of_forall hHbd)
      have hKia : Integrable K ((twoPointMean 1 0).bind fun y0 =>
          (twoPointMean 1 (b x)).map (cateWitnessFullPack x a y0)) :=
        integrable_of_measurable_ae_bounded (hg.indicator hpre) _
          (Filter.Eventually.of_forall hKbd)
      change (∫ U, H U ∂(twoPointMean 1 0).bind fun y0 =>
        (twoPointMean 1 (b x)).map (cateWitnessFullPack x a y0)) =
        (∫ U, K U ∂(twoPointMean 1 0).bind fun y0 =>
          (twoPointMean 1 (b x)).map (cateWitnessFullPack x a y0))
      rw [Causalean.Mathlib.MeasureTheory.integral_bind_map measurable_const hp hm hHia]
      rw [Causalean.Mathlib.MeasureTheory.integral_bind_map measurable_const hp hm hKia]
      by_cases hs : r (cateWitnessFullPack x a 0 0) ∈ S
      · have hmem (y0 y1 : ℝ) : r (cateWitnessFullPack x a y0 y1) ∈ S := by
          rw [hrpack]
          exact hs
        simp_rw [H, K, Set.indicator_of_mem (show _ ∈ r ⁻¹' S from hmem _ _)]
        simp [F, g, g0, cateWitnessFullPack, integral_const, measureReal_def]
      · have hnmem (y0 y1 : ℝ) : r (cateWitnessFullPack x a y0 y1) ∉ S := by
          rw [hrpack]
          exact hs
        simp_rw [H, K, Set.indicator_of_notMem (show _ ∉ r ⁻¹' S from hnmem _ _)]
  rw [← integral_indicator hpre, ← integral_indicator hpre]
  change ∫ U, H U ∂μ = ∫ U, K U ∂μ
  rw [show μ = Q.PX.bind (cateWitnessFullKernel e0 b) by
    rfl, Causalean.Mathlib.MeasureTheory.integral_bind
      (measurable_cateWitnessFullKernel e0 hbmeas) hHint,
    Causalean.Mathlib.MeasureTheory.integral_bind
      (measurable_cateWitnessFullKernel e0 hbmeas) hKint]
  exact integral_congr_ae (Filter.Eventually.of_forall hinner)

/-- The latent outcome pair is conditionally independent of treatment given X. -/
lemma cateWitnessLaw_condExchangeability {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    {b : (Fin d → ℝ) → ℝ} [IsProbabilityMeasure Q.PX]
    (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) :
    CondExchangeability (cateWitnessLaw Q e0 b) := by
  classical
  intro f hf ⟨Mf, hMf⟩
  let P := cateWitnessLaw Q e0 b
  let μ := P.fullMeasure
  let mAX : MeasurableSpace (CateFull d) :=
    MeasurableSpace.comap (fun U : CateFull d => (U.A, U.X)) inferInstance
  let mX : MeasurableSpace (CateFull d) :=
    MeasurableSpace.comap (fun U : CateFull d => U.X) inferInstance
  let F : CateFull d → ℝ := fun U => f (U.Y0, U.Y1)
  let g0 : (Fin d → ℝ) → ℝ := fun x =>
    ∫ y0, ∫ y1, f (y0, y1) ∂twoPointMean 1 (b x) ∂twoPointMean 1 0
  let g : CateFull d → ℝ := fun U => g0 U.X
  letI : IsProbabilityMeasure μ := by
    simpa [μ, P, cateWitnessLaw] using
      cateWitnessFullMeasure_isProbabilityMeasure Q e0 hbmeas hb he0 he1
  have hmAX : mAX ≤ instMeasurableSpaceCateFull :=
    (measurable_CateFull_A.prod measurable_CateFull_X).comap_le
  have hmX : mX ≤ instMeasurableSpaceCateFull := measurable_CateFull_X.comap_le
  have hF : @Measurable (CateFull d) ℝ instMeasurableSpaceCateFull inferInstance F :=
    hf.comp (measurable_CateFull_Y0.prodMk measurable_CateFull_Y1)
  have hFint : Integrable F μ := by
    refine @integrable_of_measurable_ae_bounded (CateFull d)
      instMeasurableSpaceCateFull μ inferInstance F hF (max Mf 0) ?_
    exact Filter.Eventually.of_forall fun U => (hMf _).trans (le_max_left _ _)
  have hg0 : Measurable g0 := by
    have hform : g0 = fun x =>
        ((1 + b x) / 2) * ((f (1, 1) + f (-1, 1)) / 2) +
        ((1 - b x) / 2) * ((f (1, -1) + f (-1, -1)) / 2) := by
      funext x
      dsimp [g0]
      rw [twoPointMean_integral (by norm_num) (by norm_num),
        twoPointMean_integral (by norm_num) (hb x),
        twoPointMean_integral (by norm_num) (hb x)]
      ring
    rw [hform]
    fun_prop
  have hgX : Measurable[mX] g := hg0.comp (Measurable.of_comap_le le_rfl)
  have hgAX : Measurable[mAX] g := by
    exact hg0.comp (measurable_snd.comp (Measurable.of_comap_le le_rfl))
  have hgint : Integrable g μ := by
    refine @integrable_of_measurable_ae_bounded (CateFull d)
      instMeasurableSpaceCateFull μ inferInstance g
      (hg0.comp measurable_CateFull_X) (max Mf 0) ?_
    exact Filter.Eventually.of_forall fun U => by
      rw [show g U = ∫ y0, ∫ y1, f (y0, y1) ∂twoPointMean 1 (b U.X)
        ∂twoPointMean 1 0 by rfl]
      letI : IsProbabilityMeasure (twoPointMean 1 0) :=
        twoPointMean_isProbabilityMeasure (by norm_num) (by norm_num)
      letI : IsProbabilityMeasure (twoPointMean 1 (b U.X)) :=
        twoPointMean_isProbabilityMeasure (by norm_num) (hb U.X)
      have hi (y0 : ℝ) :
          |∫ y1, f (y0, y1) ∂twoPointMean 1 (b U.X)| ≤ max Mf 0 := by
        simpa only [Real.norm_eq_abs, measureReal_def, measure_univ,
          ENNReal.toReal_one, mul_one] using norm_integral_le_of_norm_le_const
            (μ := twoPointMean 1 (b U.X)) (f := fun y1 => f (y0, y1))
            (C := max Mf 0) (Filter.Eventually.of_forall fun y1 => by
              simpa only [Real.norm_eq_abs] using
                (hMf (y0, y1)).trans (le_max_left _ _))
      simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one,
        mul_one] using norm_integral_le_of_norm_le_const
          (μ := twoPointMean 1 0)
          (f := fun y0 => ∫ y1, f (y0, y1) ∂twoPointMean 1 (b U.X))
          (C := max Mf 0) (Filter.Eventually.of_forall fun y0 => by
            simpa only [Real.norm_eq_abs] using hi y0)
  have hsetAX : ∀ s, MeasurableSet[mAX] s → μ s < ∞ →
      ∫ U in s, g U ∂μ = ∫ U in s, F U ∂μ := by
    intro s hs _
    rcases MeasurableSpace.measurableSet_comap.mp hs with ⟨S, hS, rfl⟩
    symm
    simpa [μ, P, F, g, g0] using cateWitness_setIntegral_potential_eq
      Q e0 hbmeas hb he0 he1 f hf Mf hMf
      (fun U : CateFull d => (U.A, U.X))
      (measurable_CateFull_A.prod measurable_CateFull_X) (by intros; rfl) S hS
  have hsetX : ∀ s, MeasurableSet[mX] s → μ s < ∞ →
      ∫ U in s, g U ∂μ = ∫ U in s, F U ∂μ := by
    intro s hs _
    rcases MeasurableSpace.measurableSet_comap.mp hs with ⟨S, hS, rfl⟩
    symm
    simpa [μ, P, F, g, g0] using cateWitness_setIntegral_potential_eq
      Q e0 hbmeas hb he0 he1 f hf Mf hMf (fun U : CateFull d => U.X)
      measurable_CateFull_X (by intros; rfl) S hS
  have hAX := (ae_eq_condExp_of_forall_setIntegral_eq hmAX hFint
    (fun _ _ _ => hgint.integrableOn) hsetAX hgAX.aestronglyMeasurable).symm
  have hX := (ae_eq_condExp_of_forall_setIntegral_eq hmX hFint
    (fun _ _ _ => hgint.integrableOn) hsetX hgX.aestronglyMeasurable).symm
  exact hAX.trans hX.symm

private lemma measurableSet_cube (d : ℕ) : MeasurableSet (cube d) := by
  rw [show cube d = Set.univ.pi fun _ : Fin d => Set.Icc (0 : ℝ) 1 by
    ext x
    simp only [cube, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_univ_pi]]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Icc

/-- Marginalizing a witness observation to its covariate returns the retained
covariate law. -/
lemma cateWitnessLaw_map_X {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    {b : (Fin d → ℝ) → ℝ} (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) :
    (cateWitnessLaw Q e0 b).dataMeasure.map (fun O => O.X) = Q.PX := by
  classical
  letI : IsProbabilityMeasure (cateWitnessTreatmentMeasure e0) :=
    cateWitnessTreatmentMeasure_isProbabilityMeasure he0 he1
  ext S hS
  have hpre : MeasurableSet ((fun O : CateObs d => O.X) ⁻¹' S) :=
    hS.preimage measurable_CateObs_X
  rw [Measure.map_apply measurable_CateObs_X hS]
  unfold cateWitnessLaw cateWitnessDataMeasure
  rw [Measure.bind_apply hpre
    (measurable_cateWitnessObservationKernel e0 hbmeas).aemeasurable]
  have hinner : (fun x : Fin d → ℝ =>
      ((cateWitnessTreatmentMeasure e0).bind fun a =>
        (twoPointMean 1 (if a then b x else 0)).map
          (cateWitnessPack x a)) ((fun O : CateObs d => O.X) ⁻¹' S)) =
      Set.indicator S (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    have hout : Measurable (fun a : Bool =>
        (twoPointMean 1 (if a then b x else 0)).map
          (cateWitnessPack x a)) :=
      (measurable_cateWitnessOutcomeKernel hbmeas).comp
        (measurable_const.prodMk measurable_id)
    rw [Measure.bind_apply hpre hout.aemeasurable]
    have hy (a : Bool) :
        ((twoPointMean 1 (if a then b x else 0)).map
          (cateWitnessPack x a)) ((fun O : CateObs d => O.X) ⁻¹' S) =
        Set.indicator S (fun _ => (1 : ℝ≥0∞)) x := by
      have hpack : Measurable (cateWitnessPack (d := d) x a) := by
        rw [measurable_comap_iff]
        fun_prop
      rw [Measure.map_apply hpack hpre]
      by_cases hx : x ∈ S
      · have hset : (cateWitnessPack x a) ⁻¹'
            ((fun O : CateObs d => O.X) ⁻¹' S) = Set.univ := by
          ext y
          change (x ∈ S ↔ y ∈ Set.univ)
          simp [hx]
        rw [hset]
        letI : IsProbabilityMeasure
            (twoPointMean 1 (if a then b x else 0)) := by
          apply twoPointMean_isProbabilityMeasure (by norm_num)
          cases a <;> simp [hb x]
        simp [Set.indicator, hx]
      · have hset : (cateWitnessPack x a) ⁻¹'
            ((fun O : CateObs d => O.X) ⁻¹' S) = ∅ := by
          ext y
          change (x ∈ S ↔ y ∈ (∅ : Set ℝ))
          simp [hx]
        rw [hset]
        simp [Set.indicator, hx]
    simp_rw [hy]
    rw [lintegral_const]
    rw [measure_univ]
    simp
  rw [hinner, lintegral_indicator hS, lintegral_const]
  simp

private lemma cateWitnessLaw_ae_Y_mem {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    {b : (Fin d → ℝ) → ℝ} [IsProbabilityMeasure Q.PX]
    (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) :
    ∀ᵐ O ∂(cateWitnessLaw Q e0 b).dataMeasure, O.Y ∈ Set.Icc (-1 : ℝ) 1 := by
  classical
  let μ := (cateWitnessLaw Q e0 b).dataMeasure
  haveI : IsProbabilityMeasure μ :=
    cateWitnessLaw_isProbabilityMeasure Q e0 b hbmeas hb he0 he1
  rw [ae_iff]
  have hbad : {O : CateObs d | O.Y ∉ Set.Icc (-1 : ℝ) 1} =
      (fun O : CateObs d => O.Y) ⁻¹' (Set.Icc (-1 : ℝ) 1)ᶜ := by ext O; simp
  change μ {O : CateObs d | O.Y ∉ Set.Icc (-1 : ℝ) 1} = 0
  have hmeas : MeasurableSet {O : CateObs d | O.Y ∉ Set.Icc (-1 : ℝ) 1} := by
    rw [hbad]
    exact measurableSet_Icc.compl.preimage measurable_CateObs_Y
  dsimp [μ]
  unfold cateWitnessLaw cateWitnessDataMeasure
  rw [Measure.bind_apply hmeas
    (measurable_cateWitnessObservationKernel e0 hbmeas).aemeasurable]
  apply lintegral_eq_zero_of_ae_eq_zero
  exact Filter.Eventually.of_forall fun x => by
    change (((cateWitnessTreatmentMeasure e0).bind fun a =>
      (twoPointMean 1 (if a then b x else 0)).map
        (cateWitnessPack x a)) {O : CateObs d | O.Y ∉ Set.Icc (-1 : ℝ) 1}) = 0
    have hout : Measurable (fun a : Bool =>
        (twoPointMean 1 (if a then b x else 0)).map
          (cateWitnessPack x a)) :=
      (measurable_cateWitnessOutcomeKernel hbmeas).comp
        (measurable_const.prodMk measurable_id)
    rw [Measure.bind_apply hmeas hout.aemeasurable]
    apply lintegral_eq_zero_of_ae_eq_zero
    exact Filter.Eventually.of_forall fun a => by
      have hpack : Measurable (cateWitnessPack (d := d) x a) := by
        rw [measurable_comap_iff]
        fun_prop
      change ((twoPointMean 1 (if a then b x else 0)).map
        (cateWitnessPack x a)) {O : CateObs d | O.Y ∉ Set.Icc (-1 : ℝ) 1} = 0
      rw [Measure.map_apply hpack hmeas]
      change (twoPointMean 1 (if a then b x else 0))
        {y | y ∉ Set.Icc (-1 : ℝ) 1} = 0
      exact twoPointMean_bad_support_zero (by norm_num)

private lemma cateWitnessLaw_ae_A_mem {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    {b : (Fin d → ℝ) → ℝ} [IsProbabilityMeasure Q.PX]
    (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) :
    ∀ᵐ O ∂(cateWitnessLaw Q e0 b).dataMeasure, O.A ∈ ({0, 1} : Set ℝ) := by
  classical
  let μ := (cateWitnessLaw Q e0 b).dataMeasure
  haveI : IsProbabilityMeasure μ :=
    cateWitnessLaw_isProbabilityMeasure Q e0 b hbmeas hb he0 he1
  rw [ae_iff]
  change μ {O : CateObs d | O.A ∉ ({0, 1} : Set ℝ)} = 0
  have hmeas : MeasurableSet {O : CateObs d | O.A ∉ ({0, 1} : Set ℝ)} := by
    exact ((measurableSet_singleton 0).union (measurableSet_singleton 1)).compl.preimage
      measurable_CateObs_A
  dsimp [μ]
  unfold cateWitnessLaw cateWitnessDataMeasure
  rw [Measure.bind_apply hmeas
    (measurable_cateWitnessObservationKernel e0 hbmeas).aemeasurable]
  apply lintegral_eq_zero_of_ae_eq_zero
  exact Filter.Eventually.of_forall fun x => by
    change (((cateWitnessTreatmentMeasure e0).bind fun a =>
      (twoPointMean 1 (if a then b x else 0)).map
        (cateWitnessPack x a)) {O : CateObs d | O.A ∉ ({0, 1} : Set ℝ)}) = 0
    have hout : Measurable (fun a : Bool =>
        (twoPointMean 1 (if a then b x else 0)).map
          (cateWitnessPack x a)) :=
      (measurable_cateWitnessOutcomeKernel hbmeas).comp
        (measurable_const.prodMk measurable_id)
    rw [Measure.bind_apply hmeas hout.aemeasurable]
    apply lintegral_eq_zero_of_ae_eq_zero
    exact Filter.Eventually.of_forall fun a => by
      have hpack : Measurable (cateWitnessPack (d := d) x a) := by
        rw [measurable_comap_iff]
        fun_prop
      change ((twoPointMean 1 (if a then b x else 0)).map
        (cateWitnessPack x a)) {O : CateObs d | O.A ∉ ({0, 1} : Set ℝ)} = 0
      rw [Measure.map_apply hpack hmeas]
      have hempty : (cateWitnessPack x a) ⁻¹'
          {O : CateObs d | O.A ∉ ({0, 1} : Set ℝ)} = ∅ := by
        ext y
        cases a <;> simp [cateWitnessPack]
      rw [hempty]
      simp

/-- The witness is a genuine probability law with the required observation
support and has the standard infinite-product i.i.d. realization. -/
lemma cateWitnessLaw_iidSampling {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    {b : (Fin d → ℝ) → ℝ} (hQiid : IidSampling Q)
    (hQpx : PXIsXMarginal Q) (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) : IidSampling (cateWitnessLaw Q e0 b) := by
  classical
  haveI : IsProbabilityMeasure Q.dataMeasure := hQiid.1
  haveI : IsProbabilityMeasure Q.PX := by
    rw [hQpx]
    exact Measure.isProbabilityMeasure_map measurable_CateObs_X.aemeasurable
  let P := cateWitnessLaw Q e0 b
  letI : IsProbabilityMeasure P.dataMeasure :=
    cateWitnessLaw_isProbabilityMeasure Q e0 b hbmeas hb he0 he1
  have hXQ : ∀ᵐ x ∂Q.PX, x ∈ cube d := by
    rw [hQpx]
    exact (ae_map_iff measurable_CateObs_X.aemeasurable (measurableSet_cube d)).2
      hQiid.2.2.2.1
  have hX : ∀ᵐ O ∂P.dataMeasure, O.X ∈ cube d := by
    have hXQ' := hXQ
    rw [show Q.PX = P.dataMeasure.map (fun O => O.X) by
      simpa [P] using (cateWitnessLaw_map_X Q e0 hbmeas hb he0 he1).symm] at hXQ'
    exact (ae_map_iff measurable_CateObs_X.aemeasurable (measurableSet_cube d)).1 hXQ'
  refine ⟨inferInstance, ?_, ?_, hX, ?_⟩
  · simpa [P] using cateWitnessLaw_ae_Y_mem Q e0 hbmeas hb he0 he1
  · simpa [P] using cateWitnessLaw_ae_A_mem Q e0 hbmeas hb he0 he1
  · let Ω := ℕ → CateObs d
    let μ : Measure Ω := Measure.infinitePi fun _ : ℕ => P.dataMeasure
    letI : IsProbabilityMeasure μ := inferInstance
    refine ⟨Ω, inferInstance, μ, ⟨fun i ω => ω i, ?_, ?_, ?_, ?_⟩⟩
    · intro i
      fun_prop
    · exact iIndepFun_infinitePi fun _ => measurable_id
    · intro i
      exact ⟨measurable_pi_apply 0 |>.aemeasurable,
        measurable_pi_apply i |>.aemeasurable, by
        rw [Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]⟩
    · exact Measure.infinitePi_map_eval _ 0

/-- Both independently drawn latent outcomes retain the fixed two-point support. -/
lemma cateWitnessLaw_potentialOutcomeRange {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    {b : (Fin d → ℝ) → ℝ} [IsProbabilityMeasure Q.PX]
    (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) :
    PotentialOutcomeRange (cateWitnessLaw Q e0 b) := by
  classical
  let bad : Set ℝ := (Set.Icc (-1 : ℝ) 1)ᶜ
  have hbad : MeasurableSet bad := measurableSet_Icc.compl
  have hfull : MeasurableSet {U : CateFull d | U.Y0 ∈ bad} :=
    hbad.preimage measurable_CateFull_Y0
  have hfull1 : MeasurableSet {U : CateFull d | U.Y1 ∈ bad} :=
    hbad.preimage measurable_CateFull_Y1
  have hzero : (twoPointMean 1 0) bad = 0 := by
    change (twoPointMean 1 0) {y | y ∉ Set.Icc (-1 : ℝ) 1} = 0
    exact twoPointMean_bad_support_zero (by norm_num)
  have hzero1 (x : Fin d → ℝ) : (twoPointMean 1 (b x)) bad = 0 := by
    change (twoPointMean 1 (b x)) {y | y ∉ Set.Icc (-1 : ℝ) 1} = 0
    exact twoPointMean_bad_support_zero (by norm_num)
  have hkernel0 (x : Fin d → ℝ) :
      cateWitnessFullKernel e0 b x {U : CateFull d | U.Y0 ∈ bad} = 0 := by
    change ((cateWitnessTreatmentMeasure e0).bind fun a =>
      (twoPointMean 1 0).bind fun y0 =>
        (twoPointMean 1 (b x)).map (cateWitnessFullPack x a y0)) _ = 0
    rw [Measure.bind_apply hfull (measurable_of_finite _).aemeasurable]
    apply lintegral_eq_zero_of_ae_eq_zero
    exact Filter.Eventually.of_forall fun a => by
      have hy : Measurable (fun y0 : ℝ =>
          (twoPointMean 1 (b x)).map (cateWitnessFullPack x a y0)) :=
        (measurable_cateWitnessFullOutcomeKernel hbmeas).comp
          ((measurable_const.prodMk measurable_const).prodMk measurable_id)
      change ((twoPointMean 1 0).bind fun y0 =>
        (twoPointMean 1 (b x)).map (cateWitnessFullPack x a y0))
          {U : CateFull d | U.Y0 ∈ bad} = 0
      rw [Measure.bind_apply hfull hy.aemeasurable]
      apply lintegral_eq_zero_of_ae_eq_zero
      have hae : ∀ᵐ y0 ∂twoPointMean 1 0, y0 ∉ bad := by
        rw [ae_iff]
        simpa only [not_not, Set.setOf_mem_eq] using hzero
      filter_upwards [hae] with y0 hy0
      have hp : Measurable (cateWitnessFullPack (d := d) x a y0) := by
        rw [measurable_comap_iff]
        fun_prop
      change ((twoPointMean 1 (b x)).map (cateWitnessFullPack x a y0))
        {U : CateFull d | U.Y0 ∈ bad} = 0
      rw [Measure.map_apply hp hfull]
      have heq : (cateWitnessFullPack x a y0) ⁻¹'
          {U : CateFull d | U.Y0 ∈ bad} = ∅ := by
        ext y1
        simp [cateWitnessFullPack, hy0]
      simp [heq]
  have hkernel1 (x : Fin d → ℝ) :
      cateWitnessFullKernel e0 b x {U : CateFull d | U.Y1 ∈ bad} = 0 := by
    change ((cateWitnessTreatmentMeasure e0).bind fun a =>
      (twoPointMean 1 0).bind fun y0 =>
        (twoPointMean 1 (b x)).map (cateWitnessFullPack x a y0)) _ = 0
    rw [Measure.bind_apply hfull1 (measurable_of_finite _).aemeasurable]
    apply lintegral_eq_zero_of_ae_eq_zero
    exact Filter.Eventually.of_forall fun a => by
      have hy : Measurable (fun y0 : ℝ =>
          (twoPointMean 1 (b x)).map (cateWitnessFullPack x a y0)) :=
        (measurable_cateWitnessFullOutcomeKernel hbmeas).comp
          ((measurable_const.prodMk measurable_const).prodMk measurable_id)
      change ((twoPointMean 1 0).bind fun y0 =>
        (twoPointMean 1 (b x)).map (cateWitnessFullPack x a y0))
          {U : CateFull d | U.Y1 ∈ bad} = 0
      rw [Measure.bind_apply hfull1 hy.aemeasurable]
      apply lintegral_eq_zero_of_ae_eq_zero
      exact Filter.Eventually.of_forall fun y0 => by
        have hp : Measurable (cateWitnessFullPack (d := d) x a y0) := by
          rw [measurable_comap_iff]
          fun_prop
        change ((twoPointMean 1 (b x)).map (cateWitnessFullPack x a y0))
          {U : CateFull d | U.Y1 ∈ bad} = 0
        rw [Measure.map_apply hp hfull1]
        have heq : (cateWitnessFullPack x a y0) ⁻¹' {U : CateFull d | U.Y1 ∈ bad} = bad := by
          ext y1
          rfl
        rw [heq, hzero1]
  constructor <;> rw [ae_iff]
  · change (cateWitnessFullMeasure Q e0 b) {U : CateFull d | U.Y0 ∈ bad} = 0
    rw [cateWitnessFullMeasure, Measure.bind_apply hfull
      (measurable_cateWitnessFullKernel e0 hbmeas).aemeasurable]
    exact lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall hkernel0)
  · change (cateWitnessFullMeasure Q e0 b) {U : CateFull d | U.Y1 ∈ bad} = 0
    rw [cateWitnessFullMeasure, Measure.bind_apply hfull1
      (measurable_cateWitnessFullKernel e0 hbmeas).aemeasurable]
    exact lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall hkernel1)

private lemma cateWitness_regression_setIntegral_eq {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    {b : (Fin d → ℝ) → ℝ} [IsProbabilityMeasure Q.PX]
    (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1)
    (S : Set (ℝ × (Fin d → ℝ))) (hS : MeasurableSet S) :
    ∫ O in (fun O : CateObs d => (O.A, O.X)) ⁻¹' S,
        (if O.A = 1 then (cateWitnessLaw Q e0 b).mu1 O.X
          else (cateWitnessLaw Q e0 b).mu0 O.X)
        ∂(cateWitnessLaw Q e0 b).dataMeasure =
      ∫ O in (fun O : CateObs d => (O.A, O.X)) ⁻¹' S, O.Y
        ∂(cateWitnessLaw Q e0 b).dataMeasure := by
  classical
  let μ : Measure (CateObs d) := (cateWitnessLaw Q e0 b).dataMeasure
  let ν : Measure Bool := cateWitnessTreatmentMeasure e0
  let κ : (Fin d → ℝ) → Bool → Measure ℝ := fun x a =>
    twoPointMean 1 (if a then b x else 0)
  let pack : (Fin d → ℝ) → Bool → ℝ → CateObs d := cateWitnessPack
  let obs : (Fin d → ℝ) → Measure (CateObs d) := fun x =>
    ν.bind fun a => (κ x a).map (pack x a)
  let pair : CateObs d → ℝ × (Fin d → ℝ) := fun O => (O.A, O.X)
  let R : CateObs d → ℝ := fun O =>
    if O.A = 1 then (cateWitnessLaw Q e0 b).mu1 O.X
      else (cateWitnessLaw Q e0 b).mu0 O.X
  let H : CateObs d → ℝ := (pair ⁻¹' S).indicator R
  let K : CateObs d → ℝ :=
    (pair ⁻¹' S).indicator fun O => max (-1) (min 1 O.Y)
  haveI : IsProbabilityMeasure ν := cateWitnessTreatmentMeasure_isProbabilityMeasure he0 he1
  have hmeanbd (x : Fin d → ℝ) (a : Bool) :
      |if a then b x else 0| ≤ 1 := by
    cases a <;> simp [hb x]
  have hκprob (x) (a) : IsProbabilityMeasure (κ x a) :=
    twoPointMean_isProbabilityMeasure (by norm_num) (hmeanbd x a)
  have hobsprob (x) : IsProbabilityMeasure (obs x) := by
    letI (a : Bool) : IsProbabilityMeasure (κ x a) := hκprob x a
    apply isProbabilityMeasure_bind
    · simpa [κ, pack] using ((measurable_cateWitnessOutcomeKernel hbmeas).comp
        (measurable_const.prodMk measurable_id)).aemeasurable
    · exact Filter.Eventually.of_forall fun a =>
        Measure.isProbabilityMeasure_map ((by
          dsimp [pack]
          rw [measurable_comap_iff]
          fun_prop : Measurable (pack x a)).aemeasurable)
  letI : IsProbabilityMeasure μ :=
    cateWitnessLaw_isProbabilityMeasure Q e0 b hbmeas hb he0 he1
  have hpair : Measurable pair := measurable_CateObs_A.prod measurable_CateObs_X
  have hpre : MeasurableSet (pair ⁻¹' S) := hS.preimage hpair
  have hR : Measurable R := by
    dsimp [R, cateWitnessLaw]
    exact Measurable.ite
      (measurableSet_eq_fun measurable_CateObs_A measurable_const)
      (hbmeas.comp measurable_CateObs_X) measurable_const
  have hH : Measurable H := hR.indicator hpre
  have hK : Measurable K :=
    (measurable_const.max (measurable_const.min measurable_CateObs_Y)).indicator hpre
  have hRbd (O : CateObs d) : |R O| ≤ 1 := by
    dsimp [R, cateWitnessLaw]
    split_ifs
    · exact hmeanbd O.X true
    · exact hmeanbd O.X false
  have hHbd (O : CateObs d) : |H O| ≤ 1 := by
    by_cases h : pair O ∈ S <;> simp [H, Set.indicator, h, hRbd O]
  have hKbd (O : CateObs d) : |K O| ≤ 1 := by
    by_cases h : pair O ∈ S
    · simp [K, Set.indicator, h, abs_le, min_le_left, le_max_left]
    · simp [K, Set.indicator, h]
  have hHint : Integrable H μ :=
    integrable_of_measurable_ae_bounded hH 1 (Filter.Eventually.of_forall hHbd)
  have hKint : Integrable K μ :=
    integrable_of_measurable_ae_bounded hK 1 (Filter.Eventually.of_forall hKbd)
  have hobsmeas : Measurable obs := by
    simpa [obs, ν, κ, pack] using measurable_cateWitnessObservationKernel e0 hbmeas
  have hinner (x : Fin d → ℝ) : ∫ O, H O ∂obs x = ∫ O, K O ∂obs x := by
    letI : IsProbabilityMeasure (obs x) := hobsprob x
    have hHi : Integrable H (obs x) :=
      integrable_of_measurable_ae_bounded hH 1 (Filter.Eventually.of_forall hHbd)
    have hKi : Integrable K (obs x) :=
      integrable_of_measurable_ae_bounded hK 1 (Filter.Eventually.of_forall hKbd)
    have hκmeas : Measurable (fun a : Bool => κ x a) := measurable_of_finite _
    have hpackmeas (a : Bool) : Measurable (pack x a) := by
      dsimp [pack]
      rw [measurable_comap_iff]
      fun_prop
    have hmapmeas : Measurable (fun a : Bool => (κ x a).map (pack x a)) := by
      simpa [κ, pack] using (measurable_cateWitnessOutcomeKernel hbmeas).comp
        (measurable_const.prodMk measurable_id)
    rw [show obs x = ν.bind fun a => (κ x a).map (pack x a) by rfl]
    rw [Causalean.Mathlib.MeasureTheory.integral_bind_map hκmeas hpackmeas hmapmeas hHi]
    rw [Causalean.Mathlib.MeasureTheory.integral_bind_map hκmeas hpackmeas hmapmeas hKi]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun a => by
      letI : IsProbabilityMeasure (κ x a) := hκprob x a
      by_cases hxa : (if a then (1 : ℝ) else 0, x) ∈ S
      · have hmem (y : ℝ) : pair (pack x a y) ∈ S := by simpa [pair, pack, cateWitnessPack] using hxa
        have hHval : (fun y => H (pack x a y)) = fun y => R (pack x a y) := by
          funext y
          exact Set.indicator_of_mem
            (show pack x a y ∈ pair ⁻¹' S from hmem y) R
        have hKval : (fun y => K (pack x a y)) = fun y => max (-1) (min 1 y) := by
          funext y
          change (pair ⁻¹' S).indicator (fun O : CateObs d => max (-1) (min 1 O.Y))
            (pack x a y) = max (-1) (min 1 y)
          rw [Set.indicator_of_mem
            (show pack x a y ∈ pair ⁻¹' S from hmem y)]
          rfl
        change (∫ y, H (pack x a y) ∂κ x a) = ∫ y, K (pack x a y) ∂κ x a
        rw [hHval, hKval]
        have hRpack : (fun y => R (pack x a y)) =
            fun _ => if a then b x else 0 := by
          funext y
          cases a <;> simp [R, pack, cateWitnessPack, cateWitnessLaw]
        rw [hRpack]
        change (∫ _ : ℝ, (if a then b x else 0) ∂κ x a) =
          ∫ y : ℝ, max (-1) (min 1 y) ∂κ x a
        rw [integral_const, measureReal_def]
        rw [twoPointMean_integral (by norm_num) (hmeanbd x a)]
        simp
        ring
      · have hnmem (y : ℝ) : pair (pack x a y) ∉ S := by
          simpa [pair, pack, cateWitnessPack] using hxa
        have hHval : (fun y => H (pack x a y)) = fun _ => 0 := by
          funext y
          exact Set.indicator_of_notMem
            (show pack x a y ∉ pair ⁻¹' S from hnmem y) R
        have hKval : (fun y => K (pack x a y)) = fun _ => 0 := by
          funext y
          exact Set.indicator_of_notMem
            (show pack x a y ∉ pair ⁻¹' S from hnmem y)
            (fun O : CateObs d => max (-1) (min 1 O.Y))
        change (∫ y, H (pack x a y) ∂κ x a) = ∫ y, K (pack x a y) ∂κ x a
        rw [hHval, hKval]
  have hcollapseH : ∫ O, H O ∂μ = ∫ x, ∫ O, H O ∂obs x ∂Q.PX := by
    simpa [μ, cateWitnessLaw, cateWitnessDataMeasure, obs, ν, κ, pack] using
      Causalean.Mathlib.MeasureTheory.integral_bind hobsmeas hHint
  have hcollapseK : ∫ O, K O ∂μ = ∫ x, ∫ O, K O ∂obs x ∂Q.PX := by
    simpa [μ, cateWitnessLaw, cateWitnessDataMeasure, obs, ν, κ, pack] using
      Causalean.Mathlib.MeasureTheory.integral_bind hobsmeas hKint
  rw [← integral_indicator hpre]
  change ∫ O, H O ∂μ = ∫ O in pair ⁻¹' S, O.Y ∂μ
  calc
    ∫ O, H O ∂μ = ∫ O, K O ∂μ := by
      rw [hcollapseH, hcollapseK]
      exact integral_congr_ae (Filter.Eventually.of_forall hinner)
    _ = ∫ O in pair ⁻¹' S, O.Y ∂μ := by
      rw [← integral_indicator hpre]
      apply integral_congr_ae
      filter_upwards [cateWitnessLaw_ae_Y_mem Q e0 hbmeas hb he0 he1] with O hO
      by_cases h : pair O ∈ S
      · simp only [K]
        simp only [Set.indicator, h, ↓reduceIte]
        simp [hO.1, hO.2]
      · simp [K, Set.indicator, h]

/-- The declared zero/control and `b`/treated arm means are the genuine
conditional outcome regressions of the witness law. -/
lemma cateWitnessLaw_muIsRegression {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    {b : (Fin d → ℝ) → ℝ} [IsProbabilityMeasure Q.PX]
    (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) : MuIsRegression (cateWitnessLaw Q e0 b) := by
  classical
  let P := cateWitnessLaw Q e0 b
  let μ : Measure (CateObs d) := P.dataMeasure
  let mAX : MeasurableSpace (CateObs d) :=
    MeasurableSpace.comap (fun O : CateObs d => (O.A, O.X)) inferInstance
  let R : CateObs d → ℝ := fun O => if O.A = 1 then P.mu1 O.X else P.mu0 O.X
  letI : IsProbabilityMeasure μ :=
    cateWitnessLaw_isProbabilityMeasure Q e0 b hbmeas hb he0 he1
  have hmAX : mAX ≤ instMeasurableSpaceCateObs := by
    dsimp [mAX]
    exact (measurable_CateObs_A.prod measurable_CateObs_X).comap_le
  have hYint : Integrable (fun O : CateObs d => O.Y) μ := by
    refine @integrable_of_measurable_ae_bounded (CateObs d) instMeasurableSpaceCateObs μ
      inferInstance (fun O : CateObs d => O.Y) measurable_CateObs_Y 1 ?_
    exact (cateWitnessLaw_ae_Y_mem Q e0 hbmeas hb he0 he1).mono fun O hO => abs_le.mpr hO
  have hRmeas : Measurable[mAX] R := by
    have hpair : Measurable[mAX] (fun O : CateObs d => (O.A, O.X)) :=
      Measurable.of_comap_le le_rfl
    have ha : Measurable[mAX] (fun O : CateObs d => O.A) := measurable_fst.comp hpair
    have hx : Measurable[mAX] (fun O : CateObs d => O.X) := measurable_snd.comp hpair
    dsimp [R, P, cateWitnessLaw]
    exact Measurable.ite (measurableSet_eq_fun ha measurable_const)
      (hbmeas.comp hx) measurable_const
  have hRint : Integrable R μ := by
    refine @integrable_of_measurable_ae_bounded (CateObs d) instMeasurableSpaceCateObs μ
      inferInstance R (hRmeas.mono hmAX le_rfl) 1 ?_
    exact Filter.Eventually.of_forall fun O => by
      dsimp [R, P, cateWitnessLaw]
      split_ifs
      · exact hb O.X
      · norm_num
  have hR_int_finite :
      ∀ s : Set (CateObs d), MeasurableSet[mAX] s → μ s < ∞ → IntegrableOn R s μ := by
    intro s _ _
    exact hRint.integrableOn
  have hset : ∀ s : Set (CateObs d), MeasurableSet[mAX] s → μ s < ∞ →
      ∫ O in s, R O ∂μ = ∫ O in s, O.Y ∂μ := by
    intro s hs _
    rcases MeasurableSpace.measurableSet_comap.mp hs with ⟨S, hS, rfl⟩
    simpa [μ, P, R] using
      cateWitness_regression_setIntegral_eq Q e0 hbmeas hb he0 he1 S hS
  unfold MuIsRegression
  change μ[(fun O : CateObs d => O.Y) | mAX] =ᵐ[μ] R
  exact (ae_eq_condExp_of_forall_setIntegral_eq hmAX hYint hR_int_finite hset
    hRmeas.aestronglyMeasurable).symm

private lemma cateWitnessTreatmentMeasure_mean {e0 : ℝ}
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) :
    ∫ a : Bool, (if a then (1 : ℝ) else 0) ∂cateWitnessTreatmentMeasure e0 = e0 := by
  unfold cateWitnessTreatmentMeasure
  rw [integral_add_measure]
  · simp [he0]
  · exact Integrable.smul_measure (integrable_dirac (by simp [enorm])) (by simp)
  · exact Integrable.smul_measure (integrable_dirac (by simp [enorm])) (by simp)

private lemma cateWitness_propensity_setIntegral_eq {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    {b : (Fin d → ℝ) → ℝ} [IsProbabilityMeasure Q.PX]
    (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S) :
    ∫ O in (fun O : CateObs d => O.X) ⁻¹' S, e0
        ∂(cateWitnessLaw Q e0 b).dataMeasure =
      ∫ O in (fun O : CateObs d => O.X) ⁻¹' S,
        (if O.A = 1 then (1 : ℝ) else 0)
        ∂(cateWitnessLaw Q e0 b).dataMeasure := by
  classical
  let μ : Measure (CateObs d) := (cateWitnessLaw Q e0 b).dataMeasure
  let ν : Measure Bool := cateWitnessTreatmentMeasure e0
  let κ : (Fin d → ℝ) → Bool → Measure ℝ := fun x a =>
    twoPointMean 1 (if a then b x else 0)
  let pack : (Fin d → ℝ) → Bool → ℝ → CateObs d := cateWitnessPack
  let obs : (Fin d → ℝ) → Measure (CateObs d) := fun x =>
    ν.bind fun a => (κ x a).map (pack x a)
  let H : CateObs d → ℝ := ((fun O : CateObs d => O.X) ⁻¹' S).indicator fun _ => e0
  let K : CateObs d → ℝ := ((fun O : CateObs d => O.X) ⁻¹' S).indicator fun O =>
    if O.A = 1 then 1 else 0
  haveI : IsProbabilityMeasure ν := cateWitnessTreatmentMeasure_isProbabilityMeasure he0 he1
  have hmeanbd (x) (a : Bool) : |if a then b x else 0| ≤ 1 := by
    cases a <;> simp [hb x]
  have hκprob (x) (a) : IsProbabilityMeasure (κ x a) :=
    twoPointMean_isProbabilityMeasure (by norm_num) (hmeanbd x a)
  have hobsprob (x) : IsProbabilityMeasure (obs x) := by
    letI (a : Bool) : IsProbabilityMeasure (κ x a) := hκprob x a
    apply isProbabilityMeasure_bind
    · simpa [κ, pack] using ((measurable_cateWitnessOutcomeKernel hbmeas).comp
        (measurable_const.prodMk measurable_id)).aemeasurable
    · exact Filter.Eventually.of_forall fun a =>
        Measure.isProbabilityMeasure_map ((by
          dsimp [pack]
          rw [measurable_comap_iff]
          fun_prop : Measurable (pack x a)).aemeasurable)
  letI : IsProbabilityMeasure μ :=
    cateWitnessLaw_isProbabilityMeasure Q e0 b hbmeas hb he0 he1
  have hpre : MeasurableSet ((fun O : CateObs d => O.X) ⁻¹' S) :=
    hS.preimage measurable_CateObs_X
  have hH : Measurable H := measurable_const.indicator hpre
  have hK : Measurable K := (Measurable.ite
    (measurableSet_eq_fun measurable_CateObs_A measurable_const)
    measurable_const measurable_const).indicator hpre
  have hbdH (O) : |H O| ≤ 1 := by
    by_cases h : O.X ∈ S
    · simp [H, Set.indicator, h, abs_of_nonneg he0, he1]
    · simp [H, Set.indicator, h]
  have hbdK (O) : |K O| ≤ 1 := by
    by_cases h : O.X ∈ S
    · simp [K, h]
      split_ifs <;> norm_num
    · simp [K, h]
  have hHint : Integrable H μ :=
    integrable_of_measurable_ae_bounded hH 1 (Filter.Eventually.of_forall hbdH)
  have hKint : Integrable K μ :=
    integrable_of_measurable_ae_bounded hK 1 (Filter.Eventually.of_forall hbdK)
  have hobsmeas : Measurable obs := by
    simpa [obs, ν, κ, pack] using measurable_cateWitnessObservationKernel e0 hbmeas
  have hinner (x : Fin d → ℝ) : ∫ O, H O ∂obs x = ∫ O, K O ∂obs x := by
    letI : IsProbabilityMeasure (obs x) := hobsprob x
    have hHi : Integrable H (obs x) :=
      integrable_of_measurable_ae_bounded hH 1 (Filter.Eventually.of_forall hbdH)
    have hKi : Integrable K (obs x) :=
      integrable_of_measurable_ae_bounded hK 1 (Filter.Eventually.of_forall hbdK)
    have hκmeas : Measurable (fun a : Bool => κ x a) := measurable_of_finite _
    have hpackmeas (a : Bool) : Measurable (pack x a) := by
      dsimp [pack]
      rw [measurable_comap_iff]
      fun_prop
    have hmapmeas : Measurable (fun a : Bool => (κ x a).map (pack x a)) := by
      simpa [κ, pack] using (measurable_cateWitnessOutcomeKernel hbmeas).comp
        (measurable_const.prodMk measurable_id)
    rw [show obs x = ν.bind fun a => (κ x a).map (pack x a) by rfl]
    rw [Causalean.Mathlib.MeasureTheory.integral_bind_map hκmeas hpackmeas hmapmeas hHi]
    rw [Causalean.Mathlib.MeasureTheory.integral_bind_map hκmeas hpackmeas hmapmeas hKi]
    by_cases hx : x ∈ S
    · have hHval : (fun y => H (pack x false y)) = fun _ => e0 := by
        funext y
        simp [H, pack, cateWitnessPack, hx]
      have hKval (a : Bool) : (fun y => K (pack x a y)) =
          fun _ => if a then (1 : ℝ) else 0 := by
        funext y
        cases a <;> simp [K, pack, cateWitnessPack, hx]
      have hHvala (a : Bool) : (fun y => H (pack x a y)) = fun _ => e0 := by
        funext y
        simp [H, pack, cateWitnessPack, hx]
      simp_rw [hHvala, hKval]
      simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
        one_smul, Bool.false_eq_true, ite_eq_right_iff]
      simpa [ν] using (cateWitnessTreatmentMeasure_mean he0 he1).symm
    · have hHvala (a : Bool) : (fun y => H (pack x a y)) = fun _ => 0 := by
        funext y
        simp [H, pack, cateWitnessPack, hx]
      have hKval (a : Bool) : (fun y => K (pack x a y)) = fun _ => 0 := by
        funext y
        simp [K, pack, cateWitnessPack, hx]
      simp_rw [hHvala, hKval]
  have hcollapseH : ∫ O, H O ∂μ = ∫ x, ∫ O, H O ∂obs x ∂Q.PX := by
    simpa [μ, cateWitnessLaw, cateWitnessDataMeasure, obs, ν, κ, pack] using
      Causalean.Mathlib.MeasureTheory.integral_bind hobsmeas hHint
  have hcollapseK : ∫ O, K O ∂μ = ∫ x, ∫ O, K O ∂obs x ∂Q.PX := by
    simpa [μ, cateWitnessLaw, cateWitnessDataMeasure, obs, ν, κ, pack] using
      Causalean.Mathlib.MeasureTheory.integral_bind hobsmeas hKint
  rw [← integral_indicator hpre, ← integral_indicator hpre]
  change ∫ O, H O ∂μ = ∫ O, K O ∂μ
  rw [hcollapseH, hcollapseK]
  exact integral_congr_ae (Filter.Eventually.of_forall hinner)

/-- The constant declared propensity is the genuine conditional treatment
probability under the independent Bernoulli treatment draw. -/
lemma cateWitnessLaw_piIsPropensity {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    {b : (Fin d → ℝ) → ℝ} [IsProbabilityMeasure Q.PX]
    (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) : PiIsPropensity (cateWitnessLaw Q e0 b) := by
  classical
  let P := cateWitnessLaw Q e0 b
  let μ : Measure (CateObs d) := P.dataMeasure
  let mX : MeasurableSpace (CateObs d) :=
    MeasurableSpace.comap (fun O : CateObs d => O.X) inferInstance
  let score : CateObs d → ℝ := fun O => if O.A = 1 then 1 else 0
  let c : CateObs d → ℝ := fun _ => e0
  letI : IsProbabilityMeasure μ :=
    cateWitnessLaw_isProbabilityMeasure Q e0 b hbmeas hb he0 he1
  have hmX : mX ≤ instMeasurableSpaceCateObs := by
    dsimp [mX]
    exact measurable_CateObs_X.comap_le
  have hscoreGlobal :
      @Measurable (CateObs d) ℝ instMeasurableSpaceCateObs inferInstance score := by
    dsimp [score]
    exact Measurable.ite
      (measurableSet_eq_fun measurable_CateObs_A measurable_const)
      measurable_const measurable_const
  have hscoreInt : Integrable score μ := by
    refine @integrable_of_measurable_ae_bounded (CateObs d) instMeasurableSpaceCateObs μ
      inferInstance score hscoreGlobal 1 ?_
    exact Filter.Eventually.of_forall fun O => by
      dsimp [score]
      split_ifs <;> norm_num
  have hcX : Measurable[mX] c := measurable_const
  have hcInt : Integrable c μ := by
    refine @integrable_of_measurable_ae_bounded (CateObs d) instMeasurableSpaceCateObs μ
      inferInstance c measurable_const 1 ?_
    exact Filter.Eventually.of_forall fun _ => by rw [abs_of_nonneg he0]; exact he1
  have hc_int_finite :
      ∀ s : Set (CateObs d), MeasurableSet[mX] s → μ s < ∞ → IntegrableOn c s μ := by
    intro s _ _
    exact hcInt.integrableOn
  have hset : ∀ s : Set (CateObs d), MeasurableSet[mX] s → μ s < ∞ →
      ∫ O in s, c O ∂μ = ∫ O in s, score O ∂μ := by
    intro s hs _
    rcases MeasurableSpace.measurableSet_comap.mp hs with ⟨S, hS, rfl⟩
    simpa [μ, P, c, score] using
      cateWitness_propensity_setIntegral_eq Q e0 hbmeas hb he0 he1 S hS
  unfold PiIsPropensity
  change μ[score | mX] =ᵐ[μ] c
  exact (ae_eq_condExp_of_forall_setIntegral_eq hmX hscoreInt hc_int_finite hset
    hcX.aestronglyMeasurable).symm

/-- The retained density field represents the induced witness X-marginal. -/
lemma cateWitnessLaw_pxIsXDensity {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    {b : (Fin d → ℝ) → ℝ} (hQdens : PxIsXDensity Q) (hQmarg : PXIsXMarginal Q)
    (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) : PxIsXDensity (cateWitnessLaw Q e0 b) := by
  unfold PxIsXDensity
  calc
    (cateWitnessLaw Q e0 b).dataMeasure.map (fun O => O.X) = Q.PX :=
      cateWitnessLaw_map_X Q e0 hbmeas hb he0 he1
    _ = Q.dataMeasure.map (fun O => O.X) := hQmarg
    _ = (volume.restrict (cube d)).withDensity
        (fun x => ENNReal.ofReal ((cateWitnessLaw Q e0 b).px x)) := by
      simpa [cateWitnessLaw] using hQdens

/-- The witness's retained `PX` field equals its induced X-pushforward. -/
lemma cateWitnessLaw_pXIsXMarginal {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    {b : (Fin d → ℝ) → ℝ} (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) : PXIsXMarginal (cateWitnessLaw Q e0 b) := by
  unfold PXIsXMarginal
  simpa [cateWitnessLaw] using (cateWitnessLaw_map_X Q e0 hbmeas hb he0 he1).symm

lemma holderBallStd_const {d : ℕ} (c order M : ℝ) (S : Set (Fin d → ℝ))
    (hcM : |c| ≤ M) : HolderBallStd (fun _ => c) order M S := by
  have hM : 0 ≤ M := (abs_nonneg c).trans hcM
  refine ⟨contDiff_const.contDiffOn, ?_, ?_⟩
  · intro j hj x hx
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      exact hcM
    · rw [iteratedFDeriv_const_of_ne hj0.ne']
      simp only [Pi.zero_apply, norm_zero]
      exact hM
  · intro x hx y hy
    rcases Nat.eq_zero_or_pos (⌈order⌉₊ - 1) with hk0 | hk0
    · rw [hk0]
      have hcong : iteratedFDeriv ℝ 0 (fun _ : Fin d → ℝ => c) x =
          iteratedFDeriv ℝ 0 (fun _ : Fin d → ℝ => c) y := by
        ext m
        simp [iteratedFDeriv_zero_apply]
      rw [hcong, sub_self, norm_zero]
      positivity
    · rw [iteratedFDeriv_const_of_ne hk0.ne']
      simp only [Pi.zero_apply, sub_zero, norm_zero]
      positivity

/-- Assemble all class-membership fields for the latent independent two-point
witness.  The zero arm is Hölder for free. -/
lemma cateWitnessLaw_mem_class {d : ℕ}
    (alpha beta gamma L e0 f0 f1 r0 : ℝ) (x0 : Fin d → ℝ)
    (Q : CateLaw d) (b : (Fin d → ℝ) → ℝ)
    (hQ : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 Q)
    (hQiid : IidSampling Q)
    (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1)
    (he0 : 0 ≤ e0) (hehalf : e0 ≤ 1 / 2) (he0L : |e0| ≤ L)
    (hmu1 : HolderBallStd b beta L (cube d))
    (htau : HolderBallStd b gamma L (cube d)) :
    HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0
      (cateWitnessLaw Q e0 b) := by
  have he1 : e0 ≤ 1 := by linarith
  have hL : 0 ≤ L := by
    have : e0 ≤ L := by simpa [abs_of_nonneg he0] using he0L
    exact he0.trans this
  haveI : IsProbabilityMeasure Q.dataMeasure := hQiid.1
  haveI : IsProbabilityMeasure Q.PX := by
    rw [hQ.pxMarginal]
    exact Measure.isProbabilityMeasure_map measurable_CateObs_X.aemeasurable
  refine
    { consistency := cateWitnessLaw_consistency Q e0 hbmeas hb he0 he1
      exchangeability := cateWitnessLaw_condExchangeability Q e0 hbmeas hb he0 he1
      overlap := ?_
      piH := ?_
      muH := ⟨by
        simpa only [cateWitnessLaw] using
          holderBallStd_const (d := d) 0 beta L (cube d) (by simpa using hL), hmu1⟩
      tauH := ?_
      order := hQ.order
      localDensity := ?_
      muReg := cateWitnessLaw_muIsRegression Q e0 hbmeas hb he0 he1
      pxDens := cateWitnessLaw_pxIsXDensity Q e0 hQ.pxDens hQ.pxMarginal
        hbmeas hb he0 he1
      pxMarginal := cateWitnessLaw_pXIsXMarginal Q e0 hbmeas hb he0 he1
      piProp := cateWitnessLaw_piIsPropensity Q e0 hbmeas hb he0 he1
      potRange := cateWitnessLaw_potentialOutcomeRange Q e0 hbmeas hb he0 he1 }
  · intro x hx
    simp only [cateWitnessLaw]
    exact ⟨le_rfl, by linarith⟩
  · simpa only [PiHolder, cateWitnessLaw] using
      holderBallStd_const (d := d) e0 alpha L (cube d) he0L
  · unfold TauHolder
    convert htau using 1
    funext x
    simp only [cateWitnessLaw]
    ring
  · intro x hball hcube
    exact hQ.localDensity x hball hcube

end CausalSmith.Stat.DpCateMinimax
