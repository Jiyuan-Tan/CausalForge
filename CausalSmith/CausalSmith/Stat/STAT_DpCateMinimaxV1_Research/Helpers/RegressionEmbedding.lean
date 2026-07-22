/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.CateWitness

/-! # Regression embedding for the private CATE witness

This module identifies the treated arm of the two-point CATE witness with a
pointwise-regression experiment.  It also isolates the common, contrast-independent
control law and proves that the full observed law is the corresponding mixture.
-/

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory
open Causalean.Stat
open ProbabilityTheory
open Causalean.Mathlib.Probability
open scoped ENNReal

-- @node: regToTreated
/-- The reduction sends a covariate-response pair to a treated causal observation. -/
def regToTreated {d : ℕ} (p : (Fin d → ℝ) × ℝ) : CateObs d :=
  cateWitnessPack p.1 true p.2

-- @node: regToTreated_Y
/-- The reduced observation retains the regression response as its outcome. -/
@[simp] lemma regToTreated_Y {d : ℕ} (p : (Fin d → ℝ) × ℝ) :
    (regToTreated p).Y = p.2 := rfl

-- @node: regToTreated_A
/-- The reduced observation is always assigned to the treated arm. -/
@[simp] lemma regToTreated_A {d : ℕ} (p : (Fin d → ℝ) × ℝ) :
    (regToTreated p).A = 1 := rfl

-- @node: regToTreated_X
/-- The reduced observation retains the regression covariate. -/
@[simp] lemma regToTreated_X {d : ℕ} (p : (Fin d → ℝ) × ℝ) :
    (regToTreated p).X = p.1 := rfl

-- @node: measurable_regToTreated
/-- The regression-to-treated-observation reduction is measurable. -/
@[fun_prop, measurability]
lemma measurable_regToTreated {d : ℕ} : Measurable (regToTreated (d := d)) := by
  exact measurable_cateWitnessPack true

-- @node: regToTreated_replacementAdjacent
/-- Applying the reduction coordinatewise preserves replacement adjacency of samples. -/
lemma regToTreated_replacementAdjacent {d m : ℕ}
    {D D' : Fin m → (Fin d → ℝ) × ℝ} (h : ReplacementAdjacent D D') :
    ReplacementAdjacent (fun i => regToTreated (D i))
      (fun i => regToTreated (D' i)) := by
  rcases h with ⟨i, hi⟩
  exact ⟨i, fun j hj => congrArg regToTreated (hi j hj)⟩

-- @node: cateWitnessRegressionLaw
/-- The regression law first draws a covariate and then a signed two-point response with the prescribed mean. -/
noncomputable def cateWitnessRegressionLaw {d : ℕ} (Q : CateLaw d)
    (b : (Fin d → ℝ) → ℝ) : Measure ((Fin d → ℝ) × ℝ) :=
  Q.PX.bind fun x => (twoPointMean 1 (b x)).map (fun y => (x, y))

-- @node: cateWitnessControlLaw
/-- The shared control law draws a covariate and a mean-zero response, independently of the regression function. -/
noncomputable def cateWitnessControlLaw {d : ℕ} (Q : CateLaw d) : Measure (CateObs d) :=
  Q.PX.bind fun x => (twoPointMean 1 0).map (cateWitnessPack x false)

private lemma measurable_regression_indicator {d : ℕ} (y : ℝ)
    (S : Set ((Fin d → ℝ) × ℝ)) (hS : MeasurableSet S) :
    Measurable (fun x : Fin d → ℝ =>
      ((fun z : ℝ => (x, z)) ⁻¹' S).indicator (fun _ => (1 : ℝ≥0∞)) y) := by
  convert measurable_const.indicator
    (hS.preimage (measurable_id.prodMk (measurable_const :
      Measurable (fun _ : Fin d → ℝ => y)))) using 1

private lemma measurable_regressionKernel {d : ℕ} {b : (Fin d → ℝ) → ℝ}
    (hb : Measurable b) : Measurable (fun x : Fin d → ℝ =>
      (twoPointMean 1 (b x)).map (fun y => (x, y))) := by
  refine Measure.measurable_of_measurable_coe _ ?_
  intro S hS
  have hp (x : Fin d → ℝ) : Measurable (fun y : ℝ => (x, y)) :=
    measurable_const.prodMk measurable_id
  simp_rw [Measure.map_apply (hp _) hS]
  unfold twoPointMean
  simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  simpa only [div_one] using
    ((by fun_prop (disch := assumption) : Measurable fun x : Fin d → ℝ =>
      ENNReal.ofReal ((1 + b x) / 2)).mul
        (measurable_regression_indicator (d := d) 1 S hS)).add
    ((by fun_prop (disch := assumption) : Measurable fun x : Fin d → ℝ =>
      ENNReal.ofReal ((1 - b x) / 2)).mul
        (measurable_regression_indicator (d := d) (-1) S hS))

private lemma measurable_controlKernel {d : ℕ} : Measurable (fun x : Fin d → ℝ =>
    (twoPointMean 1 0).map (cateWitnessPack x false)) := by
  have h := measurable_cateWitnessOutcomeKernel (d := d)
    (b := fun _ : Fin d → ℝ => 0) measurable_const
  simpa using h.comp (measurable_id.prodMk (measurable_const :
    Measurable (fun _ : Fin d → ℝ => false)))

-- @node: cateWitnessRegressionLaw_isProbabilityMeasure
/-- A measurable unit-bounded regression function produces a probability regression law. -/
lemma cateWitnessRegressionLaw_isProbabilityMeasure {d : ℕ} (Q : CateLaw d)
    {b : (Fin d → ℝ) → ℝ} [IsProbabilityMeasure Q.PX]
    (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1) :
    IsProbabilityMeasure (cateWitnessRegressionLaw Q b) := by
  unfold cateWitnessRegressionLaw
  apply isProbabilityMeasure_bind (measurable_regressionKernel hbmeas).aemeasurable
  exact Filter.Eventually.of_forall fun x => by
    letI : IsProbabilityMeasure (twoPointMean 1 (b x)) :=
      twoPointMean_isProbabilityMeasure (by norm_num) (hb x)
    exact Measure.isProbabilityMeasure_map
      (measurable_const.prodMk measurable_id).aemeasurable

-- @node: cateWitnessControlLaw_isProbabilityMeasure
/-- A probability covariate design produces a probability shared control law. -/
lemma cateWitnessControlLaw_isProbabilityMeasure {d : ℕ} (Q : CateLaw d)
    [IsProbabilityMeasure Q.PX] :
    IsProbabilityMeasure (cateWitnessControlLaw Q) := by
  unfold cateWitnessControlLaw
  apply isProbabilityMeasure_bind measurable_controlKernel.aemeasurable
  exact Filter.Eventually.of_forall fun x => by
    letI : IsProbabilityMeasure (twoPointMean 1 0) :=
      twoPointMean_isProbabilityMeasure (by norm_num) (by norm_num)
    have hp : Measurable (cateWitnessPack (d := d) x false) := by
      rw [measurable_comap_iff]
      fun_prop
    exact Measure.isProbabilityMeasure_map hp.aemeasurable

-- @node: cateWitnessControlLaw_support
/-- The shared control law assigns zero mass outside the untreated arm. -/
lemma cateWitnessControlLaw_support {d : ℕ} (Q : CateLaw d) :
    (cateWitnessControlLaw Q) {O : CateObs d | O.A = 0}ᶜ = 0 := by
  classical
  have hset : MeasurableSet ({O : CateObs d | O.A = 0}ᶜ) :=
    (measurableSet_eq_fun measurable_CateObs_A measurable_const).compl
  rw [cateWitnessControlLaw, Measure.bind_apply hset measurable_controlKernel.aemeasurable]
  apply lintegral_eq_zero_of_ae_eq_zero
  exact Filter.Eventually.of_forall fun x => by
    change ((twoPointMean 1 0).map (cateWitnessPack x false))
      {O : CateObs d | O.A = 0}ᶜ = 0
    have hp : Measurable (cateWitnessPack (d := d) x false) := by
      rw [measurable_comap_iff]
      fun_prop
    rw [Measure.map_apply hp hset]
    have he : (cateWitnessPack x false) ⁻¹' {O : CateObs d | O.A = 0}ᶜ = ∅ := by
      ext y
      simp [cateWitnessPack]
    simp [he]

-- @node: cateWitnessRegressionLaw_map_fst
/-- The embedded regression experiment has the same covariate marginal as the causal design. -/
lemma cateWitnessRegressionLaw_map_fst {d : ℕ} (Q : CateLaw d)
    {b : (Fin d → ℝ) → ℝ} [IsProbabilityMeasure Q.PX]
    (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1) :
    (cateWitnessRegressionLaw Q b).map Prod.fst = Q.PX := by
  classical
  ext S hS
  have hfst : Measurable (Prod.fst : ((Fin d → ℝ) × ℝ) → (Fin d → ℝ)) := measurable_fst
  rw [Measure.map_apply hfst hS]
  rw [cateWitnessRegressionLaw, Measure.bind_apply (hS.preimage hfst)
    (measurable_regressionKernel hbmeas).aemeasurable]
  have hinner (x : Fin d → ℝ) :
      ((twoPointMean 1 (b x)).map (fun y => (x, y))) (Prod.fst ⁻¹' S) =
        Set.indicator S (fun _ => (1 : ℝ≥0∞)) x := by
    have hp : Measurable (fun y : ℝ => (x, y)) := measurable_const.prodMk measurable_id
    rw [Measure.map_apply hp (hS.preimage hfst)]
    by_cases hx : x ∈ S
    · have he : (fun y : ℝ => (x, y)) ⁻¹' (Prod.fst ⁻¹' S) = Set.univ := by
        ext y
        simp [hx]
      rw [he]
      letI : IsProbabilityMeasure (twoPointMean 1 (b x)) :=
        twoPointMean_isProbabilityMeasure (by norm_num) (hb x)
      simp [hx]
    · have he : (fun y : ℝ => (x, y)) ⁻¹' (Prod.fst ⁻¹' S) = ∅ := by
        ext y
        simp [hx]
      simp [he, hx]
  simp_rw [hinner]
  rw [lintegral_indicator hS, lintegral_const]
  simp

-- @node: IsRegressionFn
/-- A function is a regression function when it equals the conditional mean of the response given the covariate. -/
def IsRegressionFn {d : ℕ} (rho : Measure ((Fin d → ℝ) × ℝ))
    (m : (Fin d → ℝ) → ℝ) : Prop :=
  rho[(fun p => p.2) |
      MeasurableSpace.comap (fun p : (Fin d → ℝ) × ℝ => p.1) inferInstance]
    =ᵐ[rho] (fun p => m p.1)

private lemma integrable_of_measurable_unit_bounded {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f)
    (h : ∀ᵐ x ∂μ, |f x| ≤ 1) : Integrable f μ := by
  refine Integrable.of_bound hf.aestronglyMeasurable 1 ?_
  filter_upwards [h] with x hx
  simpa [Real.norm_eq_abs] using hx

private lemma regression_response_ae_bounded {d : ℕ} (Q : CateLaw d)
    {b : (Fin d → ℝ) → ℝ} (hbmeas : Measurable b) :
    ∀ᵐ p ∂cateWitnessRegressionLaw Q b, |p.2| ≤ 1 := by
  rw [ae_iff]
  have hbad : {p : (Fin d → ℝ) × ℝ | ¬|p.2| ≤ 1} =
      (fun p : (Fin d → ℝ) × ℝ => p.2) ⁻¹' (Set.Icc (-1 : ℝ) 1)ᶜ := by
    ext p
    simp [abs_le]
  change (cateWitnessRegressionLaw Q b) {p | ¬|p.2| ≤ 1} = 0
  rw [hbad]
  have hs : MeasurableSet
      ((fun p : (Fin d → ℝ) × ℝ => p.2) ⁻¹' (Set.Icc (-1 : ℝ) 1)ᶜ) :=
    measurableSet_Icc.compl.preimage measurable_snd
  rw [cateWitnessRegressionLaw, Measure.bind_apply hs
    (measurable_regressionKernel hbmeas).aemeasurable]
  apply lintegral_eq_zero_of_ae_eq_zero
  exact Filter.Eventually.of_forall fun x => by
    change ((twoPointMean 1 (b x)).map (fun y => (x, y)))
      ((fun p : (Fin d → ℝ) × ℝ => p.2) ⁻¹' (Set.Icc (-1 : ℝ) 1)ᶜ) = 0
    have hp : Measurable (fun y : ℝ => (x, y)) := measurable_const.prodMk measurable_id
    rw [Measure.map_apply hp hs]
    change (twoPointMean 1 (b x)) {y | y ∉ Set.Icc (-1 : ℝ) 1} = 0
    exact twoPointMean_bad_support_zero (by norm_num)

private lemma regression_setIntegral_eq {d : ℕ} (Q : CateLaw d)
    {b : (Fin d → ℝ) → ℝ} [IsProbabilityMeasure Q.PX]
    (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S) :
    ∫ p in (Prod.fst ⁻¹' S), b p.1 ∂cateWitnessRegressionLaw Q b =
      ∫ p in (Prod.fst ⁻¹' S), p.2 ∂cateWitnessRegressionLaw Q b := by
  classical
  let rho := cateWitnessRegressionLaw Q b
  let k : (Fin d → ℝ) → Measure ((Fin d → ℝ) × ℝ) := fun x =>
    (twoPointMean 1 (b x)).map (fun y => (x, y))
  let F : ((Fin d → ℝ) × ℝ) → ℝ := (Prod.fst ⁻¹' S).indicator (fun p => b p.1)
  let G : ((Fin d → ℝ) × ℝ) → ℝ := (Prod.fst ⁻¹' S).indicator (fun p => p.2)
  letI : IsProbabilityMeasure rho :=
    cateWitnessRegressionLaw_isProbabilityMeasure Q hbmeas hb
  have hpre : MeasurableSet
      ((Prod.fst : ((Fin d → ℝ) × ℝ) → (Fin d → ℝ)) ⁻¹' S) :=
    hS.preimage measurable_fst
  have hF : Measurable F := (hbmeas.comp measurable_fst).indicator hpre
  have hG : Measurable G := measurable_snd.indicator hpre
  have hFbd : ∀ p, |F p| ≤ 1 := by
    intro p
    by_cases hp : p.1 ∈ S <;> simp [F, Set.indicator, hp, hb p.1]
  have hGae : ∀ᵐ p ∂rho, |G p| ≤ 1 := by
    have hsupp := regression_response_ae_bounded Q hbmeas
    change ∀ᵐ p ∂rho, |G p| ≤ 1
    filter_upwards [hsupp] with p hp
    by_cases hxy : p.1 ∈ S
    · simp [G, Set.indicator, hxy, hp]
    · simp [G, Set.indicator, hxy]
  have hFint : Integrable F rho := integrable_of_measurable_unit_bounded hF
    (Filter.Eventually.of_forall hFbd)
  have hGint : Integrable G rho := integrable_of_measurable_unit_bounded hG hGae
  have hk : Measurable k := measurable_regressionKernel hbmeas
  have hinner (x : Fin d → ℝ) : ∫ p, F p ∂k x = ∫ p, G p ∂k x := by
    letI : IsProbabilityMeasure (twoPointMean 1 (b x)) :=
      twoPointMean_isProbabilityMeasure (by norm_num) (hb x)
    have hp : Measurable (fun y : ℝ => (x, y)) := measurable_const.prodMk measurable_id
    by_cases hx : x ∈ S
    · have hFval : (fun y => F (x, y)) = fun _ => b x := by
        funext y
        simp [F, Set.indicator, hx]
      have hGval : (fun y => G (x, y)) = fun y => y := by
        funext y
        simp [G, Set.indicator, hx]
      change (∫ p, F p ∂(twoPointMean 1 (b x)).map (fun y => (x, y))) =
        ∫ p, G p ∂(twoPointMean 1 (b x)).map (fun y => (x, y))
      rw [integral_map hp.aemeasurable hF.aestronglyMeasurable,
        integral_map hp.aemeasurable hG.aestronglyMeasurable, hFval, hGval]
      rw [integral_const, measureReal_def, twoPointMean_mean (by norm_num) (hb x)]
      simp
    · have hFval : (fun y => F (x, y)) = fun _ => 0 := by
        funext y
        simp [F, Set.indicator, hx]
      have hGval : (fun y => G (x, y)) = fun _ => 0 := by
        funext y
        simp [G, Set.indicator, hx]
      change (∫ p, F p ∂(twoPointMean 1 (b x)).map (fun y => (x, y))) =
        ∫ p, G p ∂(twoPointMean 1 (b x)).map (fun y => (x, y))
      rw [integral_map hp.aemeasurable hF.aestronglyMeasurable,
        integral_map hp.aemeasurable hG.aestronglyMeasurable, hFval, hGval]
  have hcollapseF : ∫ p, F p ∂rho = ∫ x, ∫ p, F p ∂k x ∂Q.PX := by
    simpa [rho, cateWitnessRegressionLaw, k] using
      Causalean.Mathlib.MeasureTheory.integral_bind hk hFint
  have hcollapseG : ∫ p, G p ∂rho = ∫ x, ∫ p, G p ∂k x ∂Q.PX := by
    simpa [rho, cateWitnessRegressionLaw, k] using
      Causalean.Mathlib.MeasureTheory.integral_bind hk hGint
  rw [← integral_indicator hpre, ← integral_indicator hpre]
  change ∫ p, F p ∂rho = ∫ p, G p ∂rho
  rw [hcollapseF, hcollapseG]
  exact integral_congr_ae (Filter.Eventually.of_forall hinner)

-- @node: cateWitnessRegressionLaw_isRegressionFn
/-- The prescribed mean function is the conditional regression function of the embedded experiment. -/
lemma cateWitnessRegressionLaw_isRegressionFn {d : ℕ} (Q : CateLaw d)
    {b : (Fin d → ℝ) → ℝ} [IsProbabilityMeasure Q.PX]
    (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1) :
    IsRegressionFn (cateWitnessRegressionLaw Q b) b := by
  classical
  let rho := cateWitnessRegressionLaw Q b
  let mX : MeasurableSpace ((Fin d → ℝ) × ℝ) :=
    MeasurableSpace.comap Prod.fst
      (MeasurableSpace.pi : MeasurableSpace (Fin d → ℝ))
  let R : ((Fin d → ℝ) × ℝ) → ℝ := fun p => b p.1
  letI : IsProbabilityMeasure rho :=
    cateWitnessRegressionLaw_isProbabilityMeasure Q hbmeas hb
  have hmX : mX ≤
      (Prod.instMeasurableSpace : MeasurableSpace ((Fin d → ℝ) × ℝ)) := by
    dsimp [mX]
    exact measurable_fst.comap_le
  have hZint : Integrable (fun p : (Fin d → ℝ) × ℝ => p.2) rho := by
    have hzae := regression_response_ae_bounded Q hbmeas
    exact @integrable_of_measurable_unit_bounded _
      (Prod.instMeasurableSpace : MeasurableSpace ((Fin d → ℝ) × ℝ)) rho
      inferInstance _ measurable_snd hzae
  have hRmeas : Measurable[mX] R := by
    exact hbmeas.comp (Measurable.of_comap_le le_rfl)
  have hRint : Integrable R rho :=
    @integrable_of_measurable_unit_bounded _
      (Prod.instMeasurableSpace : MeasurableSpace ((Fin d → ℝ) × ℝ)) rho
      inferInstance R (hRmeas.mono hmX le_rfl)
        (Filter.Eventually.of_forall fun p => hb p.1)
  have hRfin : ∀ s, MeasurableSet[mX] s → rho s < ∞ → IntegrableOn R s rho := by
    intro s _ _
    exact hRint.integrableOn
  have hsets : ∀ s, MeasurableSet[mX] s → rho s < ∞ →
      ∫ p in s, R p ∂rho = ∫ p in s, p.2 ∂rho := by
    intro s hs _
    rcases MeasurableSpace.measurableSet_comap.mp hs with ⟨S, hS, rfl⟩
    simpa [rho, R] using regression_setIntegral_eq Q hbmeas hb S hS
  unfold IsRegressionFn
  change rho[(fun p : (Fin d → ℝ) × ℝ => p.2) | mX] =ᵐ[rho] R
  exact (ae_eq_condExp_of_forall_setIntegral_eq (μ := rho)
    (f := fun p : (Fin d → ℝ) × ℝ => p.2) (g := R) hmX hZint hRfin hsets
      hRmeas.aestronglyMeasurable).symm

private lemma regression_map_reduction {d : ℕ} (Q : CateLaw d)
    {b : (Fin d → ℝ) → ℝ} (hbmeas : Measurable b) :
    (cateWitnessRegressionLaw Q b).map regToTreated =
      Q.PX.bind fun x => (twoPointMean 1 (b x)).map (cateWitnessPack x true) := by
  ext S hS
  rw [Measure.map_apply measurable_regToTreated hS]
  rw [cateWitnessRegressionLaw, Measure.bind_apply
    (hS.preimage measurable_regToTreated) (measurable_regressionKernel hbmeas).aemeasurable]
  change (∫⁻ x, ((twoPointMean 1 (b x)).map (fun y => (x, y)))
      (regToTreated ⁻¹' S) ∂Q.PX) =
    (Q.PX.bind fun x => (twoPointMean 1 (b x)).map (cateWitnessPack x true)) S
  rw [Measure.bind_apply (m := Q.PX)
    (f := fun x => (twoPointMean 1 (b x)).map (cateWitnessPack x true))
    hS ((measurable_cateWitnessOutcomeKernel hbmeas).comp
      (measurable_id.prodMk measurable_const)).aemeasurable]
  apply lintegral_congr
  intro x
  have hp : Measurable (fun y : ℝ => (x, y)) := measurable_const.prodMk measurable_id
  have hpack : Measurable (cateWitnessPack (d := d) x true) := by
    rw [measurable_comap_iff]
    fun_prop
  rw [Measure.map_apply hp (hS.preimage measurable_regToTreated)]
  rw [Measure.map_apply hpack hS]
  rfl

-- @node: cateWitnessLaw_dataMeasure_mixture
/-- The causal witness law is a treated regression component mixed with a shared control component. -/
lemma cateWitnessLaw_dataMeasure_mixture {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    {b : (Fin d → ℝ) → ℝ} [IsProbabilityMeasure Q.PX]
    (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) :
    (cateWitnessLaw Q e0 b).dataMeasure
      = ENNReal.ofReal e0 • ((cateWitnessRegressionLaw Q b).map regToTreated)
        + ENNReal.ofReal (1 - e0) • cateWitnessControlLaw Q := by
  classical
  rw [regression_map_reduction Q hbmeas]
  ext S hS
  have ht : Measurable (fun x : Fin d → ℝ =>
      (twoPointMean 1 (b x)).map (cateWitnessPack x true)) := by
    simpa using (measurable_cateWitnessOutcomeKernel hbmeas).comp
      (measurable_id.prodMk measurable_const)
  have hc : Measurable (fun x : Fin d → ℝ =>
      (twoPointMean 1 0).map (cateWitnessPack x false)) := measurable_controlKernel
  unfold cateWitnessControlLaw
  rw [cateWitnessLaw, cateWitnessDataMeasure,
    Measure.bind_apply hS (measurable_cateWitnessObservationKernel e0 hbmeas).aemeasurable]
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [smul_eq_mul]
  rw [Measure.bind_apply hS ht.aemeasurable, Measure.bind_apply hS hc.aemeasurable]
  change (∫⁻ x, ((cateWitnessTreatmentMeasure e0).bind fun a =>
      (twoPointMean 1 (if a then b x else 0)).map (cateWitnessPack x a)) S ∂Q.PX) = _
  have hinner (x : Fin d → ℝ) :
      ((cateWitnessTreatmentMeasure e0).bind fun a =>
        (twoPointMean 1 (if a then b x else 0)).map (cateWitnessPack x a)) S =
      ENNReal.ofReal e0 * ((twoPointMean 1 (b x)).map (cateWitnessPack x true)) S +
      ENNReal.ofReal (1 - e0) * ((twoPointMean 1 0).map (cateWitnessPack x false)) S := by
    have hk : Measurable (fun a : Bool =>
        (twoPointMean 1 (if a then b x else 0)).map (cateWitnessPack x a)) :=
      (measurable_cateWitnessOutcomeKernel hbmeas).comp
        (measurable_const.prodMk measurable_id)
    rw [Measure.bind_apply hS hk.aemeasurable]
    unfold cateWitnessTreatmentMeasure
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
    simp
  simp_rw [hinner]
  have hte : Measurable (fun x =>
      ((twoPointMean 1 (b x)).map (cateWitnessPack x true)) S) :=
    Measure.measurable_coe hS |>.comp ht
  have hce : Measurable (fun x =>
      ((twoPointMean 1 0).map (cateWitnessPack x false)) S) :=
    Measure.measurable_coe hS |>.comp hc
  rw [lintegral_add_left (hte.const_mul _) _]
  rw [lintegral_const_mul _ hte, lintegral_const_mul _ hce]

end CausalSmith.Stat.DpCateMinimax
