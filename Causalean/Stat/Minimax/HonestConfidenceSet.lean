/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Minimax.TotalVariation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Honest confidence sets and frontier risk

This module provides model-free measure and order lemmas for honest random
confidence sets. It relates expected restricted volume to pointwise inclusion
probabilities, transfers coverage through total variation, and packages
uniform asymptotic coverage and frontier-risk bounds over arbitrary model
classes. It also fixes the worst-case coverage convention for empty model
classes.
-/

namespace Causalean.Stat

open Filter MeasureTheory
open scoped Topology

/-- The volume of a set after restriction to a parameter region. -/
noncomputable def restrictedSetVolume (region set : Set ℝ) : ℝ :=
  (volume (set ∩ region)).toReal

/-- The expected restricted volume of a jointly measurable random set equals
the integral, over the parameter region, of its pointwise inclusion
probabilities. -/
theorem expected_restrictedSetVolume_eq_integral_inclusion
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsFiniteMeasure Q] (C : Ω → Set ℝ)
    (region : Set ℝ)
    (hgraph : MeasurableSet {p : Ω × ℝ | p.2 ∈ C p.1})
    (hregion : MeasurableSet region) (hregionFinite : volume region ≠ ⊤) :
    (∫ ω, restrictedSetVolume region (C ω) ∂Q) =
      ∫ u in region, (Q {ω | u ∈ C ω}).toReal := by
  let S : Set (Ω × ℝ) := {p | p.2 ∈ C p.1 ∧ p.2 ∈ region}
  let f : Ω × ℝ → ℝ := S.indicator (fun _ => 1)
  have hS : MeasurableSet S := hgraph.inter (hregion.preimage measurable_snd)
  have hSsub : S ⊆ Set.univ ×ˢ region := by
    intro p hp
    exact ⟨Set.mem_univ _, hp.2⟩
  have hSfinite : (Q.prod volume) S ≠ ⊤ := by
    apply ne_of_lt
    calc
      (Q.prod volume) S ≤ (Q.prod volume) (Set.univ ×ˢ region) :=
        measure_mono hSsub
      _ = Q Set.univ * volume region := by rw [Measure.prod_prod]
      _ < ⊤ := ENNReal.mul_lt_top (measure_lt_top Q Set.univ)
        (lt_top_iff_ne_top.mpr hregionFinite)
  have hfint : Integrable f (Q.prod volume) := by
    rw [show f = S.indicator (fun _ => (1 : ℝ)) from rfl]
    exact (integrableOn_const hSfinite).integrable_indicator hS
  calc
    (∫ ω, restrictedSetVolume region (C ω) ∂Q) =
        ∫ ω, (∫ u, f (ω, u) ∂volume) ∂Q := by
      apply integral_congr_ae
      filter_upwards with ω
      rw [show restrictedSetVolume region (C ω) =
        (volume (C ω ∩ region)).toReal from rfl]
      rw [show (fun u => f (ω, u)) =
        (C ω ∩ region).indicator (fun _ => (1 : ℝ)) by
          funext u
          simp only [f, S, Set.indicator]
          split_ifs <;> simp_all]
      exact (integral_indicator_one
        (hgraph.preimage (measurable_const.prodMk measurable_id) |>.inter
          hregion)).symm
    _ = ∫ u, (∫ ω, f (ω, u) ∂Q) ∂volume := by
      calc
        _ = ∫ z, f z ∂Q.prod volume :=
          (integral_prod (μ := Q) (ν := volume) f hfint).symm
        _ = _ := integral_prod_symm (μ := Q) (ν := volume) f hfint
    _ = ∫ u in region, (Q {ω | u ∈ C ω}).toReal := by
      rw [← MeasureTheory.integral_indicator hregion]
      apply integral_congr_ae
      filter_upwards with u
      by_cases hu : u ∈ region
      · rw [show (fun ω => f (ω, u)) =
          {ω | u ∈ C ω}.indicator (fun _ => (1 : ℝ)) by
            funext ω
            simp only [f, S, Set.indicator]
            split_ifs <;> simp_all]
        rw [Set.indicator_of_mem hu]
        exact integral_indicator_one (μ := Q)
          (hgraph.preimage (measurable_id.prodMk measurable_const))
      · simp [f, S, hu]

/-- Uniform coverage on a measurable subset of a finite-volume parameter
region, together with a total-variation comparison to a reference law, forces
a lower bound on expected restricted volume under the reference law. -/
theorem coverage_tv_expectedRestrictedVolume_lower
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : ℝ → Measure Ω) (C : Ω → Set ℝ) (region I : Set ℝ)
    (reference coverage tv : ℝ)
    (hQ : ∀ u, IsProbabilityMeasure (Q u))
    (hcover : ∀ u ∈ I, coverage ≤ (Q u {ω | u ∈ C ω}).toReal)
    (htv : ∀ u ∈ I, tvDist (Q u) (Q reference) ≤ tv)
    (hgraph : MeasurableSet {p : Ω × ℝ | p.2 ∈ C p.1})
    (hregion : MeasurableSet region) (hregionFinite : volume region ≠ ⊤)
    (hI : MeasurableSet I) (hI_sub : I ⊆ region) :
    (volume I).toReal * (coverage - tv) ≤
      ∫ ω, restrictedSetVolume region (C ω) ∂Q reference := by
  letI : IsProbabilityMeasure (Q reference) := hQ reference
  have hpoint : ∀ u ∈ I,
      coverage - tv ≤ (Q reference {ω | u ∈ C ω}).toReal := by
    intro u hu
    letI : IsProbabilityMeasure (Q u) := hQ u
    have hE : MeasurableSet {ω | u ∈ C ω} :=
      hgraph.preimage (measurable_id.prodMk measurable_const)
    have hgap := measureReal_sub_le_tvDist
      (μ := Q reference) (ν := Q u) hE
    change (Q u {ω | u ∈ C ω}).toReal -
      (Q reference {ω | u ∈ C ω}).toReal ≤
        tvDist (Q reference) (Q u) at hgap
    rw [tvDist_symm] at hgap
    linarith [hcover u hu, htv u hu]
  rw [expected_restrictedSetVolume_eq_integral_inclusion
    (Q := Q reference) C region hgraph hregion hregionFinite]
  have hmeas : Measurable fun u =>
      (Q reference {ω | u ∈ C ω}).toReal :=
    Measurable.ennreal_toReal (measurable_measure_prodMk_right hgraph)
  have hIfinite : volume I ≠ ⊤ := ne_top_of_le_ne_top hregionFinite
    (measure_mono hI_sub)
  have hrhsint : IntegrableOn
      (fun u => (Q reference {ω | u ∈ C ω}).toReal) I := by
    letI : IsFiniteMeasure (volume.restrict I) :=
      isFiniteMeasure_restrict.mpr hIfinite
    exact Integrable.of_bound
      hmeas.aestronglyMeasurable.restrict 1
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        simpa only [← measureReal_def] using
          (measureReal_le_one (μ := Q reference)
            (s := {ω | u ∈ C ω})))
  have hrhsRegion : IntegrableOn
      (fun u => (Q reference {ω | u ∈ C ω}).toReal) region := by
    letI : IsFiniteMeasure (volume.restrict region) :=
      isFiniteMeasure_restrict.mpr hregionFinite
    exact Integrable.of_bound hmeas.aestronglyMeasurable.restrict 1
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        simpa only [← measureReal_def] using
          (measureReal_le_one (μ := Q reference)
            (s := {ω | u ∈ C ω})))
  calc
    (volume I).toReal * (coverage - tv) =
        ∫ _u in I, coverage - tv := by
      rw [setIntegral_const]
      simp [measureReal_def]
    _ ≤ ∫ u in I, (Q reference {ω | u ∈ C ω}).toReal :=
      setIntegral_mono_on (integrableOn_const hIfinite) hrhsint hI hpoint
    _ ≤ ∫ u in region, (Q reference {ω | u ∈ C ω}).toReal :=
      setIntegral_mono_set hrhsRegion
        (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
        (Filter.Eventually.of_forall hI_sub)

/-- Pointwise coverage rows with a vanishing uniform error imply asymptotic
uniform coverage over any eventually inhabited sequence of model classes. -/
theorem classCoverage_liminf
    {Model : Type*} (cls : ℕ → Model → Prop)
    (coverage : ℕ → Model → ℝ) (alpha : ℝ) (delta : ℕ → ℝ)
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hInhab : ∀ᶠ n in atTop, ∃ P, cls n P)
    (hcoverage : ∀ n P, cls n P →
      0 ≤ coverage n P ∧ coverage n P ≤ 1)
    (hrow : ∀ n P, cls n P → 1 - alpha - delta n ≤ coverage n P) :
    1 - alpha ≤ Filter.liminf
      (fun n => ⨅ P : {P : Model // cls n P}, coverage n P) atTop := by
  let row : ℕ → ℝ := fun n =>
    ⨅ P : {P : Model // cls n P}, coverage n P
  have hrows : ∀ᶠ n in atTop, 1 - alpha - delta n ≤ row n := by
    filter_upwards [hInhab] with n hn
    letI : Nonempty {P : Model // cls n P} :=
      ⟨⟨Classical.choose hn, Classical.choose_spec hn⟩⟩
    apply le_ciInf
    intro P
    exact hrow n P P.2
  have hrowUpper : ∀ᶠ n in atTop, row n ≤ 1 := by
    filter_upwards [hInhab] with n hn
    obtain ⟨P₀, hP₀⟩ := hn
    have hbdd : BddBelow
        (Set.range fun P : {P : Model // cls n P} => coverage n P) := by
      refine ⟨0, ?_⟩
      rintro y ⟨P, rfl⟩
      exact (hcoverage n P P.2).1
    exact (ciInf_le hbdd ⟨P₀, hP₀⟩).trans (hcoverage n P₀ hP₀).2
  have hlowerBounded :
      IsBoundedUnder (· ≥ ·) atTop (fun n => 1 - alpha - delta n) := by
    change ∃ b, ∀ᶠ n in atTop, b ≤ 1 - alpha - delta n
    have hdeltalt : ∀ᶠ n in atTop, delta n < 1 :=
      (tendsto_order.1 hdelta).2 1 zero_lt_one
    exact ⟨-alpha, hdeltalt.mono fun _ hn => by linarith⟩
  have hrowCobounded : IsCoboundedUnder (· ≥ ·) atTop row := by
    change ∃ b, ∀ a, (∀ᶠ n in atTop, a ≤ row n) → a ≤ b
    refine ⟨1, fun a ha => ?_⟩
    obtain ⟨n, han, hn1⟩ := (ha.and hrowUpper).exists
    exact han.trans hn1
  have hlowerTendsto :
      Tendsto (fun n => 1 - alpha - delta n) atTop (𝓝 (1 - alpha)) := by
    simpa using ((tendsto_const_nhds.sub tendsto_const_nhds).sub hdelta)
  change 1 - alpha ≤ Filter.liminf row atTop
  rw [← hlowerTendsto.liminf_eq]
  exact Filter.liminf_le_liminf hrows hlowerBounded hrowCobounded

/-- The capped inverse-square-root rate is antitone on positive strengths. -/
theorem inverseSqrtCap_anti {t0 t : ℝ} (ht0 : 0 < t0) (htt : t0 ≤ t) :
    min 1 (t ^ (-1 / 2 : ℝ)) ≤ min 1 (t0 ^ (-1 / 2 : ℝ)) := by
  apply min_le_min_left
  exact Real.rpow_le_rpow_of_nonpos ht0 htt (by norm_num)

/-- The asymptotic frontier risk of an arbitrary model class is the limsup of
the worst expected length among models above a strength threshold. -/
noncomputable def classFrontierRisk
    {Model : Type*} (cls : ℕ → Model → Prop)
    (strength expectedLength : ℕ → Model → ℝ) (t0 : ℝ) : ℝ :=
  Filter.limsup
    (fun n => ⨆ P : {P : Model // cls n P ∧ t0 ≤ strength n P},
      expectedLength n P) atTop

/-- A pointwise capped inverse-square-root expected-length bound passes through
both the class supremum and asymptotic limsup at the threshold value. -/
theorem classFrontierRisk_le
    {Model : Type*} (cls : ℕ → Model → Prop)
    (strength expectedLength : ℕ → Model → ℝ)
    (C0 t0 : ℝ) (hC0 : 0 ≤ C0) (ht0 : 0 < t0)
    (hLengthNonneg : ∀ n P, cls n P → 0 ≤ expectedLength n P)
    (hpoint : ∀ n P, cls n P →
      expectedLength n P ≤ C0 * min 1 (strength n P ^ (-1 / 2 : ℝ))) :
    classFrontierRisk cls strength expectedLength t0 ≤
      C0 * min 1 (t0 ^ (-1 / 2 : ℝ)) := by
  let bound : ℝ := C0 * min 1 (t0 ^ (-1 / 2 : ℝ))
  have hmin0 : 0 ≤ min 1 (t0 ^ (-1 / 2 : ℝ)) :=
    le_min (by norm_num) (Real.rpow_nonneg ht0.le _)
  have hbound0 : 0 ≤ bound := mul_nonneg hC0 hmin0
  let row : ℕ → ℝ := fun n =>
    ⨆ P : {P : Model // cls n P ∧ t0 ≤ strength n P}, expectedLength n P
  have hrowUpper : ∀ n, row n ≤ bound := by
    intro n
    let I := {P : Model // cls n P ∧ t0 ≤ strength n P}
    cases isEmpty_or_nonempty I with
    | inl hEmpty =>
        letI : IsEmpty I := hEmpty
        change (⨆ P : I, expectedLength n P) ≤ bound
        simpa using hbound0
    | inr hNonempty =>
        letI : Nonempty I := hNonempty
        apply ciSup_le
        intro P
        exact (hpoint n P P.2.1).trans
          (mul_le_mul_of_nonneg_left (inverseSqrtCap_anti ht0 P.2.2) hC0)
  have hrowLower : ∀ n, 0 ≤ row n := by
    intro n
    let I := {P : Model // cls n P ∧ t0 ≤ strength n P}
    cases isEmpty_or_nonempty I with
    | inl hEmpty =>
        letI : IsEmpty I := hEmpty
        change 0 ≤ ⨆ P : I, expectedLength n P
        simp
    | inr hNonempty =>
        letI : Nonempty I := hNonempty
        obtain ⟨P⟩ := hNonempty
        have hbdd : BddAbove (Set.range fun Q : I => expectedLength n Q) := by
          refine ⟨bound, ?_⟩
          rintro y ⟨Q, rfl⟩
          exact (hpoint n Q Q.2.1).trans
            (mul_le_mul_of_nonneg_left (inverseSqrtCap_anti ht0 Q.2.2) hC0)
        exact (hLengthNonneg n P P.2.1).trans (le_ciSup hbdd P)
  have hcob : IsCoboundedUnder (· ≤ ·) atTop row :=
    Filter.isCoboundedUnder_le_of_le atTop hrowLower
  change Filter.limsup row atTop ≤ bound
  exact Filter.limsup_le_of_le hcob (Filter.Eventually.of_forall hrowUpper)

/-- Worst-case coverage is the ordinary infimum when the model class is nonempty, but is
defined as one when the class is empty. A real-valued infimum over an empty index would
otherwise equal zero and misleadingly signal coverage failure for a vacuous model class.

The related `classCoverage_liminf` theorem avoids this issue by assuming that its model
classes are eventually inhabited; this definition instead makes the empty-class convention
explicit. -/
noncomputable def coverageInfOrOne {ι : Sort*} (f : ι → ℝ) : ℝ := by
  classical
  exact if Nonempty ι then ⨅ i, f i else 1

/-- On a nonempty model class, worst-case coverage with the empty-class convention is the
ordinary infimum of coverage across the class. -/
theorem coverageInfOrOne_of_nonempty {ι : Sort*} [Nonempty ι] (f : ι → ℝ) :
    coverageInfOrOne f = ⨅ i, f i := by
  have hne : Nonempty ι := inferInstance
  simp [coverageInfOrOne, hne]

/-- On an empty model class, worst-case coverage with the empty-class convention is one,
expressing that the coverage requirement is vacuously satisfied. -/
theorem coverageInfOrOne_of_isEmpty {ι : Sort*} [IsEmpty ι] (f : ι → ℝ) :
    coverageInfOrOne f = 1 := by
  simp [coverageInfOrOne, not_nonempty_iff.mpr inferInstance]

end Causalean.Stat
