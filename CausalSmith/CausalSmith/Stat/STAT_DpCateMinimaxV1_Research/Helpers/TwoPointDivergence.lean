/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.TwoPointDivergenceAux
import Causalean.Mathlib.InformationTheory.ProductKLLeCam
import Causalean.Stat.Minimax.Pinsker

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory ProbabilityTheory
open Causalean.Stat
open Causalean.Mathlib.Probability
open scoped ENNReal

private lemma cateWitness_mean_half {d : ℕ} {b : (Fin d → ℝ) → ℝ}
    (hb : ∀ x, |b x| ≤ 1 / 2) (p : (Fin d → ℝ) × Bool) :
    |if p.2 then b p.1 else 0| ≤ 1 / 2 := by
  cases p.2 <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.true_eq]
  · norm_num
  · exact hb p.1

/-- The single-draw KL is the covariate-treatment average of the signed
two-point mean-channel budget. -/
lemma cateWitness_kl_single_le {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    (b : (Fin d → ℝ) → ℝ) [IsProbabilityMeasure Q.PX]
    (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1 / 2)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) :
    InformationTheory.klDiv
      (cateWitnessLaw Q e0 b).dataMeasure
      (cateWitnessLaw Q e0 0).dataMeasure ≤
      ∫⁻ p, ENNReal.ofReal (2 * (b p.1) ^ 2) ∂cateWitnessAXMeasure Q e0 := by
  classical
  let m := cateWitnessAXMeasure Q e0
  let κ := cateWitnessChannel e0 b hbmeas
  let η := cateWitnessChannel e0 (0 : (Fin d → ℝ) → ℝ) measurable_const
  letI : IsProbabilityMeasure m := cateWitnessAXMeasure_isProbabilityMeasure Q e0 he0 he1
  letI : IsMarkovKernel κ := cateWitnessChannel_isMarkov e0 b hbmeas hb
  letI : IsMarkovKernel η := cateWitnessChannel_isMarkov e0 0 measurable_const (by simp)
  have hproj : Measurable (cateWitnessProj (d := d)) := measurable_cateWitnessProj
  have hgraph : MeasurableSet
      {p : ((Fin d → ℝ) × Bool) × CateObs d | p.1 = cateWitnessProj p.2} :=
    measurableSet_eq_fun measurable_fst (hproj.comp measurable_snd)
  have hκη : ∀ p, κ p ≪ η p := by
    intro p
    dsimp [κ, η]
    simpa using (twoPointMean_ac_zero (cateWitness_mean_half hb p)).map
      (measurableEmbedding_cateWitnessPack p.1 p.2).measurable
  haveI : MeasurableSpace.CountablyGenerated (CateObs d) := by
    change @MeasurableSpace.CountablyGenerated (CateObs d)
      (MeasurableSpace.comap (fun O : CateObs d => (O.Y, O.A, O.X)) inferInstance)
    exact MeasurableSpace.CountablyGenerated.comap
      (fun O : CateObs d => (O.Y, O.A, O.X))
  have hchain : InformationTheory.klDiv
      (cateWitnessLaw Q e0 b).dataMeasure
      (cateWitnessLaw Q e0 0).dataMeasure =
      ∫⁻ p, InformationTheory.klDiv (κ p) (η p) ∂m := by
    rw [show (cateWitnessLaw Q e0 b).dataMeasure = cateWitnessDataMeasure Q e0 b by rfl,
      show (cateWitnessLaw Q e0 0).dataMeasure = cateWitnessDataMeasure Q e0 0 by rfl,
      cateWitnessDataMeasure_eq_AXbind Q e0 b hbmeas,
      cateWitnessDataMeasure_eq_AXbind Q e0 0 measurable_const]
    exact Causalean.Mathlib.InformationTheory.Measure.klDiv_bind_eq_of_base_recording
      m κ η cateWitnessProj hproj hgraph
      (cateWitnessChannel_fibre_support e0 b hbmeas)
      (cateWitnessChannel_fibre_support e0 0 measurable_const) hκη
  rw [hchain]
  apply lintegral_mono
  intro p
  let u := if p.2 then b p.1 else 0
  have hu := cateWitness_mean_half hb p
  have hmap : InformationTheory.klDiv (κ p) (η p) =
      InformationTheory.klDiv (twoPointMean 1 u) (twoPointMean 1 0) := by
    dsimp [κ, η, u]
    haveI : IsProbabilityMeasure (twoPointMean 1
        (if p.2 then b p.1 else 0)) :=
      twoPointMean_isProbabilityMeasure (by norm_num) (hu.trans (by norm_num))
    haveI : IsProbabilityMeasure (twoPointMean 1 0) :=
      twoPointMean_isProbabilityMeasure (by norm_num) (by norm_num)
    simpa using Causalean.Mathlib.InformationTheory.Measure.klDiv_map_measurableEmbedding
      (μ := twoPointMean 1 u) (ν := twoPointMean 1 0)
      (measurableEmbedding_cateWitnessPack p.1 p.2)
  change InformationTheory.klDiv (κ p) (η p) ≤ ENNReal.ofReal (2 * (b p.1) ^ 2)
  rw [hmap]
  calc
    InformationTheory.klDiv (twoPointMean 1 u) (twoPointMean 1 0)
        ≤ ENNReal.ofReal (2 * (u - 0) ^ 2 / 1 ^ 2) :=
      bernoulli_mean_channel_kl 1 u 0 (by norm_num) hu (by norm_num)
    _ ≤ ENNReal.ofReal (2 * (b p.1) ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      dsimp [u]
      cases p.2 <;> simp [sq_nonneg]

/-- Finite single-draw KL supplies the absolute continuity and log-likelihood
integrability needed by product tensorization. -/
lemma cateWitness_single_ac_and_int {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    (b : (Fin d → ℝ) → ℝ) [IsProbabilityMeasure Q.PX]
    (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1 / 2)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) :
    (cateWitnessLaw Q e0 b).dataMeasure ≪ (cateWitnessLaw Q e0 0).dataMeasure ∧
    (cateWitnessLaw Q e0 0).dataMeasure ≪ (cateWitnessLaw Q e0 b).dataMeasure ∧
    Integrable (llr (cateWitnessLaw Q e0 b).dataMeasure
      (cateWitnessLaw Q e0 0).dataMeasure) (cateWitnessLaw Q e0 b).dataMeasure := by
  letI : IsProbabilityMeasure (cateWitnessAXMeasure Q e0) :=
    cateWitnessAXMeasure_isProbabilityMeasure Q e0 he0 he1
  have hbudget : InformationTheory.klDiv (cateWitnessLaw Q e0 b).dataMeasure
      (cateWitnessLaw Q e0 0).dataMeasure ≤ ENNReal.ofReal (1 / 2) := by
    calc
      _ ≤ ∫⁻ p, ENNReal.ofReal (2 * (b p.1) ^ 2) ∂cateWitnessAXMeasure Q e0 :=
        cateWitness_kl_single_le Q e0 b hbmeas hb he0 he1
      _ ≤ ∫⁻ _p, ENNReal.ofReal (1 / 2) ∂cateWitnessAXMeasure Q e0 := by
        apply lintegral_mono
        intro p
        apply ENNReal.ofReal_le_ofReal
        nlinarith [sq_abs (b p.1),
          (sq_le_sq₀ (abs_nonneg (b p.1)) (by norm_num)).mpr (hb p.1)]
      _ = ENNReal.ofReal (1 / 2) := by simp
  have hfinite : InformationTheory.klDiv (cateWitnessLaw Q e0 b).dataMeasure
      (cateWitnessLaw Q e0 0).dataMeasure ≠ ∞ := by
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbudget
  have hf := InformationTheory.klDiv_ne_top_iff.mp hfinite
  refine ⟨hf.1, ?_, hf.2⟩
  -- The fair channel gives positive mass to both support points, so the reverse AC is immediate.
  let m := cateWitnessAXMeasure Q e0
  let κ := cateWitnessChannel e0 b hbmeas
  let η := cateWitnessChannel e0 (0 : (Fin d → ℝ) → ℝ) measurable_const
  letI : IsMarkovKernel κ := cateWitnessChannel_isMarkov e0 b hbmeas hb
  letI : IsMarkovKernel η := cateWitnessChannel_isMarkov e0 0 measurable_const (by simp)
  haveI : MeasurableSpace.CountablyGenerated (CateObs d) := by
    change @MeasurableSpace.CountablyGenerated (CateObs d)
      (MeasurableSpace.comap (fun O : CateObs d => (O.Y, O.A, O.X)) inferInstance)
    exact MeasurableSpace.CountablyGenerated.comap
      (fun O : CateObs d => (O.Y, O.A, O.X))
  have hpoint : ∀ᵐ p ∂m, η p ≪ κ p := by
    filter_upwards [] with p
    dsimp [η, κ]
    have hu := cateWitness_mean_half hb p
    -- Both tilted channel masses are strictly positive in the half-band.
    have hac : twoPointMean 1 0 ≪
        twoPointMean 1 (if p.2 then b p.1 else 0) := by
      apply Measure.AbsolutelyContinuous.mk
      intro s hs hzero
      have h1 : (1 : ℝ) ∉ s := by
        intro h
        unfold twoPointMean at hzero
        rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply] at hzero
        have hcoef : 0 < (1 + (if p.2 then b p.1 else 0)) / 2 := by
          rcases abs_le.mp hu with ⟨hl, hr⟩
          linarith
        simp [h] at hzero
        linarith [hcoef, hzero.1]
      have hn1 : (-1 : ℝ) ∉ s := by
        intro h
        unfold twoPointMean at hzero
        rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply] at hzero
        have hcoef : 0 < (1 - (if p.2 then b p.1 else 0)) / 2 := by
          rcases abs_le.mp hu with ⟨hl, hr⟩
          linarith
        simp [h] at hzero
        linarith [hcoef, hzero.2]
      unfold twoPointMean
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
      simp [h1, hn1]
    simpa using hac.map (measurableEmbedding_cateWitnessPack p.1 p.2).measurable
  have hacprod : m ⊗ₘ η ≪ m ⊗ₘ κ :=
    Measure.AbsolutelyContinuous.compProd_right hpoint
  have hacmap := hacprod.map measurable_snd
  change (m ⊗ₘ η).snd ≪ (m ⊗ₘ κ).snd at hacmap
  rw [Measure.snd_compProd, Measure.snd_compProd] at hacmap
  simpa [m, κ, η,
    ← cateWitnessDataMeasure_eq_AXbind Q e0 b hbmeas,
    ← cateWitnessDataMeasure_eq_AXbind Q e0 (0 : (Fin d → ℝ) → ℝ) measurable_const] using hacmap

end CausalSmith.Stat.DpCateMinimax
