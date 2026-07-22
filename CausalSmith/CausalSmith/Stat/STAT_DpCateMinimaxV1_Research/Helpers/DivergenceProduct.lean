/- Copyright (c) 2026 Jiyuan Tan. All rights reserved. -/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.TwoPointDivergence
import Causalean.Mathlib.InformationTheory.ProductKLLeCam
import Causalean.Stat.Minimax.Pinsker

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory ProbabilityTheory
open Causalean.Stat
open scoped ENNReal

/-- Tensorization plus Pinsker for the causal two-point witness. -/
lemma cateWitness_tv_product_le {d n : ℕ} (Q : CateLaw d) (e0 K : ℝ)
    (b : (Fin d → ℝ) → ℝ) [IsProbabilityMeasure Q.PX]
    (hbmeas : Measurable b) (hb : ∀ x, |b x| ≤ 1 / 2)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) (hK : 0 ≤ K)
    (hkl : InformationTheory.klDiv (cateWitnessLaw Q e0 b).dataMeasure
      (cateWitnessLaw Q e0 0).dataMeasure ≤ ENNReal.ofReal K) :
    tvDist (Measure.pi fun _ : Fin n => (cateWitnessLaw Q e0 0).dataMeasure)
        (Measure.pi fun _ : Fin n => (cateWitnessLaw Q e0 b).dataMeasure)
      ≤ Real.sqrt ((n : ℝ) * K / 2) := by
  let μ := (cateWitnessLaw Q e0 b).dataMeasure
  let ν := (cateWitnessLaw Q e0 0).dataMeasure
  have hb1 : ∀ x, |b x| ≤ 1 := fun x => (hb x).trans (by norm_num)
  letI : IsProbabilityMeasure μ :=
    cateWitnessLaw_isProbabilityMeasure Q e0 b hbmeas hb1 he0 he1
  letI : IsProbabilityMeasure ν :=
    cateWitnessLaw_isProbabilityMeasure Q e0 0 measurable_const (by simp) he0 he1
  obtain ⟨hac, hac', hint⟩ :=
    cateWitness_single_ac_and_int Q e0 b hbmeas hb he0 he1
  have ht := Causalean.Mathlib.InformationTheory.productKL_tensorization_iid
    n μ ν hac hac' hint
  have hsingle : (InformationTheory.klDiv μ ν).toReal ≤ K := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hkl
    simpa [μ, ν, ENNReal.toReal_ofReal hK] using this
  have hprod : (InformationTheory.klDiv
      (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => ν)).toReal
      ≤ (n : ℝ) * K :=
    ht.apply.trans (mul_le_mul_of_nonneg_left hsingle (Nat.cast_nonneg n))
  have hpinsker := pinskerBound_of_ac_of_ne_top
    (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => ν)
    (Causalean.Mathlib.InformationTheory.pi_iid_absolutelyContinuous μ ν hac n)
    ht.product_ne_top
  rw [tvDist_symm]
  calc
    tvDist (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => ν)
        ≤ Real.sqrt ((InformationTheory.klDiv
            (Measure.pi fun _ : Fin n => μ)
            (Measure.pi fun _ : Fin n => ν)).toReal / 2) := hpinsker
    _ ≤ Real.sqrt ((n : ℝ) * K / 2) := by
      apply Real.sqrt_le_sqrt
      linarith

end CausalSmith.Stat.DpCateMinimax
