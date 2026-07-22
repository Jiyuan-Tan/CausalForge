/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.Probability.StdNormalMoments

/-!
# General Gaussian survival and truncated first moment

This file lifts standard-normal tail identities to a real Gaussian law `N(m, v)` with
variance parameter `v > 0`.  The proofs use the affine change of variables
`y = m + sqrt v * z` from the standard normal and reuse the standard-normal survival and
truncated-moment formulas.

The public results are:

* `gaussianReal_Ioi_eq`: the right-tail probability
  `(gaussianReal m v) (Ioi c)` is `1 - stdNormalCDF ((c - m) / sqrt v)`;
* `integral_Ioi_id_gaussianReal`: the truncated first moment over `(c, infinity)` is
  `m * (1 - stdNormalCDF ((c - m) / sqrt v))
    + sqrt v * stdNormalPDF ((c - m) / sqrt v)`.
-/

namespace Causalean.Mathlib

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

private lemma gaussianReal_eq_map_std (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    gaussianReal m v = (gaussianReal 0 1).map (fun z => Real.sqrt (v : ℝ) * z + m) := by
  have hvpos_nn : (0 : ℝ≥0) < v := by
    exact bot_lt_iff_ne_bot.mpr hv
  have hvpos : 0 < (v : ℝ) := by
    exact_mod_cast hvpos_nn
  have hcoe : (⟨(v : ℝ), hvpos.le⟩ : ℝ≥0) = v := by
    ext
    simp
  calc
    gaussianReal m v = gaussianReal (0 + m) v := by simp
    _ = (gaussianReal 0 v).map (· + m) := by
      rw [gaussianReal_map_add_const]
    _ = ((gaussianReal 0 1).map (Real.sqrt (v : ℝ) * ·)).map (· + m) := by
      congr 1
      rw [gaussianReal_map_const_mul]
      simp [Real.sq_sqrt hvpos.le, hcoe]
    _ = (gaussianReal 0 1).map (fun z => Real.sqrt (v : ℝ) * z + m) := by
      rw [Measure.map_map]
      · rfl
      · exact (continuous_id.add continuous_const).measurable
      · exact (continuous_const.mul continuous_id).measurable

private lemma affine_preimage_Ioi {s c m : ℝ} (hs : 0 < s) :
    (fun z : ℝ => s * z + m) ⁻¹' Set.Ioi c = Set.Ioi ((c - m) / s) := by
  ext z
  dsimp [Set.preimage, Set.Ioi]
  constructor
  · intro hz
    have hz' : c - m < z * s := by nlinarith
    exact (div_lt_iff₀ hs).2 hz'
  · intro hz
    have hz' : c - m < z * s := (div_lt_iff₀ hs).1 hz
    nlinarith [hz']

private lemma stdNormalMeasure_Ioi_toReal_eq_integral (t : ℝ) :
    ((gaussianReal 0 1) (Set.Ioi t)).toReal = ∫ x in Set.Ioi t, stdNormalPDF x := by
  have hmeasure := ProbabilityTheory.gaussianReal_apply_eq_integral
    (μ := 0) (v := 1) (by norm_num) (Set.Ioi t)
  have hnonneg : 0 ≤ ∫ x in Set.Ioi t, gaussianPDFReal 0 1 x := by
    exact integral_nonneg fun x => gaussianPDFReal_nonneg 0 1 x
  rw [hmeasure]
  rw [ENNReal.toReal_ofReal hnonneg]
  simp [stdNormalPDF]

private lemma integrable_id_mul_stdNormalPDF : Integrable (fun x : ℝ => x * stdNormalPDF x) := by
  have hbase : Integrable (fun x : ℝ => x * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
    simpa using integrable_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
  have hpdf : ∀ x : ℝ,
      gaussianPDFReal 0 1 x =
        (Real.sqrt (2 * π))⁻¹ * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
    intro x
    unfold gaussianPDFReal
    congr 2
    · norm_num
    · norm_num
      ring
  convert hbase.const_mul (Real.sqrt (2 * π))⁻¹ using 1
  ext x
  rw [stdNormalPDF, hpdf x]
  ring

private lemma integral_Ioi_affine_stdNormal (s m t : ℝ) :
    ∫ z in Set.Ioi t, gaussianPDFReal 0 1 z * (s * z + m)
      = s * (∫ z in Set.Ioi t, z * stdNormalPDF z)
        + m * (∫ z in Set.Ioi t, stdNormalPDF z) := by
  have h_int_id : Integrable (fun z : ℝ => z * stdNormalPDF z)
      (volume.restrict (Set.Ioi t)) :=
    integrable_id_mul_stdNormalPDF.integrableOn
  have h_int_pdf : Integrable (fun z : ℝ => stdNormalPDF z)
      (volume.restrict (Set.Ioi t)) := by
    exact ((integrable_gaussianPDFReal 0 1).integrableOn :
      Integrable (fun z : ℝ => gaussianPDFReal 0 1 z) (volume.restrict (Set.Ioi t)))
  calc
    ∫ z in Set.Ioi t, gaussianPDFReal 0 1 z * (s * z + m)
        = ∫ z in Set.Ioi t, (s * (z * stdNormalPDF z) + m * stdNormalPDF z) := by
          congr 1
          ext z
          simp [stdNormalPDF]
          ring
    _ = (∫ z in Set.Ioi t, s * (z * stdNormalPDF z))
        + ∫ z in Set.Ioi t, m * stdNormalPDF z := by
          rw [integral_add]
          · exact h_int_id.const_mul s
          · exact h_int_pdf.const_mul m
    _ = s * (∫ z in Set.Ioi t, z * stdNormalPDF z)
        + m * (∫ z in Set.Ioi t, stdNormalPDF z) := by
          rw [integral_const_mul, integral_const_mul]

private lemma integral_Ioi_affine_gaussianReal_eq_density (s m t : ℝ) :
    ∫ z in Set.Ioi t, (s * z + m) ∂(gaussianReal 0 1)
      = ∫ z in Set.Ioi t, gaussianPDFReal 0 1 z * (s * z + m) := by
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero]
  · rw [setIntegral_withDensity_eq_setIntegral_toReal_smul]
    · congr 1
      ext z
      simp [ProbabilityTheory.gaussianPDF, ENNReal.toReal_ofReal, gaussianPDFReal_nonneg]
    · exact ProbabilityTheory.measurable_gaussianPDF 0 1
    · exact ae_of_all _ fun _ => ProbabilityTheory.gaussianPDF_lt_top
    · exact measurableSet_Ioi
  · norm_num

/-- **Gaussian survival.** For `N(m, v)` with `v > 0`, the right-tail mass is
`P(Y > c) = 1 − Φ((c − m)/√v)`. -/
lemma gaussianReal_Ioi_eq (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (c : ℝ) :
    ((gaussianReal m v) (Set.Ioi c)).toReal
      = 1 - stdNormalCDF ((c - m) / Real.sqrt (v : ℝ)) := by
  let s : ℝ := Real.sqrt (v : ℝ)
  let t : ℝ := (c - m) / s
  have hvpos_nn : (0 : ℝ≥0) < v := by
    exact bot_lt_iff_ne_bot.mpr hv
  have hvpos : 0 < (v : ℝ) := by
    exact_mod_cast hvpos_nn
  have hspos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 hvpos
  have hpre : (fun z : ℝ => s * z + m) ⁻¹' Set.Ioi c = Set.Ioi t := by
    simpa [t] using affine_preimage_Ioi (s := s) (c := c) (m := m) hspos
  calc
    ((gaussianReal m v) (Set.Ioi c)).toReal
        = (((gaussianReal 0 1).map (fun z : ℝ => s * z + m)) (Set.Ioi c)).toReal := by
          rw [gaussianReal_eq_map_std m v hv]
    _ = ((gaussianReal 0 1) (Set.Ioi t)).toReal := by
          rw [Measure.map_apply]
          · rw [hpre]
          · exact (continuous_const.mul continuous_id |>.add continuous_const).measurable
          · exact measurableSet_Ioi
    _ = ∫ x in Set.Ioi t, stdNormalPDF x := stdNormalMeasure_Ioi_toReal_eq_integral t
    _ = 1 - stdNormalCDF t := integral_Ioi_stdNormalPDF t
    _ = 1 - stdNormalCDF ((c - m) / Real.sqrt (v : ℝ)) := by rfl

/-- **Gaussian truncated first moment.** For `N(m, v)` with `v > 0`,
`∫_{c}^∞ y dN(m,v) = m·(1 − Φ((c − m)/√v)) + √v · φ((c − m)/√v)`.
The affine image of the standard-normal
truncated moment `∫_{t}^∞ z φ(z) dz = φ(t)`. -/
lemma integral_Ioi_id_gaussianReal (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (c : ℝ) :
    ∫ y in Set.Ioi c, y ∂(gaussianReal m v)
      = m * (1 - stdNormalCDF ((c - m) / Real.sqrt (v : ℝ)))
        + Real.sqrt (v : ℝ) * stdNormalPDF ((c - m) / Real.sqrt (v : ℝ)) := by
  let s : ℝ := Real.sqrt (v : ℝ)
  let t : ℝ := (c - m) / s
  have hvpos_nn : (0 : ℝ≥0) < v := by
    exact bot_lt_iff_ne_bot.mpr hv
  have hvpos : 0 < (v : ℝ) := by
    exact_mod_cast hvpos_nn
  have hspos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 hvpos
  have hpre : (fun z : ℝ => s * z + m) ⁻¹' Set.Ioi c = Set.Ioi t := by
    simpa [t] using affine_preimage_Ioi (s := s) (c := c) (m := m) hspos
  calc
    ∫ y in Set.Ioi c, y ∂(gaussianReal m v)
        = ∫ y in Set.Ioi c, y ∂Measure.map
            (fun z : ℝ => s * z + m) (gaussianReal 0 1) := by
          rw [gaussianReal_eq_map_std m v hv]
    _ = ∫ z in (fun z : ℝ => s * z + m) ⁻¹' Set.Ioi c,
          (s * z + m) ∂(gaussianReal 0 1) := by
          rw [setIntegral_map]
          · exact measurableSet_Ioi
          · exact continuous_id.aestronglyMeasurable
          · exact
              (continuous_const.mul continuous_id |>.add continuous_const).measurable.aemeasurable
    _ = ∫ z in Set.Ioi t, (s * z + m) ∂(gaussianReal 0 1) := by
          rw [hpre]
    _ = ∫ z in Set.Ioi t, gaussianPDFReal 0 1 z * (s * z + m) :=
          integral_Ioi_affine_gaussianReal_eq_density s m t
    _ = s * (∫ z in Set.Ioi t, z * stdNormalPDF z)
          + m * (∫ z in Set.Ioi t, stdNormalPDF z) :=
          integral_Ioi_affine_stdNormal s m t
    _ = s * stdNormalPDF t + m * (1 - stdNormalCDF t) := by
          rw [integral_Ioi_id_mul_stdNormalPDF, integral_Ioi_stdNormalPDF]
    _ = m * (1 - stdNormalCDF ((c - m) / Real.sqrt (v : ℝ)))
          + Real.sqrt (v : ℝ) * stdNormalPDF ((c - m) / Real.sqrt (v : ℝ)) := by
          dsimp [s, t]
          ring

end Causalean.Mathlib
