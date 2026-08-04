/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Minimax.HonestConfidenceSet
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Affine test inversion

This module develops model-free geometry and expected-volume bounds for
confidence sets obtained by inverting a scalar affine inequality over a
finite-volume parameter region. The final result converts a mean-radius bound
and a bad-slope probability into the capped inverse-square-root frontier rate.
-/

namespace Causalean.Stat

open MeasureTheory

/-- The subset of a parameter region accepted by a scalar affine inequality. -/
noncomputable def affineInversionSet (region : Set ℝ) (A B r : ℝ) : Set ℝ :=
  {theta | theta ∈ region ∧ |A - theta * B| ≤ r}

/-- Affine inversion has restricted volume at most the parameter-region volume
and at most twice the radius divided by the nonzero slope. -/
theorem affineInversionSet_restrictedVolume_le
    (region : Set ℝ) (hregionFinite : volume region ≠ ⊤)
    (A B r : ℝ) (hB : B ≠ 0) (hr : 0 ≤ r) :
    restrictedSetVolume region (affineInversionSet region A B r) ≤
      min (volume region).toReal (2 * r / |B|) := by
  have hAbsB : 0 < |B| := abs_pos.mpr hB
  apply le_min
  · unfold restrictedSetVolume
    exact ENNReal.toReal_mono hregionFinite (measure_mono Set.inter_subset_right)
  · have hsub :
        affineInversionSet region A B r ∩ region ⊆
          Set.Icc (A / B - r / |B|) (A / B + r / |B|) := by
      intro x hx
      have hscore := hx.1.2
      change A / B - r / |B| ≤ x ∧ x ≤ A / B + r / |B|
      have hid : A - x * B = B * (A / B - x) := by field_simp [hB]
      rw [hid, abs_mul] at hscore
      have hx' : |A / B - x| ≤ r / |B| := by
        rw [le_div_iff₀ hAbsB]
        simpa [mul_comm] using hscore
      rw [abs_le] at hx'
      constructor <;> linarith
    unfold restrictedSetVolume
    calc
      (volume (affineInversionSet region A B r ∩ region)).toReal ≤
          (volume (Set.Icc (A / B - r / |B|)
            (A / B + r / |B|))).toReal :=
        ENNReal.toReal_mono (by simp [Real.volume_Icc]) (measure_mono hsub)
      _ = 2 * r / |B| := by
        simp [Real.volume_Icc, ENNReal.toReal_ofReal,
          div_nonneg hr hAbsB.le]
        field_simp
        ring

/-- Affine inversion is always bounded by the volume of its parameter region. -/
theorem affineInversionSet_restrictedVolume_le_region
    (region : Set ℝ) (hregionFinite : volume region ≠ ⊤) (A B r : ℝ) :
    restrictedSetVolume region (affineInversionSet region A B r) ≤
      (volume region).toReal := by
  unfold restrictedSetVolume
  exact ENNReal.toReal_mono hregionFinite (measure_mono Set.inter_subset_right)

private theorem integrable_sqrt_of_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsFiniteMeasure Q]
    (f : Ω → ℝ) (hf : Integrable f Q) (hfn : ∀ w, 0 ≤ f w) :
    Integrable (fun w => Real.sqrt (f w)) Q := by
  apply (hf.norm.add (integrable_const (1 : ℝ))).mono'
  · exact Real.continuous_sqrt.comp_aestronglyMeasurable
      hf.aestronglyMeasurable
  · filter_upwards with w
    have hs := Real.sqrt_nonneg (f w)
    have hsq := Real.sq_sqrt (hfn w)
    have hamgm : 2 * Real.sqrt (f w) ≤ f w + 1 := by
      nlinarith [sq_nonneg (Real.sqrt (f w) - 1)]
    simp only [Pi.add_apply, Real.norm_eq_abs,
      abs_of_nonneg hs, abs_of_nonneg (hfn w)]
    linarith

/-- Expected restricted volume for affine inversion is controlled by the mean
radius and by the probability that the random slope is less than half its
positive target value. -/
theorem expectedRestrictedVolume_affineInversion_le
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (region : Set ℝ) (hregionFinite : volume region ≠ ⊤)
    (A B K : Ω → ℝ) (n : ℕ) (L mu Kbar q : ℝ)
    (hL : 0 ≤ L) (hmu : 0 < mu) (hn : 0 < n)
    (hK : ∀ w, 0 ≤ K w) (hKint : Integrable K Q)
    (hKbar : (∫ w, K w ∂Q) ≤ Kbar)
    (hbad : (Q {w | mu / 2 < |B w - mu|}).toReal ≤ q) :
    (∫ w, restrictedSetVolume region
      (affineInversionSet region (A w) (B w)
        (L * Real.sqrt (K w / n))) ∂Q) ≤
      4 * L * Real.sqrt (Kbar / n) / mu + (volume region).toReal * q := by
  let F : Ω → ℝ := fun w =>
    restrictedSetVolume region
      (affineInversionSet region (A w) (B w)
        (L * Real.sqrt (K w / n)))
  let S : Ω → ℝ := fun w => Real.sqrt (K w / n)
  let c : ℝ := 4 * L / mu
  let d : ℝ := (volume region).toReal
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hSn : ∀ w, 0 ≤ K w / (n : ℝ) :=
    fun w => div_nonneg (hK w) hnR.le
  have hKnInt : Integrable (fun w => K w / (n : ℝ)) Q :=
    hKint.div_const _
  have hSint : Integrable S Q := integrable_sqrt_of_nonneg _ hKnInt hSn
  have hc : 0 ≤ c := div_nonneg (mul_nonneg (by norm_num) hL) hmu.le
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have hIntK_nonneg : 0 ≤ ∫ w, K w ∂Q :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall hK)
  have hKbar_nonneg : 0 ≤ Kbar := hIntK_nonneg.trans hKbar
  have hq : 0 ≤ q := ENNReal.toReal_nonneg.trans hbad
  have hright_nonneg :
      0 ≤ 4 * L * Real.sqrt (Kbar / (n : ℝ)) / mu + d * q := by
    positivity
  by_cases hFi : Integrable F Q
  · have hgood_pointwise :
        ∀ w, |B w - mu| ≤ mu / 2 → F w ≤ c * S w := by
      intro w hw
      have hBabs : mu / 2 ≤ |B w| := by
        have hrev := abs_sub_abs_le_abs_sub mu (B w)
        rw [abs_of_pos hmu, abs_sub_comm] at hrev
        linarith
      have hBpos : 0 < |B w| := (half_pos hmu).trans_le hBabs
      have hBne : B w ≠ 0 := abs_pos.mp hBpos
      have hr : 0 ≤ L * S w := mul_nonneg hL (Real.sqrt_nonneg _)
      have hlen : F w ≤ 2 * (L * S w) / |B w| :=
        (affineInversionSet_restrictedVolume_le region hregionFinite
          (A w) (B w) (L * S w) hBne hr).trans (min_le_right _ _)
      have hdiv :
          2 * (L * S w) / |B w| ≤ 2 * (L * S w) / (mu / 2) :=
        div_le_div_of_nonneg_left (mul_nonneg (by positivity) hr)
          (half_pos hmu) hBabs
      calc
        F w ≤ 2 * (L * S w) / |B w| := hlen
        _ ≤ 2 * (L * S w) / (mu / 2) := hdiv
        _ = c * S w := by
          dsimp [c]
          field_simp
          ring
    let Fm : Ω → ℝ := hFi.aestronglyMeasurable.mk F
    let Sm : Ω → ℝ := hSint.aestronglyMeasurable.mk S
    let D : Set Ω := {w | c * Sm w < Fm w}
    have hFm : Measurable Fm := hFi.aestronglyMeasurable.measurable_mk
    have hSm : Measurable Sm := hSint.aestronglyMeasurable.measurable_mk
    have hD : MeasurableSet D := measurableSet_lt (hSm.const_mul c) hFm
    have hFeq : F =ᵐ[Q] Fm := hFi.aestronglyMeasurable.ae_eq_mk
    have hSeq : S =ᵐ[Q] Sm := hSint.aestronglyMeasurable.ae_eq_mk
    have hD_bad : D ≤ᵐ[Q] {w | mu / 2 < |B w - mu|} := by
      filter_upwards [hFeq, hSeq] with w hFw hSw hwD
      by_contra hwbad
      have hwgood : |B w - mu| ≤ mu / 2 := le_of_not_gt hwbad
      have hwle := hgood_pointwise w hwgood
      change c * Sm w < Fm w at hwD
      rw [← hFw, ← hSw] at hwD
      linarith
    have hDreal : (Q D).toReal ≤ q :=
      (ENNReal.toReal_mono (by finiteness) (measure_mono_ae hD_bad)).trans hbad
    have hmajorant_int : Integrable
        (fun w => c * S w + D.indicator (fun _ => d) w) Q :=
      (hSint.const_mul c).add ((integrable_const d).indicator hD)
    have hmajorant :
        F ≤ᵐ[Q] fun w => c * S w + D.indicator (fun _ => d) w := by
      filter_upwards [hFeq, hSeq] with w hFw hSw
      by_cases hwD : w ∈ D
      · simp only [Set.indicator_of_mem hwD]
        have hFd : F w ≤ d :=
          affineInversionSet_restrictedVolume_le_region region hregionFinite _ _ _
        have hSnonneg : 0 ≤ S w := Real.sqrt_nonneg _
        nlinarith
      · simp only [Set.indicator, hwD, if_false]
        have hwle : Fm w ≤ c * Sm w := le_of_not_gt hwD
        rw [← hFw, ← hSw] at hwle
        simpa using hwle
    have hJensen :
        (∫ w, S w ∂Q) ≤ Real.sqrt ((∫ w, K w ∂Q) / (n : ℝ)) := by
      have hj := Real.strictConcaveOn_sqrt.concaveOn.le_map_integral
        Real.continuous_sqrt.continuousOn isClosed_Ici
        (Filter.Eventually.of_forall hSn) hKnInt hSint
      simpa [S, Function.comp_def, integral_div] using hj
    have hsqrt_mono :
        Real.sqrt ((∫ w, K w ∂Q) / (n : ℝ)) ≤
          Real.sqrt (Kbar / (n : ℝ)) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hKbar hnR.le)
    calc
      (∫ w, restrictedSetVolume region
          (affineInversionSet region (A w) (B w)
            (L * Real.sqrt (K w / n))) ∂Q) = ∫ w, F w ∂Q := by rfl
      _ ≤ ∫ w, c * S w + D.indicator (fun _ => d) w ∂Q :=
        integral_mono_ae hFi hmajorant_int hmajorant
      _ = c * (∫ w, S w ∂Q) + d * (Q D).toReal := by
        rw [integral_add (hSint.const_mul c)
          ((integrable_const d).indicator hD), integral_const_mul,
          integral_indicator_const d hD]
        simp only [smul_eq_mul, Measure.real]
        ring
      _ ≤ c * Real.sqrt (Kbar / (n : ℝ)) + d * q := by
        gcongr
        exact hJensen.trans hsqrt_mono
      _ = 4 * L * Real.sqrt (Kbar / (n : ℝ)) / mu + d * q := by
        dsimp [c]
        ring
  · rw [show (∫ w, restrictedSetVolume region
        (affineInversionSet region (A w) (B w)
          (L * Real.sqrt (K w / n))) ∂Q) = 0 by exact integral_undef hFi]
    exact hright_nonneg

private theorem expectedRestrictedVolume_affineInversion_le_region
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (region : Set ℝ) (hregionFinite : volume region ≠ ⊤)
    (A B r : Ω → ℝ) :
    (∫ w, restrictedSetVolume region
      (affineInversionSet region (A w) (B w) (r w)) ∂Q) ≤
      (volume region).toReal := by
  let F : Ω → ℝ := fun w => restrictedSetVolume region
    (affineInversionSet region (A w) (B w) (r w))
  by_cases hFi : Integrable F Q
  · exact (integral_mono_ae hFi (integrable_const _)
      (Filter.Eventually.of_forall fun w =>
        affineInversionSet_restrictedVolume_le_region region hregionFinite
          (A w) (B w) (r w))).trans_eq (by simp)
  · rw [show (∫ w, restrictedSetVolume region
        (affineInversionSet region (A w) (B w) (r w)) ∂Q) = 0 by
      exact integral_undef hFi]
    exact ENNReal.toReal_nonneg

/-- An inverse-root plus inverse-strength bound, capped by a nonnegative region
volume, is bounded by the compact inverse-square-root frontier form. -/
theorem inverseStrength_to_frontier
    {cap A B t : ℝ} (hB : 0 ≤ B) (ht : 0 < t) :
    min cap (A / Real.sqrt t + B / t) ≤
      max cap (A + B) * min 1 (t ^ (-1 / 2 : ℝ)) := by
  by_cases ht1 : t ≤ 1
  · rw [min_eq_left
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (by norm_num))]
    simp only [mul_one]
    exact (min_le_left _ _).trans (le_max_left _ _)
  · have h1t : 1 ≤ t := le_of_not_ge ht1
    rw [min_eq_right
      (Real.rpow_le_one_of_one_le_of_nonpos h1t (by norm_num))]
    have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    have hsqrt_le_t : Real.sqrt t ≤ t := by
      nlinarith [Real.sq_sqrt ht.le]
    have hBt : B / t ≤ B / Real.sqrt t :=
      div_le_div_of_nonneg_left hB hsqrt hsqrt_le_t
    have hsum : A / Real.sqrt t + B / t ≤ (A + B) / Real.sqrt t := by
      calc
        A / Real.sqrt t + B / t ≤ A / Real.sqrt t + B / Real.sqrt t :=
          add_le_add_right hBt _
        _ = (A + B) / Real.sqrt t := by ring
    calc
      min cap (A / Real.sqrt t + B / t) ≤
          A / Real.sqrt t + B / t := min_le_right _ _
      _ ≤ (A + B) / Real.sqrt t := hsum
      _ = (A + B) * t ^ (-1 / 2 : ℝ) := by
        rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num,
          Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
        simp [div_eq_mul_inv]
      _ ≤ max cap (A + B) * t ^ (-1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _)
          (Real.rpow_nonneg ht.le _)

private theorem sqrt_mul_kappa_div_n_div_mu
    (a n mu kappa t : ℝ)
    (ha : 0 ≤ a) (hn : 0 < n) (hmu : 0 < mu) (hkappa : 0 < kappa)
    (ht : t = n * mu ^ 2 / kappa) :
    Real.sqrt (a * kappa / n) / mu = Real.sqrt a / Real.sqrt t := by
  have htpos : 0 < t := by rw [ht]; positivity
  have hleft : 0 ≤ Real.sqrt (a * kappa / n) / mu :=
    div_nonneg (Real.sqrt_nonneg _) hmu.le
  have hright : 0 ≤ Real.sqrt a / Real.sqrt t :=
    div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq :
      (Real.sqrt (a * kappa / n) / mu) ^ 2 =
        (Real.sqrt a / Real.sqrt t) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (div_nonneg
      (mul_nonneg ha hkappa.le) hn.le), div_pow, Real.sq_sqrt ha,
      Real.sq_sqrt htpos.le, ht]
    field_simp [hn.ne', hmu.ne', hkappa.ne']
  nlinarith

/-- The complete affine-inversion frontier chain over a finite-volume region:
an inflated mean-radius proxy and a controlled bad-slope contribution yield a
capped inverse-square-root expected-volume bound. -/
theorem expectedRestrictedVolume_affineInversion_frontier_le
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (region : Set ℝ) (hregionFinite : volume region ≠ ⊤)
    (A B K : Ω → ℝ) (n : ℕ)
    (L mu Kbar q kappa inflation Y t : ℝ)
    (hL : 0 ≤ L) (hmu : 0 < mu) (hn : 0 < n)
    (hK : ∀ w, 0 ≤ K w) (hKint : Integrable K Q)
    (hKbar : (∫ w, K w ∂Q) ≤ Kbar)
    (hbad : (Q {w | mu / 2 < |B w - mu|}).toReal ≤ q)
    (hkappa : 0 < kappa) (hinflation : 0 ≤ inflation) (hY : 0 ≤ Y)
    (hKbar_le : Kbar ≤ inflation * kappa)
    (hbadContribution : (volume region).toReal * q ≤ Y / t)
    (ht : t = (n : ℝ) * mu ^ 2 / kappa) :
    (∫ w, restrictedSetVolume region
      (affineInversionSet region (A w) (B w)
        (L * Real.sqrt (K w / n))) ∂Q) ≤
      max (volume region).toReal (4 * Real.sqrt inflation * L + Y) *
        min 1 (t ^ (-1 / 2 : ℝ)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have htpos : 0 < t := by rw [ht]; positivity
  have hbase := expectedRestrictedVolume_affineInversion_le
    Q region hregionFinite A B K n L mu Kbar q hL hmu hn hK hKint
      hKbar hbad
  have hcap := expectedRestrictedVolume_affineInversion_le_region
    Q region hregionFinite A B (fun w => L * Real.sqrt (K w / n))
  have hsqrt :
      Real.sqrt (Kbar / (n : ℝ)) ≤
        Real.sqrt (inflation * kappa / (n : ℝ)) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hKbar_le hnR.le)
  have hratio :
      Real.sqrt (inflation * kappa / (n : ℝ)) / mu =
        Real.sqrt inflation / Real.sqrt t :=
    sqrt_mul_kappa_div_n_div_mu inflation n mu kappa t hinflation
      hnR hmu hkappa ht
  have hradius :
      4 * L * Real.sqrt (Kbar / (n : ℝ)) / mu ≤
        (4 * Real.sqrt inflation * L) / Real.sqrt t := by
    calc
      4 * L * Real.sqrt (Kbar / (n : ℝ)) / mu ≤
          4 * L * Real.sqrt (inflation * kappa / (n : ℝ)) / mu := by
        gcongr
      _ = 4 * L *
          (Real.sqrt (inflation * kappa / (n : ℝ)) / mu) := by ring
      _ = (4 * Real.sqrt inflation * L) / Real.sqrt t := by
        rw [hratio]
        ring
  have hsum :
      4 * L * Real.sqrt (Kbar / (n : ℝ)) / mu +
          (volume region).toReal * q ≤
        (4 * Real.sqrt inflation * L) / Real.sqrt t + Y / t :=
    add_le_add hradius hbadContribution
  calc
    (∫ w, restrictedSetVolume region
        (affineInversionSet region (A w) (B w)
          (L * Real.sqrt (K w / n))) ∂Q) ≤
        min (volume region).toReal
          (4 * L * Real.sqrt (Kbar / (n : ℝ)) / mu +
            (volume region).toReal * q) := le_min hcap hbase
    _ ≤ min (volume region).toReal
        ((4 * Real.sqrt inflation * L) / Real.sqrt t + Y / t) :=
      min_le_min_left _ hsum
    _ ≤ max (volume region).toReal (4 * Real.sqrt inflation * L + Y) *
        min 1 (t ^ (-1 / 2 : ℝ)) :=
      inverseStrength_to_frontier hY htpos

end Causalean.Stat
