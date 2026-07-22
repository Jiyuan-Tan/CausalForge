/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Coupling.ProductLossMonotoneCoupling.FrechetHoeffding

/-!
# Sharp Fréchet-Hoeffding attainability for monotone quantile couplings

This file proves that the quantile couplings attain the Fréchet-Hoeffding
bounds on the joint distribution function. The comonotone coupling realizes the
upper envelope, and the countermonotone coupling realizes the lower envelope.

The resulting pointwise comparisons are the cdf-order inputs used by the
product-expectation optimality theorem.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Set
open Causalean.Stat

variable {π : Measure (ℝ × ℝ)} {μ ν : Measure ℝ}

/-- The comonotone coupling **attains** the Fréchet–Hoeffding upper bound:
`H = min (cdf μ x) (cdf ν y)`. For `U ~ Unif(0,1)`,
`{u | quantile μ u ≤ x ∧ quantile ν u ≤ y} = {u | u ≤ cdf μ x} ∩ {u | u ≤ cdf ν y}
 = {u | u ≤ min (cdf μ x) (cdf ν y)}`, of uniform mass `min (cdf μ x) (cdf ν y)`. -/
theorem jointCdf_comonotoneCoupling (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (x y : ℝ) :
    jointCdf (comonotoneCoupling μ ν) x y = min (cdf μ x) (cdf ν y) := by
  let m : ℝ := min (cdf μ x) (cdf ν y)
  have hm0 : 0 ≤ m := le_min (cdf_nonneg μ x) (cdf_nonneg ν y)
  have hm1 : m ≤ 1 := by
    exact (min_le_left (cdf μ x) (cdf ν y)).trans (cdf_le_one μ x)
  have hpair_ae : AEMeasurable (fun u : ℝ => (quantile μ u, quantile ν u)) unifOI :=
    (aemeasurable_quantile_unifOI μ).prodMk (aemeasurable_quantile_unifOI ν)
  have hquad_meas : MeasurableSet (Iic x ×ˢ Iic y : Set (ℝ × ℝ)) :=
    measurableSet_Iic.prod measurableSet_Iic
  have hpre_null : NullMeasurableSet
      ((fun u : ℝ => (quantile μ u, quantile ν u)) ⁻¹'
        (Iic x ×ˢ Iic y : Set (ℝ × ℝ))) unifOI :=
    hpair_ae.nullMeasurableSet_preimage hquad_meas
  unfold jointCdf comonotoneCoupling
  rw [Measure.map_apply_of_aemeasurable hpair_ae hquad_meas]
  rw [unifOI, Measure.restrict_apply₀]
  · have hset : ((fun u : ℝ => (quantile μ u, quantile ν u)) ⁻¹'
        (Iic x ×ˢ Iic y : Set (ℝ × ℝ))) ∩ Ioo (0 : ℝ) 1 =
        Ioc (0 : ℝ) m ∩ Ioo (0 : ℝ) 1 := by
      ext u
      constructor
      · intro hu
        rcases hu with ⟨huq, hu01⟩
        have hu0 : 0 < u := hu01.1
        have hu1 : u < 1 := hu01.2
        have hux : quantile μ u ≤ x := by simpa using huq.1
        have huy : quantile ν u ≤ y := by simpa using huq.2
        have hucdfx : u ≤ cdf μ x := (quantile_le_iff (μ := μ) hu0 hu1).1 hux
        have hucdfy : u ≤ cdf ν y := (quantile_le_iff (μ := ν) hu0 hu1).1 huy
        exact ⟨⟨hu0, le_min hucdfx hucdfy⟩, hu01⟩
      · intro hu
        rcases hu with ⟨hu0m, hu01⟩
        have hu0 : 0 < u := hu0m.1
        have hum : u ≤ m := hu0m.2
        have hu1 : u < 1 := hu01.2
        have hux : quantile μ u ≤ x :=
          (quantile_le_iff (μ := μ) hu0 hu1).2 (hum.trans (min_le_left _ _))
        have huy : quantile ν u ≤ y :=
          (quantile_le_iff (μ := ν) hu0 hu1).2 (hum.trans (min_le_right _ _))
        exact ⟨⟨hux, huy⟩, ⟨hu0, hu1⟩⟩
    rw [hset]
    have hvol : volume (Ioc (0 : ℝ) m ∩ Ioo (0 : ℝ) 1) = volume (Ioc (0 : ℝ) m) := by
      apply le_antisymm
      · exact measure_mono inter_subset_left
      · calc
          volume (Ioc (0 : ℝ) m) ≤
              volume ((Ioc (0 : ℝ) m ∩ Ioo (0 : ℝ) 1) ∪ ({1} : Set ℝ)) := by
            apply measure_mono
            intro u hu
            by_cases hu1eq : u = 1
            · right
              simp [hu1eq]
            · left
              have hu1lt : u < 1 := lt_of_le_of_ne (hu.2.trans hm1) hu1eq
              exact ⟨hu, ⟨hu.1, hu1lt⟩⟩
          _ ≤ volume (Ioc (0 : ℝ) m ∩ Ioo (0 : ℝ) 1) + volume ({1} : Set ℝ) :=
            measure_union_le _ _
          _ = volume (Ioc (0 : ℝ) m ∩ Ioo (0 : ℝ) 1) := by simp
    rw [hvol, Real.volume_Ioc]
    simp only [sub_zero]
    rw [ENNReal.toReal_ofReal hm0]
  · simpa [unifOI] using hpre_null

/-- The countermonotone coupling **attains** the Fréchet–Hoeffding lower bound:
`H = max (cdf μ x + cdf ν y - 1) 0`. For `U ~ Unif(0,1)`,
`{u | quantile μ u ≤ x ∧ quantile ν (1-u) ≤ y}
 = {u | u ≤ cdf μ x} ∩ {u | 1 - cdf ν y ≤ u}`, of uniform mass
`max (cdf μ x - (1 - cdf ν y)) 0 = max (cdf μ x + cdf ν y - 1) 0`. -/
theorem jointCdf_countermonotoneCoupling (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (x y : ℝ) :
    jointCdf (countermonotoneCoupling μ ν) x y = max (cdf μ x + cdf ν y - 1) 0 := by
  let a : ℝ := cdf μ x
  let b : ℝ := cdf ν y
  let l : ℝ := 1 - b
  have ha1 : a ≤ 1 := cdf_le_one μ x
  have hb0 : 0 ≤ b := cdf_nonneg ν y
  have hb1 : b ≤ 1 := cdf_le_one ν y
  have hl0 : 0 ≤ l := sub_nonneg.mpr hb1
  have hone_sub_meas : Measurable (fun u : ℝ => 1 - u) := by fun_prop
  have hquant_reflect_ae : AEMeasurable (fun u : ℝ => quantile ν (1 - u)) unifOI :=
    by
      have hq : AEMeasurable (quantile ν) (unifOI.map (fun u : ℝ => 1 - u)) := by
        rw [map_one_sub_unifOI]
        exact aemeasurable_quantile_unifOI ν
      exact hq.comp_measurable hone_sub_meas
  have hpair_ae :
      AEMeasurable (fun u : ℝ => (quantile μ u, quantile ν (1 - u))) unifOI :=
    (aemeasurable_quantile_unifOI μ).prodMk hquant_reflect_ae
  have hquad_meas : MeasurableSet (Iic x ×ˢ Iic y : Set (ℝ × ℝ)) :=
    measurableSet_Iic.prod measurableSet_Iic
  have hpre_null : NullMeasurableSet
      ((fun u : ℝ => (quantile μ u, quantile ν (1 - u))) ⁻¹'
        (Iic x ×ˢ Iic y : Set (ℝ × ℝ))) unifOI :=
    hpair_ae.nullMeasurableSet_preimage hquad_meas
  unfold jointCdf countermonotoneCoupling
  rw [Measure.map_apply_of_aemeasurable hpair_ae hquad_meas]
  rw [unifOI, Measure.restrict_apply₀]
  · have hset : ((fun u : ℝ => (quantile μ u, quantile ν (1 - u))) ⁻¹'
        (Iic x ×ˢ Iic y : Set (ℝ × ℝ))) ∩ Ioo (0 : ℝ) 1 =
        Icc l a ∩ Ioo (0 : ℝ) 1 := by
      ext u
      constructor
      · intro hu
        rcases hu with ⟨huq, hu01⟩
        have hu0 : 0 < u := hu01.1
        have hu1 : u < 1 := hu01.2
        have h1u0 : 0 < 1 - u := sub_pos.mpr hu1
        have h1u1 : 1 - u < 1 := by linarith
        have hux : quantile μ u ≤ x := by simpa using huq.1
        have huy : quantile ν (1 - u) ≤ y := by simpa using huq.2
        have hua : u ≤ a := by
          dsimp [a]
          exact (quantile_le_iff (μ := μ) hu0 hu1).1 hux
        have h1ub : 1 - u ≤ b := by
          dsimp [b]
          exact (quantile_le_iff (μ := ν) h1u0 h1u1).1 huy
        have hlu : l ≤ u := by
          dsimp [l]
          linarith
        exact ⟨⟨hlu, hua⟩, hu01⟩
      · intro hu
        rcases hu with ⟨hulua, hu01⟩
        have hu0 : 0 < u := hu01.1
        have hu1 : u < 1 := hu01.2
        have h1u0 : 0 < 1 - u := sub_pos.mpr hu1
        have h1u1 : 1 - u < 1 := by linarith
        have hua : u ≤ cdf μ x := by simpa [a] using hulua.2
        have h1ub : 1 - u ≤ cdf ν y := by
          have hle : 1 - cdf ν y ≤ u := by simpa [l, b] using hulua.1
          linarith
        have hux : quantile μ u ≤ x := (quantile_le_iff (μ := μ) hu0 hu1).2 hua
        have huy : quantile ν (1 - u) ≤ y :=
          (quantile_le_iff (μ := ν) h1u0 h1u1).2 h1ub
        exact ⟨⟨hux, huy⟩, hu01⟩
    rw [hset]
    have hvol : volume (Icc l a ∩ Ioo (0 : ℝ) 1) = volume (Icc l a) := by
      have hpoints : volume ({0} ∪ {1} : Set ℝ) = 0 := by
        apply le_antisymm
        · calc
            volume ({0} ∪ {1} : Set ℝ) ≤ volume ({0} : Set ℝ) + volume ({1} : Set ℝ) :=
              measure_union_le _ _
            _ = 0 := by simp
        · exact zero_le _
      apply le_antisymm
      · exact measure_mono inter_subset_left
      · calc
          volume (Icc l a) ≤
              volume ((Icc l a ∩ Ioo (0 : ℝ) 1) ∪ ({0} ∪ {1} : Set ℝ)) := by
            apply measure_mono
            intro u hu
            by_cases hu0eq : u = 0
            · right
              left
              simp [hu0eq]
            · by_cases hu1eq : u = 1
              · right
                right
                simp [hu1eq]
              · left
                have hu0lt : 0 < u := lt_of_le_of_ne (hl0.trans hu.1) (Ne.symm hu0eq)
                have hu1lt : u < 1 := lt_of_le_of_ne (hu.2.trans ha1) hu1eq
                exact ⟨hu, ⟨hu0lt, hu1lt⟩⟩
          _ ≤ volume (Icc l a ∩ Ioo (0 : ℝ) 1) + volume ({0} ∪ {1} : Set ℝ) :=
            measure_union_le _ _
          _ = volume (Icc l a ∩ Ioo (0 : ℝ) 1) := by rw [hpoints, add_zero]
    rw [hvol, Real.volume_Icc]
    have hcalc : a - l = cdf μ x + cdf ν y - 1 := by
      dsimp [a, b, l]
      ring
    rw [hcalc]
    simp [ENNReal.toReal_ofReal']
  · simpa [unifOI] using hpre_null

/-- Corollary: for any coupling `π` of `(μ, ν)`, its joint cdf is dominated
pointwise by the comonotone joint cdf. This is the pointwise inequality that the
covariance identity turns into optimality of `E[XY]`. -/
theorem jointCdf_le_comonotone (h : IsCoupling π μ ν)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (x y : ℝ) :
    jointCdf π x y ≤ jointCdf (comonotoneCoupling μ ν) x y := by
  rw [jointCdf_comonotoneCoupling]; exact frechet_hoeffding_upper h x y

/-- Corollary: the countermonotone joint cdf is dominated pointwise by any other
coupling's joint cdf. -/
theorem countermonotone_le_jointCdf (h : IsCoupling π μ ν)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (x y : ℝ) :
    jointCdf (countermonotoneCoupling μ ν) x y ≤ jointCdf π x y := by
  rw [jointCdf_countermonotoneCoupling]; exact frechet_hoeffding_lower h x y

end Causalean.Stat
