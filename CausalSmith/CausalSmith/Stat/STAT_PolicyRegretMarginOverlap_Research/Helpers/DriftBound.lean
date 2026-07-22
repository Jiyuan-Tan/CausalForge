/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Helpers.FeasibleERM

/-! Provides clipped-region localization and drift-bound helpers. -/

namespace CausalSmith.Stat.PolicyRegretMarginOverlap

open MeasureTheory
open scoped BigOperators

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

-- @node: lem:clipped-region-localization
/-- `lem:clipped-region-localization`. For `γ>0`, the disagreement mass inside
the clipped region is controlled: `P_X(D_π ∩ {p_P≤q}) ≤ C u^α q^{1/γ}+r/u`. -/
lemma clipped_region_localization (P : ObservedLaw 𝒳)
    (policySet : Set (Policy 𝒳)) (Co co α γ u0 : ℝ)
    (hod : OverlapDecay P u0 Co co α γ) (hze : ZeroEffectRegular P policySet)
    (hbdd : BoundedOutcome P) (hwf : WellFormedLaw P)
    (hπmeas : ∀ π ∈ policySet, Measurable π) (hγ : 0 < γ) :
    0 < max Co 1 ∧ ∀ π ∈ policySet, ∀ u q : ℝ,
      0 < u → u ≤ u0 → 0 < q → q ≤ co * u ^ γ →
        P.PX.real (disagreementSet π (lawOptimalPolicy P) ∩ {x | overlap P x ≤ q})
          ≤ max Co 1 * u ^ α * q ^ (1 / γ) + lawRegret P π / u
    := by
  refine ⟨lt_of_lt_of_le zero_lt_one (le_max_right Co 1), ?_⟩
  intro π hπmem u q hu hu_le hq hqle
  letI : IsProbabilityMeasure P.PX := hwf.2.1
  let D : Set 𝒳 := disagreementSet π (lawOptimalPolicy P)
  let T : Set 𝒳 := D ∩ {x | overlap P x ≤ q}
  let ZD : Set 𝒳 := {x | P.contrast x = 0 ∧ π x ≠ lawOptimalPolicy P x}
  let S : Set 𝒳 := {x | overlap P x ≤ q ∧ 0 < |P.contrast x| ∧ |P.contrast x| ≤ u}
  let B : Set 𝒳 := D ∩ {x | u < |P.contrast x|}
  have hZD_zero : P.PX.real ZD = 0 := by
    rcases hze with hzero | hzeroD
    · have hle : P.PX.real ZD ≤ P.PX.real {x | P.contrast x = 0} := by
        exact measureReal_mono (μ := P.PX) (by
          intro x hx
          exact hx.1) (measure_ne_top P.PX {x | P.contrast x = 0})
      have hle0 : P.PX.real ZD ≤ 0 := by
        simpa [hzero] using hle
      exact le_antisymm hle0 measureReal_nonneg
    · simpa [ZD] using hzeroD π hπmem
  have hsmall :
      P.PX.real S ≤ max Co 1 * u ^ α * q ^ (1 / γ) := by
    have hod' := hod u q hu hu_le hq hqle
    have hfac_nonneg : 0 ≤ u ^ α * q ^ (1 / γ) :=
      mul_nonneg (Real.rpow_nonneg hu.le _) (Real.rpow_nonneg hq.le _)
    have hcoef : Co * (u ^ α * q ^ (1 / γ)) ≤ max Co 1 * (u ^ α * q ^ (1 / γ)) :=
      mul_le_mul_of_nonneg_right (le_max_left Co 1) hfac_nonneg
    calc
      P.PX.real S ≤ Co * u ^ α * q ^ (1 / γ) := by
        simpa [S, hγ.ne'] using hod'
      _ = Co * (u ^ α * q ^ (1 / γ)) := by ring
      _ ≤ max Co 1 * (u ^ α * q ^ (1 / γ)) := hcoef
      _ = max Co 1 * u ^ α * q ^ (1 / γ) := by ring
  have hbig :
      P.PX.real B ≤ lawRegret P π / u := by
    simpa [B, D] using
      regret_disagreement_large_contrast_le P π hwf hbdd (hπmeas π hπmem) hu
  have hsubset : T ⊆ ZD ∪ S ∪ B := by
    intro x hx
    rcases hx with ⟨hxD, hxOverlap⟩
    by_cases hτzero : P.contrast x = 0
    · left
      left
      exact ⟨hτzero, by simpa [D, disagreementSet] using hxD⟩
    · by_cases hsmallContrast : |P.contrast x| ≤ u
      · left
        right
        exact ⟨hxOverlap, abs_pos.mpr hτzero, hsmallContrast⟩
      · right
        exact ⟨hxD, lt_of_not_ge hsmallContrast⟩
  have htarget_decomp :
      P.PX.real T ≤ P.PX.real S + P.PX.real B := by
    calc
      P.PX.real T ≤ P.PX.real (ZD ∪ S ∪ B) :=
        measureReal_mono (μ := P.PX) hsubset (measure_ne_top P.PX (ZD ∪ S ∪ B))
      _ ≤ P.PX.real (ZD ∪ S) + P.PX.real B := measureReal_union_le _ _
      _ ≤ (P.PX.real ZD + P.PX.real S) + P.PX.real B := by
        have h := measureReal_union_le (μ := P.PX) ZD S
        linarith
      _ = P.PX.real S + P.PX.real B := by
        rw [hZD_zero]
        ring
  calc
    P.PX.real (disagreementSet π (lawOptimalPolicy P) ∩ {x | overlap P x ≤ q})
        = P.PX.real T := rfl
    _ ≤ P.PX.real S + P.PX.real B := htarget_decomp
    _ ≤ max Co 1 * u ^ α * q ^ (1 / γ) + lawRegret P π / u :=
        add_le_add hsmall hbig

-- @node: l2_abs_product_integral_le
private lemma l2_abs_product_integral_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f g : Ω → ℝ} {rf rg : ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hsqf : ∫ x, f x ^ 2 ∂μ ≤ rf ^ 2)
    (hsqg : ∫ x, g x ^ 2 ∂μ ≤ rg ^ 2)
    (hrf : 0 ≤ rf) (hrg : 0 ≤ rg) :
    ∫ x, |f x| * |g x| ∂μ ≤ rf * rg := by
  have hf_nonneg : ∀ᵐ x ∂μ, 0 ≤ |f x| := by
    filter_upwards with x
    exact abs_nonneg _
  have hg_nonneg : ∀ᵐ x ∂μ, 0 ≤ |g x| := by
    filter_upwards with x
    exact abs_nonneg _
  have hf_abs2 : MemLp (fun x => |f x|) (ENNReal.ofReal 2) μ := by
    simpa using (hf.norm : MemLp (fun x => ‖f x‖) 2 μ)
  have hg_abs2 : MemLp (fun x => |g x|) (ENNReal.ofReal 2) μ := by
    simpa using (hg.norm : MemLp (fun x => ‖g x‖) 2 μ)
  have hholder :
      ∫ x, |f x| * |g x| ∂μ ≤
        (∫ x, |f x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫ x, |g x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
    integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      hf_nonneg hg_nonneg hf_abs2 hg_abs2
  have hf_sq_eq : (∫ x, |f x| ^ (2 : ℝ) ∂μ) = ∫ x, f x ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Real.rpow_two]
    exact sq_abs (f x)
  have hg_sq_eq : (∫ x, |g x| ^ (2 : ℝ) ∂μ) = ∫ x, g x ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Real.rpow_two]
    exact sq_abs (g x)
  have hf_sqrt_le : (∫ x, |f x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤ rf := by
    calc
      (∫ x, |f x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
          = Real.sqrt (∫ x, |f x| ^ (2 : ℝ) ∂μ) := by
            rw [Real.sqrt_eq_rpow]
      _ ≤ Real.sqrt (rf ^ 2) := Real.sqrt_le_sqrt (by simpa [hf_sq_eq] using hsqf)
      _ = rf := Real.sqrt_sq hrf
  have hg_sqrt_le : (∫ x, |g x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤ rg := by
    calc
      (∫ x, |g x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
          = Real.sqrt (∫ x, |g x| ^ (2 : ℝ) ∂μ) := by
            rw [Real.sqrt_eq_rpow]
      _ ≤ Real.sqrt (rg ^ 2) := Real.sqrt_le_sqrt (by simpa [hg_sq_eq] using hsqg)
      _ = rg := Real.sqrt_sq hrg
  calc
    ∫ x, |f x| * |g x| ∂μ
        ≤ (∫ x, |f x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫ x, |g x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hholder
    _ ≤ rf * rg :=
        mul_le_mul hf_sqrt_le hg_sqrt_le
          (Real.rpow_nonneg (by positivity) _) hrf

-- @node: l2_set_abs_integral_le
private lemma l2_set_abs_integral_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {S : Set Ω} (hS : MeasurableSet S)
    {f : Ω → ℝ} {r : ℝ}
    (hf : MemLp f 2 μ) (hsq : ∫ x, f x ^ 2 ∂μ ≤ r ^ 2) (hr : 0 ≤ r) :
    ∫ x, S.indicator (fun _ => (1 : ℝ)) x * |f x| ∂μ ≤
      Real.sqrt (μ.real S) * r := by
  let ind : Ω → ℝ := S.indicator (fun _ => (1 : ℝ))
  have hind_meas : AEStronglyMeasurable ind μ :=
    (measurable_const.indicator hS).aestronglyMeasurable
  have hind_int_sq : Integrable (fun x => ind x ^ 2) μ := by
    refine Integrable.of_bound (hind_meas.pow 2) 1 ?_
    filter_upwards with x
    by_cases hx : x ∈ S <;> simp [ind, hx]
  have hind_L2 : MemLp ind (ENNReal.ofReal 2) μ := by
    simpa using (memLp_two_iff_integrable_sq hind_meas).2 hind_int_sq
  have hf_abs2 : MemLp (fun x => |f x|) (ENNReal.ofReal 2) μ := by
    simpa using (hf.norm : MemLp (fun x => ‖f x‖) 2 μ)
  have hind_nonneg : ∀ᵐ x ∂μ, 0 ≤ ind x := by
    filter_upwards with x
    by_cases hx : x ∈ S <;> simp [ind, hx]
  have hf_nonneg : ∀ᵐ x ∂μ, 0 ≤ |f x| := by
    filter_upwards with x
    exact abs_nonneg _
  have hholder :
      ∫ x, ind x * |f x| ∂μ ≤
        (∫ x, ind x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫ x, |f x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
    integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      hind_nonneg hf_nonneg hind_L2 hf_abs2
  have hind_sq_eq : (∫ x, ind x ^ (2 : ℝ) ∂μ) = μ.real S := by
    calc
      ∫ x, ind x ^ (2 : ℝ) ∂μ = ∫ x, ind x ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ S <;> simp [ind, hx]
      _ = μ.real S := by
        simpa [ind] using integral_indicator_one (μ := μ) hS
  have hf_sq_eq : (∫ x, |f x| ^ (2 : ℝ) ∂μ) = ∫ x, f x ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Real.rpow_two]
    exact sq_abs (f x)
  have hf_sqrt_le : (∫ x, |f x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤ r := by
    calc
      (∫ x, |f x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
          = Real.sqrt (∫ x, |f x| ^ (2 : ℝ) ∂μ) := by
            rw [Real.sqrt_eq_rpow]
      _ ≤ Real.sqrt (r ^ 2) := Real.sqrt_le_sqrt (by simpa [hf_sq_eq] using hsq)
      _ = r := Real.sqrt_sq hr
  calc
    ∫ x, S.indicator (fun _ => (1 : ℝ)) x * |f x| ∂μ
        = ∫ x, ind x * |f x| ∂μ := rfl
    _ ≤ (∫ x, ind x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫ x, |f x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hholder
    _ = Real.sqrt (μ.real S) * (∫ x, |f x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
          rw [hind_sq_eq, Real.sqrt_eq_rpow]
    _ ≤ Real.sqrt (μ.real S) * r :=
        mul_le_mul_of_nonneg_left hf_sqrt_le (Real.sqrt_nonneg _)

-- @node: clippedPropensity_lipschitz
private lemma clippedPropensity_lipschitz (q y z : ℝ) :
    |min (1 - q) (max q y) - min (1 - q) (max q z)| ≤ |y - z| := by
  have hmax : |max q y - max q z| ≤ |y - z| := by
    simpa [abs_sub_comm, max_comm] using (abs_max_sub_max_le_abs y z q)
  have hmin : |min (1 - q) (max q y) - min (1 - q) (max q z)| ≤
      |max q y - max q z| := by
    simpa [min_comm] using (abs_inf_sub_inf_le_abs (max q y) (max q z) (1 - q))
  exact le_trans hmin hmax

-- @node: clippedPropensity_error_le_error_plus_overlap_indicator
private lemma clippedPropensity_error_le_error_plus_overlap_indicator
    (P : ObservedLaw 𝒳) (q : ℝ) (eHat : 𝒳 → ℝ) (x : 𝒳)
    (hwf : WellFormedLaw P) (hq : 0 < q) (hq_half : q ≤ 1 / 2) :
    |clippedPropensity q eHat x - P.propensity x| ≤
      |eHat x - P.propensity x| +
        q * ({x | overlap P x ≤ q}.indicator (fun _ : 𝒳 => (1 : ℝ)) x) := by
  classical
  have he01 : P.propensity x ∈ Set.Icc (0 : ℝ) 1 :=
    hwf.2.2.2.2.2.2.2.2.1 x
  have hlip : |clippedPropensity q eHat x - clippedPropensity q P.propensity x| ≤
      |eHat x - P.propensity x| := by
    simpa [clippedPropensity] using
      clippedPropensity_lipschitz q (eHat x) (P.propensity x)
  have hself_le : |clippedPropensity q P.propensity x - P.propensity x| ≤
      q * ({x | overlap P x ≤ q}.indicator (fun _ : 𝒳 => (1 : ℝ)) x) := by
    by_cases hxlow : overlap P x ≤ q
    · have hdist : |clippedPropensity q P.propensity x - P.propensity x| ≤ q := by
        unfold clippedPropensity
        by_cases he_low : P.propensity x < q
        · have hmax : max q (P.propensity x) = q := max_eq_left he_low.le
          have hmin : min (1 - q) q = q := by
            apply min_eq_right
            linarith
          rw [hmax, hmin]
          rw [abs_of_nonneg]
          · linarith [he01.1]
          · linarith
        · have hqe : q ≤ P.propensity x := le_of_not_gt he_low
          by_cases he_high : 1 - q < P.propensity x
          · have hmax : max q (P.propensity x) = P.propensity x := max_eq_right hqe
            have hmin : min (1 - q) (P.propensity x) = 1 - q :=
              min_eq_left he_high.le
            rw [hmax, hmin]
            rw [abs_of_nonpos]
            · linarith [he01.2]
            · linarith
          · have heq : P.propensity x ≤ 1 - q := le_of_not_gt he_high
            have hmax : max q (P.propensity x) = P.propensity x := max_eq_right hqe
            have hmin : min (1 - q) (P.propensity x) = P.propensity x :=
              min_eq_right heq
            rw [hmax, hmin]
            simp [hq.le]
      simpa [hxlow] using hdist
    · have hgt : q < overlap P x := lt_of_not_ge hxlow
      have hqe : q ≤ P.propensity x := by
        have hminle : overlap P x ≤ P.propensity x := by
          unfold overlap
          exact min_le_left _ _
        linarith
      have heq : P.propensity x ≤ 1 - q := by
        have hminle : overlap P x ≤ 1 - P.propensity x := by
          unfold overlap
          exact min_le_right _ _
        linarith
      have hmax : max q (P.propensity x) = P.propensity x := max_eq_right hqe
      have hmin : min (1 - q) (P.propensity x) = P.propensity x := min_eq_right heq
      have hzero : |clippedPropensity q P.propensity x - P.propensity x| = 0 := by
        simp [clippedPropensity, hmax, hmin]
      simp [hxlow, hzero]
  calc
    |clippedPropensity q eHat x - P.propensity x|
        = |(clippedPropensity q eHat x - clippedPropensity q P.propensity x) +
            (clippedPropensity q P.propensity x - P.propensity x)| := by
          ring_nf
    _ ≤ |clippedPropensity q eHat x - clippedPropensity q P.propensity x| +
            |clippedPropensity q P.propensity x - P.propensity x| := abs_add_le _ _
    _ ≤ |eHat x - P.propensity x| +
          q * ({x | overlap P x ≤ q}.indicator (fun _ : 𝒳 => (1 : ℝ)) x) :=
        add_le_add hlip hself_le

-- @node: policy_overlap_indicator_mul_le_inter_indicator
private lemma policy_overlap_indicator_mul_le_inter_indicator
    (π πstar : Policy 𝒳) (S : Set 𝒳) (x : 𝒳) :
    |boolIndicator (π x) - boolIndicator (πstar x)| *
        (S.indicator (fun _ : 𝒳 => (1 : ℝ)) x)
      ≤ ((disagreementSet π πstar ∩ S).indicator (fun _ : 𝒳 => (1 : ℝ)) x) := by
  classical
  have hdiff_le : |boolIndicator (π x) - boolIndicator (πstar x)| ≤ (1 : ℝ) := by
    cases π x <;> cases πstar x <;> simp [boolIndicator]
  have hdiff_zero : x ∉ disagreementSet π πstar →
      |boolIndicator (π x) - boolIndicator (πstar x)| = 0 := by
    intro hxD
    unfold disagreementSet at hxD
    have heq : π x = πstar x := not_not.mp hxD
    simp [heq]
  by_cases hxD : x ∈ disagreementSet π πstar
  · by_cases hxS : x ∈ S
    · simp [hxD, hxS]
      exact hdiff_le
    · simp [hxS]
  · have hz := hdiff_zero hxD
    by_cases hxS : x ∈ S <;> simp [hz, hxD, hxS]

-- @node: policy_clipBias_abs_pointwise_le
private lemma policy_clipBias_abs_pointwise_le (P : ObservedLaw 𝒳) (q : ℝ)
    (muHat0 muHat1 eHat : 𝒳 → ℝ) (π : Policy 𝒳) (x : 𝒳)
    (hwf : WellFormedLaw P) (hq : 0 < q) (hq_half : q ≤ 1 / 2) :
    |(boolIndicator (π x) - boolIndicator (lawOptimalPolicy P x)) *
        clipBias P q muHat0 muHat1 eHat x| ≤
      (|eHat x - P.propensity x| * |muHat1 x - P.mu1 x| +
          |eHat x - P.propensity x| * |muHat0 x - P.mu0 x|) / q +
        ((disagreementSet π (lawOptimalPolicy P) ∩ {x | overlap P x ≤ q}).indicator
          (fun _ : 𝒳 => (1 : ℝ)) x) * |muHat1 x - P.mu1 x| +
        ((disagreementSet π (lawOptimalPolicy P) ∩ {x | overlap P x ≤ q}).indicator
          (fun _ : 𝒳 => (1 : ℝ)) x) * |muHat0 x - P.mu0 x| := by
  classical
  have hq1 : q < 1 := by linarith
  let cp := clippedPropensity q eHat x
  let e := P.propensity x
  let de := |eHat x - e|
  let indO := ({x | overlap P x ≤ q}.indicator (fun _ : 𝒳 => (1 : ℝ)) x)
  let indT := ((disagreementSet π (lawOptimalPolicy P) ∩ {x | overlap P x ≤ q}).indicator
    (fun _ : 𝒳 => (1 : ℝ)) x)
  let d1 := |muHat1 x - P.mu1 x|
  let d0 := |muHat0 x - P.mu0 x|
  let ph := |boolIndicator (π x) - boolIndicator (lawOptimalPolicy P x)|
  have hcp_pos : 0 < cp := clippedPropensity_pos q eHat x hq hq1
  have hden_pos : 0 < 1 - cp := one_sub_clippedPropensity_pos q eHat x hq
  have hcp_inv : cp⁻¹ ≤ q⁻¹ := by
    have hcp_lower : q ≤ cp := by
      have hmin := clippedPropensity_lower_min q eHat x
      have hmin_eq : min q (1 - q) = q := by
        apply min_eq_left
        linarith
      simpa [cp, hmin_eq] using hmin
    rw [inv_le_inv₀ hcp_pos hq]
    exact hcp_lower
  have hden_inv : (1 - cp)⁻¹ ≤ q⁻¹ := by
    have hden_lower : q ≤ 1 - cp := by
      have hle := clippedPropensity_le_one_sub q eHat x
      linarith [show cp = clippedPropensity q eHat x from rfl]
    rw [inv_le_inv₀ hden_pos hq]
    exact hden_lower
  have hcliperr : |cp - e| ≤ de + q * indO := by
    simpa [cp, e, de, indO] using
      clippedPropensity_error_le_error_plus_overlap_indicator P q eHat x hwf hq hq_half
  have hfrac1 : |(muHat1 x - P.mu1 x) / cp| ≤ d1 / q := by
    calc
      |(muHat1 x - P.mu1 x) / cp| = d1 * cp⁻¹ := by
        rw [abs_div, abs_of_pos hcp_pos, div_eq_mul_inv]
      _ ≤ d1 * q⁻¹ := by
            exact mul_le_mul_of_nonneg_left hcp_inv (abs_nonneg _)
      _ = d1 / q := by rw [div_eq_mul_inv]
  have hfrac0 : |(muHat0 x - P.mu0 x) / (1 - cp)| ≤ d0 / q := by
    calc
      |(muHat0 x - P.mu0 x) / (1 - cp)| = d0 * (1 - cp)⁻¹ := by
        rw [abs_div, abs_of_pos hden_pos, div_eq_mul_inv]
      _ ≤ d0 * q⁻¹ := by
            exact mul_le_mul_of_nonneg_left hden_inv (abs_nonneg _)
      _ = d0 / q := by rw [div_eq_mul_inv]
  have hnon_indO : 0 ≤ indO := by
    by_cases hx : overlap P x ≤ q <;> simp [indO, hx]
  have hcliperr_rhs_nonneg : 0 ≤ de + q * indO :=
    add_nonneg (abs_nonneg _) (mul_nonneg hq.le hnon_indO)
  have hclipBias_abs : |clipBias P q muHat0 muHat1 eHat x| ≤
      (de + q * indO) * (d1 / q + d0 / q) := by
    change
      |(cp - e) * ((muHat1 x - P.mu1 x) / cp +
          (muHat0 x - P.mu0 x) / (1 - cp))| ≤
        (de + q * indO) * (d1 / q + d0 / q)
    calc
      |(cp - e) * ((muHat1 x - P.mu1 x) / cp +
          (muHat0 x - P.mu0 x) / (1 - cp))|
          = |cp - e| * |(muHat1 x - P.mu1 x) / cp +
              (muHat0 x - P.mu0 x) / (1 - cp)| := abs_mul _ _
      _ ≤ |cp - e| * (|(muHat1 x - P.mu1 x) / cp| +
              |(muHat0 x - P.mu0 x) / (1 - cp)|) := by
            exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
      _ ≤ (de + q * indO) * (d1 / q + d0 / q) := by
            exact mul_le_mul hcliperr (add_le_add hfrac1 hfrac0)
              (add_nonneg (abs_nonneg _) (abs_nonneg _))
              hcliperr_rhs_nonneg
  have hph_le_one : ph ≤ 1 := by
    dsimp [ph]
    cases π x <;> cases lawOptimalPolicy P x <;> simp [boolIndicator]
  have hph_ind : ph * indO ≤ indT := by
    simpa [ph, indO, indT] using
      policy_overlap_indicator_mul_le_inter_indicator π (lawOptimalPolicy P)
        {x | overlap P x ≤ q} x
  have hnon_de : 0 ≤ de := abs_nonneg _
  have hnon_d1 : 0 ≤ d1 := abs_nonneg _
  have hnon_d0 : 0 ≤ d0 := abs_nonneg _
  calc
    |(boolIndicator (π x) - boolIndicator (lawOptimalPolicy P x)) *
        clipBias P q muHat0 muHat1 eHat x|
        = ph * |clipBias P q muHat0 muHat1 eHat x| := by
          rw [abs_mul]
    _ ≤ ph * ((de + q * indO) * (d1 / q + d0 / q)) :=
        mul_le_mul_of_nonneg_left hclipBias_abs (abs_nonneg _)
    _ = ph * (de * d1 / q + de * d0 / q + indO * d1 + indO * d0) := by
        field_simp [hq.ne']
        ring
    _ ≤ de * d1 / q + de * d0 / q + indT * d1 + indT * d0 := by
        have h1 : ph * (de * d1 / q) ≤ de * d1 / q :=
          mul_le_of_le_one_left (div_nonneg (mul_nonneg hnon_de hnon_d1) hq.le)
            hph_le_one
        have h2 : ph * (de * d0 / q) ≤ de * d0 / q :=
          mul_le_of_le_one_left (div_nonneg (mul_nonneg hnon_de hnon_d0) hq.le)
            hph_le_one
        have h3 : ph * (indO * d1) ≤ indT * d1 := by
          calc
            ph * (indO * d1) = (ph * indO) * d1 := by ring
            _ ≤ indT * d1 := mul_le_mul_of_nonneg_right hph_ind hnon_d1
        have h4 : ph * (indO * d0) ≤ indT * d0 := by
          calc
            ph * (indO * d0) = (ph * indO) * d0 := by ring
            _ ≤ indT * d0 := mul_le_mul_of_nonneg_right hph_ind hnon_d0
        nlinarith
    _ = (|eHat x - P.propensity x| * |muHat1 x - P.mu1 x| +
          |eHat x - P.propensity x| * |muHat0 x - P.mu0 x|) / q +
        ((disagreementSet π (lawOptimalPolicy P) ∩ {x | overlap P x ≤ q}).indicator
          (fun _ : 𝒳 => (1 : ℝ)) x) * |muHat1 x - P.mu1 x| +
        ((disagreementSet π (lawOptimalPolicy P) ∩ {x | overlap P x ≤ q}).indicator
          (fun _ : 𝒳 => (1 : ℝ)) x) * |muHat0 x - P.mu0 x| := by
        simp [de, d1, d0, indT]
        ring

-- @node: clipBias_drift_l2_mass_bound
private lemma clipBias_drift_l2_mass_bound (P : ObservedLaw 𝒳)
    (q rMu rE : ℝ) (muHat0 muHat1 eHat : 𝒳 → ℝ)
    (hsq0 : ∫ x, (muHat0 x - P.mu0 x) ^ 2 ∂P.PX ≤ rMu ^ 2)
    (hsq1 : ∫ x, (muHat1 x - P.mu1 x) ^ 2 ∂P.PX ≤ rMu ^ 2)
    (hse : ∫ x, (eHat x - P.propensity x) ^ 2 ∂P.PX ≤ rE ^ 2)
    (hμ0L2 : MemLp (fun x => muHat0 x - P.mu0 x) 2 P.PX)
    (hμ1L2 : MemLp (fun x => muHat1 x - P.mu1 x) 2 P.PX)
    (heL2 : MemLp (fun x => eHat x - P.propensity x) 2 P.PX)
    (hrMu_nonneg : 0 ≤ rMu) (hrE_nonneg : 0 ≤ rE)
    (hwf : WellFormedLaw P) (hq : 0 < q) (hq_half : q ≤ 1 / 2)
    (π : Policy 𝒳) (hπ : Measurable π) :
    |driftIntegral P q muHat0 muHat1 eHat π| ≤
      2 * (rMu * rE / q) +
        2 * rMu *
          Real.sqrt
            (P.PX.real (disagreementSet π (lawOptimalPolicy P) ∩ {x | overlap P x ≤ q})) := by
  classical
  rcases hwf with
    ⟨hPprob, hPXprob, hmap, hτmeas, hpropmeas, hmu0meas, hmu1meas,
      hτdef, hprop01, hA, hAY, hCY⟩
  let hwf' : WellFormedLaw P :=
    ⟨hPprob, hPXprob, hmap, hτmeas, hpropmeas, hmu0meas, hmu1meas,
      hτdef, hprop01, hA, hAY, hCY⟩
  letI : IsProbabilityMeasure P.PX := hPXprob
  let T : Set 𝒳 := disagreementSet π (lawOptimalPolicy P) ∩ {x | overlap P x ≤ q}
  let prod1 : 𝒳 → ℝ :=
    fun x => |eHat x - P.propensity x| * |muHat1 x - P.mu1 x|
  let prod0 : 𝒳 → ℝ :=
    fun x => |eHat x - P.propensity x| * |muHat0 x - P.mu0 x|
  let set1 : 𝒳 → ℝ := fun x => T.indicator (fun _ : 𝒳 => (1 : ℝ)) x *
    |muHat1 x - P.mu1 x|
  let set0 : 𝒳 → ℝ := fun x => T.indicator (fun _ : 𝒳 => (1 : ℝ)) x *
    |muHat0 x - P.mu0 x|
  let major : 𝒳 → ℝ := fun x => (prod1 x + prod0 x) / q + set1 x + set0 x
  have hoverlap_meas : Measurable fun x => overlap P x := by
    unfold overlap
    exact hpropmeas.min (measurable_const.sub hpropmeas)
  have hSmeas : MeasurableSet {x | overlap P x ≤ q} :=
    measurableSet_le hoverlap_meas measurable_const
  have hDmeas : MeasurableSet (disagreementSet π (lawOptimalPolicy P)) :=
    measurableSet_disagreementSet P π hτmeas hπ
  have hTmeas : MeasurableSet T := hDmeas.inter hSmeas
  have he_abs : MemLp (fun x => |eHat x - P.propensity x|) 2 P.PX := by
    simpa using heL2.norm
  have hμ1_abs : MemLp (fun x => |muHat1 x - P.mu1 x|) 2 P.PX := by
    simpa using hμ1L2.norm
  have hμ0_abs : MemLp (fun x => |muHat0 x - P.mu0 x|) 2 P.PX := by
    simpa using hμ0L2.norm
  have hprod1_int : Integrable prod1 P.PX := by
    simpa [prod1] using (he_abs.integrable_mul hμ1_abs)
  have hprod0_int : Integrable prod0 P.PX := by
    simpa [prod0] using (he_abs.integrable_mul hμ0_abs)
  have hset1_int : Integrable set1 P.PX := by
    let ind : 𝒳 → ℝ := T.indicator (fun _ : 𝒳 => (1 : ℝ))
    have hind_meas : AEStronglyMeasurable ind P.PX :=
      (measurable_const.indicator hTmeas).aestronglyMeasurable
    have hind_int_sq : Integrable (fun x => ind x ^ 2) P.PX := by
      refine Integrable.of_bound (hind_meas.pow 2) 1 ?_
      filter_upwards with x
      by_cases hx : x ∈ T <;> simp [ind, hx]
    have hind_L2 : MemLp ind 2 P.PX := by
      simpa using (memLp_two_iff_integrable_sq hind_meas).2 hind_int_sq
    have hmul : Integrable (ind * fun x => |muHat1 x - P.mu1 x|) P.PX :=
      hind_L2.integrable_mul hμ1_abs
    simpa [set1, ind] using hmul
  have hset0_int : Integrable set0 P.PX := by
    let ind : 𝒳 → ℝ := T.indicator (fun _ : 𝒳 => (1 : ℝ))
    have hind_meas : AEStronglyMeasurable ind P.PX :=
      (measurable_const.indicator hTmeas).aestronglyMeasurable
    have hind_int_sq : Integrable (fun x => ind x ^ 2) P.PX := by
      refine Integrable.of_bound (hind_meas.pow 2) 1 ?_
      filter_upwards with x
      by_cases hx : x ∈ T <;> simp [ind, hx]
    have hind_L2 : MemLp ind 2 P.PX := by
      simpa using (memLp_two_iff_integrable_sq hind_meas).2 hind_int_sq
    have hmul : Integrable (ind * fun x => |muHat0 x - P.mu0 x|) P.PX :=
      hind_L2.integrable_mul hμ0_abs
    simpa [set0, ind] using hmul
  have hprod_div_int : Integrable (fun x => (prod1 x + prod0 x) / q) P.PX := by
    simpa [div_eq_mul_inv, mul_comm] using (hprod1_int.add hprod0_int).const_mul q⁻¹
  have hmajor_int : Integrable major P.PX := by
    exact (hprod_div_int.add hset1_int).add hset0_int
  have hpoint : ∀ x,
      |(boolIndicator (π x) - boolIndicator (lawOptimalPolicy P x)) *
          clipBias P q muHat0 muHat1 eHat x| ≤ major x := by
    intro x
    simpa [major, prod1, prod0, set1, set0, T] using
      policy_clipBias_abs_pointwise_le P q muHat0 muHat1 eHat π x hwf' hq hq_half
  have hnonneg_abs : 0 ≤ᵐ[P.PX]
      fun x => |(boolIndicator (π x) - boolIndicator (lawOptimalPolicy P x)) *
        clipBias P q muHat0 muHat1 eHat x| := by
    filter_upwards with x
    exact abs_nonneg _
  have hmajor_le :
      ∫ x, |(boolIndicator (π x) - boolIndicator (lawOptimalPolicy P x)) *
          clipBias P q muHat0 muHat1 eHat x| ∂P.PX
        ≤ ∫ x, major x ∂P.PX :=
    integral_mono_of_nonneg hnonneg_abs hmajor_int
      (Filter.Eventually.of_forall hpoint)
  have hprod1_bound : ∫ x, prod1 x ∂P.PX ≤ rE * rMu := by
    simpa [prod1, mul_comm] using
      l2_abs_product_integral_le heL2 hμ1L2 hse hsq1 hrE_nonneg hrMu_nonneg
  have hprod0_bound : ∫ x, prod0 x ∂P.PX ≤ rE * rMu := by
    simpa [prod0, mul_comm] using
      l2_abs_product_integral_le heL2 hμ0L2 hse hsq0 hrE_nonneg hrMu_nonneg
  have hprod_div_bound :
      ∫ x, (prod1 x + prod0 x) / q ∂P.PX ≤ (rE * rMu + rE * rMu) / q := by
    calc
      ∫ x, (prod1 x + prod0 x) / q ∂P.PX =
          (∫ x, prod1 x + prod0 x ∂P.PX) / q := by
            simp [div_eq_mul_inv]
            rw [integral_mul_const]
      _ = (∫ x, prod1 x ∂P.PX + ∫ x, prod0 x ∂P.PX) / q := by
            rw [integral_add hprod1_int hprod0_int]
      _ ≤ (rE * rMu + rE * rMu) / q :=
            div_le_div_of_nonneg_right (add_le_add hprod1_bound hprod0_bound) hq.le
  have hset1_bound :
      ∫ x, set1 x ∂P.PX ≤ Real.sqrt (P.PX.real T) * rMu := by
    simpa [set1] using
      l2_set_abs_integral_le (μ := P.PX) hTmeas hμ1L2 hsq1 hrMu_nonneg
  have hset0_bound :
      ∫ x, set0 x ∂P.PX ≤ Real.sqrt (P.PX.real T) * rMu := by
    simpa [set0] using
      l2_set_abs_integral_le (μ := P.PX) hTmeas hμ0L2 hsq0 hrMu_nonneg
  have hmajor_bound :
      ∫ x, major x ∂P.PX ≤
        (rE * rMu + rE * rMu) / q +
          Real.sqrt (P.PX.real T) * rMu + Real.sqrt (P.PX.real T) * rMu := by
    have hprod_set1_int : Integrable
        (fun x => (prod1 x + prod0 x) / q + set1 x) P.PX :=
      hprod_div_int.add hset1_int
    have hmajor_eq :
        ∫ x, major x ∂P.PX =
          ∫ x, (prod1 x + prod0 x) / q ∂P.PX +
            ∫ x, set1 x ∂P.PX + ∫ x, set0 x ∂P.PX := by
      rw [show (fun x => major x) =
          (fun x => ((prod1 x + prod0 x) / q + set1 x) + set0 x) by
            funext x
            rfl]
      rw [integral_add hprod_set1_int hset0_int]
      rw [integral_add hprod_div_int hset1_int]
    calc
      ∫ x, major x ∂P.PX =
          ∫ x, (prod1 x + prod0 x) / q ∂P.PX +
            ∫ x, set1 x ∂P.PX + ∫ x, set0 x ∂P.PX := hmajor_eq
      _ ≤ (rE * rMu + rE * rMu) / q +
          Real.sqrt (P.PX.real T) * rMu + Real.sqrt (P.PX.real T) * rMu := by
            nlinarith [hprod_div_bound, hset1_bound, hset0_bound]
  calc
    |driftIntegral P q muHat0 muHat1 eHat π|
        = |∫ x, (boolIndicator (π x) - boolIndicator (lawOptimalPolicy P x)) *
            clipBias P q muHat0 muHat1 eHat x ∂P.PX| := rfl
    _ ≤ ∫ x, |(boolIndicator (π x) - boolIndicator (lawOptimalPolicy P x)) *
          clipBias P q muHat0 muHat1 eHat x| ∂P.PX :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, major x ∂P.PX := hmajor_le
    _ ≤ (rE * rMu + rE * rMu) / q +
          Real.sqrt (P.PX.real T) * rMu + Real.sqrt (P.PX.real T) * rMu := hmajor_bound
    _ = 2 * (rMu * rE / q) +
        2 * rMu * Real.sqrt (P.PX.real
          (disagreementSet π (lawOptimalPolicy P) ∩ {x | overlap P x ≤ q})) := by
        simp [T]
        ring

-- @node: sqrt_add_le_sqrt_add_sqrt
private lemma sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · calc
      a + b ≤ (Real.sqrt a) ^ 2 + (Real.sqrt b) ^ 2 +
            2 * Real.sqrt a * Real.sqrt b := by
        rw [Real.sq_sqrt ha, Real.sq_sqrt hb]
        nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
      _ = (Real.sqrt a + Real.sqrt b) ^ 2 := by ring

-- @node: sqrt_margin_overlap_product
private lemma sqrt_margin_overlap_product {Creg u q α γ : ℝ}
    (hC : 0 < Creg) (hu : 0 < u) (hq : 0 < q) :
    Real.sqrt (Creg * u ^ α * q ^ (1 / γ)) =
      Creg ^ (1 / 2 : ℝ) * u ^ (α / 2) * q ^ (1 / (2 * γ)) := by
  have hCnn : 0 ≤ Creg := hC.le
  have hunn : 0 ≤ u := hu.le
  have hqnn : 0 ≤ q := hq.le
  calc
    Real.sqrt (Creg * u ^ α * q ^ (1 / γ))
        = (Creg * u ^ α * q ^ (1 / γ)) ^ (1 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow]
    _ = (Creg * u ^ α) ^ (1 / 2 : ℝ) *
          (q ^ (1 / γ)) ^ (1 / 2 : ℝ) := by
          rw [Real.mul_rpow (mul_nonneg hCnn (Real.rpow_nonneg hunn _))
            (Real.rpow_nonneg hqnn _)]
    _ = Creg ^ (1 / 2 : ℝ) * (u ^ α) ^ (1 / 2 : ℝ) *
          (q ^ (1 / γ)) ^ (1 / 2 : ℝ) := by
          rw [Real.mul_rpow hCnn (Real.rpow_nonneg hunn _)]
    _ = Creg ^ (1 / 2 : ℝ) * u ^ (α / 2) * q ^ (1 / (2 * γ)) := by
          rw [← Real.rpow_mul hunn, ← Real.rpow_mul hqnn]
          ring_nf

-- @node: lem:localized-clipped-drift-bound
/-- `lem:localized-clipped-drift-bound`. Deterministic drift bound for the actual
policy-weighted drift `|P[(π-π_⋆) b_q]| = |driftIntegral …|`, in BOTH overlap
regimes, from `clip_bias`, clipping, and clipped-region localization (which needs
overlap-decay and zero-effect). For `γ>0` and `q ≤ c_o u^γ` it is the three-term
bound; for `γ=0` with fixed `q ≤ underline_p/2` (the strict-overlap endpoint
`underline_p`, NOT hard-coded), strict overlap collapses it to `C r_μ r_e`. -/
-- @node: lem:clip-bias-drift-l2-localized-from-region
private lemma clipBias_drift_l2_localized_from_region (P : ObservedLaw 𝒳)
    (q rMu rE α γ underlineP : ℝ) (muHat0 muHat1 eHat : 𝒳 → ℝ)
    (hsq0 : ∫ x, (muHat0 x - P.mu0 x) ^ 2 ∂P.PX ≤ rMu ^ 2)
    (hsq1 : ∫ x, (muHat1 x - P.mu1 x) ^ 2 ∂P.PX ≤ rMu ^ 2)
    (hse : ∫ x, (eHat x - P.propensity x) ^ 2 ∂P.PX ≤ rE ^ 2)
    (hμ0L2 : MemLp (fun x => muHat0 x - P.mu0 x) 2 P.PX)
    (hμ1L2 : MemLp (fun x => muHat1 x - P.mu1 x) 2 P.PX)
    (heL2 : MemLp (fun x => eHat x - P.propensity x) 2 P.PX)
    (hrMu_nonneg : 0 ≤ rMu) (hrE_nonneg : 0 ≤ rE)
    (hwf : WellFormedLaw P) (hbdd : BoundedOutcome P)
    (hstrict : StrictOverlapEndpoint P γ underlineP)
    (hq : 0 < q) (hq_half : q ≤ 1 / 2) :
    (∃ C0 : ℝ, 0 < C0 ∧ C0 = 4 ∧
      ∀ (Creg : ℝ), 0 < Creg → ∀ π : Policy 𝒳, Measurable π → ∀ u : ℝ,
        0 < u → 0 < γ →
          P.PX.real (disagreementSet π (lawOptimalPolicy P) ∩ {x | overlap P x ≤ q})
            ≤ Creg * u ^ α * q ^ (1 / γ) + lawRegret P π / u →
          |driftIntegral P q muHat0 muHat1 eHat π|
            ≤ C0 * (rMu * rE / q
                + rMu * Creg ^ (1 / 2 : ℝ) * u ^ (α / 2) * q ^ (1 / (2 * γ))
                + rMu * (lawRegret P π / u) ^ (1 / 2 : ℝ))) ∧
      (∃ C1 : ℝ, 0 < C1 ∧
        C1 = max 1 (2 / q) ∧
        (γ = 0 → q ≤ underlineP / 2 → ∀ π : Policy 𝒳, Measurable π →
          |driftIntegral P q muHat0 muHat1 eHat π| ≤ C1 * (rMu * rE)))
    := by
  refine ⟨?_, ?_⟩
  · refine ⟨4, by norm_num, rfl, ?_⟩
    intro Creg hCreg π hπ u hu hγpos hmass
    let M : ℝ :=
      P.PX.real (disagreementSet π (lawOptimalPolicy P) ∩ {x | overlap P x ≤ q})
    let A : ℝ := rMu * rE / q
    let B : ℝ := Creg ^ (1 / 2 : ℝ) * u ^ (α / 2) * q ^ (1 / (2 * γ))
    let T : ℝ := (lawRegret P π / u) ^ (1 / 2 : ℝ)
    have hcore := clipBias_drift_l2_mass_bound P q rMu rE muHat0 muHat1 eHat
      hsq0 hsq1 hse hμ0L2 hμ1L2 heL2 hrMu_nonneg hrE_nonneg hwf hq hq_half π hπ
    have hR_nonneg : 0 ≤ lawRegret P π := lawRegret_nonneg P π hwf hbdd hπ
    have hA_nonneg : 0 ≤ A := by
      exact div_nonneg (mul_nonneg hrMu_nonneg hrE_nonneg) hq.le
    have hB_nonneg : 0 ≤ B := by
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg hCreg.le _) (Real.rpow_nonneg hu.le _))
        (Real.rpow_nonneg hq.le _)
    have hT_nonneg : 0 ≤ T := by
      exact Real.rpow_nonneg (div_nonneg hR_nonneg hu.le) _
    have hsmall_nonneg : 0 ≤ Creg * u ^ α * q ^ (1 / γ) := by
      exact mul_nonneg (mul_nonneg hCreg.le (Real.rpow_nonneg hu.le _))
        (Real.rpow_nonneg hq.le _)
    have hbig_nonneg : 0 ≤ lawRegret P π / u :=
      div_nonneg hR_nonneg hu.le
    have hsqrt_mass : Real.sqrt M ≤ B + T := by
      calc
        Real.sqrt M
            ≤ Real.sqrt (Creg * u ^ α * q ^ (1 / γ) + lawRegret P π / u) :=
              Real.sqrt_le_sqrt (by simpa [M] using hmass)
        _ ≤ Real.sqrt (Creg * u ^ α * q ^ (1 / γ)) +
              Real.sqrt (lawRegret P π / u) :=
              sqrt_add_le_sqrt_add_sqrt hsmall_nonneg hbig_nonneg
        _ = B + T := by
              rw [sqrt_margin_overlap_product hCreg hu hq, Real.sqrt_eq_rpow]
    have hcoef_nonneg : 0 ≤ 2 * rMu := by nlinarith
    have hcore_to_BT :
        |driftIntegral P q muHat0 muHat1 eHat π| ≤ 2 * A + 2 * rMu * (B + T) := by
      have hsqrt_term : 2 * rMu * Real.sqrt M ≤ 2 * rMu * (B + T) := by
        exact mul_le_mul_of_nonneg_left hsqrt_mass hcoef_nonneg
      have hcore' :
          |driftIntegral P q muHat0 muHat1 eHat π| ≤
            2 * A + 2 * rMu * Real.sqrt M := by
        simpa [A, M] using hcore
      nlinarith
    calc
      |driftIntegral P q muHat0 muHat1 eHat π|
          ≤ 2 * A + 2 * rMu * (B + T) := hcore_to_BT
      _ ≤ 4 * (A + rMu * B + rMu * T) := by
            nlinarith [hA_nonneg, hB_nonneg, hT_nonneg, hrMu_nonneg]
      _ = 4 * (rMu * rE / q
              + rMu * Creg ^ (1 / 2 : ℝ) * u ^ (α / 2) * q ^ (1 / (2 * γ))
              + rMu * (lawRegret P π / u) ^ (1 / 2 : ℝ)) := by
            rw [show A = rMu * rE / q from rfl,
              show B = Creg ^ (1 / 2 : ℝ) * u ^ (α / 2) * q ^ (1 / (2 * γ)) from rfl,
              show T = (lawRegret P π / u) ^ (1 / 2 : ℝ) from rfl]
            ring_nf
  · let C : ℝ := max 1 (2 / q)
    have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    refine ⟨C, hCpos, rfl, ?_⟩
    intro hγ0 hq_under π hπ
    let M : ℝ :=
      P.PX.real (disagreementSet π (lawOptimalPolicy P) ∩ {x | overlap P x ≤ q})
    have hcore := clipBias_drift_l2_mass_bound P q rMu rE muHat0 muHat1 eHat
      hsq0 hsq1 hse hμ0L2 hμ1L2 heL2 hrMu_nonneg hrE_nonneg hwf hq hq_half π hπ
    letI : IsProbabilityMeasure P.PX := hwf.2.1
    rcases hstrict hγ0 with ⟨hunderline_pos, _hunderline_le, hunderline_ae⟩
    let S : Set 𝒳 := disagreementSet π (lawOptimalPolicy P) ∩ {x | overlap P x ≤ q}
    have hS_zero : P.PX.real S = 0 := by
      apply (measureReal_eq_zero_iff (μ := P.PX) (s := S) (measure_ne_top P.PX S)).2
      apply measure_eq_zero_iff_ae_notMem.2
      filter_upwards [hunderline_ae] with x hx_under hxS
      rcases hxS with ⟨_hxD, hxlow⟩
      have hxlow' : overlap P x ≤ q := hxlow
      have hq_lt_under : q < underlineP := by linarith
      linarith
    have hcore_zero :
        |driftIntegral P q muHat0 muHat1 eHat π| ≤ 2 * (rMu * rE / q) := by
      have hcore' :
          |driftIntegral P q muHat0 muHat1 eHat π| ≤
            2 * (rMu * rE / q) + 2 * rMu * Real.sqrt (P.PX.real S) := by
        simpa [S] using hcore
      simpa [hS_zero] using hcore'
    have hprod_nonneg : 0 ≤ rMu * rE := mul_nonneg hrMu_nonneg hrE_nonneg
    have hCge : 2 / q ≤ C := by
      exact le_max_right _ _
    calc
      |driftIntegral P q muHat0 muHat1 eHat π|
          ≤ 2 * (rMu * rE / q) := hcore_zero
      _ = (2 / q) * (rMu * rE) := by ring
      _ ≤ C * (rMu * rE) :=
            mul_le_mul_of_nonneg_right hCge hprod_nonneg

-- @node: lem:localized-clipped-drift-bound
lemma localized_clipped_drift_bound (P : ObservedLaw 𝒳)
    (policySet : Set (Policy 𝒳)) (q rMu rE α γ Co co u0 underlineP : ℝ)
    (muHat0 muHat1 eHat : 𝒳 → ℝ)
    (hsq0 : ∫ x, (muHat0 x - P.mu0 x) ^ 2 ∂P.PX ≤ rMu ^ 2)
    (hsq1 : ∫ x, (muHat1 x - P.mu1 x) ^ 2 ∂P.PX ≤ rMu ^ 2)
    (hse : ∫ x, (eHat x - P.propensity x) ^ 2 ∂P.PX ≤ rE ^ 2)
    -- regularity: L² nuisance-error functions are genuine Bochner/MemLp inputs
    -- for the Cauchy-Schwarz step; this is intrinsic to the stated L² rates.
    (hμ0L2 : MemLp (fun x => muHat0 x - P.mu0 x) 2 P.PX)
    (hμ1L2 : MemLp (fun x => muHat1 x - P.mu1 x) 2 P.PX)
    (heL2 : MemLp (fun x => eHat x - P.propensity x) 2 P.PX)
    -- regularity: nuisance rates are nonnegative radii (NuisanceRate /
    -- PolynomialNuisanceExponents bookkeeping in the note).
    (hrMu_nonneg : 0 ≤ rMu) (hrE_nonneg : 0 ≤ rE)
    -- regularity: standing observed-law setup needed for welfare identity,
    -- strict-overlap projection, and measurable disagreement sets.
    (hwf : WellFormedLaw P)
    -- regularity: policy measurability needed by `clipped_region_localization`.
    (hπmeas : ∀ π ∈ policySet, Measurable π)
    -- regularity: `q` is a clipping level, so denominators obey
    -- `q ≤ ē_q ≤ 1-q`; the note's selected clips satisfy this.
    (hq_half : q ≤ 1 / 2)
    (hod : OverlapDecay P u0 Co co α γ) (hze : ZeroEffectRegular P policySet)
    (hbdd : BoundedOutcome P)
    (hstrict : StrictOverlapEndpoint P γ underlineP) (hq : 0 < q) :
    (∃ C0 : ℝ, 0 < C0 ∧ C0 = 4 * (1 + (max Co 1) ^ (1 / 2 : ℝ)) ∧
      (0 < γ → ∀ π ∈ policySet, ∀ u : ℝ,
        0 < u → u ≤ u0 → q ≤ co * u ^ γ →
          |driftIntegral P q muHat0 muHat1 eHat π|
            ≤ C0 * (rMu * rE / q + rMu * u ^ (α / 2) * q ^ (1 / (2 * γ))
                + rMu * (lawRegret P π / u) ^ (1 / 2 : ℝ)))) ∧
      (∃ C1 : ℝ, 0 < C1 ∧
        C1 = max 1 (2 / q) ∧
        (γ = 0 → q ≤ underlineP / 2 → ∀ π ∈ policySet,
          |driftIntegral P q muHat0 muHat1 eHat π| ≤ C1 * (rMu * rE)))
    := by
  rcases clipBias_drift_l2_localized_from_region P q rMu rE α γ underlineP
      muHat0 muHat1 eHat hsq0 hsq1 hse hμ0L2 hμ1L2 heL2
      hrMu_nonneg hrE_nonneg hwf hbdd hstrict hq hq_half with
    ⟨⟨Cdrift, hCdrift, hCdrift_eq, hregionDrift⟩,
      ⟨Cstrict, hCstrict, hCstrict_eq, hstrictDrift⟩⟩
  let Cpos : ℝ := 4 * (1 + (max Co 1) ^ (1 / 2 : ℝ))
  let S : ℝ := (max Co 1) ^ (1 / 2 : ℝ)
  have hCreg : 0 < max Co 1 := lt_of_lt_of_le zero_lt_one (le_max_right Co 1)
  have hS_nonneg : 0 ≤ S := Real.rpow_nonneg hCreg.le _
  have hfactor_pos : 0 < 1 + S := by nlinarith
  have hCpos : 0 < Cpos := by
    dsimp [Cpos, S]
    nlinarith
  refine ⟨⟨Cpos, hCpos, rfl, ?_⟩, ⟨Cstrict, hCstrict, hCstrict_eq, ?_⟩⟩
  · intro hγpos π hπmem u hu hu_le hq_le
    rcases clipped_region_localization P policySet Co co α γ u0
        hod hze hbdd hwf hπmeas hγpos with
      ⟨_hCreg_loc, hloc⟩
    have hπ : Measurable π := hπmeas π hπmem
    have hmass := hloc π hπmem u q hu hu_le hq hq_le
    have hbase := hregionDrift (max Co 1) hCreg π hπ u hu hγpos hmass
    let A : ℝ := rMu * rE / q
    let B : ℝ := u ^ (α / 2) * q ^ (1 / (2 * γ))
    let T : ℝ := (lawRegret P π / u) ^ (1 / 2 : ℝ)
    have hA_nonneg : 0 ≤ A := by
      exact div_nonneg (mul_nonneg hrMu_nonneg hrE_nonneg) hq.le
    have hB_nonneg : 0 ≤ B := by
      exact mul_nonneg (Real.rpow_nonneg hu.le _) (Real.rpow_nonneg hq.le _)
    have hR_nonneg : 0 ≤ lawRegret P π := lawRegret_nonneg P π hwf hbdd hπ
    have hT_nonneg : 0 ≤ T := by
      exact Real.rpow_nonneg (div_nonneg hR_nonneg hu.le) _
    have hY_nonneg : 0 ≤ rMu * B := mul_nonneg hrMu_nonneg hB_nonneg
    have hZ_nonneg : 0 ≤ rMu * T := mul_nonneg hrMu_nonneg hT_nonneg
    have hinside :
        A + rMu * S * B + rMu * T
          ≤ (1 + S) * (A + rMu * B + rMu * T) := by
      nlinarith [hA_nonneg, hY_nonneg, hZ_nonneg, hS_nonneg]
    calc
      |driftIntegral P q muHat0 muHat1 eHat π|
          ≤ 4 * (A + rMu * S * B + rMu * T) := by
            simpa [A, B, T, S, hCdrift_eq, mul_assoc, mul_left_comm, mul_comm] using hbase
      _ ≤ 4 * ((1 + S) * (A + rMu * B + rMu * T)) :=
            mul_le_mul_of_nonneg_left hinside (by norm_num)
      _ = Cpos * (rMu * rE / q + rMu * u ^ (α / 2) * q ^ (1 / (2 * γ))
              + rMu * (lawRegret P π / u) ^ (1 / 2 : ℝ)) := by
            simp [A, B, T, Cpos, S]
            ring
  · intro hγ0 hq_le π hπmem
    exact hstrictDrift hγ0 hq_le π (hπmeas π hπmem)


end CausalSmith.Stat.PolicyRegretMarginOverlap
