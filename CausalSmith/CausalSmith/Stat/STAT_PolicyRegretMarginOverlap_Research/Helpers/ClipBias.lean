/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Helpers.CrossfitProcess

/-! Provides clipped AIPW drift and clip-bias helper lemmas. -/

namespace CausalSmith.Stat.PolicyRegretMarginOverlap

open MeasureTheory
open scoped BigOperators

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- Pointwise clip-bias drift `b_q(x)` of the clipped-AIPW conditional mean. -/
noncomputable def clipBias (P : ObservedLaw 𝒳) (q : ℝ)
    (muHat0 muHat1 eHat : 𝒳 → ℝ) (x : 𝒳) : ℝ :=
  (clippedPropensity q eHat x - P.propensity x) *
    ((muHat1 x - P.mu1 x) / clippedPropensity q eHat x
      + (muHat0 x - P.mu0 x) / (1 - clippedPropensity q eHat x))

/-- Policy-weighted population drift `P[(π-π_⋆) b_q]`. -/
noncomputable def driftIntegral (P : ObservedLaw 𝒳) (q : ℝ)
    (muHat0 muHat1 eHat : 𝒳 → ℝ) (π : Policy 𝒳) : ℝ :=
  ∫ x, (boolIndicator (π x) - boolIndicator (lawOptimalPolicy P x))
        * clipBias P q muHat0 muHat1 eHat x ∂P.PX

/-- Cross-fit centered-process increment for the feasible clipped-AIPW ERM bridge. -/
noncomputable def clippedPolicyIncrement {K : ℕ} (P : ObservedLaw 𝒳) (q : ℝ)
    (muHat0 muHat1 eHat : Fin K → 𝒳 → ℝ)
    (k : Fin K) (π : Policy 𝒳) (O : Observation 𝒳) : ℝ :=
  (boolIndicator (π O.X) - boolIndicator (lawOptimalPolicy P O.X)) *
    clippedAIPWScore q (muHat0 k) (muHat1 k) (eHat k) O

private noncomputable def clipReal (B z : ℝ) : ℝ :=
  max (-B) (min B z)

-- @node: clippedScoreTrunc
noncomputable def clippedScoreTrunc (q B : ℝ)
    (muHat0 muHat1 eHat : 𝒳 → ℝ) (O : Observation 𝒳) : ℝ :=
  clipReal B (clippedAIPWScore q muHat0 muHat1 eHat O)

-- @node: clippedPolicyIncrementTrunc
noncomputable def clippedPolicyIncrementTrunc {K : ℕ}
    (P : ObservedLaw 𝒳) (q B : ℝ)
    (muHat0 muHat1 eHat : Fin K → 𝒳 → ℝ)
    (k : Fin K) (π : Policy 𝒳) (O : Observation 𝒳) : ℝ :=
  (boolIndicator (π O.X) - boolIndicator (lawOptimalPolicy P O.X)) *
    clippedScoreTrunc q B (muHat0 k) (muHat1 k) (eHat k) O

private lemma measurable_observation_tuple :
    Measurable (fun O : Observation 𝒳 => (O.X, O.A, O.Y)) := by
  exact Measurable.of_comap_le le_rfl

lemma measurable_observation_X :
    Measurable (fun O : Observation 𝒳 => O.X) := by
  exact measurable_fst.comp measurable_observation_tuple

private lemma measurable_observation_A :
    Measurable (fun O : Observation 𝒳 => O.A) := by
  exact measurable_fst.comp (measurable_snd.comp measurable_observation_tuple)

lemma measurable_observation_Y :
    Measurable (fun O : Observation 𝒳 => O.Y) := by
  exact measurable_snd.comp (measurable_snd.comp measurable_observation_tuple)

lemma measurable_boolIndicator_observation_A :
    Measurable (fun O : Observation 𝒳 => boolIndicator O.A) := by
  exact (measurable_of_finite (fun b : Bool => boolIndicator b)).comp
    measurable_observation_A

lemma measurable_clippedPropensity (q : ℝ) {e : 𝒳 → ℝ}
    (he : Measurable e) : Measurable (clippedPropensity q e) := by
  simpa [clippedPropensity] using
    (Measurable.min measurable_const (Measurable.max measurable_const he))

omit [MeasurableSpace 𝒳] in
private lemma clipReal_abs_le {B z : ℝ} (hB : 0 ≤ B) :
    |clipReal B z| ≤ B := by
  unfold clipReal
  have hlow : -B ≤ max (-B) (min B z) := le_max_left _ _
  have hhigh : max (-B) (min B z) ≤ B := by
    exact max_le (by linarith) (min_le_left B z)
  exact abs_le.mpr ⟨hlow, hhigh⟩

omit [MeasurableSpace 𝒳] in
lemma clipReal_eq_self_of_abs_le {B z : ℝ} (hz : |z| ≤ B) :
    clipReal B z = z := by
  have hz' := abs_le.mp hz
  unfold clipReal
  rw [min_eq_right hz'.2, max_eq_right hz'.1]

omit [MeasurableSpace 𝒳] in
private lemma boolIndicator_sub_abs_le_one (b c : Bool) :
    |boolIndicator b - boolIndicator c| ≤ (1 : ℝ) := by
  cases b <;> cases c <;> norm_num [boolIndicator]

private lemma measurable_clippedAIPWScore_observation (q : ℝ)
    (muHat0 muHat1 eHat : 𝒳 → ℝ)
    (hμ0meas : Measurable muHat0) (hμ1meas : Measurable muHat1)
    (hemeas : Measurable eHat) :
    Measurable (fun O : Observation 𝒳 =>
      clippedAIPWScore q muHat0 muHat1 eHat O) := by
  have hX : Measurable (fun O : Observation 𝒳 => O.X) := measurable_observation_X
  have hA : Measurable (fun O : Observation 𝒳 => boolIndicator O.A) :=
    measurable_boolIndicator_observation_A
  have hY : Measurable (fun O : Observation 𝒳 => O.Y) := measurable_observation_Y
  have hμ0 : Measurable (fun O : Observation 𝒳 => muHat0 O.X) := hμ0meas.comp hX
  have hμ1 : Measurable (fun O : Observation 𝒳 => muHat1 O.X) := hμ1meas.comp hX
  have hcp : Measurable (fun O : Observation 𝒳 => clippedPropensity q eHat O.X) :=
    (measurable_clippedPropensity q hemeas).comp hX
  unfold clippedAIPWScore
  exact ((hμ1.sub hμ0).add ((hA.div hcp).mul (hY.sub hμ1))).sub
    (((measurable_const.sub hA).div (measurable_const.sub hcp)).mul (hY.sub hμ0))

private lemma measurable_clipReal {α : Type*} [MeasurableSpace α] {B : ℝ}
    {f : α → ℝ} (hf : Measurable f) :
    Measurable (fun x => clipReal B (f x)) := by
  simpa [clipReal] using
    (Measurable.max measurable_const (Measurable.min measurable_const hf))

lemma clippedPolicyIncrementTrunc_compatible {K : ℕ}
    (P : ObservedLaw 𝒳) (q B : ℝ)
    (muHat0 muHat1 eHat : Fin K → 𝒳 → ℝ) (k : Fin K) :
    PolicyCompatible (clippedPolicyIncrementTrunc P q B muHat0 muHat1 eHat k) := by
  refine ⟨fun O b =>
    (boolIndicator b - boolIndicator (lawOptimalPolicy P O.X)) *
      clippedScoreTrunc q B (muHat0 k) (muHat1 k) (eHat k) O, ?_⟩
  intro π O
  rfl

lemma clippedPolicyIncrementTrunc_measurable {K : ℕ}
    (P : ObservedLaw 𝒳) (q B : ℝ)
    (muHat0 muHat1 eHat : Fin K → 𝒳 → ℝ) (k : Fin K)
    (π : Policy 𝒳) (hwf : WellFormedLaw P) (hπ : Measurable π)
    (hμ0meas : Measurable (muHat0 k)) (hμ1meas : Measurable (muHat1 k))
    (hemeas : Measurable (eHat k)) :
    Measurable (clippedPolicyIncrementTrunc P q B muHat0 muHat1 eHat k π) := by
  have hπind : Measurable (fun O : Observation 𝒳 => boolIndicator (π O.X)) :=
    (measurable_of_finite (fun b : Bool => boolIndicator b)).comp
      (hπ.comp measurable_observation_X)
  have hstar : Measurable (fun O : Observation 𝒳 =>
      boolIndicator (lawOptimalPolicy P O.X)) :=
    (measurable_of_finite (fun b : Bool => boolIndicator b)).comp
      ((lawOptimalPolicy_measurable P hwf).comp measurable_observation_X)
  have hscore : Measurable (fun O : Observation 𝒳 =>
      clippedScoreTrunc q B (muHat0 k) (muHat1 k) (eHat k) O) :=
    measurable_clipReal
      (measurable_clippedAIPWScore_observation q (muHat0 k) (muHat1 k) (eHat k)
        hμ0meas hμ1meas hemeas)
  simpa [clippedPolicyIncrementTrunc, clippedScoreTrunc] using
    ((hπind.sub hstar).mul hscore)

lemma clippedPolicyIncrementTrunc_bound {K : ℕ}
    (P : ObservedLaw 𝒳) (q B : ℝ)
    (muHat0 muHat1 eHat : Fin K → 𝒳 → ℝ) (k : Fin K)
    (π : Policy 𝒳) (O : Observation 𝒳) (hB : 0 ≤ B) :
    |clippedPolicyIncrementTrunc P q B muHat0 muHat1 eHat k π O| ≤ B := by
  have hdiff :
      |boolIndicator (π O.X) - boolIndicator (lawOptimalPolicy P O.X)| ≤ (1 : ℝ) :=
    boolIndicator_sub_abs_le_one _ _
  have hscore :
      |clippedScoreTrunc q B (muHat0 k) (muHat1 k) (eHat k) O| ≤ B := by
    simpa [clippedScoreTrunc] using
      clipReal_abs_le (B := B)
        (z := clippedAIPWScore q (muHat0 k) (muHat1 k) (eHat k) O) hB
  calc
    |clippedPolicyIncrementTrunc P q B muHat0 muHat1 eHat k π O|
        =
        |boolIndicator (π O.X) - boolIndicator (lawOptimalPolicy P O.X)| *
          |clippedScoreTrunc q B (muHat0 k) (muHat1 k) (eHat k) O| := by
          simp [clippedPolicyIncrementTrunc, abs_mul]
    _ ≤ 1 * B := by
          exact mul_le_mul hdiff hscore (abs_nonneg _) zero_le_one
    _ = B := by ring

omit [MeasurableSpace 𝒳] in
lemma bounded_mul {f g : 𝒳 → ℝ}
    (hf : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (hg : ∃ M : ℝ, ∀ x, |g x| ≤ M) :
    ∃ M : ℝ, ∀ x, |f x * g x| ≤ M := by
  rcases hf with ⟨Mf, hMf⟩
  rcases hg with ⟨Mg, hMg⟩
  refine ⟨max Mf 0 * max Mg 0, ?_⟩
  intro x
  have hf' : |f x| ≤ max Mf 0 := le_trans (hMf x) (le_max_left Mf 0)
  have hg' : |g x| ≤ max Mg 0 := le_trans (hMg x) (le_max_left Mg 0)
  calc
    |f x * g x| = |f x| * |g x| := abs_mul _ _
    _ ≤ max Mf 0 * max Mg 0 := by gcongr

omit [MeasurableSpace 𝒳] in
private lemma bounded_add {f g : 𝒳 → ℝ}
    (hf : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (hg : ∃ M : ℝ, ∀ x, |g x| ≤ M) :
    ∃ M : ℝ, ∀ x, |f x + g x| ≤ M := by
  rcases hf with ⟨Mf, hMf⟩
  rcases hg with ⟨Mg, hMg⟩
  refine ⟨max Mf 0 + max Mg 0, ?_⟩
  intro x
  calc
    |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ max Mf 0 + max Mg 0 := by
      gcongr
      · exact le_trans (hMf x) (le_max_left Mf 0)
      · exact le_trans (hMg x) (le_max_left Mg 0)

omit [MeasurableSpace 𝒳] in
private lemma bounded_sub {f g : 𝒳 → ℝ}
    (hf : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (hg : ∃ M : ℝ, ∀ x, |g x| ≤ M) :
    ∃ M : ℝ, ∀ x, |f x - g x| ≤ M := by
  rcases hf with ⟨Mf, hMf⟩
  rcases hg with ⟨Mg, hMg⟩
  refine ⟨max Mf 0 + max Mg 0, ?_⟩
  intro x
  calc
    |f x - g x| ≤ |f x| + |g x| := abs_sub _ _
    _ ≤ max Mf 0 + max Mg 0 := by
      gcongr
      · exact le_trans (hMf x) (le_max_left Mf 0)
      · exact le_trans (hMg x) (le_max_left Mg 0)

lemma integrable_of_measurable_bounded {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hfmeas : Measurable f) (hfbdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) :
    Integrable f μ := by
  rcases hfbdd with ⟨M, hM⟩
  refine MeasureTheory.Integrable.of_bound hfmeas.aestronglyMeasurable (max M 0) ?_
  exact Filter.Eventually.of_forall (fun x => by
    simpa [Real.norm_eq_abs] using le_trans (hM x) (le_max_left M 0))

private lemma integrable_covariate_test (P : ObservedLaw 𝒳)
    (hwf : WellFormedLaw P) {ψ : 𝒳 → ℝ}
    (hψmeas : Measurable ψ) (hψbdd : ∃ M : ℝ, ∀ x, |ψ x| ≤ M) :
    Integrable (fun O : Observation 𝒳 => ψ O.X) P.dataMeasure := by
  letI : IsProbabilityMeasure P.dataMeasure := hwf.1
  exact integrable_of_measurable_bounded
    (hψmeas.comp measurable_observation_X)
    (by
      rcases hψbdd with ⟨M, hM⟩
      exact ⟨M, fun O => hM O.X⟩)

private lemma boolIndicator_abs_le_one (b : Bool) :
    |boolIndicator b| ≤ (1 : ℝ) := by
  cases b <;> simp [boolIndicator]

private lemma one_sub_boolIndicator_abs_le_one (b : Bool) :
    |1 - boolIndicator b| ≤ (1 : ℝ) := by
  cases b <;> simp [boolIndicator]

private lemma integrable_treated_test (P : ObservedLaw 𝒳)
    (hwf : WellFormedLaw P) {ψ : 𝒳 → ℝ}
    (hψmeas : Measurable ψ) (hψbdd : ∃ M : ℝ, ∀ x, |ψ x| ≤ M) :
    Integrable (fun O : Observation 𝒳 => boolIndicator O.A * ψ O.X)
      P.dataMeasure := by
  letI : IsProbabilityMeasure P.dataMeasure := hwf.1
  refine integrable_of_measurable_bounded
    (measurable_boolIndicator_observation_A.mul (hψmeas.comp measurable_observation_X)) ?_
  rcases hψbdd with ⟨M, hM⟩
  refine ⟨max M 0, ?_⟩
  intro O
  calc
    |boolIndicator O.A * ψ O.X| = |boolIndicator O.A| * |ψ O.X| := abs_mul _ _
    _ ≤ 1 * max M 0 := by
      gcongr
      · exact boolIndicator_abs_le_one O.A
      · exact le_trans (hM O.X) (le_max_left M 0)
    _ = max M 0 := by ring

private lemma integrable_control_test (P : ObservedLaw 𝒳)
    (hwf : WellFormedLaw P) {ψ : 𝒳 → ℝ}
    (hψmeas : Measurable ψ) (hψbdd : ∃ M : ℝ, ∀ x, |ψ x| ≤ M) :
    Integrable (fun O : Observation 𝒳 => (1 - boolIndicator O.A) * ψ O.X)
      P.dataMeasure := by
  letI : IsProbabilityMeasure P.dataMeasure := hwf.1
  refine integrable_of_measurable_bounded
    ((measurable_const.sub measurable_boolIndicator_observation_A).mul
      (hψmeas.comp measurable_observation_X)) ?_
  rcases hψbdd with ⟨M, hM⟩
  refine ⟨max M 0, ?_⟩
  intro O
  calc
    |(1 - boolIndicator O.A) * ψ O.X|
        = |1 - boolIndicator O.A| * |ψ O.X| := abs_mul _ _
    _ ≤ 1 * max M 0 := by
      gcongr
      · exact one_sub_boolIndicator_abs_le_one O.A
      · exact le_trans (hM O.X) (le_max_left M 0)
    _ = max M 0 := by ring

private lemma integrable_treated_outcome_test (P : ObservedLaw 𝒳)
    (hwf : WellFormedLaw P) (hbdd : BoundedOutcome P) {ψ : 𝒳 → ℝ}
    (hψmeas : Measurable ψ) (hψbdd : ∃ M : ℝ, ∀ x, |ψ x| ≤ M) :
    Integrable (fun O : Observation 𝒳 => boolIndicator O.A * O.Y * ψ O.X)
      P.dataMeasure := by
  letI : IsProbabilityMeasure P.dataMeasure := hwf.1
  rcases hψbdd with ⟨M, hM⟩
  refine MeasureTheory.Integrable.of_bound
    ((measurable_boolIndicator_observation_A.mul measurable_observation_Y).mul
      (hψmeas.comp measurable_observation_X)).aestronglyMeasurable
    (max M 0) ?_
  filter_upwards [hbdd.1] with O hY
  have hYabs : |O.Y| ≤ (1 : ℝ) := abs_le.mpr ⟨hY.1, hY.2⟩
  calc
    ‖boolIndicator O.A * O.Y * ψ O.X‖
        = |boolIndicator O.A| * |O.Y| * |ψ O.X| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul]
    _ ≤ 1 * 1 * max M 0 := by
      exact mul_le_mul
        (mul_le_mul (boolIndicator_abs_le_one O.A) hYabs (abs_nonneg _) zero_le_one)
        (le_trans (hM O.X) (le_max_left M 0))
        (abs_nonneg _) (mul_nonneg zero_le_one zero_le_one)
    _ = max M 0 := by ring

private lemma integrable_control_outcome_test (P : ObservedLaw 𝒳)
    (hwf : WellFormedLaw P) (hbdd : BoundedOutcome P) {ψ : 𝒳 → ℝ}
    (hψmeas : Measurable ψ) (hψbdd : ∃ M : ℝ, ∀ x, |ψ x| ≤ M) :
    Integrable (fun O : Observation 𝒳 => (1 - boolIndicator O.A) * O.Y * ψ O.X)
      P.dataMeasure := by
  letI : IsProbabilityMeasure P.dataMeasure := hwf.1
  rcases hψbdd with ⟨M, hM⟩
  refine MeasureTheory.Integrable.of_bound
    (((measurable_const.sub measurable_boolIndicator_observation_A).mul
      measurable_observation_Y).mul (hψmeas.comp measurable_observation_X)).aestronglyMeasurable
    (max M 0) ?_
  filter_upwards [hbdd.1] with O hY
  have hYabs : |O.Y| ≤ (1 : ℝ) := abs_le.mpr ⟨hY.1, hY.2⟩
  calc
    ‖(1 - boolIndicator O.A) * O.Y * ψ O.X‖
        = |1 - boolIndicator O.A| * |O.Y| * |ψ O.X| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul]
    _ ≤ 1 * 1 * max M 0 := by
      exact mul_le_mul
        (mul_le_mul (one_sub_boolIndicator_abs_le_one O.A) hYabs (abs_nonneg _) zero_le_one)
        (le_trans (hM O.X) (le_max_left M 0))
        (abs_nonneg _) (mul_nonneg zero_le_one zero_le_one)
    _ = max M 0 := by ring

omit [MeasurableSpace 𝒳] in
lemma clippedPropensity_lower_min (q : ℝ) (e : 𝒳 → ℝ) (x : 𝒳) :
    min q (1 - q) ≤ clippedPropensity q e x := by
  unfold clippedPropensity
  exact le_min (min_le_right q (1 - q))
    (le_trans (min_le_left q (1 - q)) (le_max_left q (e x)))

omit [MeasurableSpace 𝒳] in
lemma clippedPropensity_le_one_sub (q : ℝ) (e : 𝒳 → ℝ) (x : 𝒳) :
    clippedPropensity q e x ≤ 1 - q := by
  unfold clippedPropensity
  exact min_le_left (1 - q) (max q (e x))

omit [MeasurableSpace 𝒳] in
lemma clippedPropensity_pos (q : ℝ) (e : 𝒳 → ℝ) (x : 𝒳)
    (hq : 0 < q) (hq1 : q < 1) :
    0 < clippedPropensity q e x := by
  have hr : 0 < min q (1 - q) := lt_min hq (by linarith)
  exact lt_of_lt_of_le hr (clippedPropensity_lower_min q e x)

omit [MeasurableSpace 𝒳] in
lemma one_sub_clippedPropensity_pos (q : ℝ) (e : 𝒳 → ℝ) (x : 𝒳)
    (hq : 0 < q) :
    0 < 1 - clippedPropensity q e x := by
  have hle := clippedPropensity_le_one_sub q e x
  linarith

omit [MeasurableSpace 𝒳] in
private lemma bounded_div_clipped (q : ℝ) (e φ : 𝒳 → ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hφbdd : ∃ M : ℝ, ∀ x, |φ x| ≤ M) :
    ∃ M : ℝ, ∀ x, |φ x / clippedPropensity q e x| ≤ M := by
  rcases hφbdd with ⟨Mφ, hMφ⟩
  let r : ℝ := min q (1 - q)
  have hr : 0 < r := lt_min hq (by linarith)
  refine ⟨max Mφ 0 / r, ?_⟩
  intro x
  have hcp_pos : 0 < clippedPropensity q e x :=
    clippedPropensity_pos q e x hq hq1
  have hcp_lower : r ≤ clippedPropensity q e x :=
    clippedPropensity_lower_min q e x
  have h_inv : (clippedPropensity q e x)⁻¹ ≤ r⁻¹ := by
    rw [inv_le_inv₀ hcp_pos hr]
    exact hcp_lower
  have hφ : |φ x| ≤ max Mφ 0 := le_trans (hMφ x) (le_max_left Mφ 0)
  calc
    |φ x / clippedPropensity q e x|
        = |φ x| * (clippedPropensity q e x)⁻¹ := by
          rw [abs_div, abs_of_pos hcp_pos, div_eq_mul_inv]
    _ ≤ max Mφ 0 * r⁻¹ := by
          gcongr
    _ = max Mφ 0 / r := by
          rw [div_eq_mul_inv]

omit [MeasurableSpace 𝒳] in
private lemma bounded_div_one_sub_clipped (q : ℝ) (e φ : 𝒳 → ℝ)
    (hq : 0 < q) (hφbdd : ∃ M : ℝ, ∀ x, |φ x| ≤ M) :
    ∃ M : ℝ, ∀ x, |φ x / (1 - clippedPropensity q e x)| ≤ M := by
  rcases hφbdd with ⟨Mφ, hMφ⟩
  refine ⟨max Mφ 0 / q, ?_⟩
  intro x
  have hden_pos : 0 < 1 - clippedPropensity q e x :=
    one_sub_clippedPropensity_pos q e x hq
  have hden_lower : q ≤ 1 - clippedPropensity q e x := by
    have hle := clippedPropensity_le_one_sub q e x
    linarith
  have h_inv : (1 - clippedPropensity q e x)⁻¹ ≤ q⁻¹ := by
    rw [inv_le_inv₀ hden_pos hq]
    exact hden_lower
  have hφ : |φ x| ≤ max Mφ 0 := le_trans (hMφ x) (le_max_left Mφ 0)
  calc
    |φ x / (1 - clippedPropensity q e x)|
        = |φ x| * (1 - clippedPropensity q e x)⁻¹ := by
          rw [abs_div, abs_of_pos hden_pos, div_eq_mul_inv]
    _ ≤ max Mφ 0 * q⁻¹ := by
          gcongr
    _ = max Mφ 0 / q := by
          rw [div_eq_mul_inv]

omit [MeasurableSpace 𝒳] in
private lemma bounded_mul_div_clipped (q : ℝ) (e f φ : 𝒳 → ℝ)
    (hq : 0 < q) (hq1 : q < 1)
    (hfbdd : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (hφbdd : ∃ M : ℝ, ∀ x, |φ x| ≤ M) :
    ∃ M : ℝ, ∀ x, |f x * φ x / clippedPropensity q e x| ≤ M := by
  rcases hfbdd with ⟨Mf, hMf⟩
  rcases hφbdd with ⟨Mφ, hMφ⟩
  let r : ℝ := min q (1 - q)
  have hr : 0 < r := lt_min hq (by linarith)
  refine ⟨max Mf 0 * max Mφ 0 / r, ?_⟩
  intro x
  have hcp_pos : 0 < clippedPropensity q e x :=
    clippedPropensity_pos q e x hq hq1
  have hcp_lower : r ≤ clippedPropensity q e x :=
    clippedPropensity_lower_min q e x
  have h_inv : (clippedPropensity q e x)⁻¹ ≤ r⁻¹ := by
    rw [inv_le_inv₀ hcp_pos hr]
    exact hcp_lower
  have hf : |f x| ≤ max Mf 0 := le_trans (hMf x) (le_max_left Mf 0)
  have hφ : |φ x| ≤ max Mφ 0 := le_trans (hMφ x) (le_max_left Mφ 0)
  calc
    |f x * φ x / clippedPropensity q e x|
        = |f x| * |φ x| * (clippedPropensity q e x)⁻¹ := by
          rw [abs_div, abs_mul, abs_of_pos hcp_pos, div_eq_mul_inv]
    _ ≤ max Mf 0 * max Mφ 0 * r⁻¹ := by
          gcongr
    _ = max Mf 0 * max Mφ 0 / r := by
          rw [div_eq_mul_inv]

omit [MeasurableSpace 𝒳] in
private lemma bounded_mul_div_one_sub_clipped (q : ℝ) (e f φ : 𝒳 → ℝ)
    (hq : 0 < q)
    (hfbdd : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (hφbdd : ∃ M : ℝ, ∀ x, |φ x| ≤ M) :
    ∃ M : ℝ, ∀ x, |f x * φ x / (1 - clippedPropensity q e x)| ≤ M := by
  rcases hfbdd with ⟨Mf, hMf⟩
  rcases hφbdd with ⟨Mφ, hMφ⟩
  refine ⟨max Mf 0 * max Mφ 0 / q, ?_⟩
  intro x
  have hden_pos : 0 < 1 - clippedPropensity q e x :=
    one_sub_clippedPropensity_pos q e x hq
  have hden_lower : q ≤ 1 - clippedPropensity q e x := by
    have hle := clippedPropensity_le_one_sub q e x
    linarith
  have h_inv : (1 - clippedPropensity q e x)⁻¹ ≤ q⁻¹ := by
    rw [inv_le_inv₀ hden_pos hq]
    exact hden_lower
  have hf : |f x| ≤ max Mf 0 := le_trans (hMf x) (le_max_left Mf 0)
  have hφ : |φ x| ≤ max Mφ 0 := le_trans (hMφ x) (le_max_left Mφ 0)
  calc
    |f x * φ x / (1 - clippedPropensity q e x)|
        = |f x| * |φ x| * (1 - clippedPropensity q e x)⁻¹ := by
          rw [abs_div, abs_mul, abs_of_pos hden_pos, div_eq_mul_inv]
    _ ≤ max Mf 0 * max Mφ 0 * q⁻¹ := by
          gcongr
    _ = max Mf 0 * max Mφ 0 / q := by
          rw [div_eq_mul_inv]

private lemma covariate_integral_eq_px (P : ObservedLaw 𝒳)
    (hwf : WellFormedLaw P) (f : 𝒳 → ℝ) (hf : Measurable f) :
    ∫ O, f O.X ∂P.dataMeasure = ∫ x, f x ∂P.PX := by
  have hmap : P.dataMeasure.map (fun O => O.X) = P.PX := hwf.2.2.1
  have hfm : AEStronglyMeasurable f (Measure.map (fun O : Observation 𝒳 => O.X) P.dataMeasure) :=
    hf.aestronglyMeasurable
  have hmap_int :=
    integral_map (μ := P.dataMeasure) (φ := fun O : Observation 𝒳 => O.X)
      measurable_observation_X.aemeasurable (f := f) hfm
  rw [hmap] at hmap_int
  exact hmap_int.symm

-- @node: clippedPolicyIncrementTrunc_second_moment
lemma clippedPolicyIncrementTrunc_second_moment {K : ℕ}
    (P : ObservedLaw 𝒳) (q B : ℝ)
    (muHat0 muHat1 eHat : Fin K → 𝒳 → ℝ) (k : Fin K)
    (π : Policy 𝒳) (hwf : WellFormedLaw P) (hπ : Measurable π)
    (hB : 0 ≤ B) :
    ∫ O, (clippedPolicyIncrementTrunc P q B muHat0 muHat1 eHat k π O) ^ 2
        ∂P.dataMeasure
      ≤ B ^ 2 * P.PX.real (disagreementSet π (lawOptimalPolicy P)) := by
  classical
  let D : Set 𝒳 := disagreementSet π (lawOptimalPolicy P)
  let ind : 𝒳 → ℝ := D.indicator (fun _ : 𝒳 => (1 : ℝ))
  have hτmeas : Measurable P.contrast := hwf.2.2.2.1
  have hDmeas : MeasurableSet D :=
    measurableSet_disagreementSet P π hτmeas hπ
  have hind_meas : Measurable ind := measurable_const.indicator hDmeas
  have hBsq_nonneg : 0 ≤ B ^ 2 := sq_nonneg B
  have hcov_meas : Measurable (fun x : 𝒳 => B ^ 2 * ind x) :=
    measurable_const.mul hind_meas
  have hcov_bdd : ∃ M : ℝ, ∀ x : 𝒳, |B ^ 2 * ind x| ≤ M := by
    refine ⟨B ^ 2, ?_⟩
    intro x
    by_cases hx : x ∈ D <;> simp [ind, hx, abs_of_nonneg hBsq_nonneg, hBsq_nonneg]
  have hcov_int : Integrable (fun O : Observation 𝒳 => B ^ 2 * ind O.X)
      P.dataMeasure :=
    integrable_covariate_test P hwf hcov_meas hcov_bdd
  have hpoint :
      ∀ O : Observation 𝒳,
        (clippedPolicyIncrementTrunc P q B muHat0 muHat1 eHat k π O) ^ 2
          ≤ B ^ 2 * ind O.X := by
    intro O
    by_cases hD : π O.X ≠ lawOptimalPolicy P O.X
    · have habs :
          |clippedPolicyIncrementTrunc P q B muHat0 muHat1 eHat k π O| ≤ B :=
        clippedPolicyIncrementTrunc_bound P q B muHat0 muHat1 eHat k π O hB
      have hsq :
          (clippedPolicyIncrementTrunc P q B muHat0 muHat1 eHat k π O) ^ 2
            ≤ B ^ 2 := by
        rw [← sq_abs]
        exact sq_le_sq.mpr (by
          simpa [abs_of_nonneg (abs_nonneg _), abs_of_nonneg hB] using habs)
      simpa [ind, D, disagreementSet, hD] using hsq
    · have hEq : π O.X = lawOptimalPolicy P O.X := not_not.mp hD
      have hgzero :
          clippedPolicyIncrementTrunc P q B muHat0 muHat1 eHat k π O = 0 := by
        simp [clippedPolicyIncrementTrunc, hEq]
      simp [hgzero, ind, D, disagreementSet, hD]
  have hnonneg : 0 ≤ᵐ[P.dataMeasure] fun O : Observation 𝒳 =>
      (clippedPolicyIncrementTrunc P q B muHat0 muHat1 eHat k π O) ^ 2 := by
    filter_upwards with O
    exact sq_nonneg _
  have hle :
      ∫ O, (clippedPolicyIncrementTrunc P q B muHat0 muHat1 eHat k π O) ^ 2
          ∂P.dataMeasure
        ≤ ∫ O, B ^ 2 * ind O.X ∂P.dataMeasure :=
    integral_mono_of_nonneg hnonneg hcov_int (Filter.Eventually.of_forall hpoint)
  have hrhs :
      ∫ O, B ^ 2 * ind O.X ∂P.dataMeasure =
        B ^ 2 * P.PX.real D := by
    calc
      ∫ O, B ^ 2 * ind O.X ∂P.dataMeasure
          = ∫ x, B ^ 2 * ind x ∂P.PX :=
            covariate_integral_eq_px P hwf (fun x : 𝒳 => B ^ 2 * ind x) hcov_meas
      _ = B ^ 2 * ∫ x, ind x ∂P.PX := by
            rw [integral_const_mul]
      _ = B ^ 2 * P.PX.real D := by
            congr 1
            simpa [ind] using integral_indicator_one (μ := P.PX) hDmeas
  simpa [D, hrhs] using hle

private lemma control_test_integral_eq (P : ObservedLaw 𝒳)
    (hwf : WellFormedLaw P) {ψ : 𝒳 → ℝ}
    (hψmeas : Measurable ψ) (hψbdd : ∃ M : ℝ, ∀ x, |ψ x| ≤ M) :
    ∫ O, (1 - boolIndicator O.A) * ψ O.X ∂P.dataMeasure
      = ∫ x, (1 - P.propensity x) * ψ x ∂P.PX := by
  rcases hwf with
    ⟨hPprob, hPXprob, hmap, hτmeas, hpropmeas, hmu0meas, hmu1meas,
      hτdef, hprop01, hA, hAY, hCY⟩
  let hwf' : WellFormedLaw P :=
    ⟨hPprob, hPXprob, hmap, hτmeas, hpropmeas, hmu0meas, hmu1meas,
      hτdef, hprop01, hA, hAY, hCY⟩
  letI : IsProbabilityMeasure P.dataMeasure := hPprob
  letI : IsProbabilityMeasure P.PX := hPXprob
  have hcov_int : Integrable (fun O : Observation 𝒳 => ψ O.X) P.dataMeasure :=
    integrable_covariate_test P hwf' hψmeas hψbdd
  have htr_int :
      Integrable (fun O : Observation 𝒳 => boolIndicator O.A * ψ O.X)
        P.dataMeasure :=
    integrable_treated_test P hwf' hψmeas hψbdd
  have hψ_px : Integrable ψ P.PX :=
    integrable_of_measurable_bounded hψmeas hψbdd
  have heψ_px : Integrable (fun x => P.propensity x * ψ x) P.PX := by
    refine integrable_of_measurable_bounded (hpropmeas.mul hψmeas) ?_
    rcases hψbdd with ⟨M, hM⟩
    refine ⟨max M 0, ?_⟩
    intro x
    have heabs : |P.propensity x| ≤ (1 : ℝ) := by
      exact abs_le.mpr ⟨by linarith [(hprop01 x).1], (hprop01 x).2⟩
    calc
      |P.propensity x * ψ x| = |P.propensity x| * |ψ x| := abs_mul _ _
      _ ≤ 1 * max M 0 := by
        exact mul_le_mul heabs (le_trans (hM x) (le_max_left M 0))
          (abs_nonneg _) zero_le_one
      _ = max M 0 := by ring
  calc
    ∫ O, (1 - boolIndicator O.A) * ψ O.X ∂P.dataMeasure
        = ∫ O, ψ O.X - boolIndicator O.A * ψ O.X ∂P.dataMeasure := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun O => by ring)
    _ = ∫ O, ψ O.X ∂P.dataMeasure
        - ∫ O, boolIndicator O.A * ψ O.X ∂P.dataMeasure := by
          rw [integral_sub hcov_int htr_int]
    _ = ∫ x, ψ x ∂P.PX - ∫ x, P.propensity x * ψ x ∂P.PX := by
          rw [covariate_integral_eq_px P hwf' ψ hψmeas, hA ψ hψmeas hψbdd]
    _ = ∫ x, ψ x - P.propensity x * ψ x ∂P.PX := by
          rw [integral_sub hψ_px heψ_px]
    _ = ∫ x, (1 - P.propensity x) * ψ x ∂P.PX := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun x => by ring)

private lemma bounded_law_mu0 (P : ObservedLaw 𝒳) (hbdd : BoundedOutcome P) :
    ∃ M : ℝ, ∀ x, |P.mu0 x| ≤ M := by
  exact ⟨1, fun x => abs_le.mpr ⟨(hbdd.2 x).1.1, (hbdd.2 x).1.2⟩⟩

private lemma bounded_law_mu1 (P : ObservedLaw 𝒳) (hbdd : BoundedOutcome P) :
    ∃ M : ℝ, ∀ x, |P.mu1 x| ≤ M := by
  exact ⟨1, fun x => abs_le.mpr ⟨(hbdd.2 x).2.1, (hbdd.2 x).2.2⟩⟩

lemma bounded_law_contrast (P : ObservedLaw 𝒳)
    (hwf : WellFormedLaw P) (hbdd : BoundedOutcome P) :
    ∃ M : ℝ, ∀ x, |P.contrast x| ≤ M := by
  rcases hwf with ⟨_, _, _, _, _, _, _, hτeq, _⟩
  refine ⟨2, ?_⟩
  intro x
  have hmu0 : |P.mu0 x| ≤ (1 : ℝ) :=
    abs_le.mpr ⟨(hbdd.2 x).1.1, (hbdd.2 x).1.2⟩
  have hmu1 : |P.mu1 x| ≤ (1 : ℝ) :=
    abs_le.mpr ⟨(hbdd.2 x).2.1, (hbdd.2 x).2.2⟩
  calc
    |P.contrast x| = |P.mu1 x - P.mu0 x| := by rw [hτeq]
    _ ≤ |P.mu1 x| + |P.mu0 x| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add hmu1 hmu0
    _ = (2 : ℝ) := by norm_num

private lemma measurable_clipBias (P : ObservedLaw 𝒳) (q : ℝ)
    {muHat0 muHat1 eHat : 𝒳 → ℝ}
    (hwf : WellFormedLaw P)
    (hμ0meas : Measurable muHat0) (hμ1meas : Measurable muHat1)
    (hemeas : Measurable eHat) :
    Measurable (clipBias P q muHat0 muHat1 eHat) := by
  rcases hwf with
    ⟨_, _, _, _, hpropmeas, hmu0meas, hmu1meas, _⟩
  unfold clipBias
  exact
    ((measurable_clippedPropensity q hemeas).sub hpropmeas).mul
      (((hμ1meas.sub hmu1meas).div (measurable_clippedPropensity q hemeas)).add
        ((hμ0meas.sub hmu0meas).div
          (measurable_const.sub (measurable_clippedPropensity q hemeas))))

private lemma bounded_clipBias (P : ObservedLaw 𝒳) (q : ℝ)
    (muHat0 muHat1 eHat : 𝒳 → ℝ)
    (hwf : WellFormedLaw P) (hbdd : BoundedOutcome P)
    (hμ0bdd : ∃ M : ℝ, ∀ x, |muHat0 x| ≤ M)
    (hμ1bdd : ∃ M : ℝ, ∀ x, |muHat1 x| ≤ M)
    (hq : 0 < q) (hq1 : q < 1) :
    ∃ M : ℝ, ∀ x, |clipBias P q muHat0 muHat1 eHat x| ≤ M := by
  rcases hwf with
    ⟨_, _, _, _, _, _, _, _, hprop01, _⟩
  have hcp_sub_e : ∃ M : ℝ,
      ∀ x, |clippedPropensity q eHat x - P.propensity x| ≤ M := by
    refine ⟨2, ?_⟩
    intro x
    have hcp_pos : 0 < clippedPropensity q eHat x :=
      clippedPropensity_pos q eHat x hq hq1
    have hcp_le : clippedPropensity q eHat x ≤ 1 := by
      have hle := clippedPropensity_le_one_sub q eHat x
      linarith
    have hcp_abs : |clippedPropensity q eHat x| ≤ (1 : ℝ) :=
      abs_le.mpr ⟨by linarith, hcp_le⟩
    have he_abs : |P.propensity x| ≤ (1 : ℝ) :=
      abs_le.mpr ⟨by linarith [(hprop01 x).1], (hprop01 x).2⟩
    calc
      |clippedPropensity q eHat x - P.propensity x|
          ≤ |clippedPropensity q eHat x| + |P.propensity x| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add hcp_abs he_abs
      _ = (2 : ℝ) := by norm_num
  have hΔ1 : ∃ M : ℝ, ∀ x, |muHat1 x - P.mu1 x| ≤ M :=
    bounded_sub hμ1bdd (bounded_law_mu1 P hbdd)
  have hΔ0 : ∃ M : ℝ, ∀ x, |muHat0 x - P.mu0 x| ≤ M :=
    bounded_sub hμ0bdd (bounded_law_mu0 P hbdd)
  have hfrac1 :
      ∃ M : ℝ, ∀ x,
        |(muHat1 x - P.mu1 x) / clippedPropensity q eHat x| ≤ M :=
    bounded_div_clipped q eHat (fun x => muHat1 x - P.mu1 x) hq hq1 hΔ1
  have hfrac0 :
      ∃ M : ℝ, ∀ x,
        |(muHat0 x - P.mu0 x) / (1 - clippedPropensity q eHat x)| ≤ M :=
    bounded_div_one_sub_clipped q eHat (fun x => muHat0 x - P.mu0 x) hq hΔ0
  have hsum := bounded_add hfrac1 hfrac0
  simpa [clipBias] using bounded_mul hcp_sub_e hsum

omit [MeasurableSpace 𝒳] in
private lemma clippedAIPWScore_test_expand_pointwise (q : ℝ)
    (muHat0 muHat1 eHat φ : 𝒳 → ℝ) (O : Observation 𝒳) :
    φ O.X * clippedAIPWScore q muHat0 muHat1 eHat O =
      (((φ O.X * (muHat1 O.X - muHat0 O.X)
          + boolIndicator O.A * O.Y *
              (φ O.X / clippedPropensity q eHat O.X))
        - boolIndicator O.A *
            (muHat1 O.X * φ O.X / clippedPropensity q eHat O.X))
        - (1 - boolIndicator O.A) * O.Y *
            (φ O.X / (1 - clippedPropensity q eHat O.X)))
        + (1 - boolIndicator O.A) *
            (muHat0 O.X * φ O.X / (1 - clippedPropensity q eHat O.X)) := by
  unfold clippedAIPWScore
  ring

private lemma clipBias_integrand_collect_pointwise (P : ObservedLaw 𝒳) (q : ℝ)
    (muHat0 muHat1 eHat φ : 𝒳 → ℝ) (x : 𝒳)
    (hτ : P.contrast x = P.mu1 x - P.mu0 x)
    (hcp : clippedPropensity q eHat x ≠ 0)
    (hden : 1 - clippedPropensity q eHat x ≠ 0) :
    (((φ x * (muHat1 x - muHat0 x)
        + P.propensity x * P.mu1 x *
            (φ x / clippedPropensity q eHat x))
      - P.propensity x *
          (muHat1 x * φ x / clippedPropensity q eHat x))
      - (1 - P.propensity x) * P.mu0 x *
          (φ x / (1 - clippedPropensity q eHat x)))
      + (1 - P.propensity x) *
          (muHat0 x * φ x / (1 - clippedPropensity q eHat x))
      = φ x * (P.contrast x + clipBias P q muHat0 muHat1 eHat x) := by
  rw [hτ]
  unfold clipBias
  field_simp [hcp, hden]
  ring

private lemma ennreal_inv_two_add_inv_two :
    (2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ = 1 := by
  apply (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp
  · rw [ENNReal.toReal_add]
    · norm_num [ENNReal.toReal_inv]
    · rw [ENNReal.inv_ne_top]
      norm_num
    · rw [ENNReal.inv_ne_top]
      norm_num
  · rw [ENNReal.add_ne_top]
    constructor <;> rw [ENNReal.inv_ne_top] <;> norm_num
  · norm_num

private instance instMeasurableSingletonClassObservationReal :
    MeasurableSingletonClass (Observation ℝ) := by
  refine ⟨?_⟩
  intro O
  have hset : MeasurableSet ((fun O' : Observation ℝ => (O'.X, O'.A, O'.Y)) ⁻¹'
      ({(O.X, O.A, O.Y)} : Set (ℝ × Bool × ℝ))) :=
    measurable_observation_tuple (𝒳 := ℝ) (measurableSet_singleton _)
  convert hset using 1
  ext O'
  cases O
  cases O'
  simp

private noncomputable def clipBiasCounterObsT : Observation ℝ :=
  { X := 0, A := true, Y := 0 }

private noncomputable def clipBiasCounterObsF : Observation ℝ :=
  { X := 0, A := false, Y := 0 }

private noncomputable def clipBiasCounterMeasure : Measure (Observation ℝ) :=
  (2 : ENNReal)⁻¹ • Measure.dirac clipBiasCounterObsT
    + (2 : ENNReal)⁻¹ • Measure.dirac clipBiasCounterObsF

private noncomputable def clipBiasCounterLaw : ObservedLaw ℝ :=
  { dataMeasure := clipBiasCounterMeasure
    PX := Measure.dirac (0 : ℝ)
    contrast := fun _ => 0
    propensity := fun _ => (1 / 2 : ℝ)
    mu0 := fun _ => 0
    mu1 := fun _ => 0 }

private lemma integral_clipBiasCounterMeasure (f : Observation ℝ → ℝ) :
    ∫ O, f O ∂clipBiasCounterMeasure =
      (1 / 2 : ℝ) * f clipBiasCounterObsT + (1 / 2 : ℝ) * f clipBiasCounterObsF := by
  unfold clipBiasCounterMeasure
  have hne : (2 : ENNReal)⁻¹ ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  have hIntT : Integrable f ((2 : ENNReal)⁻¹ • Measure.dirac clipBiasCounterObsT) := by
    exact (integrable_dirac (a := clipBiasCounterObsT) (f := f) (by finiteness)).smul_measure hne
  have hIntF : Integrable f ((2 : ENNReal)⁻¹ • Measure.dirac clipBiasCounterObsF) := by
    exact (integrable_dirac (a := clipBiasCounterObsF) (f := f) (by finiteness)).smul_measure hne
  rw [integral_add_measure hIntT hIntF]
  rw [integral_smul_measure, integral_smul_measure]
  rw [integral_dirac, integral_dirac]
  norm_num [ENNReal.toReal_inv]

private lemma clipBiasCounterLaw_wf : WellFormedLaw clipBiasCounterLaw := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    change clipBiasCounterMeasure Set.univ = 1
    unfold clipBiasCounterMeasure
    simp [ennreal_inv_two_add_inv_two]
  · unfold clipBiasCounterLaw
    infer_instance
  · change clipBiasCounterMeasure.map (fun O => O.X) = Measure.dirac (0 : ℝ)
    unfold clipBiasCounterMeasure clipBiasCounterObsT clipBiasCounterObsF
    rw [Measure.map_add _ _ measurable_observation_X]
    rw [Measure.map_smul, Measure.map_smul]
    rw [Measure.map_dirac, Measure.map_dirac]
    rw [← add_smul, ennreal_inv_two_add_inv_two, one_smul]
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · intro x
    simp [clipBiasCounterLaw]
  · intro x
    norm_num [clipBiasCounterLaw]
  · intro φ hφmeas hφbdd
    change
      ∫ O, boolIndicator O.A * φ O.X ∂clipBiasCounterMeasure
        = ∫ x, (1 / 2 : ℝ) * φ x ∂Measure.dirac (0 : ℝ)
    rw [integral_clipBiasCounterMeasure, integral_dirac]
    simp [clipBiasCounterObsT, clipBiasCounterObsF, boolIndicator]
  · intro φ hφmeas hφbdd
    change
      ∫ O, boolIndicator O.A * O.Y * φ O.X ∂clipBiasCounterMeasure
        = ∫ x, (1 / 2 : ℝ) * 0 * φ x ∂Measure.dirac (0 : ℝ)
    rw [integral_clipBiasCounterMeasure, integral_dirac]
    simp [clipBiasCounterObsT, clipBiasCounterObsF, boolIndicator]
  · intro φ hφmeas hφbdd
    change
      ∫ O, (1 - boolIndicator O.A) * O.Y * φ O.X ∂clipBiasCounterMeasure
        = ∫ x, (1 - (1 / 2 : ℝ)) * 0 * φ x ∂Measure.dirac (0 : ℝ)
    rw [integral_clipBiasCounterMeasure, integral_dirac]
    simp [clipBiasCounterObsT, clipBiasCounterObsF, boolIndicator]

private lemma clipBiasCounterLaw_bounded : BoundedOutcome clipBiasCounterLaw := by
  constructor
  · unfold clipBiasCounterLaw clipBiasCounterMeasure clipBiasCounterObsT clipBiasCounterObsF
    simp
  · intro x
    simp [clipBiasCounterLaw]

private lemma clipBiasCounterLaw_pos : Positivity clipBiasCounterLaw := by
  unfold Positivity clipBiasCounterLaw
  simp
  norm_num

private lemma clipBiasCounterLaw_overlap :
    (1 / 4 : ℝ) < overlap clipBiasCounterLaw (0 : ℝ) := by
  norm_num [clipBiasCounterLaw, overlap]

private lemma clipBiasCounterLaw_bias_ne :
    clipBias clipBiasCounterLaw (1 / 4)
      (fun _ : ℝ => 0) (fun _ : ℝ => 1) (fun _ : ℝ => 0) (0 : ℝ) ≠ 0 := by
  norm_num [clipBiasCounterLaw, clipBias, clippedPropensity]

-- @node: lem:clip-bias
/-- `lem:clip-bias`. Exact clipped-score conditional-mean drift identity
`E_P[Γ_q(O;η̄)∣X]-τ_P = (ē_q-e_P)(Δ₁/ē_q+Δ₀/(1-ē_q)) = b_q`. This is the GENUINE
conditional-expectation identity: its first conjunct is stated against the data law
`P.dataMeasure` via the observed-law SEMANTIC conditions packaged in
`WellFormedLaw P` (which pin `e_P=P(A=1∣X)`, `μ_a=E[Y∣A=a,X]`), so it is NOT a
free-standing algebraic identity over the nuisance fields — it ties the
`dataMeasure`-integral of the clipped score to the closed-form drift `b_q = clipBias`.
In tested (conditional-expectation defining) form: for every bounded measurable
covariate test function `φ`,
`∫ φ(X) Γ_q dP - ∫ φ τ_P dP_X = ∫ φ b_q dP_X`, i.e. `E_P[Γ_q∣X] = τ_P + b_q` a.s.
`hbdd` (bounded outcomes) is the regularity premise making the score integrals
genuine. The second conjunct records the NL CANCELLATION characterization read off
`b_q`: the drift vanishes WHERE the clipped propensity already equals the true
propensity (`ē_q(x)=e_P(x)`) or both regression errors vanish (`μ̂_a(x)=μ_a(x)`) —
so double-robust cancellation does NOT follow merely from `p_P(x)>q`.

The THIRD conjunct records the note's NEGATIVE conclusion that the prior lemma
OMITTED: under the frozen assumptions alone (bounded outcomes, positivity, the
observed-law semantics) NO additive clipped-region bound of the form previously
asserted is derivable. We encode this impossibility faithfully as the existence of
a COUNTEREXAMPLE configuration — a well-formed law `P'` satisfying the very same
frozen assumptions (`WellFormedLaw`, `BoundedOutcome`, `Positivity`) and a clip
`q' ∈ (0,1)` with a point `x` strictly INSIDE the clipped region (`q' < p_{P'}(x)`,
i.e. `p_P > q`) at which the clip-bias drift is NONZERO. Its existence shows that
`p_P(x) > q` alone (under the frozen assumptions) does not force the additive
clipped-region cancellation, so no such bound is derivable. The carrier is fixed to
`ℝ` so the witness does not depend on the ambient `𝒳` being inhabited.

This conditional-mean drift identity is enumeration-independent (it does not
reference the ERM `enum`), exactly as the note's `lem:clip-bias` is stated for an
arbitrary measurable plug-in nuisance triple with no dense-`Π₀` condition; so its
signature faithfully carries no `enum`/skeleton hypothesis. -/
lemma clip_bias (P : ObservedLaw 𝒳) (q : ℝ) (muHat0 muHat1 eHat : 𝒳 → ℝ)
    (hwf : WellFormedLaw P) (hbdd : BoundedOutcome P) (hpos : Positivity P)
    -- regularity: nuisances are measurable bounded plug-ins (BoundedCrossfitNuisances)
    (hμ0meas : Measurable muHat0) (hμ1meas : Measurable muHat1)
    (hemeas : Measurable eHat)
    (hμ0bdd : ∃ M : ℝ, ∀ x, |muHat0 x| ≤ M)
    (hμ1bdd : ∃ M : ℝ, ∀ x, |muHat1 x| ≤ M)
    (hq : 0 < q) (hq1 : q < 1)
    (φ : 𝒳 → ℝ) (hφmeas : Measurable φ) (hφbdd : ∃ M : ℝ, ∀ x, |φ x| ≤ M) :
    ((∫ O, φ O.X * clippedAIPWScore q muHat0 muHat1 eHat O ∂P.dataMeasure)
        - ∫ x, φ x * P.contrast x ∂P.PX
      = ∫ x, φ x * clipBias P q muHat0 muHat1 eHat x ∂P.PX) ∧
    (∀ x : 𝒳, clippedPropensity q eHat x = P.propensity x ∨
          (muHat1 x = P.mu1 x ∧ muHat0 x = P.mu0 x) →
        clipBias P q muHat0 muHat1 eHat x = 0) ∧
    (∃ (P' : ObservedLaw ℝ) (q' : ℝ) (m0 m1 e' : ℝ → ℝ) (x : ℝ),
        WellFormedLaw P' ∧ BoundedOutcome P' ∧ Positivity P' ∧
          0 < q' ∧ q' < 1 ∧ q' < overlap P' x ∧
          clipBias P' q' m0 m1 e' x ≠ 0)
    := by
  have _hpos_retained : Positivity P := hpos
  rcases hwf with
    ⟨hPprob, hPXprob, hmap, hτmeas, hpropmeas, hPmu0meas, hPmu1meas,
      hτdef, hprop01, hA, hAY, hCY⟩
  let hwf' : WellFormedLaw P :=
    ⟨hPprob, hPXprob, hmap, hτmeas, hpropmeas, hPmu0meas, hPmu1meas,
      hτdef, hprop01, hA, hAY, hCY⟩
  letI : IsProbabilityMeasure P.dataMeasure := hPprob
  letI : IsProbabilityMeasure P.PX := hPXprob
  have hcpmeas : Measurable (clippedPropensity q eHat) :=
    measurable_clippedPropensity q hemeas
  have hψ0meas :
      Measurable (fun x => φ x * (muHat1 x - muHat0 x)) :=
    hφmeas.mul (hμ1meas.sub hμ0meas)
  have hψ0bdd :
      ∃ M : ℝ, ∀ x, |φ x * (muHat1 x - muHat0 x)| ≤ M :=
    bounded_mul hφbdd (bounded_sub hμ1bdd hμ0bdd)
  have hψ1meas :
      Measurable (fun x => φ x / clippedPropensity q eHat x) :=
    hφmeas.div hcpmeas
  have hψ1bdd :
      ∃ M : ℝ, ∀ x, |φ x / clippedPropensity q eHat x| ≤ M :=
    bounded_div_clipped q eHat φ hq hq1 hφbdd
  have hψ2meas :
      Measurable (fun x => muHat1 x * φ x / clippedPropensity q eHat x) :=
    (hμ1meas.mul hφmeas).div hcpmeas
  have hψ2bdd :
      ∃ M : ℝ, ∀ x, |muHat1 x * φ x / clippedPropensity q eHat x| ≤ M :=
    bounded_mul_div_clipped q eHat muHat1 φ hq hq1 hμ1bdd hφbdd
  have hψ3meas :
      Measurable (fun x => φ x / (1 - clippedPropensity q eHat x)) :=
    hφmeas.div (measurable_const.sub hcpmeas)
  have hψ3bdd :
      ∃ M : ℝ, ∀ x, |φ x / (1 - clippedPropensity q eHat x)| ≤ M :=
    bounded_div_one_sub_clipped q eHat φ hq hφbdd
  have hψ4meas :
      Measurable (fun x => muHat0 x * φ x / (1 - clippedPropensity q eHat x)) :=
    (hμ0meas.mul hφmeas).div (measurable_const.sub hcpmeas)
  have hψ4bdd :
      ∃ M : ℝ, ∀ x,
        |muHat0 x * φ x / (1 - clippedPropensity q eHat x)| ≤ M :=
    bounded_mul_div_one_sub_clipped q eHat muHat0 φ hq hμ0bdd hφbdd
  have hf0_data :
      Integrable (fun O : Observation 𝒳 => φ O.X * (muHat1 O.X - muHat0 O.X))
        P.dataMeasure :=
    integrable_covariate_test P hwf' hψ0meas hψ0bdd
  have hf1_data :
      Integrable
        (fun O : Observation 𝒳 =>
          boolIndicator O.A * O.Y * (φ O.X / clippedPropensity q eHat O.X))
        P.dataMeasure :=
    integrable_treated_outcome_test P hwf' hbdd hψ1meas hψ1bdd
  have hf2_data :
      Integrable
        (fun O : Observation 𝒳 =>
          boolIndicator O.A *
            (muHat1 O.X * φ O.X / clippedPropensity q eHat O.X))
        P.dataMeasure :=
    integrable_treated_test P hwf' hψ2meas hψ2bdd
  have hf3_data :
      Integrable
        (fun O : Observation 𝒳 =>
          (1 - boolIndicator O.A) * O.Y *
            (φ O.X / (1 - clippedPropensity q eHat O.X)))
        P.dataMeasure :=
    integrable_control_outcome_test P hwf' hbdd hψ3meas hψ3bdd
  have hf4_data :
      Integrable
        (fun O : Observation 𝒳 =>
          (1 - boolIndicator O.A) *
            (muHat0 O.X * φ O.X / (1 - clippedPropensity q eHat O.X)))
        P.dataMeasure :=
    integrable_control_test P hwf' hψ4meas hψ4bdd
  have hscore_split :
      ∫ O, φ O.X * clippedAIPWScore q muHat0 muHat1 eHat O ∂P.dataMeasure
        =
        ((((∫ O, φ O.X * (muHat1 O.X - muHat0 O.X) ∂P.dataMeasure)
          + ∫ O, boolIndicator O.A * O.Y *
              (φ O.X / clippedPropensity q eHat O.X) ∂P.dataMeasure)
          - ∫ O, boolIndicator O.A *
              (muHat1 O.X * φ O.X / clippedPropensity q eHat O.X) ∂P.dataMeasure)
          - ∫ O, (1 - boolIndicator O.A) * O.Y *
              (φ O.X / (1 - clippedPropensity q eHat O.X)) ∂P.dataMeasure
          + ∫ O, (1 - boolIndicator O.A) *
              (muHat0 O.X * φ O.X / (1 - clippedPropensity q eHat O.X))
              ∂P.dataMeasure) := by
    calc
      ∫ O, φ O.X * clippedAIPWScore q muHat0 muHat1 eHat O ∂P.dataMeasure
          =
        ∫ O, (((φ O.X * (muHat1 O.X - muHat0 O.X)
            + boolIndicator O.A * O.Y *
                (φ O.X / clippedPropensity q eHat O.X))
          - boolIndicator O.A *
              (muHat1 O.X * φ O.X / clippedPropensity q eHat O.X))
          - (1 - boolIndicator O.A) * O.Y *
              (φ O.X / (1 - clippedPropensity q eHat O.X)))
          + (1 - boolIndicator O.A) *
              (muHat0 O.X * φ O.X / (1 - clippedPropensity q eHat O.X))
          ∂P.dataMeasure := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall
              (clippedAIPWScore_test_expand_pointwise q muHat0 muHat1 eHat φ)
      _ =
        ((((∫ O, φ O.X * (muHat1 O.X - muHat0 O.X) ∂P.dataMeasure)
          + ∫ O, boolIndicator O.A * O.Y *
              (φ O.X / clippedPropensity q eHat O.X) ∂P.dataMeasure)
          - ∫ O, boolIndicator O.A *
              (muHat1 O.X * φ O.X / clippedPropensity q eHat O.X) ∂P.dataMeasure)
          - ∫ O, (1 - boolIndicator O.A) * O.Y *
              (φ O.X / (1 - clippedPropensity q eHat O.X)) ∂P.dataMeasure
          + ∫ O, (1 - boolIndicator O.A) *
              (muHat0 O.X * φ O.X / (1 - clippedPropensity q eHat O.X))
              ∂P.dataMeasure) := by
            let f0 : Observation 𝒳 → ℝ :=
              fun O => φ O.X * (muHat1 O.X - muHat0 O.X)
            let f1 : Observation 𝒳 → ℝ :=
              fun O => boolIndicator O.A * O.Y *
                (φ O.X / clippedPropensity q eHat O.X)
            let f2 : Observation 𝒳 → ℝ :=
              fun O => boolIndicator O.A *
                (muHat1 O.X * φ O.X / clippedPropensity q eHat O.X)
            let f3 : Observation 𝒳 → ℝ :=
              fun O => (1 - boolIndicator O.A) * O.Y *
                (φ O.X / (1 - clippedPropensity q eHat O.X))
            let f4 : Observation 𝒳 → ℝ :=
              fun O => (1 - boolIndicator O.A) *
                (muHat0 O.X * φ O.X / (1 - clippedPropensity q eHat O.X))
            change
              ∫ O, (((f0 O + f1 O) - f2 O) - f3 O) + f4 O ∂P.dataMeasure
                =
              ((((∫ O, f0 O ∂P.dataMeasure) + ∫ O, f1 O ∂P.dataMeasure)
                - ∫ O, f2 O ∂P.dataMeasure)
                - ∫ O, f3 O ∂P.dataMeasure)
                + ∫ O, f4 O ∂P.dataMeasure
            have hs4 :
                ∫ O, (((f0 O + f1 O) - f2 O) - f3 O) + f4 O ∂P.dataMeasure
                  =
                ∫ O, ((f0 O + f1 O) - f2 O) - f3 O ∂P.dataMeasure
                  + ∫ O, f4 O ∂P.dataMeasure := by
              simpa [f0, f1, f2, f3, f4, Pi.add_apply, Pi.sub_apply] using
                (integral_add (((hf0_data.add hf1_data).sub hf2_data).sub hf3_data)
                  hf4_data)
            have hs3 :
                ∫ O, ((f0 O + f1 O) - f2 O) - f3 O ∂P.dataMeasure
                  =
                ∫ O, (f0 O + f1 O) - f2 O ∂P.dataMeasure
                  - ∫ O, f3 O ∂P.dataMeasure := by
              simpa [f0, f1, f2, f3, Pi.add_apply, Pi.sub_apply] using
                (integral_sub ((hf0_data.add hf1_data).sub hf2_data) hf3_data)
            have hs2 :
                ∫ O, (f0 O + f1 O) - f2 O ∂P.dataMeasure
                  =
                ∫ O, f0 O + f1 O ∂P.dataMeasure
                  - ∫ O, f2 O ∂P.dataMeasure := by
              simpa [f0, f1, f2, Pi.add_apply, Pi.sub_apply] using
                (integral_sub (hf0_data.add hf1_data) hf2_data)
            have hs1 :
                ∫ O, f0 O + f1 O ∂P.dataMeasure
                  =
                ∫ O, f0 O ∂P.dataMeasure + ∫ O, f1 O ∂P.dataMeasure := by
              simpa [f0, f1, Pi.add_apply] using
                (integral_add hf0_data hf1_data)
            rw [hs4, hs3, hs2, hs1]
  have hI0 :
      ∫ O, φ O.X * (muHat1 O.X - muHat0 O.X) ∂P.dataMeasure
        = ∫ x, φ x * (muHat1 x - muHat0 x) ∂P.PX :=
    covariate_integral_eq_px P hwf' (fun x => φ x * (muHat1 x - muHat0 x))
      hψ0meas
  have hI1 :
      ∫ O, boolIndicator O.A * O.Y *
          (φ O.X / clippedPropensity q eHat O.X) ∂P.dataMeasure
        =
      ∫ x, P.propensity x * P.mu1 x *
          (φ x / clippedPropensity q eHat x) ∂P.PX :=
    hAY (fun x => φ x / clippedPropensity q eHat x) hψ1meas hψ1bdd
  have hI2 :
      ∫ O, boolIndicator O.A *
          (muHat1 O.X * φ O.X / clippedPropensity q eHat O.X) ∂P.dataMeasure
        =
      ∫ x, P.propensity x *
          (muHat1 x * φ x / clippedPropensity q eHat x) ∂P.PX :=
    hA (fun x => muHat1 x * φ x / clippedPropensity q eHat x) hψ2meas hψ2bdd
  have hI3 :
      ∫ O, (1 - boolIndicator O.A) * O.Y *
          (φ O.X / (1 - clippedPropensity q eHat O.X)) ∂P.dataMeasure
        =
      ∫ x, (1 - P.propensity x) * P.mu0 x *
          (φ x / (1 - clippedPropensity q eHat x)) ∂P.PX :=
    hCY (fun x => φ x / (1 - clippedPropensity q eHat x)) hψ3meas hψ3bdd
  have hI4 :
      ∫ O, (1 - boolIndicator O.A) *
          (muHat0 O.X * φ O.X / (1 - clippedPropensity q eHat O.X))
          ∂P.dataMeasure
        =
      ∫ x, (1 - P.propensity x) *
          (muHat0 x * φ x / (1 - clippedPropensity q eHat x)) ∂P.PX :=
    control_test_integral_eq P hwf' hψ4meas hψ4bdd
  have hscore_px :
      ∫ O, φ O.X * clippedAIPWScore q muHat0 muHat1 eHat O ∂P.dataMeasure
        =
        ((((∫ x, φ x * (muHat1 x - muHat0 x) ∂P.PX)
          + ∫ x, P.propensity x * P.mu1 x *
              (φ x / clippedPropensity q eHat x) ∂P.PX)
          - ∫ x, P.propensity x *
              (muHat1 x * φ x / clippedPropensity q eHat x) ∂P.PX)
          - ∫ x, (1 - P.propensity x) * P.mu0 x *
              (φ x / (1 - clippedPropensity q eHat x)) ∂P.PX
          + ∫ x, (1 - P.propensity x) *
              (muHat0 x * φ x / (1 - clippedPropensity q eHat x)) ∂P.PX) := by
    rw [hscore_split, hI0, hI1, hI2, hI3, hI4]
  have hpropbdd : ∃ M : ℝ, ∀ x, |P.propensity x| ≤ M := by
    refine ⟨1, ?_⟩
    intro x
    exact abs_le.mpr ⟨by linarith [(hprop01 x).1], (hprop01 x).2⟩
  have honepropbdd : ∃ M : ℝ, ∀ x, |1 - P.propensity x| ≤ M := by
    refine ⟨1, ?_⟩
    intro x
    exact abs_le.mpr ⟨by linarith [(hprop01 x).2], by linarith [(hprop01 x).1]⟩
  have hg0_int :
      Integrable (fun x => φ x * (muHat1 x - muHat0 x)) P.PX :=
    integrable_of_measurable_bounded hψ0meas hψ0bdd
  have hg1_int :
      Integrable
        (fun x => P.propensity x * P.mu1 x *
          (φ x / clippedPropensity q eHat x)) P.PX := by
    refine integrable_of_measurable_bounded
      ((hpropmeas.mul hPmu1meas).mul hψ1meas) ?_
    exact bounded_mul (bounded_mul hpropbdd (bounded_law_mu1 P hbdd)) hψ1bdd
  have hg2_int :
      Integrable
        (fun x => P.propensity x *
          (muHat1 x * φ x / clippedPropensity q eHat x)) P.PX := by
    refine integrable_of_measurable_bounded (hpropmeas.mul hψ2meas) ?_
    exact bounded_mul hpropbdd hψ2bdd
  have hg3_int :
      Integrable
        (fun x => (1 - P.propensity x) * P.mu0 x *
          (φ x / (1 - clippedPropensity q eHat x))) P.PX := by
    refine integrable_of_measurable_bounded
      (((measurable_const.sub hpropmeas).mul hPmu0meas).mul hψ3meas) ?_
    exact bounded_mul (bounded_mul honepropbdd (bounded_law_mu0 P hbdd)) hψ3bdd
  have hg4_int :
      Integrable
        (fun x => (1 - P.propensity x) *
          (muHat0 x * φ x / (1 - clippedPropensity q eHat x))) P.PX := by
    refine integrable_of_measurable_bounded
      ((measurable_const.sub hpropmeas).mul hψ4meas) ?_
    exact bounded_mul honepropbdd hψ4bdd
  have hτφ_int :
      Integrable (fun x => φ x * P.contrast x) P.PX := by
    refine integrable_of_measurable_bounded (hφmeas.mul hτmeas) ?_
    exact bounded_mul hφbdd (bounded_law_contrast P hwf' hbdd)
  have hbφ_int :
      Integrable (fun x => φ x * clipBias P q muHat0 muHat1 eHat x) P.PX := by
    refine integrable_of_measurable_bounded
      (hφmeas.mul (measurable_clipBias P q hwf' hμ0meas hμ1meas hemeas)) ?_
    exact bounded_mul hφbdd
      (bounded_clipBias P q muHat0 muHat1 eHat hwf' hbdd hμ0bdd hμ1bdd hq hq1)
  have hpx_collect :
      ((((∫ x, φ x * (muHat1 x - muHat0 x) ∂P.PX)
        + ∫ x, P.propensity x * P.mu1 x *
            (φ x / clippedPropensity q eHat x) ∂P.PX)
        - ∫ x, P.propensity x *
            (muHat1 x * φ x / clippedPropensity q eHat x) ∂P.PX)
        - ∫ x, (1 - P.propensity x) * P.mu0 x *
            (φ x / (1 - clippedPropensity q eHat x)) ∂P.PX
        + ∫ x, (1 - P.propensity x) *
            (muHat0 x * φ x / (1 - clippedPropensity q eHat x)) ∂P.PX)
      =
        ∫ x, φ x * P.contrast x ∂P.PX
          + ∫ x, φ x * clipBias P q muHat0 muHat1 eHat x ∂P.PX := by
    calc
      ((((∫ x, φ x * (muHat1 x - muHat0 x) ∂P.PX)
        + ∫ x, P.propensity x * P.mu1 x *
            (φ x / clippedPropensity q eHat x) ∂P.PX)
        - ∫ x, P.propensity x *
            (muHat1 x * φ x / clippedPropensity q eHat x) ∂P.PX)
        - ∫ x, (1 - P.propensity x) * P.mu0 x *
            (φ x / (1 - clippedPropensity q eHat x)) ∂P.PX
        + ∫ x, (1 - P.propensity x) *
            (muHat0 x * φ x / (1 - clippedPropensity q eHat x)) ∂P.PX)
          =
        ∫ x, ((((φ x * (muHat1 x - muHat0 x)
            + P.propensity x * P.mu1 x *
                (φ x / clippedPropensity q eHat x))
          - P.propensity x *
              (muHat1 x * φ x / clippedPropensity q eHat x))
          - (1 - P.propensity x) * P.mu0 x *
              (φ x / (1 - clippedPropensity q eHat x)))
          + (1 - P.propensity x) *
              (muHat0 x * φ x / (1 - clippedPropensity q eHat x))
          )
          ∂P.PX := by
            let g0 : 𝒳 → ℝ := fun x => φ x * (muHat1 x - muHat0 x)
            let g1 : 𝒳 → ℝ :=
              fun x => P.propensity x * P.mu1 x *
                (φ x / clippedPropensity q eHat x)
            let g2 : 𝒳 → ℝ :=
              fun x => P.propensity x *
                (muHat1 x * φ x / clippedPropensity q eHat x)
            let g3 : 𝒳 → ℝ :=
              fun x => (1 - P.propensity x) * P.mu0 x *
                (φ x / (1 - clippedPropensity q eHat x))
            let g4 : 𝒳 → ℝ :=
              fun x => (1 - P.propensity x) *
                (muHat0 x * φ x / (1 - clippedPropensity q eHat x))
            change
              ((((∫ x, g0 x ∂P.PX) + ∫ x, g1 x ∂P.PX)
                - ∫ x, g2 x ∂P.PX)
                - ∫ x, g3 x ∂P.PX)
                + ∫ x, g4 x ∂P.PX
                =
              ∫ x, (((g0 x + g1 x) - g2 x) - g3 x) + g4 x ∂P.PX
            symm
            have hs4 :
                ∫ x, (((g0 x + g1 x) - g2 x) - g3 x) + g4 x ∂P.PX
                  =
                ∫ x, ((g0 x + g1 x) - g2 x) - g3 x ∂P.PX
                  + ∫ x, g4 x ∂P.PX := by
              simpa [g0, g1, g2, g3, g4, Pi.add_apply, Pi.sub_apply] using
                (integral_add (((hg0_int.add hg1_int).sub hg2_int).sub hg3_int)
                  hg4_int)
            have hs3 :
                ∫ x, ((g0 x + g1 x) - g2 x) - g3 x ∂P.PX
                  =
                ∫ x, (g0 x + g1 x) - g2 x ∂P.PX
                  - ∫ x, g3 x ∂P.PX := by
              simpa [g0, g1, g2, g3, Pi.add_apply, Pi.sub_apply] using
                (integral_sub ((hg0_int.add hg1_int).sub hg2_int) hg3_int)
            have hs2 :
                ∫ x, (g0 x + g1 x) - g2 x ∂P.PX
                  =
                ∫ x, g0 x + g1 x ∂P.PX
                  - ∫ x, g2 x ∂P.PX := by
              simpa [g0, g1, g2, Pi.add_apply, Pi.sub_apply] using
                (integral_sub (hg0_int.add hg1_int) hg2_int)
            have hs1 :
                ∫ x, g0 x + g1 x ∂P.PX
                  =
                ∫ x, g0 x ∂P.PX + ∫ x, g1 x ∂P.PX := by
              simpa [g0, g1, Pi.add_apply] using
                (integral_add hg0_int hg1_int)
            rw [hs4, hs3, hs2, hs1]
      _ = ∫ x, φ x * P.contrast x
            + φ x * clipBias P q muHat0 muHat1 eHat x ∂P.PX := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun x => by
              have hcp_ne : clippedPropensity q eHat x ≠ 0 :=
                ne_of_gt (clippedPropensity_pos q eHat x hq hq1)
              have hden_ne : 1 - clippedPropensity q eHat x ≠ 0 :=
                ne_of_gt (one_sub_clippedPropensity_pos q eHat x hq)
              calc
                ((((φ x * (muHat1 x - muHat0 x)
                    + P.propensity x * P.mu1 x *
                        (φ x / clippedPropensity q eHat x))
                  - P.propensity x *
                      (muHat1 x * φ x / clippedPropensity q eHat x))
                  - (1 - P.propensity x) * P.mu0 x *
                      (φ x / (1 - clippedPropensity q eHat x)))
                  + (1 - P.propensity x) *
                      (muHat0 x * φ x / (1 - clippedPropensity q eHat x))
                    )
                    = φ x * (P.contrast x
                        + clipBias P q muHat0 muHat1 eHat x) :=
                      clipBias_integrand_collect_pointwise P q muHat0 muHat1 eHat φ x
                        (hτdef x) hcp_ne hden_ne
                _ = φ x * P.contrast x
                    + φ x * clipBias P q muHat0 muHat1 eHat x := by
                      ring)
      _ = ∫ x, φ x * P.contrast x ∂P.PX
          + ∫ x, φ x * clipBias P q muHat0 muHat1 eHat x ∂P.PX := by
            simpa [Pi.add_apply] using integral_add hτφ_int hbφ_int
  refine ⟨?_, ?_, ?_⟩
  · calc
      (∫ O, φ O.X * clippedAIPWScore q muHat0 muHat1 eHat O ∂P.dataMeasure)
          - ∫ x, φ x * P.contrast x ∂P.PX
          =
        (∫ x, φ x * P.contrast x ∂P.PX
          + ∫ x, φ x * clipBias P q muHat0 muHat1 eHat x ∂P.PX)
          - ∫ x, φ x * P.contrast x ∂P.PX := by
            rw [hscore_px, hpx_collect]
      _ = ∫ x, φ x * clipBias P q muHat0 muHat1 eHat x ∂P.PX := by
            ring
  · intro x hx
    unfold clipBias
    rcases hx with hcp_eq | ⟨h1, h0⟩
    · simp [hcp_eq]
    · simp [h1, h0]
  · refine ⟨clipBiasCounterLaw, 1 / 4, (fun _ : ℝ => 0), (fun _ : ℝ => 1),
      (fun _ : ℝ => 0), 0, ?_⟩
    exact ⟨clipBiasCounterLaw_wf, clipBiasCounterLaw_bounded, clipBiasCounterLaw_pos,
      by norm_num, by norm_num, clipBiasCounterLaw_overlap, clipBiasCounterLaw_bias_ne⟩


end CausalSmith.Stat.PolicyRegretMarginOverlap
