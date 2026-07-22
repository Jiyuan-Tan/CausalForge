/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Marginal Sensitivity Model — closed-form bounds for `E[Y(1)]`

The MSM interval endpoints `msmUpper Λ`, `msmLower Λ` (the `sSup`/`sInf` of the candidate IPW mean
over the odds-ratio ambiguity set `MSMSet Λ`, from `Setup.lean`) have a **closed form**. Because
the ambiguity set is the literal Zhao–Small–Bhattacharya odds-ratio box (no calibration constraint),
the optimization over candidate complete propensities is *pointwise separable*: writing the
inverse-propensity weight `w = 1/ẽ`, the candidate mean is `∫ A·Y·w` with `w` ranging pointwise over
`[wMin, wMax]`, where

    wMin(X) = 1 + (1 − e(X)) / (Λ · e(X)),   wMax(X) = 1 + Λ · (1 − e(X)) / e(X),

(`e(X) = propScore true`). The worst case puts `w = wMax` where `Y ≥ 0` and `w = wMin` where `Y < 0`,
giving the closed form

    msmUpper Λ = E[ A · Y · (wMax if Y ≥ 0 else wMin) ],
    msmLower Λ = E[ A · Y · (wMin if Y ≥ 0 else wMax) ].

The proof is the two-sided `sSup`/`sInf` argument: the pointwise box bound shows every candidate mean
is `≤` (resp. `≥`) the closed form, and the boundary weight `w* = (wMax if Y ≥ 0 else wMin)` is
attained by a feasible `ẽ* = 1/w* ∈ MSMSet Λ`, so the closed form is the genuine extremum.

These are valid (and equal to the sup/inf over the ZSB box). They are *not* the sharp Dorn-Guo (2022)
bounds, which additionally impose a weight-calibration constraint that tightens the box into a
conditional-quantile / CVaR balancing functional; the calibrated sharp bounds are developed in the
`Sharp`, `QuantileBalance`, and cutoff-construction modules.
-/

import Causalean.PO.ID.Partial.Sensitivity.MSM.Setup

/-! # Closed-form uncalibrated marginal-sensitivity bounds

This file computes the Zhao-Small-Bhattacharya box bounds for `E[Y(1)]`. Because
the uncalibrated odds-ratio ambiguity set is pointwise separable, the supremum
and infimum of the candidate mean are attained by boundary inverse-propensity
weights selected according to the sign of the observed outcome.

The public surface consists of the endpoint weights `wMin` and `wMax`, the
integral forms `msmUpperForm` and `msmLowerForm`, and the closed-form identities
`msmUpper_eq` and `msmLower_eq`.
-/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- The **smallest** admissible inverse-propensity weight at sensitivity level `Λ`:
`wMin = 1 + (1 − e(X)) / (Λ · e(X))`, the `OR = 1/Λ` endpoint of the odds-ratio box. -/
noncomputable def wMin (Λ : ℝ) (ω : P.Ω) : ℝ :=
  1 + (1 - S.propScore true ω) / (Λ * S.propScore true ω)

/-- The **largest** admissible inverse-propensity weight at sensitivity level `Λ`:
`wMax = 1 + Λ · (1 − e(X)) / e(X)`, the `OR = Λ` endpoint of the odds-ratio box. -/
noncomputable def wMax (Λ : ℝ) (ω : P.Ω) : ℝ :=
  1 + Λ * (1 - S.propScore true ω) / S.propScore true ω

/-- The closed-form **upper** integrand: `wMax` where `Y ≥ 0`, `wMin` where `Y < 0`. -/
noncomputable def msmUpperForm (Λ : ℝ) : ℝ :=
  ∫ ω, S.dVar.indicator true ω * S.factualY ω
      * (if 0 ≤ S.factualY ω then S.wMax Λ ω else S.wMin Λ ω) ∂P.μ

/-- The closed-form **lower** bound: `wMin` where `Y ≥ 0`, `wMax` where `Y < 0`. -/
noncomputable def msmLowerForm (Λ : ℝ) : ℝ :=
  ∫ ω, S.dVar.indicator true ω * S.factualY ω
      * (if 0 ≤ S.factualY ω then S.wMin Λ ω else S.wMax Λ ω) ∂P.μ

/-- Algebraic box characterization (one point). For `e, ẽ ∈ (0,1)` and `Λ > 0`, with
`w = 1/ẽ`, the odds-ratio bound `1/Λ ≤ OR ẽ e ∧ OR ẽ e ≤ Λ` is equivalent to
`wMin Λ ≤ w ∧ w ≤ wMax Λ` (pointwise). -/
private lemma OR_box_iff {Λ e et : ℝ} (hΛ : 0 < Λ)
    (he0 : 0 < e) (he1 : e < 1) (het0 : 0 < et) (het1 : et < 1) :
    (1 / Λ ≤ OR et e ∧ OR et e ≤ Λ)
      ↔ (1 + (1 - e) / (Λ * e) ≤ 1 / et ∧ 1 / et ≤ 1 + Λ * (1 - e) / e) := by
  have h1e : 0 < 1 - e := by linarith
  have h1et : 0 < 1 - et := by linarith
  have hOReq : OR et e = et * (1 - e) / ((1 - et) * e) := by
    rw [OR, div_div_eq_mul_div, div_mul_eq_mul_div, mul_comm, mul_div_mul_comm]; ring_nf
  rw [hOReq]
  -- `1/Λ ≤ OR ⟺ 1/et ≤ wMax`, and `OR ≤ Λ ⟺ wMin ≤ 1/et`; reorder.
  have hMax : (1 / Λ ≤ et * (1 - e) / ((1 - et) * e))
      ↔ (1 / et ≤ 1 + Λ * (1 - e) / e) := by
    rw [div_le_div_iff₀ hΛ (by positivity : (0:ℝ) < (1 - et) * e),
      show (1:ℝ) + Λ * (1 - e) / e = (e + Λ * (1 - e)) / e by field_simp,
      div_le_div_iff₀ het0 he0]
    constructor <;> intro h <;> nlinarith [h, mul_pos hΛ he0]
  have hMin : (et * (1 - e) / ((1 - et) * e) ≤ Λ)
      ↔ (1 + (1 - e) / (Λ * e) ≤ 1 / et) := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (1 - et) * e),
      show (1:ℝ) + (1 - e) / (Λ * e) = (Λ * e + (1 - e)) / (Λ * e) by field_simp,
      div_le_div_iff₀ (by positivity : (0:ℝ) < Λ * e) het0]
    constructor <;> intro h <;> nlinarith [h, mul_pos hΛ he0]
  rw [hMax, hMin, and_comm]

/-- Pointwise worst-case step (upper): if `0 ≤ a`, `wm ≤ w ≤ wM`, then
`a*y*w ≤ a*y*(wM if 0≤y else wm)`. -/
private lemma weight_mul_le_upper {a y w wm wM : ℝ} (ha : 0 ≤ a)
    (hlo : wm ≤ w) (hhi : w ≤ wM) :
    a * y * w ≤ a * y * (if 0 ≤ y then wM else wm) := by
  rcases le_or_gt 0 y with hy | hy
  · rw [if_pos hy]
    have : a * y * w ≤ a * y * wM := by
      apply mul_le_mul_of_nonneg_left hhi (mul_nonneg ha hy)
    simpa using this
  · rw [if_neg (not_le.mpr hy)]
    -- `y < 0`, so `a*y ≤ 0`; `wm ≤ w` reverses.
    have hay : a * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha (le_of_lt hy)
    have : a * y * w ≤ a * y * wm := mul_le_mul_of_nonpos_left hlo hay
    simpa using this

/-- Pointwise worst-case step (lower): if `0 ≤ a`, `wm ≤ w ≤ wM`, then
`a*y*(wm if 0≤y else wM) ≤ a*y*w`. -/
private lemma weight_mul_ge_lower {a y w wm wM : ℝ} (ha : 0 ≤ a)
    (hlo : wm ≤ w) (hhi : w ≤ wM) :
    a * y * (if 0 ≤ y then wm else wM) ≤ a * y * w := by
  rcases le_or_gt 0 y with hy | hy
  · rw [if_pos hy]
    exact mul_le_mul_of_nonneg_left hlo (mul_nonneg ha hy)
  · rw [if_neg (not_le.mpr hy)]
    have hay : a * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha (le_of_lt hy)
    exact mul_le_mul_of_nonpos_left hhi hay

/-- **Closed form of the MSM upper bound.** Over the odds-ratio ambiguity set the supremum of the
candidate IPW mean is attained pointwise, giving `msmUpper Λ = E[A·Y·(wMax if Y≥0 else wMin)]`.

Hypotheses: `1 ≤ Λ`; two-sided overlap `0 < e(X) < 1` a.e.; and an **envelope-integrability**
condition `Integrable (fun ω => A·|Y|·wMax)` — which dominates every candidate integrand `A·Y/ẽ`
(since `1/ẽ ≤ wMax`), giving both `BddAbove` of the image and integrability of the closed form. -/
theorem msmUpper_eq (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1)
    (hmeas : ∀ etilde ∈ S.MSMSet Λ, AEMeasurable etilde P.μ)
    (henv : Integrable (fun ω => S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω) P.μ) :
    S.msmUpper Λ = S.msmUpperForm Λ := by
  classical
  have hΛ0 : (0:ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
  -- Abbreviations.
  set A : P.Ω → ℝ := S.dVar.indicator true with hA_def
  set Y : P.Ω → ℝ := S.factualY with hY_def
  set e : P.Ω → ℝ := S.propScore true with he_def
  -- Measurability.
  have hAm : Measurable A := S.dVar.measurable_indicator true
  have hYm : Measurable Y := S.measurable_factualY
  have hem : Measurable e := by
    rw [he_def]; unfold POBackdoorSystem.propScore
    exact (stronglyMeasurable_condExp.mono S.sigmaX_le).measurable
  have hwMaxm : Measurable (S.wMax Λ) := by
    unfold POBackdoorSystem.wMax
    exact (measurable_const.add
      ((measurable_const.mul (measurable_const.sub hem)).div hem))
  have hwMinm : Measurable (S.wMin Λ) := by
    unfold POBackdoorSystem.wMin
    exact (measurable_const.add
      ((measurable_const.sub hem).div (measurable_const.mul hem)))
  -- `A` is in `[0,1]`.
  have hA0 : ∀ ω, 0 ≤ A ω := fun ω => by
    rcases S.dVar.indicator_eq_one_or_zero true ω with h | h <;> simp [hA_def, h]
  have hA1 : ∀ ω, A ω ≤ 1 := fun ω => by
    rcases S.dVar.indicator_eq_one_or_zero true ω with h | h <;> simp [hA_def, h]
  -- The optimal weight and candidate propensity.
  set wstar : P.Ω → ℝ := fun ω => if 0 ≤ Y ω then S.wMax Λ ω else S.wMin Λ ω with hwstar_def
  set estar : P.Ω → ℝ := fun ω => 1 / wstar ω with hestar_def
  -- a.e. positivity / ordering of the weights from overlap.
  have hae : ∀ᵐ ω ∂P.μ, (1:ℝ) < S.wMin Λ ω ∧ S.wMin Λ ω ≤ S.wMax Λ ω := by
    filter_upwards [hoverlap] with ω hω
    obtain ⟨he0, he1⟩ := hω
    have h1e : 0 < 1 - e ω := by rw [he_def] at *; linarith
    have he0' : 0 < e ω := by rw [he_def] at *; exact he0
    refine ⟨?_, ?_⟩
    · have : 0 < (1 - e ω) / (Λ * e ω) := by positivity
      simp only [POBackdoorSystem.wMin, ← he_def]; linarith
    · simp only [POBackdoorSystem.wMin, POBackdoorSystem.wMax, ← he_def]
      have hd1 : (1 - e ω) / (Λ * e ω) ≤ Λ * (1 - e ω) / e ω := by
        rw [div_le_div_iff₀ (by positivity) he0']
        nlinarith [hΛ, mul_pos h1e he0', mul_pos hΛ0 he0',
          mul_nonneg (mul_nonneg (le_of_lt h1e) (le_of_lt he0')) (sub_nonneg.mpr hΛ)]
      linarith
  -- Measurability and a.e. bounds of the optimal weight.
  have hwstar_m : Measurable wstar := by
    rw [hwstar_def]
    exact Measurable.ite (measurableSet_le measurable_const hYm) hwMaxm hwMinm
  have hwstar_ae : ∀ᵐ ω ∂P.μ,
      S.wMin Λ ω ≤ wstar ω ∧ wstar ω ≤ S.wMax Λ ω ∧ 0 < wstar ω := by
    filter_upwards [hae] with ω hω
    obtain ⟨hwm1, hwmle⟩ := hω
    rw [hwstar_def]
    by_cases hy : 0 ≤ Y ω
    · simp only [if_pos hy]; exact ⟨hwmle, le_rfl, by linarith⟩
    · simp only [if_neg hy]; exact ⟨le_rfl, hwmle, by linarith⟩
  -- `A*Y*wstar` is dominated by the envelope, hence integrable.
  have hform_int : Integrable (fun ω => A ω * Y ω * wstar ω) P.μ := by
    refine Integrable.mono' henv
      ((hAm.mul hYm).mul hwstar_m).aestronglyMeasurable ?_
    filter_upwards [hwstar_ae] with ω hω
    obtain ⟨_, hle, hpos⟩ := hω
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hA0 ω)]
    have hwabs : |wstar ω| = wstar ω := abs_of_nonneg (le_of_lt hpos)
    rw [hwabs, mul_assoc, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (hA0 ω)
    exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)
  -- `msmUpperForm = ∫ A*Y*wstar`.
  have hform_eq : S.msmUpperForm Λ = ∫ ω, A ω * Y ω * wstar ω ∂P.μ := by
    rfl
  -- Witness: `estar = 1/wstar ∈ MSMSet Λ` with `candMean estar = msmUpperForm`.
  have hestar_candMean : S.candMean estar = S.msmUpperForm Λ := by
    rw [hform_eq]
    unfold POBackdoorSystem.candMean
    refine integral_congr_ae ?_
    filter_upwards [hwstar_ae] with ω hω
    obtain ⟨_, _, hpos⟩ := hω
    change A ω * Y ω / (1 / wstar ω) = A ω * Y ω * wstar ω
    rw [div_div_eq_mul_div, div_one]
  -- a.e. `wstar > 1` (since `wstar ∈ {wMin, wMax}`, `wMin > 1`, `wMax ≥ wMin`).
  have hwstar_gt1 : ∀ᵐ ω ∂P.μ, 1 < wstar ω := by
    filter_upwards [hae] with ω hω
    obtain ⟨hwm1, hwmle⟩ := hω
    rw [hwstar_def]
    by_cases hy : 0 ≤ Y ω
    · simp only [if_pos hy]; linarith
    · simp only [if_neg hy]; exact hwm1
  have hestar_mem : estar ∈ S.MSMSet Λ := by
    refine ⟨?_, ?_⟩
    · filter_upwards [hwstar_gt1] with ω hω
      rw [hestar_def]
      constructor
      · positivity
      · rw [div_lt_one (by linarith)]; linarith
    · filter_upwards [hoverlap, hwstar_ae, hwstar_gt1] with ω hov hw hwgt
      obtain ⟨he0, he1⟩ := hov
      obtain ⟨hmin, hmax, hpos⟩ := hw
      have het0 : 0 < estar ω := by rw [hestar_def]; positivity
      have het1 : estar ω < 1 := by
        rw [hestar_def, div_lt_one (by linarith)]; linarith
      rw [OR_box_iff hΛ0 he0 he1 het0 het1]
      have hinv : 1 / estar ω = wstar ω := by
        rw [hestar_def, one_div_one_div]
      rw [hinv]
      exact ⟨hmin, hmax⟩
  -- Every candidate mean is `≤ msmUpperForm`.
  have hcand_le : ∀ etilde ∈ S.MSMSet Λ, S.candMean etilde ≤ S.msmUpperForm Λ := by
    intro et hmem
    obtain ⟨hint, hor⟩ := hmem
    have hetm : AEMeasurable et P.μ := hmeas et ⟨hint, hor⟩
    -- a.e. box bound on `w = 1/et`.
    have hbox : ∀ᵐ ω ∂P.μ,
        S.wMin Λ ω ≤ 1 / et ω ∧ 1 / et ω ≤ S.wMax Λ ω := by
      filter_upwards [hoverlap, hint, hor] with ω hov het hOR
      obtain ⟨he0, he1⟩ := hov
      obtain ⟨het0, het1⟩ := het
      have := (OR_box_iff hΛ0 he0 he1 het0 het1).mp hOR
      exact this
    -- `A*Y/et = A*Y*(1/et)` a.e.; integrable by domination.
    have hcandmean_int : Integrable (fun ω => A ω * Y ω / et ω) P.μ := by
      refine Integrable.mono' henv
        (((hAm.mul hYm).aemeasurable.div hetm).aestronglyMeasurable) ?_
      filter_upwards [hbox, hoverlap, hint] with ω hb hov het
      obtain ⟨hmin, hmax⟩ := hb
      obtain ⟨he0, he1⟩ := hov
      obtain ⟨het0, het1⟩ := het
      rw [Real.norm_eq_abs, mul_div_assoc, abs_mul, abs_of_nonneg (hA0 ω),
        mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (hA0 ω)
      have hYdiv : |Y ω / et ω| = |Y ω| * (1 / et ω) := by
        rw [abs_div, abs_of_nonneg (le_of_lt het0), mul_one_div]
      rw [hYdiv]
      exact mul_le_mul_of_nonneg_left hmax (abs_nonneg _)
    have heq_w : (fun ω => A ω * Y ω / et ω)
        =ᵐ[P.μ] (fun ω => A ω * Y ω * (1 / et ω)) := by
      filter_upwards with ω
      rw [mul_one_div]
    -- `candMean et = ∫ A*Y*(1/et) ≤ ∫ A*Y*wstar = form`.
    rw [show S.candMean et = ∫ ω, A ω * Y ω / et ω ∂P.μ from rfl, hform_eq]
    rw [integral_congr_ae heq_w]
    apply integral_mono_ae (hcandmean_int.congr heq_w) hform_int
    filter_upwards [hbox] with ω hb
    obtain ⟨hmin, hmax⟩ := hb
    exact weight_mul_le_upper (hA0 ω) hmin hmax
  -- Assemble: `msmUpper = sSup (candMean '' MSMSet) = msmUpperForm`.
  have hne : (S.candMean '' S.MSMSet Λ).Nonempty :=
    ⟨S.candMean estar, Set.mem_image_of_mem _ hestar_mem⟩
  have hbdd : BddAbove (S.candMean '' S.MSMSet Λ) := by
    refine ⟨S.msmUpperForm Λ, ?_⟩
    rintro x ⟨et, hmem, rfl⟩
    exact hcand_le et hmem
  refine le_antisymm ?_ ?_
  · apply csSup_le hne
    rintro x ⟨et, hmem, rfl⟩
    exact hcand_le et hmem
  · rw [← hestar_candMean]
    exact le_csSup hbdd (Set.mem_image_of_mem _ hestar_mem)

/-- **Closed form of the MSM lower bound.** Symmetrically,
`msmLower Λ = E[A·Y·(wMin if Y≥0 else wMax)]`. -/
theorem msmLower_eq (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1)
    (hmeas : ∀ etilde ∈ S.MSMSet Λ, AEMeasurable etilde P.μ)
    (henv : Integrable (fun ω => S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω) P.μ) :
    S.msmLower Λ = S.msmLowerForm Λ := by
  classical
  have hΛ0 : (0:ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
  set A : P.Ω → ℝ := S.dVar.indicator true with hA_def
  set Y : P.Ω → ℝ := S.factualY with hY_def
  set e : P.Ω → ℝ := S.propScore true with he_def
  have hAm : Measurable A := S.dVar.measurable_indicator true
  have hYm : Measurable Y := S.measurable_factualY
  have hem : Measurable e := by
    rw [he_def]; unfold POBackdoorSystem.propScore
    exact (stronglyMeasurable_condExp.mono S.sigmaX_le).measurable
  have hwMaxm : Measurable (S.wMax Λ) := by
    unfold POBackdoorSystem.wMax
    exact (measurable_const.add
      ((measurable_const.mul (measurable_const.sub hem)).div hem))
  have hwMinm : Measurable (S.wMin Λ) := by
    unfold POBackdoorSystem.wMin
    exact (measurable_const.add
      ((measurable_const.sub hem).div (measurable_const.mul hem)))
  have hA0 : ∀ ω, 0 ≤ A ω := fun ω => by
    rcases S.dVar.indicator_eq_one_or_zero true ω with h | h <;> simp [hA_def, h]
  -- Lower-bound optimal weight: `wMin` where `Y ≥ 0`, `wMax` where `Y < 0`.
  set wstar : P.Ω → ℝ := fun ω => if 0 ≤ Y ω then S.wMin Λ ω else S.wMax Λ ω with hwstar_def
  set estar : P.Ω → ℝ := fun ω => 1 / wstar ω with hestar_def
  have hae : ∀ᵐ ω ∂P.μ, (1:ℝ) < S.wMin Λ ω ∧ S.wMin Λ ω ≤ S.wMax Λ ω := by
    filter_upwards [hoverlap] with ω hω
    obtain ⟨he0, he1⟩ := hω
    have h1e : 0 < 1 - e ω := by rw [he_def] at *; linarith
    have he0' : 0 < e ω := by rw [he_def] at *; exact he0
    refine ⟨?_, ?_⟩
    · have : 0 < (1 - e ω) / (Λ * e ω) := by positivity
      simp only [POBackdoorSystem.wMin, ← he_def]; linarith
    · simp only [POBackdoorSystem.wMin, POBackdoorSystem.wMax, ← he_def]
      have hd1 : (1 - e ω) / (Λ * e ω) ≤ Λ * (1 - e ω) / e ω := by
        rw [div_le_div_iff₀ (by positivity) he0']
        nlinarith [hΛ, mul_pos h1e he0', mul_pos hΛ0 he0',
          mul_nonneg (mul_nonneg (le_of_lt h1e) (le_of_lt he0')) (sub_nonneg.mpr hΛ)]
      linarith
  have hwstar_m : Measurable wstar := by
    rw [hwstar_def]
    exact Measurable.ite (measurableSet_le measurable_const hYm) hwMinm hwMaxm
  have hwstar_ae : ∀ᵐ ω ∂P.μ,
      S.wMin Λ ω ≤ wstar ω ∧ wstar ω ≤ S.wMax Λ ω ∧ 0 < wstar ω := by
    filter_upwards [hae] with ω hω
    obtain ⟨hwm1, hwmle⟩ := hω
    rw [hwstar_def]
    by_cases hy : 0 ≤ Y ω
    · simp only [if_pos hy]; exact ⟨le_rfl, hwmle, by linarith⟩
    · simp only [if_neg hy]; exact ⟨hwmle, le_rfl, by linarith⟩
  have hwstar_gt1 : ∀ᵐ ω ∂P.μ, 1 < wstar ω := by
    filter_upwards [hae] with ω hω
    obtain ⟨hwm1, hwmle⟩ := hω
    rw [hwstar_def]
    by_cases hy : 0 ≤ Y ω
    · simp only [if_pos hy]; exact hwm1
    · simp only [if_neg hy]; linarith
  -- `A*Y*wstar` integrable (dominated by envelope).
  have hform_int : Integrable (fun ω => A ω * Y ω * wstar ω) P.μ := by
    refine Integrable.mono' henv
      ((hAm.mul hYm).mul hwstar_m).aestronglyMeasurable ?_
    filter_upwards [hwstar_ae] with ω hω
    obtain ⟨_, hle, hpos⟩ := hω
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hA0 ω)]
    have hwabs : |wstar ω| = wstar ω := abs_of_nonneg (le_of_lt hpos)
    rw [hwabs, mul_assoc, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (hA0 ω)
    exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)
  have hform_eq : S.msmLowerForm Λ = ∫ ω, A ω * Y ω * wstar ω ∂P.μ := by
    rfl
  -- Witness `estar = 1/wstar ∈ MSMSet`, `candMean estar = msmLowerForm`.
  have hestar_candMean : S.candMean estar = S.msmLowerForm Λ := by
    rw [hform_eq]
    unfold POBackdoorSystem.candMean
    refine integral_congr_ae ?_
    filter_upwards [hwstar_ae] with ω hω
    obtain ⟨_, _, hpos⟩ := hω
    change A ω * Y ω / (1 / wstar ω) = A ω * Y ω * wstar ω
    rw [div_div_eq_mul_div, div_one]
  have hestar_mem : estar ∈ S.MSMSet Λ := by
    refine ⟨?_, ?_⟩
    · filter_upwards [hwstar_gt1] with ω hω
      rw [hestar_def]
      exact ⟨by positivity, by rw [div_lt_one (by linarith)]; linarith⟩
    · filter_upwards [hoverlap, hwstar_ae, hwstar_gt1] with ω hov hw hwgt
      obtain ⟨he0, he1⟩ := hov
      obtain ⟨hmin, hmax, hpos⟩ := hw
      have het0 : 0 < estar ω := by rw [hestar_def]; positivity
      have het1 : estar ω < 1 := by
        rw [hestar_def, div_lt_one (by linarith)]; linarith
      rw [OR_box_iff hΛ0 he0 he1 het0 het1]
      have hinv : 1 / estar ω = wstar ω := by rw [hestar_def, one_div_one_div]
      rw [hinv]; exact ⟨hmin, hmax⟩
  -- Every candidate mean is `≥ msmLowerForm`.
  have hcand_ge : ∀ etilde ∈ S.MSMSet Λ, S.msmLowerForm Λ ≤ S.candMean etilde := by
    intro et hmem
    obtain ⟨hint, hor⟩ := hmem
    have hetm : AEMeasurable et P.μ := hmeas et ⟨hint, hor⟩
    have hbox : ∀ᵐ ω ∂P.μ,
        S.wMin Λ ω ≤ 1 / et ω ∧ 1 / et ω ≤ S.wMax Λ ω := by
      filter_upwards [hoverlap, hint, hor] with ω hov het hOR
      obtain ⟨he0, he1⟩ := hov
      obtain ⟨het0, het1⟩ := het
      exact (OR_box_iff hΛ0 he0 he1 het0 het1).mp hOR
    have hcandmean_int : Integrable (fun ω => A ω * Y ω / et ω) P.μ := by
      refine Integrable.mono' henv
        (((hAm.mul hYm).aemeasurable.div hetm).aestronglyMeasurable) ?_
      filter_upwards [hbox, hoverlap, hint] with ω hb hov het
      obtain ⟨hmin, hmax⟩ := hb
      obtain ⟨he0, he1⟩ := hov
      obtain ⟨het0, het1⟩ := het
      rw [Real.norm_eq_abs, mul_div_assoc, abs_mul, abs_of_nonneg (hA0 ω),
        mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (hA0 ω)
      have hYdiv : |Y ω / et ω| = |Y ω| * (1 / et ω) := by
        rw [abs_div, abs_of_nonneg (le_of_lt het0), mul_one_div]
      rw [hYdiv]
      exact mul_le_mul_of_nonneg_left hmax (abs_nonneg _)
    have heq_w : (fun ω => A ω * Y ω / et ω)
        =ᵐ[P.μ] (fun ω => A ω * Y ω * (1 / et ω)) := by
      filter_upwards with ω; rw [mul_one_div]
    rw [show S.candMean et = ∫ ω, A ω * Y ω / et ω ∂P.μ from rfl, hform_eq]
    rw [integral_congr_ae heq_w]
    apply integral_mono_ae hform_int (hcandmean_int.congr heq_w)
    filter_upwards [hbox] with ω hb
    obtain ⟨hmin, hmax⟩ := hb
    exact weight_mul_ge_lower (hA0 ω) hmin hmax
  -- Assemble via `sInf`.
  have hne : (S.candMean '' S.MSMSet Λ).Nonempty :=
    ⟨S.candMean estar, Set.mem_image_of_mem _ hestar_mem⟩
  have hbdd : BddBelow (S.candMean '' S.MSMSet Λ) := by
    refine ⟨S.msmLowerForm Λ, ?_⟩
    rintro x ⟨et, hmem, rfl⟩
    exact hcand_ge et hmem
  refine le_antisymm ?_ ?_
  · rw [← hestar_candMean]
    exact csInf_le hbdd (Set.mem_image_of_mem _ hestar_mem)
  · apply le_csInf hne
    rintro x ⟨et, hmem, rfl⟩
    exact hcand_ge et hmem

end POBackdoorSystem

end PO
end Causalean
