/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PopulationDesign
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The arm-`a` regression of `P`; arm one selects `mu1`, and every other value selects `mu0`. -/
def armReg {d : ℕ} (P : CateLaw d) (a : ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => if a = 1 then P.mu1 x else P.mu0 x

/-- The arm-`a` design weight of `P`: arm one has weight `π_P p_P`, while arm zero has weight `(1-π_P)p_P`. -/
noncomputable def armWeight {d : ℕ} (P : CateLaw d) (a : ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => (if a = 1 then P.pi x else 1 - P.pi x) * P.px x

/-- The arm-`a` propensity weight of `P`: `1 ↦ π_P`, `0 ↦ 1 − π_P`. -/
noncomputable def armPi {d : ℕ} (P : CateLaw d) (a : ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => if a = 1 then P.pi x else 1 - P.pi x

/-- The covariate marginal of the observed data law. -/
noncomputable def xMarginal {d : ℕ} (P : CateLaw d) : Measure (Fin d → ℝ) :=
  P.dataMeasure.map (fun O => O.X)

/-- The localization radius is nonnegative when the outer radius is nonnegative and the center lies in the open cube. -/
lemma rStar_nonneg {d : ℕ} (r0 : ℝ) (x0 : Fin d → ℝ) (hr0 : 0 ≤ r0)
    (hx0 : ∀ i, x0 i ∈ Set.Ioo (0 : ℝ) 1) : 0 ≤ rStar r0 x0 := by
  unfold rStar
  apply mul_nonneg (by norm_num)
  apply le_min hr0
  by_cases h : Nonempty (Fin d)
  · letI := h
    exact le_ciInf fun i => le_min (hx0 i).1.le (sub_nonneg.mpr (hx0 i).2.le)
  · have hd : d = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hd
      exact h (Fin.pos_iff_nonempty.mp hd)
    subst d
    simp

/-- The ball at the localization radius is contained in the ball of radius `r0`. -/
lemma supBall_rStar_subset_supBall {d : ℕ} (r0 : ℝ) (x0 : Fin d → ℝ) (hr0 : 0 ≤ r0) :
    supBall x0 (rStar r0 x0) ⊆ supBall x0 r0 := by
  by_cases hd : d = 0
  · subst d
    simp [supBall]
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hd)
  intro x hx i
  have hrs0 : 0 ≤ rStar r0 x0 := (abs_nonneg (x i - x0 i)).trans (hx i)
  have hm0 : 0 ≤ min r0 (⨅ j : Fin d, min (x0 j) (1 - x0 j)) := by
    unfold rStar at hrs0
    nlinarith
  exact (hx i).trans (by
    unfold rStar
    calc
      (1 / 2 : ℝ) * min r0 (⨅ j : Fin d, min (x0 j) (1 - x0 j))
          ≤ 1 * min r0 (⨅ j : Fin d, min (x0 j) (1 - x0 j)) := by
            apply mul_le_mul_of_nonneg_right (by norm_num) hm0
      _ ≤ r0 := by simpa using min_le_left r0 (⨅ j : Fin d, min (x0 j) (1 - x0 j)))

/-- The localization ball lies inside the covariate cube, uniformly also in dimension zero. -/
lemma supBall_rStar_subset_cube {d : ℕ} (r0 : ℝ) (x0 : Fin d → ℝ) (hr0 : 0 < r0)
    (hx0 : ∀ i, x0 i ∈ Set.Ioo (0 : ℝ) 1) : supBall x0 (rStar r0 x0) ⊆ cube d := by
  intro x hx i
  have hiInf : (⨅ j : Fin d, min (x0 j) (1 - x0 j)) ≤ min (x0 i) (1 - x0 i) :=
    ciInf_le (bddBelow_def.mpr ⟨0, fun y hy => by
      rcases hy with ⟨j, rfl⟩
      exact le_min (hx0 j).1.le (sub_nonneg.mpr (hx0 j).2.le)⟩) i
  have hrs : rStar r0 x0 ≤ (1 / 2) * min (x0 i) (1 - x0 i) := by
    unfold rStar
    exact mul_le_mul_of_nonneg_left ((min_le_right _ _).trans hiInf) (by norm_num)
  have habs := (hx i).trans hrs
  rw [abs_le] at habs
  constructor <;> linarith [min_le_left (x0 i) (1 - x0 i),
    min_le_right (x0 i) (1 - x0 i)]

/-- Every finite-dimensional sup-norm ball is a measurable set. -/
lemma measurableSet_supBall {d : ℕ} (x0 : Fin d → ℝ) (r : ℝ) :
    MeasurableSet (supBall x0 r) := by
  rw [show supBall x0 r = ⋂ i : Fin d,
      (fun x : Fin d → ℝ => |x i - x0 i|) ⁻¹' Set.Iic r by ext x; simp [supBall]]
  exact MeasurableSet.iInter fun i => measurableSet_Iic.preimage
    (by simpa only [Real.norm_eq_abs] using
      ((measurable_pi_apply i).sub measurable_const).norm)

/-- Every finite-dimensional sup-norm ball is compact. -/
lemma isCompact_supBall {d : ℕ} (x0 : Fin d → ℝ) (r : ℝ) :
    IsCompact (supBall x0 r) := by
  by_cases hd : d = 0
  · subst d
    simpa [supBall] using (isCompact_univ : IsCompact (Set.univ : Set (Fin 0 → ℝ)))
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hd)
  rw [show supBall x0 r = Metric.closedBall x0 r by
    ext x
    simp only [supBall, Set.mem_setOf_eq, Metric.mem_closedBall]
    by_cases hr : 0 ≤ r
    · rw [dist_pi_le_iff hr]
      simp only [Real.dist_eq]
    · have hempty : ¬ (∀ i, |x i - x0 i| ≤ r) := fun hall =>
        hr ((abs_nonneg _).trans (hall (Classical.choice inferInstance)))
      have hdist : ¬ dist x x0 ≤ r := fun hle => hr ((dist_nonneg).trans hle)
      simp only [hempty, false_iff, Metric.mem_closedBall, hdist]
  ]
  exact isCompact_closedBall _ _

/-- Each arm regression is bounded in absolute value by the Hölder radius on the cube. -/
theorem armReg_abs_le_L {d : ℕ} {alpha beta gamma L e0 f0 f1 r0 : ℝ}
    {x0 : Fin d → ℝ} (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (P : CateLaw d) (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P)
    {a : ℝ} (ha : a = 0 ∨ a = 1) : ∀ x ∈ cube d, |armReg P a x| ≤ L := by
  intro x hx
  rcases ha with rfl | rfl
  · rw [armReg, if_neg (by norm_num), ← Real.norm_eq_abs,
      ← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact hP.muH.1.2.1 0 (Nat.zero_le _) x hx
  · rw [armReg, if_pos rfl, ← Real.norm_eq_abs,
      ← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact hP.muH.2.2.1 0 (Nat.zero_le _) x hx

/-- Each arm regression is continuous when restricted to the covariate cube. -/
theorem continuousOn_armReg {d : ℕ} {alpha beta gamma L e0 f0 f1 r0 : ℝ}
    {x0 : Fin d → ℝ} (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (P : CateLaw d) (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P)
    {a : ℝ} (ha : a = 0 ∨ a = 1) : ContinuousOn (armReg P a) (cube d) := by
  rcases ha with rfl | rfl
  · unfold armReg
    have h01 : (0 : ℝ) ≠ 1 := by norm_num
    simp only [h01, ↓reduceIte]
    exact hP.muH.1.1.continuousOn
  · unfold armReg
    simp only [if_pos rfl]
    exact hP.muH.2.1.continuousOn

/-- Restricting an arm regression to the measurable localization ball gives a globally measurable indicator-style modification. -/
theorem measurable_indicator_armReg {d : ℕ} {alpha beta gamma L e0 f0 f1 r0 : ℝ}
    {x0 : Fin d → ℝ} (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (P : CateLaw d) (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P)
    {a : ℝ} (ha : a = 0 ∨ a = 1) :
    Measurable ((supBall x0 (rStar r0 x0)).indicator (armReg P a)) := by
  classical
  let S := supBall x0 (rStar r0 x0)
  have hS : MeasurableSet S := measurableSet_supBall _ _
  have hsub : S ⊆ cube d := supBall_rStar_subset_cube r0 x0 hreg.2.2.2.2.2.2.2.1.1
    hreg.2.2.2.2.2.2.2.2
  have hc : ContinuousOn (armReg P a) S :=
    (continuousOn_armReg hreg P hP ha).mono hsub
  simpa only [Set.piecewise, Set.indicator] using
    hc.measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const hS

/-- The arm design weight is at least `e0*f0` throughout the localization ball. -/
theorem armWeight_ge {d : ℕ} {alpha beta gamma L e0 f0 f1 r0 : ℝ}
    {x0 : Fin d → ℝ} (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (P : CateLaw d) (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P)
    {a : ℝ} (ha : a = 0 ∨ a = 1) :
    ∀ x ∈ supBall x0 (rStar r0 x0), e0 * f0 ≤ armWeight P a x := by
  intro x hx
  have hcube : x ∈ cube d := supBall_rStar_subset_cube r0 x0
    hreg.2.2.2.2.2.2.2.1.1 hreg.2.2.2.2.2.2.2.2 hx
  have hbig : x ∈ supBall x0 r0 := supBall_rStar_subset_supBall r0 x0
    hreg.2.2.2.2.2.2.2.1.1.le hx
  have hpx : f0 ≤ P.px x := (hP.localDensity x hbig hcube).1
  have hpi := hP.overlap x hcube
  have he0 : 0 < e0 := hreg.2.2.2.2.1.1
  rcases ha with rfl | rfl
  · rw [armWeight, if_neg (by norm_num)]
    exact mul_le_mul (by linarith) hpx hreg.2.2.2.2.2.1.le
      (by linarith [hpi.1, hpi.2])
  · rw [armWeight, if_pos rfl]
    exact mul_le_mul hpi.1 hpx hreg.2.2.2.2.2.1.le (by linarith [hpi.1, hpi.2])

/-- The arm propensity is bounded below by `e0` on the ball. -/
theorem armPi_ge {d : ℕ} {alpha beta gamma L e0 f0 f1 r0 : ℝ}
    {x0 : Fin d → ℝ} (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (P : CateLaw d) (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P)
    {a : ℝ} (ha : a = 0 ∨ a = 1) :
    ∀ x ∈ supBall x0 (rStar r0 x0), e0 ≤ armPi P a x := by
  intro x hx
  have hcube : x ∈ cube d := supBall_rStar_subset_cube r0 x0
    hreg.2.2.2.2.2.2.2.1.1 hreg.2.2.2.2.2.2.2.2 hx
  obtain ⟨hl, hu⟩ := hP.overlap x hcube
  have he0 : 0 < e0 := hreg.2.2.2.2.1.1
  rcases ha with h | h
  · subst a
    rw [armPi, if_neg (by norm_num)]
    linarith
  · subst a
    rw [armPi, if_pos rfl]
    exact hl

/-- The arm propensity is at most one on the ball. -/
theorem armPi_le_one {d : ℕ} {alpha beta gamma L e0 f0 f1 r0 : ℝ}
    {x0 : Fin d → ℝ} (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (P : CateLaw d) (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P)
    {a : ℝ} (ha : a = 0 ∨ a = 1) :
    ∀ x ∈ supBall x0 (rStar r0 x0), armPi P a x ≤ 1 := by
  intro x hx
  have hcube : x ∈ cube d := supBall_rStar_subset_cube r0 x0
    hreg.2.2.2.2.2.2.2.1.1 hreg.2.2.2.2.2.2.2.2 hx
  obtain ⟨hl, hu⟩ := hP.overlap x hcube
  have he0 : 0 < e0 := hreg.2.2.2.2.1.1
  rcases ha with h | h
  · subst a
    rw [armPi, if_neg (by norm_num)]
    linarith
  · subst a
    rw [armPi, if_pos rfl]
    linarith

/-- Restricting an arm propensity to the localization ball gives a globally measurable
indicator-style modification. -/
theorem measurable_indicator_armPi {d : ℕ} {alpha beta gamma L e0 f0 f1 r0 : ℝ}
    {x0 : Fin d → ℝ} (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (P : CateLaw d) (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P)
    {a : ℝ} (ha : a = 0 ∨ a = 1) :
    Measurable ((supBall x0 (rStar r0 x0)).indicator (armPi P a)) := by
  classical
  let S := supBall x0 (rStar r0 x0)
  have hS : MeasurableSet S := measurableSet_supBall _ _
  have hsub : S ⊆ cube d := supBall_rStar_subset_cube r0 x0
    hreg.2.2.2.2.2.2.2.1.1 hreg.2.2.2.2.2.2.2.2
  have hpi : ContinuousOn P.pi S := hP.piH.1.continuousOn.mono hsub
  have hc : ContinuousOn (armPi P a) S := by
    rcases ha with h | h
    · subst a
      unfold armPi
      have h01 : (0 : ℝ) ≠ 1 := by norm_num
      simp only [h01, ↓reduceIte]
      exact (continuousOn_const : ContinuousOn (fun _ : Fin d → ℝ => (1 : ℝ)) S).sub hpi
    · subst a
      unfold armPi
      simp only [if_pos rfl]
      exact hpi
  simpa only [Set.piecewise, Set.indicator] using
    hc.measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const hS

/-- Measure form of the local density-floor domination. -/
theorem smul_volume_restrict_le_xMarginal_restrict {d : ℕ}
    {alpha beta gamma L e0 f0 f1 r0 : ℝ} {x0 : Fin d → ℝ}
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (P : CateLaw d) (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P) :
    ENNReal.ofReal f0 • (volume.restrict (supBall x0 (rStar r0 x0))) ≤
      (xMarginal P).restrict (supBall x0 (rStar r0 x0)) := by
  let S := supBall x0 (rStar r0 x0)
  let ν : Measure (Fin d → ℝ) := volume.restrict S
  have hS : MeasurableSet S := measurableSet_supBall _ _
  have hScube : S ⊆ cube d := supBall_rStar_subset_cube r0 x0
    hreg.2.2.2.2.2.2.2.1.1 hreg.2.2.2.2.2.2.2.2
  have hSball : S ⊆ supBall x0 r0 := supBall_rStar_subset_supBall r0 x0
    hreg.2.2.2.2.2.2.2.1.1.le
  have hlo : (fun _ : Fin d → ℝ => ENNReal.ofReal f0) ≤ᵐ[ν]
      (fun x => ENNReal.ofReal (P.px x)) := by
    filter_upwards [ae_restrict_mem hS] with x hx
    exact ENNReal.ofReal_le_ofReal (hP.localDensity x (hSball hx) (hScube hx)).1
  calc
    ENNReal.ofReal f0 • volume.restrict S =
        ν.withDensity (fun _ => ENNReal.ofReal f0) := (withDensity_const _).symm
    _ ≤ ν.withDensity (fun x => ENNReal.ofReal (P.px x)) := withDensity_mono hlo
    _ = (xMarginal P).restrict S := by
      rw [xMarginal, hP.pxDens, restrict_withDensity hS,
        Measure.restrict_restrict hS]
      rw [Set.inter_eq_left.mpr hScube]

/-- The covariate marginal dominates `f0 ·` Lebesgue on the localization ball. -/
theorem ofReal_f0_mul_volume_le_xMarginal {d : ℕ}
    {alpha beta gamma L e0 f0 f1 r0 : ℝ} {x0 : Fin d → ℝ}
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (P : CateLaw d) (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P) :
    ∀ E : Set (Fin d → ℝ), MeasurableSet E →
      E ⊆ supBall x0 (rStar r0 x0) →
      ENNReal.ofReal f0 * volume E ≤ xMarginal P E := by
  intro E hE hES
  have hdom := smul_volume_restrict_le_xMarginal_restrict hreg P hP E
  simpa [Measure.smul_apply, Measure.restrict_apply hE, Set.inter_eq_left.mpr hES] using hdom

/-- The covariate marginal is absolutely continuous w.r.t. Lebesgue. -/
theorem xMarginal_absolutelyContinuous {d : ℕ}
    {alpha beta gamma L e0 f0 f1 r0 : ℝ} {x0 : Fin d → ℝ}
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (P : CateLaw d) (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P) :
    xMarginal P ≪ volume := by
  rw [xMarginal, hP.pxDens]
  exact (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict

/-- Bochner corollary of the density-floor domination. -/
theorem mul_setIntegral_volume_le_setIntegral_xMarginal {d : ℕ}
    {alpha beta gamma L e0 f0 f1 r0 : ℝ} {x0 : Fin d → ℝ}
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (P : CateLaw d) (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P)
    (hIid : IidSampling P) (h : (Fin d → ℝ) → ℝ) (hmeas : Measurable h)
    (hnn : ∀ x, 0 ≤ h x) (B : ℝ) (hbd : ∀ x, h x ≤ B) :
    f0 * (∫ x in supBall x0 (rStar r0 x0), h x ∂volume) ≤
      ∫ x in supBall x0 (rStar r0 x0), h x ∂(xMarginal P) := by
  let S := supBall x0 (rStar r0 x0)
  letI : IsProbabilityMeasure P.dataMeasure := hIid.1
  haveI : IsProbabilityMeasure (xMarginal P) := by
    unfold xMarginal
    exact Measure.isProbabilityMeasure_map measurable_CateObs_X.aemeasurable
  have hint : Integrable h ((xMarginal P).restrict S) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable B
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]
    exact hbd x
  have hmono := integral_mono_measure
    (smul_volume_restrict_le_xMarginal_restrict hreg P hP)
    (ae_of_all _ hnn) hint
  calc
    f0 * (∫ x in S, h x ∂volume) =
        ∫ x, h x ∂(ENNReal.ofReal f0 • volume.restrict S) := by
      rw [integral_smul_measure]
      simp only [ENNReal.toReal_ofReal hreg.2.2.2.2.2.1.le, smul_eq_mul]
    _ ≤ ∫ x, h x ∂(xMarginal P).restrict S := hmono

/-- The support factor makes the arm-pairing integrand globally measurable. -/
theorem measurable_arm_pairing_integrand {d : ℕ}
    {alpha beta gamma L e0 f0 f1 r0 : ℝ} {x0 : Fin d → ℝ}
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (P : CateLaw d) (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P)
    {a : ℝ} (ha : a = 0 ∨ a = 1) (g c : (Fin d → ℝ) → ℝ)
    (hg : Measurable g) (hc : Measurable c)
    (hgsupp : ∀ x, x ∉ supBall x0 (rStar r0 x0) → g x = 0) :
    Measurable (fun x => g x * (armReg P a x - c x) * armPi P a x) := by
  classical
  let S := supBall x0 (rStar r0 x0)
  have hm : Measurable (fun x =>
      g x * (S.indicator (armReg P a) x - c x) * S.indicator (armPi P a) x) :=
    (hg.mul ((measurable_indicator_armReg hreg P hP ha).sub hc)).mul
      (measurable_indicator_armPi hreg P hP ha)
  convert hm using 1
  funext x
  by_cases hx : x ∈ S
  · simp only [Set.indicator_of_mem hx]
  · simp only [hgsupp x hx, zero_mul]

/-- **Arm/covariate disintegration pairing.** -/
theorem integral_arm_pairing {d : ℕ} {alpha beta gamma L e0 f0 f1 r0 : ℝ}
    {x0 : Fin d → ℝ} (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (P : CateLaw d) (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P)
    (hIid : IidSampling P) {a : ℝ} (ha : a = 0 ∨ a = 1)
    (g c : (Fin d → ℝ) → ℝ) (hg : Measurable g) (hc : Measurable c)
    (hgbd : ∀ x, |g x| ≤ 1) (hcbd : ∀ x, |c x| ≤ 1)
    (hgsupp : ∀ x, x ∉ supBall x0 (rStar r0 x0) → g x = 0) :
    ∫ O, (if O.A = a then (1 : ℝ) else 0) * g O.X * (O.Y - c O.X) ∂P.dataMeasure =
      ∫ x, g x * (armReg P a x - c x) * armPi P a x ∂(xMarginal P) := by
  letI : IsProbabilityMeasure P.dataMeasure := hIid.1
  let af : Fin 2 := if a = 1 then 1 else 0
  have haf : (((af : ℕ) : ℝ)) = a := by
    rcases ha with rfl | rfl <;> simp [af]
  have hmu : armMu P af = armReg P a := by
    funext x
    rcases ha with rfl | rfl <;> simp [af, armMu] <;> unfold armReg <;> simp
  have hpi : armProb P af = armPi P a := by
    funext x
    rcases ha with rfl | rfl <;> simp [af, armProb] <;> unfold armPi <;> simp
  have hmuAE := armMu_aemeasurable P beta L hreg.2.1 hIid hP.muH af
  have hmuB := armMu_ae_bound P beta L hreg.2.1 hIid hP.muH af
  have hout := integral_arm_outcome_mul P hIid hP.piProp hP.muReg af g
    hg.aemeasurable 1 hgbd hmuAE L hmuB
  have hgcmeas : Measurable (fun x => g x * c x) := hg.mul hc
  have hgcb : ∀ x, |g x * c x| ≤ (1 : ℝ) := by
    intro x
    rw [abs_mul]
    nlinarith [abs_nonneg (g x), abs_nonneg (c x), hgbd x, hcbd x]
  have hcsel := integral_arm_indicator_mul P hIid hP.piProp af
    (fun x => g x * c x) hgcmeas.aemeasurable 1 hgcb
  let F : (Fin d → ℝ) → ℝ := fun x => g x * (armReg P a x - c x) * armPi P a x
  have hFmeas : Measurable F := measurable_arm_pairing_integrand hreg P hP ha g c hg hc hgsupp
  have hleftY : Integrable (fun O : CateObs d =>
      (if O.A = a then (1 : ℝ) else 0) * g O.X * O.Y) P.dataMeasure := by
    apply Integrable.of_bound
      (((Measurable.ite (measurableSet_eq_fun measurable_CateObs_A measurable_const)
        measurable_const measurable_const).mul (hg.comp measurable_CateObs_X)).mul
          measurable_CateObs_Y).aestronglyMeasurable 1
    filter_upwards [hIid.2.1] with O hY
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    split <;> simp only [abs_one, one_mul, abs_zero, zero_mul]
    · exact (mul_le_mul (hgbd O.X) (by simpa [abs_le] using hY)
        (abs_nonneg O.Y) (by norm_num)).trans_eq (mul_one 1)
    · norm_num
  have hleftC : Integrable (fun O : CateObs d =>
      (if O.A = a then (1 : ℝ) else 0) * (g O.X * c O.X)) P.dataMeasure := by
    apply Integrable.of_bound
      ((Measurable.ite (measurableSet_eq_fun measurable_CateObs_A measurable_const)
        measurable_const measurable_const).mul (hgcmeas.comp measurable_CateObs_X)
        |>.aestronglyMeasurable) 1
    filter_upwards with O
    rw [Real.norm_eq_abs, abs_mul]
    split
    · simpa using hgcb O.X
    · simp
  have hout' :
      (∫ O, (if O.A = a then (1 : ℝ) else 0) * g O.X * O.Y ∂P.dataMeasure) =
        ∫ O, armPi P a O.X * armReg P a O.X * g O.X ∂P.dataMeasure := by
    calc
      _ = ∫ O, (if O.A = (((af : ℕ) : ℝ)) then (1 : ℝ) else 0) * g O.X * O.Y
          ∂P.dataMeasure := by rw [haf]
      _ = _ := hout
      _ = _ := by rw [hmu, hpi]
  have hcsel' :
      (∫ O, (if O.A = a then (1 : ℝ) else 0) * (g O.X * c O.X) ∂P.dataMeasure) =
        ∫ O, armPi P a O.X * (g O.X * c O.X) ∂P.dataMeasure := by
    calc
      _ = ∫ O, (if O.A = (((af : ℕ) : ℝ)) then (1 : ℝ) else 0) *
          (g O.X * c O.X) ∂P.dataMeasure := by rw [haf]
      _ = _ := hcsel
      _ = _ := by rw [hpi]
  let FY : (Fin d → ℝ) → ℝ := fun x => armPi P a x * armReg P a x * g x
  let FC : (Fin d → ℝ) → ℝ := fun x => armPi P a x * (g x * c x)
  have hFYmeas : Measurable FY := by
    have hm := ((measurable_indicator_armPi hreg P hP ha).mul
      (measurable_indicator_armReg hreg P hP ha)).mul hg
    convert hm using 1
    funext x
    by_cases hx : x ∈ supBall x0 (rStar r0 x0)
    · simp [FY, hx]
    · simp [FY, hx, hgsupp x hx]
  have hFCmeas : Measurable FC := by
    have hm := (measurable_indicator_armPi hreg P hP ha).mul hgcmeas
    convert hm using 1
    funext x
    by_cases hx : x ∈ supBall x0 (rStar r0 x0)
    · simp [FC, hx]
    · simp [FC, hx, hgsupp x hx]
  haveI : IsProbabilityMeasure (xMarginal P) := by
    unfold xMarginal
    exact Measure.isProbabilityMeasure_map measurable_CateObs_X.aemeasurable
  have hFYint : Integrable FY (xMarginal P) := by
    apply Integrable.of_bound hFYmeas.aestronglyMeasurable L
    filter_upwards with x
    by_cases hx : x ∈ supBall x0 (rStar r0 x0)
    · rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have hp0 := armPi_ge hreg P hP ha x hx
      have hp1 := armPi_le_one hreg P hP ha x hx
      have hm := armReg_abs_le_L hreg P hP ha x
        (supBall_rStar_subset_cube r0 x0 hreg.2.2.2.2.2.2.2.1.1
          hreg.2.2.2.2.2.2.2.2 hx)
      have hpabs : |armPi P a x| ≤ 1 := by
        rw [abs_of_nonneg (hreg.2.2.2.2.1.1.le.trans hp0)]
        exact hp1
      have hpμ : |armPi P a x| * |armReg P a x| ≤ 1 * L :=
        mul_le_mul hpabs hm (abs_nonneg _) zero_le_one
      calc
        |armPi P a x| * |armReg P a x| * |g x| ≤ 1 * L * 1 :=
          mul_le_mul hpμ (hgbd x) (abs_nonneg _) (mul_nonneg zero_le_one hreg.2.2.2.1.le)
        _ = L := by ring
    · have : FY x = 0 := by simp [FY, hgsupp x hx]
      simp [this, hreg.2.2.2.1.le]
  have hFCint : Integrable FC (xMarginal P) := by
    apply Integrable.of_bound hFCmeas.aestronglyMeasurable 1
    filter_upwards with x
    by_cases hx : x ∈ supBall x0 (rStar r0 x0)
    · rw [Real.norm_eq_abs, abs_mul]
      have hp0 := armPi_ge hreg P hP ha x hx
      have hp1 := armPi_le_one hreg P hP ha x hx
      rw [abs_of_nonneg (hreg.2.2.2.2.1.1.le.trans hp0)]
      simpa using mul_le_mul hp1 (hgcb x) (abs_nonneg _) zero_le_one
    · have : FC x = 0 := by simp [FC, hgsupp x hx]
      simp [this]
  calc
    ∫ O, (if O.A = a then (1 : ℝ) else 0) * g O.X * (O.Y - c O.X) ∂P.dataMeasure
        = (∫ O, (if O.A = a then (1 : ℝ) else 0) * g O.X * O.Y ∂P.dataMeasure) -
          ∫ O, (if O.A = a then (1 : ℝ) else 0) * (g O.X * c O.X) ∂P.dataMeasure := by
            rw [← integral_sub hleftY hleftC]
            apply integral_congr_ae
            filter_upwards with O
            ring
    _ = (∫ O, armPi P a O.X * armReg P a O.X * g O.X ∂P.dataMeasure) -
          ∫ O, armPi P a O.X * (g O.X * c O.X) ∂P.dataMeasure := by
            rw [hout', hcsel']
    _ = ∫ x, F x ∂(xMarginal P) := by
      change (∫ O, FY O.X ∂P.dataMeasure) - (∫ O, FC O.X ∂P.dataMeasure) = _
      have hFYint' : Integrable FY (Measure.map (fun O : CateObs d => O.X) P.dataMeasure) := by
        simpa only [xMarginal] using hFYint
      have hFCint' : Integrable FC (Measure.map (fun O : CateObs d => O.X) P.dataMeasure) := by
        simpa only [xMarginal] using hFCint
      rw [← integral_map measurable_CateObs_X.aemeasurable hFYmeas.aestronglyMeasurable,
        ← integral_map measurable_CateObs_X.aemeasurable hFCmeas.aestronglyMeasurable,
        ← integral_sub hFYint' hFCint']
      apply integral_congr_ae
      filter_upwards with x
      simp only [FY, FC, F]
      ring

/-- Each arm regression is bounded by one Lebesgue-a.e. on the localization ball. -/
theorem armReg_abs_le_one_ae {d : ℕ} {alpha beta gamma L e0 f0 f1 r0 : ℝ}
    {x0 : Fin d → ℝ} (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (P : CateLaw d) (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P)
    (hIid : IidSampling P) {a : ℝ} (ha : a = 0 ∨ a = 1) :
    ∀ᵐ x ∂(volume.restrict (supBall x0 (rStar r0 x0))), |armReg P a x| ≤ 1 := by
  classical
  letI : IsProbabilityMeasure P.dataMeasure := hIid.1
  let S := supBall x0 (rStar r0 x0)
  let N := S ∩ {x | 1 < |S.indicator (armReg P a) x|}
  have hS : MeasurableSet S := measurableSet_supBall _ _
  have hN : MeasurableSet N := hS.inter (measurableSet_lt measurable_const
    (by simpa only [Real.norm_eq_abs] using
      (measurable_indicator_armReg hreg P hP ha).norm))
  have hNsub : N ⊆ S := Set.inter_subset_left
  let mA := MeasurableSpace.comap (fun O : CateObs d => (O.A, O.X)) inferInstance
  have hYbdd : ∀ᵐ O ∂P.dataMeasure, |O.Y| ≤ (1 : ℝ) := by
    filter_upwards [hIid.2.1] with O hO
    simpa [abs_le] using hO
  have hCE : ∀ᵐ O ∂P.dataMeasure,
      |P.dataMeasure[(fun O => O.Y) | mA] O| ≤ (1 : ℝ) :=
    ae_bdd_condExp_of_ae_bdd (μ := P.dataMeasure) (m := mA)
      (f := fun O : CateObs d => O.Y) (R := (1 : NNReal)) hYbdd
  have hdata : ∀ᵐ O ∂P.dataMeasure, O.A = a → |armReg P a O.X| ≤ 1 := by
    filter_upwards [hCE, hP.muReg] with O hcond hmuEq
    intro hA
    have hsel : (if O.A = 1 then P.mu1 O.X else P.mu0 O.X) = armReg P a O.X := by
      rcases ha with rfl | rfl
      ·
        rw [hA]
        unfold armReg
        have h01 : (0 : ℝ) ≠ 1 := by norm_num
        simp only [h01, ↓reduceIte]
      ·
        rw [hA]
        unfold armReg
        simp only [↓reduceIte]
    rw [hmuEq, hsel] at hcond
    exact hcond
  let af : Fin 2 := if a = 1 then 1 else 0
  have haf : (((af : ℕ) : ℝ)) = a := by
    rcases ha with rfl | rfl <;> simp [af]
  have hpi : armProb P af = armPi P a := by
    funext x
    rcases ha with rfl | rfl <;> simp [af, armProb] <;> unfold armPi <;> simp
  let gN : (Fin d → ℝ) → ℝ := N.indicator (fun _ => (1 : ℝ))
  have hgN : Measurable gN := Measurable.indicator measurable_const hN
  have hgNbd : ∀ x, |gN x| ≤ (1 : ℝ) := by
    intro x
    by_cases hx : x ∈ N <;> simp [gN, hx]
  have hzeroLeft :
      ∫ O, (if O.A = a then (1 : ℝ) else 0) * gN O.X ∂P.dataMeasure = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hdata] with O hO
    by_cases hA : O.A = a
    · have hnmem : O.X ∉ N := by
        intro hxN
        have hxS : O.X ∈ S := hxN.1
        have hbad : 1 < |armReg P a O.X| := by
          simpa [Set.indicator_of_mem hxS] using hxN.2
        exact (not_lt_of_ge (hO hA)) hbad
      simp [hA, gN, hnmem]
    · simp [hA]
  have harm := integral_arm_indicator_mul P hIid hP.piProp af gN
    hgN.aemeasurable 1 hgNbd
  have hzeroData :
      ∫ O, armPi P a O.X * gN O.X ∂P.dataMeasure = 0 := by
    rw [← hpi, ← harm, haf]
    exact hzeroLeft
  let q : (Fin d → ℝ) → ℝ := fun x => armPi P a x * gN x
  have hqmeas : Measurable q := by
    have hm := (measurable_indicator_armPi hreg P hP ha).mul hgN
    convert hm using 1
    funext x
    by_cases hx : x ∈ N
    · have hxS : x ∈ S := hNsub hx
      change x ∈ supBall x0 (rStar r0 x0) at hxS
      simp [q, gN, hx, hxS]
    · simp [q, gN, hx]
  have hzeroMarg : ∫ x, q x ∂(xMarginal P) = 0 := by
    rw [xMarginal, integral_map measurable_CateObs_X.aemeasurable hqmeas.aestronglyMeasurable]
    simpa only [q] using hzeroData
  haveI : IsProbabilityMeasure (xMarginal P) := by
    unfold xMarginal
    exact Measure.isProbabilityMeasure_map measurable_CateObs_X.aemeasurable
  have hqint : Integrable q (xMarginal P) := by
    apply Integrable.of_bound hqmeas.aestronglyMeasurable 1
    filter_upwards with x
    by_cases hx : x ∈ N
    · have hxS := hNsub hx
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg
        (hreg.2.2.2.2.1.1.le.trans (armPi_ge hreg P hP ha x hxS))]
      simpa [gN, hx] using armPi_le_one hreg P hP ha x hxS
    · simp [q, gN, hx]
  have hqnn : 0 ≤ q := by
    intro x
    by_cases hx : x ∈ N
    · exact mul_nonneg (hreg.2.2.2.2.1.1.le.trans
        (armPi_ge hreg P hP ha x (hNsub hx))) (by simp [gN, hx])
    · simp [q, gN, hx]
  have hqae : q =ᶠ[ae (xMarginal P)] 0 :=
    (integral_eq_zero_iff_of_nonneg hqnn hqint).mp hzeroMarg
  have hnotN : ∀ᵐ x ∂(xMarginal P), x ∉ N := by
    filter_upwards [hqae] with x hxq
    intro hxN
    have hp := armPi_ge hreg P hP ha x (hNsub hxN)
    have : q x = armPi P a x := by simp [q, gN, hxN]
    rw [this] at hxq
    change armPi P a x = 0 at hxq
    linarith [hreg.2.2.2.2.1.1]
  have hxNzero : xMarginal P N = 0 := by
    simpa only [not_not] using (ae_iff.mp hnotN)
  have hvolN : volume N = 0 := by
    have hlo := ofReal_f0_mul_volume_le_xMarginal hreg P hP N hN hNsub
    rw [hxNzero] at hlo
    have hz : ENNReal.ofReal f0 * volume N = 0 := bot_unique hlo
    exact (mul_eq_zero.mp hz).resolve_left
      (ne_of_gt (ENNReal.ofReal_pos.mpr hreg.2.2.2.2.2.1))
  have hnotNvol : ∀ᵐ x ∂(volume.restrict S), x ∉ N := by
    rw [ae_iff]
    have hrN : (volume.restrict S) N = 0 := by
      rw [Measure.restrict_apply hN, Set.inter_eq_left.mpr hNsub, hvolN]
    simpa only [not_not] using hrN
  filter_upwards [ae_restrict_mem hS, hnotNvol] with x hxS hxN
  by_contra hbad
  apply hxN
  refine ⟨hxS, ?_⟩
  change 1 < |S.indicator (armReg P a) x|
  rw [Set.indicator_of_mem hxS]
  exact lt_of_not_ge hbad

end

end CausalSmith.Stat.DpCateMinimax
