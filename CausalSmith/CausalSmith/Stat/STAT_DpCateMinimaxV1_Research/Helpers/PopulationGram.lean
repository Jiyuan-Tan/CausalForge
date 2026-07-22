/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PopulationDesign
import Causalean.Mathlib.Analysis.MonomialGram
import Causalean.Stat.Nonparametric.Approximation.HolderTaylorMonomial
import Causalean.Mathlib.Analysis.ConvexProjection
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Algebra.Order.Chebyshev

/-!
# Population local-polynomial Gram matrices

This module defines the population normal equations for one treatment arm and proves the
uniform localization estimates used to control them.  All constants in the results are
functions only of model and kernel parameters, never of the law or bandwidth.
-/

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory Set Matrix
open scoped BigOperators ENNReal Pointwise
open Causalean.Mathlib.Analysis
open Causalean.Stat.Nonparametric

/-- The rescaled covariate coordinate `u = (x - x₀) / h`. -/
noncomputable def uCoord {d : ℕ} (h : ℝ) (x0 x : Fin d → ℝ) : Fin d → ℝ :=
  fun j ↦ (x j - x0 j) / h

/-- One observation's arm-specific kernel-weighted Gram entry. -/
noncomputable def gramSummand {d p : ℕ} (h : ℝ) (x0 : Fin d → ℝ)
    (expo : Fin p → (Fin d → ℕ)) (K : (Fin d → ℝ) → ℝ)
    (a : Fin 2) (O : CateObs d) (k l : Fin p) : ℝ :=
  (if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0) * h ^ (-(d : ℝ)) *
    K (uCoord h x0 O.X) * monomial (expo k) (uCoord h x0 O.X) *
      monomial (expo l) (uCoord h x0 O.X)

/-- One observation's arm-specific kernel-weighted (clipped) outcome moment entry. -/
noncomputable def momSummand {d p : ℕ} (h : ℝ) (x0 : Fin d → ℝ)
    (expo : Fin p → (Fin d → ℕ)) (K : (Fin d → ℝ) → ℝ)
    (a : Fin 2) (O : CateObs d) (k : Fin p) : ℝ :=
  (if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0) * h ^ (-(d : ℝ)) *
    K (uCoord h x0 O.X) * max (-1) (min 1 O.Y) *
      monomial (expo k) (uCoord h x0 O.X)

/-- The population arm-specific kernel-weighted Gram matrix. -/
noncomputable def popGram {d p : ℕ} (P : CateLaw d) (h : ℝ) (x0 : Fin d → ℝ)
    (expo : Fin p → (Fin d → ℕ)) (K : (Fin d → ℝ) → ℝ) (a : Fin 2) :
    Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun k l ↦ ∫ O, gramSummand h x0 expo K a O k l ∂P.dataMeasure

/-- The population arm-specific kernel-weighted outcome moment vector. -/
noncomputable def popMom {d p : ℕ} (P : CateLaw d) (h : ℝ) (x0 : Fin d → ℝ)
    (expo : Fin p → (Fin d → ℕ)) (K : (Fin d → ℝ) → ℝ) (a : Fin 2) :
    Fin p → ℝ :=
  fun k ↦ ∫ O, momSummand h x0 expo K a O k ∂P.dataMeasure

/-- A bandwidth no larger than `rStar` stays both inside the covariate cube and inside the
local-density neighborhood.  Positive dimension is needed because `rStar` uses a finite infimum. -/
theorem supBall_subset_of_lt_rStar {d : ℕ}
    {alpha beta gamma L e0 f0 f1 r0 : ℝ} {x0 : Fin d → ℝ}
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    {h : ℝ} (hh : 0 < h) (hhr : h ≤ rStar r0 x0) :
    supBall x0 h ⊆ cube d ∧ supBall x0 h ⊆ supBall x0 r0 := by
  have hr0 : 0 < r0 := hreg.2.2.2.2.2.2.2.1.1
  have hrstar_r0 : rStar r0 x0 ≤ r0 := by
    unfold rStar
    have hm : min r0 (⨅ i : Fin d, min (x0 i) (1 - x0 i)) ≤ r0 := min_le_left _ _
    nlinarith
  constructor
  · intro x hx i
    have hi := hreg.2.2.2.2.2.2.2.2 i
    have hinf : (⨅ j : Fin d, min (x0 j) (1 - x0 j)) ≤
        min (x0 i) (1 - x0 i) :=
      ciInf_le (Set.Finite.bddBelow (Set.finite_range
        (fun j : Fin d ↦ min (x0 j) (1 - x0 j)))) i
    have hrx0 : rStar r0 x0 ≤ x0 i / 2 := by
      unfold rStar
      have hm : min r0 (⨅ j : Fin d, min (x0 j) (1 - x0 j)) ≤ x0 i :=
        (min_le_right _ _).trans (hinf.trans (min_le_left _ _))
      nlinarith
    have hr1x0 : rStar r0 x0 ≤ (1 - x0 i) / 2 := by
      unfold rStar
      have hm : min r0 (⨅ j : Fin d, min (x0 j) (1 - x0 j)) ≤ 1 - x0 i :=
        (min_le_right _ _).trans (hinf.trans (min_le_right _ _))
      nlinarith
    have habs := hx i
    rw [abs_le] at habs
    constructor <;> linarith
  · intro x hx i
    exact (hx i).trans (hhr.trans hrstar_r0)

/-- On a localized sup-ball, every monomial feature has absolute value at most one. -/
theorem abs_monomial_uCoord_le_one {d : ℕ} {h : ℝ} {x0 x : Fin d → ℝ}
    (hh : 0 < h) (hx : x ∈ supBall x0 h) (e : Fin d → ℕ) :
    |monomial e (uCoord h x0 x)| ≤ 1 := by
  rw [monomial, show |∏ j, (uCoord h x0 x j) ^ (e j)| =
      ∏ j, |(uCoord h x0 x j) ^ (e j)| by
    simpa using (Finset.abs_prod Finset.univ (fun j ↦ (uCoord h x0 x j) ^ (e j)))]
  apply Finset.prod_le_one
  · intro j _
    positivity
  · intro j _
    rw [abs_pow]
    apply pow_le_one₀ (abs_nonneg _)
    rw [uCoord, abs_div, abs_of_pos hh]
    exact (div_le_one hh).2 (hx j)

/-- A Gram summand vanishes outside the kernel's rescaled unit cube. -/
theorem gramSummand_eq_zero_of_not_mem {d p : ℕ} {h : ℝ} {x0 : Fin d → ℝ}
    {expo : Fin p → (Fin d → ℕ)} {K : (Fin d → ℝ) → ℝ}
    (hh : 0 < h) (hKsupp : ∀ u, (∃ j, 1 < |u j|) → K u = 0)
    (a : Fin 2) (O : CateObs d) (k l : Fin p) (hO : O.X ∉ supBall x0 h) :
    gramSummand h x0 expo K a O k l = 0 := by
  have hex : ∃ j, h < |O.X j - x0 j| := by
    simpa [supBall, not_forall, not_le] using hO
  obtain ⟨j, hj⟩ := hex
  have hu : 1 < |uCoord h x0 O.X j| := by
    rw [uCoord, abs_div, abs_of_pos hh]
    exact (lt_div_iff₀ hh).2 (by simpa using hj)
  simp [gramSummand, hKsupp _ ⟨j, hu⟩]

/-- A moment summand vanishes outside the kernel's rescaled unit cube. -/
theorem momSummand_eq_zero_of_not_mem {d p : ℕ} {h : ℝ} {x0 : Fin d → ℝ}
    {expo : Fin p → (Fin d → ℕ)} {K : (Fin d → ℝ) → ℝ}
    (hh : 0 < h) (hKsupp : ∀ u, (∃ j, 1 < |u j|) → K u = 0)
    (a : Fin 2) (O : CateObs d) (k : Fin p) (hO : O.X ∉ supBall x0 h) :
    momSummand h x0 expo K a O k = 0 := by
  have hex : ∃ j, h < |O.X j - x0 j| := by
    simpa [supBall, not_forall, not_le] using hO
  obtain ⟨j, hj⟩ := hex
  have hu : 1 < |uCoord h x0 O.X j| := by
    rw [uCoord, abs_div, abs_of_pos hh]
    exact (lt_div_iff₀ hh).2 (by simpa using hj)
  simp [momSummand, hKsupp _ ⟨j, hu⟩]

/-- Every Gram summand is bounded by the bandwidth scaling times the kernel envelope. -/
theorem abs_gramSummand_le {d p : ℕ} {h Kmax : ℝ} {x0 : Fin d → ℝ}
    {expo : Fin p → (Fin d → ℕ)} {K : (Fin d → ℝ) → ℝ}
    (hh : 0 < h) (hK0 : ∀ u, 0 ≤ K u) (hKmax : ∀ u, K u ≤ Kmax)
    (hKsupp : ∀ u, (∃ j, 1 < |u j|) → K u = 0)
    (a : Fin 2) (O : CateObs d) (k l : Fin p) :
    |gramSummand h x0 expo K a O k l| ≤ h ^ (-(d : ℝ)) * Kmax := by
  by_cases hO : O.X ∈ supBall x0 h
  · have hk := abs_monomial_uCoord_le_one hh hO (expo k)
    have hl := abs_monomial_uCoord_le_one hh hO (expo l)
    have hKn : |K (uCoord h x0 O.X)| ≤ Kmax := by
      rw [abs_of_nonneg (hK0 _)]
      exact hKmax _
    rw [gramSummand, abs_mul, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hh.le _)]
    have hind : |if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0| ≤ 1 := by
      split <;> simp
    have hrp : 0 ≤ h ^ (-(d : ℝ)) := Real.rpow_nonneg hh.le _
    have hKm0 : 0 ≤ Kmax :=
      (hK0 (fun _ : Fin d ↦ 0)).trans (hKmax (fun _ : Fin d ↦ 0))
    calc
      _ ≤ 1 * h ^ (-(d : ℝ)) * Kmax * 1 * 1 := by gcongr
      _ = h ^ (-(d : ℝ)) * Kmax := by ring
  · rw [gramSummand_eq_zero_of_not_mem hh hKsupp a O k l hO, abs_zero]
    exact mul_nonneg (Real.rpow_nonneg hh.le _)
      ((hK0 (fun _ : Fin d ↦ 0)).trans (hKmax (fun _ : Fin d ↦ 0)))

/-- Every clipped outcome moment summand obeys the same envelope as a Gram entry. -/
theorem abs_momSummand_le {d p : ℕ} {h Kmax : ℝ} {x0 : Fin d → ℝ}
    {expo : Fin p → (Fin d → ℕ)} {K : (Fin d → ℝ) → ℝ}
    (hh : 0 < h) (hK0 : ∀ u, 0 ≤ K u) (hKmax : ∀ u, K u ≤ Kmax)
    (hKsupp : ∀ u, (∃ j, 1 < |u j|) → K u = 0)
    (a : Fin 2) (O : CateObs d) (k : Fin p) :
    |momSummand h x0 expo K a O k| ≤ h ^ (-(d : ℝ)) * Kmax := by
  by_cases hO : O.X ∈ supBall x0 h
  · have hk := abs_monomial_uCoord_le_one hh hO (expo k)
    have hKn : |K (uCoord h x0 O.X)| ≤ Kmax := by
      rw [abs_of_nonneg (hK0 _)]
      exact hKmax _
    have hclip : |max (-1 : ℝ) (min 1 O.Y)| ≤ 1 := by
      rw [abs_le]
      exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
    rw [momSummand, abs_mul, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hh.le _)]
    have hind : |if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0| ≤ 1 := by
      split <;> simp
    have hrp : 0 ≤ h ^ (-(d : ℝ)) := Real.rpow_nonneg hh.le _
    have hKm0 : 0 ≤ Kmax :=
      (hK0 (fun _ : Fin d ↦ 0)).trans (hKmax (fun _ : Fin d ↦ 0))
    calc
      _ ≤ 1 * h ^ (-(d : ℝ)) * Kmax * 1 * 1 := by gcongr
      _ = h ^ (-(d : ℝ)) * Kmax := by ring
  · rw [momSummand_eq_zero_of_not_mem hh hKsupp a O k hO, abs_zero]
    exact mul_nonneg (Real.rpow_nonneg hh.le _)
      ((hK0 (fun _ : Fin d ↦ 0)).trans (hKmax (fun _ : Fin d ↦ 0)))

/- The remaining population integral arguments are being developed below this checkpoint.
/-- Sup-norm balls in finite-dimensional real coordinate spaces are measurable. -/
theorem measurableSet_supBall {d : ℕ} (x0 : Fin d → ℝ) (h : ℝ) :
    MeasurableSet (supBall x0 h) := by
  rw [show supBall x0 h = ⋂ i : Fin d, {x | |x i - x0 i| ≤ h} by
    ext x
    simp [supBall]]
  exact MeasurableSet.iInter fun i ↦
    measurableSet_Iic.preimage (measurable_abs.comp
      ((measurable_pi_apply i).sub measurable_const))

private lemma measurable_gramSummand {d p : ℕ} {h : ℝ} {x0 : Fin d → ℝ}
    {expo : Fin p → (Fin d → ℕ)} {K : (Fin d → ℝ) → ℝ}
    (hKmeas : Measurable K) (a : Fin 2) (k l : Fin p) :
    Measurable (fun O : CateObs d ↦ gramSummand h x0 expo K a O k l) := by
  unfold gramSummand monomial uCoord
  exact (((Measurable.ite
    (measurableSet_eq_fun measurable_CateObs_A measurable_const)
    measurable_const measurable_const).mul measurable_const).mul
      (hKmeas.comp (measurable_pi_lambda _ fun j ↦
        ((measurable_CateObs_X.eval j).sub measurable_const).div measurable_const))).mul
      (measurable_finset_prod _ fun j _ ↦
        (((measurable_CateObs_X.eval j).sub measurable_const).div measurable_const).pow _)).mul
      (measurable_finset_prod _ fun j _ ↦
        (((measurable_CateObs_X.eval j).sub measurable_const).div measurable_const).pow _)

private lemma measurable_momSummand {d p : ℕ} {h : ℝ} {x0 : Fin d → ℝ}
    {expo : Fin p → (Fin d → ℕ)} {K : (Fin d → ℝ) → ℝ}
    (hKmeas : Measurable K) (a : Fin 2) (k : Fin p) :
    Measurable (fun O : CateObs d ↦ momSummand h x0 expo K a O k) := by
  unfold momSummand monomial uCoord
  exact ((((Measurable.ite
    (measurableSet_eq_fun measurable_CateObs_A measurable_const)
    measurable_const measurable_const).mul measurable_const).mul
      (hKmeas.comp (measurable_pi_lambda _ fun j ↦
        ((measurable_CateObs_X.eval j).sub measurable_const).div measurable_const))).mul
      (measurable_const.max (measurable_const.min measurable_CateObs_Y))).mul
      (measurable_finset_prod _ fun j _ ↦
        (((measurable_CateObs_X.eval j).sub measurable_const).div measurable_const).pow _)

private lemma integral_sq_le_ball_mass {d : ℕ} (P : CateLaw d) (hiid : IidSampling P)
    {h B : ℝ} {x0 : Fin d → ℝ} {q : CateObs d → ℝ}
    (hq : Measurable q) (hB : 0 ≤ B) (hqB : ∀ O, |q O| ≤ B)
    (hqsupp : ∀ O, O.X ∉ supBall x0 h → q O = 0) :
    ∫ O, (q O) ^ 2 ∂P.dataMeasure ≤
      B ^ 2 * (P.dataMeasure.map (fun O ↦ O.X)).real (supBall x0 h) := by
  letI : IsProbabilityMeasure P.dataMeasure := hiid.1
  let S : Set (CateObs d) := {O | O.X ∈ supBall x0 h}
  have hS : MeasurableSet S := (measurableSet_supBall x0 h).preimage measurable_CateObs_X
  have hpoint : ∀ O, (q O) ^ 2 ≤ (S.indicator fun _ ↦ B ^ 2) O := by
    intro O
    by_cases hO : O ∈ S
    · rw [Set.indicator_of_mem hO]
      exact (sq_le_sq₀ (abs_nonneg _) hB (hqB O)).mpr (hqB O)
    · simp [S, hO, hqsupp O hO]
  have hleft : Integrable (fun O ↦ (q O) ^ 2) P.dataMeasure := by
    apply Integrable.of_bound (C := B ^ 2) (hq.pow_const 2).aestronglyMeasurable
    filter_upwards with O
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (abs_nonneg _) hB (hqB O)).mpr (hqB O)
  have hright : Integrable (S.indicator fun _ ↦ B ^ 2) P.dataMeasure :=
    (integrable_const (B ^ 2)).indicator hS
  calc
    ∫ O, (q O) ^ 2 ∂P.dataMeasure ≤ ∫ O, S.indicator (fun _ ↦ B ^ 2) O ∂P.dataMeasure :=
      integral_mono hleft hright hpoint
    _ = B ^ 2 * P.dataMeasure.real S := by
      rw [integral_indicator hS]
      simp [Measure.real, mul_comm]
    _ = B ^ 2 * (P.dataMeasure.map (fun O ↦ O.X)).real (supBall x0 h) := by
      congr 1
      rw [Measure.real, Measure.real, Measure.map_apply measurable_CateObs_X
        (measurableSet_supBall x0 h)]
      rfl

private lemma bandwidth_square_mass_cancel {d : ℕ} {h : ℝ} (hh : 0 < h) :
    (h ^ (-(d : ℝ))) ^ 2 * (2 * h) ^ d = (2 : ℝ) ^ d * h ^ (-(d : ℝ)) := by
  rw [mul_pow]
  have hnat : h ^ d = h ^ (d : ℝ) := by
    symm
    exact Real.rpow_natCast h d
  rw [hnat, ← Real.rpow_natCast 2 d]
  rw [← Real.rpow_mul hh.le]
    show -(d : ℝ) * 2 = -(d : ℝ) + -(d : ℝ) by ring,
    Real.rpow_add (le_of_lt hh), mul_assoc]
  ring

/-- The second moment of a Gram entry is `O(h⁻ᵈ)`, uniformly over the model class. -/
theorem integral_gramSummand_sq_le {d p : ℕ} {alpha beta gamma L e0 f0 f1 r0 h Kmax : ℝ}
    {x0 : Fin d → ℝ} {P : CateLaw d} {expo : Fin p → (Fin d → ℕ)}
    {K : (Fin d → ℝ) → ℝ}
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P)
    (hiid : IidSampling P) (hh : 0 < h) (hhr : h ≤ r0)
    (hK0 : ∀ u, 0 ≤ K u) (hKmax : ∀ u, K u ≤ Kmax)
    (hKsupp : ∀ u, (∃ j, 1 < |u j|) → K u = 0) (hKmeas : Measurable K)
    (a : Fin 2) (k l : Fin p) :
    ∫ O, (gramSummand h x0 expo K a O k l) ^ 2 ∂P.dataMeasure ≤
      (Kmax ^ 2 * f1 * 2 ^ d) * h ^ (-(d : ℝ)) := by
  have hKmax0 : 0 ≤ Kmax := (hK0 (fun _ ↦ 0)).trans (hKmax _)
  have hb := integral_sq_le_ball_mass P hiid
    (measurable_gramSummand hKmeas a k l)
    (mul_nonneg (Real.rpow_nonneg hh.le _) hKmax0)
    (abs_gramSummand_le hh hK0 hKmax hKsupp a)
    (gramSummand_eq_zero_of_not_mem hh hKsupp a)
  have hm := design_mass_le P f0 f1 r0 x0 hiid hP.pxDens hP.localDensity
    (hreg.2.2.2.2.2.1.le.trans hreg.2.2.2.2.2.2.1) hh hhr
  calc
    _ ≤ (h ^ (-(d : ℝ)) * Kmax) ^ 2 *
        (P.dataMeasure.map (fun O ↦ O.X)).real (supBall x0 h) := hb
    _ ≤ (h ^ (-(d : ℝ)) * Kmax) ^ 2 * (f1 * (2 * h) ^ d) := by
      gcongr
    _ = (Kmax ^ 2 * f1 * 2 ^ d) * h ^ (-(d : ℝ)) := by
      rw [mul_pow, bandwidth_square_mass_cancel hh]
      ring

/-- The second moment of a clipped outcome moment entry has the same `O(h⁻ᵈ)` bound. -/
theorem integral_momSummand_sq_le {d p : ℕ} {alpha beta gamma L e0 f0 f1 r0 h Kmax : ℝ}
    {x0 : Fin d → ℝ} {P : CateLaw d} {expo : Fin p → (Fin d → ℕ)}
    {K : (Fin d → ℝ) → ℝ}
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P)
    (hiid : IidSampling P) (hh : 0 < h) (hhr : h ≤ r0)
    (hK0 : ∀ u, 0 ≤ K u) (hKmax : ∀ u, K u ≤ Kmax)
    (hKsupp : ∀ u, (∃ j, 1 < |u j|) → K u = 0) (hKmeas : Measurable K)
    (a : Fin 2) (k : Fin p) :
    ∫ O, (momSummand h x0 expo K a O k) ^ 2 ∂P.dataMeasure ≤
      (Kmax ^ 2 * f1 * 2 ^ d) * h ^ (-(d : ℝ)) := by
  have hKmax0 : 0 ≤ Kmax := (hK0 (fun _ ↦ 0)).trans (hKmax _)
  have hb := integral_sq_le_ball_mass P hiid
    (measurable_momSummand hKmeas a k)
    (mul_nonneg (Real.rpow_nonneg hh.le _) hKmax0)
    (abs_momSummand_le hh hK0 hKmax hKsupp a)
    (momSummand_eq_zero_of_not_mem hh hKsupp a)
  have hm := design_mass_le P f0 f1 r0 x0 hiid hP.pxDens hP.localDensity
    (hreg.2.2.2.2.2.1.le.trans hreg.2.2.2.2.2.2.1) hh hhr
  calc
    _ ≤ (h ^ (-(d : ℝ)) * Kmax) ^ 2 *
        (P.dataMeasure.map (fun O ↦ O.X)).real (supBall x0 h) := hb
    _ ≤ (h ^ (-(d : ℝ)) * Kmax) ^ 2 * (f1 * (2 * h) ^ d) := by
      gcongr
    _ = (Kmax ^ 2 * f1 * 2 ^ d) * h ^ (-(d : ℝ)) := by
      rw [mul_pow, bandwidth_square_mass_cancel hh]
      ring

private lemma abs_integral_le_ball_mass {d : ℕ} (P : CateLaw d) (hiid : IidSampling P)
    {h B : ℝ} {x0 : Fin d → ℝ} {q : CateObs d → ℝ}
    (hq : Measurable q) (hB : 0 ≤ B) (hqB : ∀ O, |q O| ≤ B)
    (hqsupp : ∀ O, O.X ∉ supBall x0 h → q O = 0) :
    |∫ O, q O ∂P.dataMeasure| ≤
      B * (P.dataMeasure.map (fun O ↦ O.X)).real (supBall x0 h) := by
  letI : IsProbabilityMeasure P.dataMeasure := hiid.1
  let S : Set (CateObs d) := {O | O.X ∈ supBall x0 h}
  have hS : MeasurableSet S := (measurableSet_supBall x0 h).preimage measurable_CateObs_X
  have hqint : Integrable q P.dataMeasure :=
    Integrable.of_bound hq.aestronglyMeasurable B (Filter.Eventually.of_forall fun O ↦ by
      simpa [Real.norm_eq_abs] using hqB O)
  calc
    |∫ O, q O ∂P.dataMeasure| ≤ ∫ O, |q O| ∂P.dataMeasure := abs_integral_le_integral_abs
    _ ≤ ∫ O, S.indicator (fun _ ↦ B) O ∂P.dataMeasure := by
      apply integral_mono (hqint.abs) ((integrable_const B).indicator hS)
      intro O
      by_cases hO : O ∈ S
      · simpa [Set.indicator_of_mem hO] using hqB O
      · simp [S, hO, hqsupp O hO]
    _ = B * P.dataMeasure.real S := by
      rw [integral_indicator hS]
      simp [Measure.real, mul_comm]
    _ = B * (P.dataMeasure.map (fun O ↦ O.X)).real (supBall x0 h) := by
      congr 1
      rw [Measure.real, Measure.real, Measure.map_apply measurable_CateObs_X
        (measurableSet_supBall x0 h)]
      rfl

private lemma bandwidth_mass_cancel {d : ℕ} {h : ℝ} (hh : 0 < h) :
    h ^ (-(d : ℝ)) * (2 * h) ^ d = (2 : ℝ) ^ d := by
  rw [mul_pow, ← Real.rpow_natCast 2 d, ← Real.rpow_natCast h d]
  rw [show h ^ (-(d : ℝ)) * (2 ^ (d : ℝ) * h ^ (d : ℝ)) =
    2 ^ (d : ℝ) * (h ^ (-(d : ℝ)) * h ^ (d : ℝ)) by ring,
    ← Real.rpow_add hh.le]
  simp

/-- The Euclidean norm of the population moment vector is uniformly bounded. -/
theorem norm_popMom_le {d p : ℕ} {alpha beta gamma L e0 f0 f1 r0 h Kmax : ℝ}
    {x0 : Fin d → ℝ} {P : CateLaw d} {expo : Fin p → (Fin d → ℕ)}
    {K : (Fin d → ℝ) → ℝ}
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P)
    (hiid : IidSampling P) (hh : 0 < h) (hhr : h ≤ r0)
    (hK0 : ∀ u, 0 ≤ K u) (hKmax : ∀ u, K u ≤ Kmax)
    (hKsupp : ∀ u, (∃ j, 1 < |u j|) → K u = 0) (hKmeas : Measurable K)
    (a : Fin 2) :
    Real.sqrt (∑ k, (popMom P h x0 expo K a k) ^ 2) ≤
      Real.sqrt (p : ℝ) * (Kmax * f1 * 2 ^ d) := by
  have hKmax0 : 0 ≤ Kmax := (hK0 (fun _ ↦ 0)).trans (hKmax _)
  have hf10 : 0 ≤ f1 := hreg.2.2.2.2.2.1.le.trans hreg.2.2.2.2.2.2.1
  have hcoord : ∀ k : Fin p, |popMom P h x0 expo K a k| ≤ Kmax * f1 * 2 ^ d := by
    intro k
    have hb := abs_integral_le_ball_mass P hiid
      (measurable_momSummand hKmeas a k)
      (mul_nonneg (Real.rpow_nonneg hh.le _) hKmax0)
      (abs_momSummand_le hh hK0 hKmax hKsupp a)
      (momSummand_eq_zero_of_not_mem hh hKsupp a)
    have hm := design_mass_le P f0 f1 r0 x0 hiid hP.pxDens hP.localDensity hf10 hh hhr
    calc
      |popMom P h x0 expo K a k| ≤ h ^ (-(d : ℝ)) * Kmax *
          (P.dataMeasure.map (fun O ↦ O.X)).real (supBall x0 h) := hb
      _ ≤ h ^ (-(d : ℝ)) * Kmax * (f1 * (2 * h) ^ d) := by gcongr
      _ = Kmax * f1 * 2 ^ d := by
        rw [show h ^ (-(d : ℝ)) * Kmax * (f1 * (2 * h) ^ d) =
          (Kmax * f1) * (h ^ (-(d : ℝ)) * (2 * h) ^ d) by ring,
          bandwidth_mass_cancel hh]
  have hs : ∑ k, (popMom P h x0 expo K a k) ^ 2 ≤
      (p : ℝ) * (Kmax * f1 * 2 ^ d) ^ 2 := by
    calc
      _ ≤ ∑ _k : Fin p, (Kmax * f1 * 2 ^ d) ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        nlinarith [sq_nonneg (|popMom P h x0 expo K a k| - (Kmax * f1 * 2 ^ d)),
          hcoord k]
      _ = _ := by simp
  calc
    Real.sqrt (∑ k, (popMom P h x0 expo K a k) ^ 2) ≤
        Real.sqrt ((p : ℝ) * (Kmax * f1 * 2 ^ d) ^ 2) := Real.sqrt_le_sqrt hs
    _ = Real.sqrt (p : ℝ) * (Kmax * f1 * 2 ^ d) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg p), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (mul_nonneg (mul_nonneg hKmax0 hf10) (pow_nonneg (by norm_num) _))]

-/

/-- Change variables from a localized covariate to its rescaled coordinate. -/
theorem integral_uCoord_comp {d : ℕ} (h : ℝ) (hh : 0 < h) (x0 : Fin d → ℝ)
    (r : ℝ) (hr : 0 ≤ r) (F : (Fin d → ℝ) → ℝ) (hF : Measurable F)
    (hFint : IntegrableOn F (supBall (0 : Fin d → ℝ) r)) :
    (∫ x in supBall x0 (h * r), F (uCoord h x0 x)) =
      h ^ d * ∫ u in supBall (0 : Fin d → ℝ) r, F u := by
  classical
  have _hF := hF
  have _hFint := hFint
  have _hr := hr
  let Sx := supBall x0 (h * r)
  let Sh := supBall (0 : Fin d → ℝ) (h * r)
  let S0 := supBall (0 : Fin d → ℝ) r
  have measurable_supBall (c : Fin d → ℝ) (R : ℝ) :
      MeasurableSet (supBall c R) := by
    rw [show supBall c R = ⋂ i : Fin d, {x | |x i - c i| ≤ R} by
      ext x
      simp [supBall]]
    exact MeasurableSet.iInter fun i ↦ measurableSet_le
      (continuous_abs.measurable.comp ((measurable_pi_apply i).sub measurable_const))
      measurable_const
  have htranslate :
      (∫ x in Sx, F (uCoord h x0 x)) = ∫ y in Sh, F (h⁻¹ • y) := by
    rw [← integral_indicator (measurable_supBall _ _),
      ← integral_indicator (measurable_supBall _ _)]
    rw [← integral_add_left_eq_self (Sx.indicator fun x ↦ F (uCoord h x0 x)) x0]
    apply integral_congr_ae
    filter_upwards with y
    have hmem : x0 + y ∈ Sx ↔ y ∈ Sh := by
      simp [Sx, Sh, supBall]
    have hu : uCoord h x0 (x0 + y) = h⁻¹ • y := by
      funext i
      simp [uCoord, Pi.smul_apply, div_eq_mul_inv, mul_comm]
    change (if x0 + y ∈ Sx then F (uCoord h x0 (x0 + y)) else 0) =
      if y ∈ Sh then F (h⁻¹ • y) else 0
    exact if_congr hmem (by simp [hu]) rfl
  have hscale : h⁻¹ • Sh = S0 := by
    ext u
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hh.ne')]
    simp only [Sh, S0, supBall, Set.mem_setOf_eq, Pi.zero_apply, sub_zero,
      Pi.smul_apply, inv_inv]
    constructor
    · intro hu i
      have hi := hu i
      change |h * u i| ≤ h * r at hi
      rw [abs_mul, abs_of_pos hh] at hi
      exact le_of_mul_le_mul_left hi hh
    · intro hu i
      change |h * u i| ≤ h * r
      rw [abs_mul, abs_of_pos hh]
      exact mul_le_mul_of_nonneg_left (hu i) hh.le
  calc
    (∫ x in Sx, F (uCoord h x0 x)) = ∫ y in Sh, F (h⁻¹ • y) := htranslate
    _ = ((h⁻¹) ^ Module.finrank ℝ (Fin d → ℝ))⁻¹ • ∫ u in h⁻¹ • Sh, F u :=
      Measure.setIntegral_comp_smul_of_pos volume F Sh (inv_pos.mpr hh)
    _ = h ^ d * ∫ u in S0, F u := by
      rw [hscale, Module.finrank_pi]
      simp [inv_pow]
    _ = h ^ d * ∫ u in supBall (0 : Fin d → ℝ) r, F u := rfl

private theorem measurableSet_supBall_active {d : ℕ} (c : Fin d → ℝ) (R : ℝ) :
    MeasurableSet (supBall c R) := by
  rw [show supBall c R = ⋂ i : Fin d, {x | |x i - c i| ≤ R} by
    ext x
    simp [supBall]]
  exact MeasurableSet.iInter fun i ↦ measurableSet_le
    (continuous_abs.measurable.comp ((measurable_pi_apply i).sub measurable_const))
    measurable_const

private noncomputable def gramQuad {d p : ℕ} (h : ℝ) (x0 : Fin d → ℝ)
    (expo : Fin p → (Fin d → ℕ)) (K : (Fin d → ℝ) → ℝ) (z : Fin p → ℝ)
    (x : Fin d → ℝ) : ℝ :=
  h ^ (-(d : ℝ)) * K (uCoord h x0 x) *
    (∑ k, z k * monomial (expo k) (uCoord h x0 x)) ^ 2

private theorem measurable_gramQuad {d p : ℕ} {h : ℝ} {x0 : Fin d → ℝ}
    {expo : Fin p → (Fin d → ℕ)} {K : (Fin d → ℝ) → ℝ} (hKmeas : Measurable K)
    (z : Fin p → ℝ) : Measurable (gramQuad h x0 expo K z) := by
  unfold gramQuad uCoord monomial
  fun_prop

private theorem gramQuad_nonneg {d p : ℕ} {h : ℝ} (hh : 0 < h)
    {x0 : Fin d → ℝ} {expo : Fin p → (Fin d → ℕ)} {K : (Fin d → ℝ) → ℝ}
    (hK0 : ∀ u, 0 ≤ K u) (z : Fin p → ℝ) (x : Fin d → ℝ) :
    0 ≤ gramQuad h x0 expo K z x := by
  unfold gramQuad
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hh.le _) (hK0 _)) (sq_nonneg _)

private theorem feature_sq_le {d p : ℕ} {h : ℝ} {x0 x : Fin d → ℝ}
    {expo : Fin p → (Fin d → ℕ)} (hh : 0 < h) (hx : x ∈ supBall x0 h)
    (z : Fin p → ℝ) :
    (∑ k, z k * monomial (expo k) (uCoord h x0 x)) ^ 2 ≤
      (p : ℝ) * ∑ k, (z k) ^ 2 := by
  calc
    _ ≤ ((Finset.univ.card : ℕ) : ℝ) *
        ∑ k, (z k * monomial (expo k) (uCoord h x0 x)) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ (p : ℝ) * ∑ k, (z k) ^ 2 := by
      simp only [Finset.card_univ, Fintype.card_fin]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg p)
      apply Finset.sum_le_sum
      intro k _
      have hm := abs_monomial_uCoord_le_one hh hx (expo k)
      let m := monomial (expo k) (uCoord h x0 x)
      have hm2 : m ^ 2 ≤ 1 := by
        simpa [m] using (sq_le_sq₀ (abs_nonneg m) zero_le_one).mpr hm
      calc
        (z k * m) ^ 2 = (z k) ^ 2 * m ^ 2 := by ring
        _ ≤ (z k) ^ 2 * 1 := mul_le_mul_of_nonneg_left hm2 (sq_nonneg _)
        _ = (z k) ^ 2 := by ring

private theorem gramQuad_eq_zero_of_not_mem {d p : ℕ} {h : ℝ} (hh : 0 < h)
    {x0 : Fin d → ℝ} {expo : Fin p → (Fin d → ℕ)} {K : (Fin d → ℝ) → ℝ}
    (hKsupp : ∀ u, (∃ j, 1 < |u j|) → K u = 0) (z : Fin p → ℝ)
    {x : Fin d → ℝ} (hx : x ∉ supBall x0 h) : gramQuad h x0 expo K z x = 0 := by
  have hex : ∃ j, h < |x j - x0 j| := by
    simpa [supBall, not_forall, not_le] using hx
  obtain ⟨j, hj⟩ := hex
  have hu : 1 < |uCoord h x0 x j| := by
    rw [uCoord, abs_div, abs_of_pos hh]
    exact (lt_div_iff₀ hh).2 (by simpa using hj)
  simp [gramQuad, hKsupp _ ⟨j, hu⟩]

private theorem gramQuad_le {d p : ℕ} {h Kmax : ℝ} (hh : 0 < h)
    {x0 : Fin d → ℝ} {expo : Fin p → (Fin d → ℕ)} {K : (Fin d → ℝ) → ℝ}
    (hK0 : ∀ u, 0 ≤ K u) (hKmax : ∀ u, K u ≤ Kmax)
    (hKsupp : ∀ u, (∃ j, 1 < |u j|) → K u = 0) (z : Fin p → ℝ)
    (x : Fin d → ℝ) :
    gramQuad h x0 expo K z x ≤
      h ^ (-(d : ℝ)) * Kmax * ((p : ℝ) * ∑ k, (z k) ^ 2) := by
  by_cases hx : x ∈ supBall x0 h
  · unfold gramQuad
    have hA : 0 ≤ h ^ (-(d : ℝ)) := Real.rpow_nonneg hh.le _
    have hKm : 0 ≤ Kmax := (hK0 0).trans (hKmax 0)
    calc
      _ ≤ h ^ (-(d : ℝ)) * Kmax *
          (∑ k, z k * monomial (expo k) (uCoord h x0 x)) ^ 2 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hKmax _) hA) (sq_nonneg _)
      _ ≤ _ := by gcongr; exact feature_sq_le hh hx z
  · rw [gramQuad_eq_zero_of_not_mem hh hKsupp z hx]
    have hKmax0 : 0 ≤ Kmax := (hK0 0).trans (hKmax 0)
    positivity

private theorem popGram_quadForm_eq {d p : ℕ} {P : CateLaw d} {h Kmax : ℝ}
    {x0 : Fin d → ℝ} {expo : Fin p → (Fin d → ℕ)} {K : (Fin d → ℝ) → ℝ}
    (hiid : IidSampling P) (hpi : PiIsPropensity P) (hh : 0 < h)
    (hK0 : ∀ u, 0 ≤ K u) (hKmax : ∀ u, K u ≤ Kmax)
    (hKsupp : ∀ u, (∃ j, 1 < |u j|) → K u = 0) (hKmeas : Measurable K)
    (a : Fin 2) (z : Fin p → ℝ) :
    ∑ k, ∑ l, z k * popGram P h x0 expo K a k l * z l =
      ∫ O, armProb P a O.X * gramQuad h x0 expo K z O.X ∂P.dataMeasure := by
  letI : IsProbabilityMeasure P.dataMeasure := hiid.1
  have hKmax0 : 0 ≤ Kmax := (hK0 0).trans (hKmax 0)
  have hgram (k l : Fin p) : Integrable
      (fun O : CateObs d ↦ z k * gramSummand h x0 expo K a O k l * z l)
      P.dataMeasure := by
    apply Integrable.of_bound (C := |z k| * (h ^ (-(d : ℝ)) * Kmax) * |z l|)
    · have hu : Measurable (fun O : CateObs d ↦ uCoord h x0 O.X) := by
        unfold uCoord
        fun_prop
      have hg : Measurable (fun O : CateObs d ↦ gramSummand h x0 expo K a O k l) := by
        unfold gramSummand
        have hmk : Measurable (fun O : CateObs d ↦ monomial (expo k) (uCoord h x0 O.X)) := by
          unfold monomial
          fun_prop
        have hml : Measurable (fun O : CateObs d ↦ monomial (expo l) (uCoord h x0 O.X)) := by
          unfold monomial
          fun_prop
        exact (((Measurable.ite
          (measurableSet_eq_fun measurable_CateObs_A measurable_const)
          measurable_const measurable_const).mul measurable_const).mul
            (hKmeas.comp hu)).mul hmk |>.mul hml
      exact ((measurable_const.mul hg).mul measurable_const).aestronglyMeasurable
    · filter_upwards with O
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      gcongr
      exact abs_gramSummand_le hh hK0 hKmax hKsupp a O k l
  have hsum :
      ∑ k, ∑ l, z k * popGram P h x0 expo K a k l * z l =
        ∫ O, (if O.A = ((a : ℕ) : ℝ) then 1 else 0) *
          gramQuad h x0 expo K z O.X ∂P.dataMeasure := by
    calc
      _ = ∑ k, ∑ l, ∫ O, z k * gramSummand h x0 expo K a O k l * z l
          ∂P.dataMeasure := by
        simp only [popGram, Matrix.of_apply]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        rw [← integral_const_mul, ← integral_mul_const]
      _ = ∫ O, ∑ k, ∑ l, z k * gramSummand h x0 expo K a O k l * z l
          ∂P.dataMeasure := by
        rw [integral_finset_sum Finset.univ (fun k _ ↦
          integrable_finset_sum Finset.univ fun l _ ↦ hgram k l)]
        congr 1
        funext k
        rw [integral_finset_sum Finset.univ (fun l _ ↦ hgram k l)]
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with O
        simp only [gramSummand, gramQuad]
        rw [pow_two, Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        ring
  rw [hsum]
  apply integral_arm_indicator_mul P hiid hpi a (gramQuad h x0 expo K z)
    (measurable_gramQuad hKmeas z).aemeasurable
    (h ^ (-(d : ℝ)) * Kmax * ((p : ℝ) * ∑ k, (z k) ^ 2))
  intro x
  rw [abs_of_nonneg (gramQuad_nonneg hh hK0 z x)]
  exact gramQuad_le hh hK0 hKmax hKsupp z x

private theorem armProb_aemeasurable_active {d : ℕ} {P : CateLaw d} {alpha L : ℝ}
    (hiid : IidSampling P) (hpi : PiHolder P alpha L) (a : Fin 2) :
    AEMeasurable (armProb P a) (P.dataMeasure.map (fun O ↦ O.X)) := by
  have hcontPi : ContinuousOn P.pi (cube d) := hpi.1.continuousOn
  have hcont : ContinuousOn (armProb P a) (cube d) := by
    by_cases ha : a = 1
    · simpa [armProb, ha] using hcontPi
    · rw [show armProb P a = fun x ↦ 1 - P.pi x by funext x; simp [armProb, ha]]
      exact continuousOn_const.sub hcontPi
  have hcubemeas : MeasurableSet (cube d) := by
    rw [show cube d = Set.univ.pi (fun _ : Fin d ↦ Set.Icc (0 : ℝ) 1) by
      ext x
      change (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) ↔
        ∀ i, i ∈ (Set.univ : Set (Fin d)) → x i ∈ Set.Icc (0 : ℝ) 1
      simp]
    exact MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc
  have hr := hcont.aemeasurable (μ := P.dataMeasure.map (fun O ↦ O.X)) hcubemeas
  suffices hsupp : P.dataMeasure.map (fun O ↦ O.X) =
      (P.dataMeasure.map (fun O ↦ O.X)).restrict (cube d) by
    rw [hsupp]
    exact hr
  symm
  apply Measure.restrict_eq_self_of_ae_mem
  exact (ae_map_iff measurable_CateObs_X.aemeasurable hcubemeas).2 hiid.2.2.2.1

private theorem bandwidth_cancel_active {d : ℕ} {h : ℝ} (hh : 0 < h) :
    h ^ (-(d : ℝ)) * h ^ d = 1 := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_add hh]
  simp

private theorem bandwidth_mass_cancel_active {d : ℕ} {h : ℝ} (hh : 0 < h) :
    h ^ (-(d : ℝ)) * (2 * h) ^ d = (2 : ℝ) ^ d := by
  rw [mul_pow, ← Real.rpow_natCast 2 d, ← Real.rpow_natCast h d]
  calc
    h ^ (-(d : ℝ)) * (2 ^ (d : ℝ) * h ^ (d : ℝ)) =
        2 ^ (d : ℝ) * (h ^ (-(d : ℝ)) * h ^ (d : ℝ)) := by ring
    _ = 2 ^ (d : ℝ) := by rw [← Real.rpow_add hh]; simp

set_option maxHeartbeats 1000000 in
private theorem popGram_quadForm_lower {d p : ℕ}
    {alpha beta gamma L e0 f0 f1 r0 h Kmax Kmin rinner cmin : ℝ}
    {x0 : Fin d → ℝ} {P : CateLaw d} {expo : Fin p → (Fin d → ℕ)}
    {K : (Fin d → ℝ) → ℝ}
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P)
    (hiid : IidSampling P) (hK0 : ∀ u, 0 ≤ K u) (hKmax : ∀ u, K u ≤ Kmax)
    (hKsupp : ∀ u, (∃ j, 1 < |u j|) → K u = 0)
    (hKmin : ∀ u, (∀ j, |u j| ≤ rinner) → Kmin ≤ K u)
    (hKmeas : Measurable K) (hKminpos : 0 < Kmin) (hrin : 0 < rinner)
    (hrin1 : rinner < 1) (hh : 0 < h) (hhr : h ≤ rStar r0 x0)
    (hcoer : ∀ z : Fin p → ℝ, cmin * (∑ k, (z k)^2) ≤
      ∑ k, ∑ l, z k * monomialGram expo rinner k l * z l)
    (a : Fin 2) (z : Fin p → ℝ) :
    e0 * f0 * Kmin * cmin * (∑ k, (z k) ^ 2) ≤
      ∑ k, ∑ l, z k * popGram P h x0 expo K a k l * z l := by
  classical
  letI : IsProbabilityMeasure P.dataMeasure := hiid.1
  let g := gramQuad h x0 expo K z
  let S := supBall x0 (h * rinner)
  let φ := S.indicator g
  have he0 : 0 < e0 := hreg.2.2.2.2.1.1
  have hf0 : 0 < f0 := hreg.2.2.2.2.2.1
  have hf1 : 0 ≤ f1 := hf0.le.trans hreg.2.2.2.2.2.2.1
  have hKmax0 : 0 ≤ Kmax := (hK0 0).trans (hKmax 0)
  have hgmeas : Measurable g := measurable_gramQuad hKmeas z
  have hB0 : 0 ≤ h ^ (-(d : ℝ)) * Kmax * ((p : ℝ) * ∑ k, (z k)^2) := by
    positivity
  have hgint : Integrable (fun O : CateObs d ↦ g O.X) P.dataMeasure := by
    refine Integrable.of_bound (C := h ^ (-(d : ℝ)) * Kmax *
      ((p : ℝ) * ∑ k, (z k)^2)) ?_ ?_
    · exact (hgmeas.comp measurable_CateObs_X).aestronglyMeasurable
    · filter_upwards with O
      rw [Real.norm_eq_abs, abs_of_nonneg (gramQuad_nonneg hh hK0 z O.X)]
      exact gramQuad_le hh hK0 hKmax hKsupp z O.X
  have harmae := armProb_aemeasurable_active hiid hP.piH a
  have harmX0 := harmae.aestronglyMeasurable.comp_ae_measurable'
    measurable_CateObs_X.aemeasurable
  have harmX : AEStronglyMeasurable (fun O : CateObs d ↦ armProb P a O.X)
      P.dataMeasure := by
    simpa only [Function.comp_apply] using harmX0.mono measurable_CateObs_X.comap_le
  have hbounds := armProb_ae_bounds P e0 he0 hiid hP.overlap a
  have harmgint : Integrable (fun O : CateObs d ↦ armProb P a O.X * g O.X)
      P.dataMeasure := by
    refine Integrable.of_bound (C := h ^ (-(d : ℝ)) * Kmax *
      ((p : ℝ) * ∑ k, (z k)^2)) ?_ ?_
    · simpa only [Pi.mul_apply, Function.comp_apply] using
        harmX.mul (hgmeas.comp measurable_CateObs_X).aestronglyMeasurable
    · filter_upwards [hbounds] with O hO
      change |armProb P a O.X * g O.X| ≤ _
      rw [abs_mul, abs_of_nonneg (he0.le.trans hO.1),
        abs_of_nonneg (gramQuad_nonneg hh hK0 z O.X)]
      have hg0 : 0 ≤ g O.X := by
        change 0 ≤ gramQuad h x0 expo K z O.X
        exact gramQuad_nonneg hh hK0 z O.X
      calc
        armProb P a O.X * g O.X ≤ 1 * g O.X :=
          mul_le_mul_of_nonneg_right hO.2 hg0
        _ ≤ _ := by simpa using gramQuad_le hh hK0 hKmax hKsupp z O.X
  have hSmeas : MeasurableSet S := measurableSet_supBall_active _ _
  have hSouter : S ⊆ supBall x0 h := by
    intro x hx i
    exact (hx i).trans (by nlinarith)
  have hsubs := supBall_subset_of_lt_rStar hreg hh hhr
  have hSball : S ⊆ supBall x0 r0 := hSouter.trans hsubs.2
  have hScube : S ⊆ cube d := hSouter.trans hsubs.1
  have hφmeas : Measurable φ := hgmeas.indicator hSmeas
  have hφ0 : ∀ x, 0 ≤ φ x := by
    intro x
    by_cases hx : x ∈ S
    · change 0 ≤ S.indicator g x
      rw [Set.indicator_of_mem hx]
      change 0 ≤ gramQuad h x0 expo K z x
      exact gramQuad_nonneg hh hK0 z x
    · change 0 ≤ S.indicator g x
      simp [Set.indicator, hx]
  have hφsupp : ∀ x, x ∉ S → φ x = 0 := by
    intro x hx
    simp [φ, hx]
  have hScompact : IsCompact S := by
    have heq : S = Metric.closedBall x0 (h * rinner) := by
      ext x
      simp only [S, supBall, Set.mem_setOf_eq, Metric.mem_closedBall]
      rw [dist_pi_le_iff (mul_nonneg hh.le hrin.le)]
      simp [Real.dist_eq]
    rw [heq]
    exact ProperSpace.isCompact_closedBall _ _
  have hφint : Integrable φ (volume.restrict S) := by
    change IntegrableOn φ S
    refine IntegrableOn.of_bound hScompact.measure_lt_top
      hφmeas.aestronglyMeasurable (h ^ (-(d : ℝ)) * Kmax *
        ((p : ℝ) * ∑ k, (z k)^2)) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 x)]
    by_cases hx : x ∈ S
    · change S.indicator g x ≤ _
      rw [Set.indicator_of_mem hx]
      exact gramQuad_le hh hK0 hKmax hKsupp z x
    · change S.indicator g x ≤ _
      rw [show S.indicator g x = 0 by simp [Set.indicator, hx]]
      exact hB0
  have hφXint : Integrable (fun O : CateObs d ↦ φ O.X) P.dataMeasure := by
    refine Integrable.of_bound (C := h ^ (-(d : ℝ)) * Kmax *
      ((p : ℝ) * ∑ k, (z k)^2)) ?_ ?_
    · exact (hφmeas.comp measurable_CateObs_X).aestronglyMeasurable
    · filter_upwards with O
      rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 O.X)]
      by_cases hx : O.X ∈ S
      · change S.indicator g O.X ≤ _
        rw [Set.indicator_of_mem hx]
        exact gramQuad_le hh hK0 hKmax hKsupp z O.X
      · change S.indicator g O.X ≤ _
        rw [show S.indicator g O.X = 0 by simp [Set.indicator, hx]]
        exact hB0
  have hdesign := design_lower_bound P f0 f1 r0 x0 hP.pxDens hP.localDensity hf0
    hSmeas hSball hScube φ hφmeas hφ0 hφsupp hφint
  have hshrink : ∫ O, φ O.X ∂P.dataMeasure ≤ ∫ O, g O.X ∂P.dataMeasure := by
    apply integral_mono hφXint hgint
    intro O
    by_cases hx : O.X ∈ S
    · change S.indicator g O.X ≤ g O.X
      simp [Set.indicator_of_mem hx]
    · change S.indicator g O.X ≤ g O.X
      rw [show S.indicator g O.X = 0 by simp [Set.indicator, hx]]
      change 0 ≤ gramQuad h x0 expo K z O.X
      exact gramQuad_nonneg hh hK0 z O.X
  have harmlower : e0 * ∫ O, g O.X ∂P.dataMeasure ≤
      ∫ O, armProb P a O.X * g O.X ∂P.dataMeasure := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hgint.const_mul e0) harmgint
    filter_upwards [hbounds] with O hO
    exact mul_le_mul_of_nonneg_right hO.1 (gramQuad_nonneg hh hK0 z O.X)
  let V : (Fin d → ℝ) → ℝ := fun u ↦ (∑ k, z k * monomial (expo k) u)^2
  have hVmeas : Measurable V := by unfold V monomial; fun_prop
  have hVint : IntegrableOn V (supBall (0 : Fin d → ℝ) rinner) := by
    have hcomp : IsCompact (supBall (0 : Fin d → ℝ) rinner) := by
      have heq : supBall (0 : Fin d → ℝ) rinner = Metric.closedBall 0 rinner := by
        ext u
        simp only [supBall, Set.mem_setOf_eq, Pi.zero_apply, sub_zero, Metric.mem_closedBall]
        rw [dist_pi_le_iff hrin.le]
        simp
      rw [heq]
      exact ProperSpace.isCompact_closedBall _ _
    have hVcont : Continuous V := by unfold V monomial; fun_prop
    exact hVcont.continuousOn.integrableOn_compact hcomp
  have hinner : h ^ (-(d : ℝ)) * Kmin * (∫ x in S, V (uCoord h x0 x)) ≤
      ∫ x in S, φ x := by
    have hleftint : IntegrableOn
        (fun x ↦ h ^ (-(d : ℝ)) * Kmin * V (uCoord h x0 x)) S := by
      refine IntegrableOn.of_bound hScompact.measure_lt_top
        ((measurable_const.mul measurable_const).mul
          (hVmeas.comp (by unfold uCoord; fun_prop))).aestronglyMeasurable
        (h ^ (-(d : ℝ)) * Kmin * ((p : ℝ) * ∑ k, (z k)^2)) ?_
      filter_upwards [ae_restrict_mem hSmeas] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg hh.le _) hKminpos.le) (sq_nonneg _))]
      gcongr
      exact feature_sq_le hh (hSouter hx) z
    rw [show h ^ (-(d : ℝ)) * Kmin * (∫ x in S, V (uCoord h x0 x)) =
      ∫ x in S, h ^ (-(d : ℝ)) * Kmin * V (uCoord h x0 x) by
        rw [integral_const_mul]]
    apply setIntegral_mono_on hleftint hφint hSmeas
    intro x hx
    change _ ≤ S.indicator g x
    rw [Set.indicator_of_mem hx]
    unfold g gramQuad V
    have hu : ∀ j, |uCoord h x0 x j| ≤ rinner := by
      intro j
      rw [uCoord, abs_div, abs_of_pos hh]
      exact (div_le_iff₀ hh).2 (by simpa [mul_comm] using hx j)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hKmin _ hu) (Real.rpow_nonneg hh.le _)) (sq_nonneg _)
  have hcv := integral_uCoord_comp h hh x0 rinner hrin.le V hVmeas hVint
  have hmono := monomialGram_quadForm expo hrin z
  have hbase : f0 * Kmin * cmin * (∑ k, (z k)^2) ≤ ∫ O, g O.X ∂P.dataMeasure := by
    calc
      f0 * Kmin * cmin * (∑ k, (z k)^2) =
          (f0 * Kmin) * (cmin * ∑ k, (z k)^2) := by ring
      _ ≤ (f0 * Kmin) *
          (∑ k, ∑ l, z k * monomialGram expo rinner k l * z l) :=
        mul_le_mul_of_nonneg_left (hcoer z) (mul_nonneg hf0.le hKminpos.le)
      _ = f0 * Kmin * (∑ k, ∑ l, z k * monomialGram expo rinner k l * z l) := by ring
      _ = f0 * Kmin * ∫ u in supBall (0 : Fin d → ℝ) rinner, V u := by
        rw [hmono]
        simp [V, supBall]
      _ = f0 * (h ^ (-(d : ℝ)) * Kmin *
          (∫ x in S, V (uCoord h x0 x))) := by
        rw [hcv]
        have hcancel : h ^ (-(d : ℝ)) * Kmin *
          (h ^ d * ∫ u in supBall (0 : Fin d → ℝ) rinner, V u) =
          Kmin * ∫ u in supBall (0 : Fin d → ℝ) rinner, V u := by
            calc
              _ = (h ^ (-(d : ℝ)) * h ^ d) *
                  (Kmin * ∫ u in supBall (0 : Fin d → ℝ) rinner, V u) := by ring
              _ = _ := by rw [bandwidth_cancel_active hh]; ring
        rw [hcancel]
        ring
      _ ≤ f0 * ∫ x in S, φ x := by gcongr
      _ ≤ ∫ O, φ O.X ∂P.dataMeasure := hdesign
      _ ≤ ∫ O, g O.X ∂P.dataMeasure := hshrink
  rw [popGram_quadForm_eq hiid hP.piProp hh hK0 hKmax hKsupp hKmeas a z]
  calc
    e0 * f0 * Kmin * cmin * (∑ k, (z k)^2) =
        e0 * (f0 * Kmin * cmin * (∑ k, (z k)^2)) := by ring
    _ ≤ e0 * ∫ O, g O.X ∂P.dataMeasure := by gcongr
    _ ≤ _ := harmlower

set_option maxHeartbeats 1000000 in
private theorem popGram_quadForm_upper {d p : ℕ}
    {alpha beta gamma L e0 f0 f1 r0 h Kmax : ℝ}
    {x0 : Fin d → ℝ} {P : CateLaw d} {expo : Fin p → (Fin d → ℕ)}
    {K : (Fin d → ℝ) → ℝ}
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P)
    (hiid : IidSampling P) (hK0 : ∀ u, 0 ≤ K u) (hKmax : ∀ u, K u ≤ Kmax)
    (hKsupp : ∀ u, (∃ j, 1 < |u j|) → K u = 0) (hKmeas : Measurable K)
    (hh : 0 < h) (hhr : h ≤ rStar r0 x0) (a : Fin 2) (z : Fin p → ℝ) :
    ∑ k, ∑ l, z k * popGram P h x0 expo K a k l * z l ≤
      Kmax * (p : ℝ) * f1 * 2 ^ d * (∑ k, (z k)^2) := by
  classical
  letI : IsProbabilityMeasure P.dataMeasure := hiid.1
  let g := gramQuad h x0 expo K z
  let S := supBall x0 h
  let B := h ^ (-(d : ℝ)) * Kmax * ((p : ℝ) * ∑ k, (z k)^2)
  let T : Set (CateObs d) := {O | O.X ∈ S}
  have he0 : 0 < e0 := hreg.2.2.2.2.1.1
  have hf1 : 0 ≤ f1 := hreg.2.2.2.2.2.1.le.trans hreg.2.2.2.2.2.2.1
  have hB0 : 0 ≤ B := by
    unfold B
    have hKm : 0 ≤ Kmax := (hK0 0).trans (hKmax 0)
    positivity
  have hSmeas : MeasurableSet S := measurableSet_supBall_active _ _
  have hTmeas : MeasurableSet T := hSmeas.preimage measurable_CateObs_X
  have hgmeas : Measurable g := measurable_gramQuad hKmeas z
  have harmae := armProb_aemeasurable_active hiid hP.piH a
  have harmX0 := harmae.aestronglyMeasurable.comp_ae_measurable'
    measurable_CateObs_X.aemeasurable
  have harmX : AEStronglyMeasurable (fun O : CateObs d ↦ armProb P a O.X)
      P.dataMeasure := by
    simpa only [Function.comp_apply] using harmX0.mono measurable_CateObs_X.comap_le
  have hbounds := armProb_ae_bounds P e0 he0 hiid hP.overlap a
  have harmgint : Integrable (fun O : CateObs d ↦ armProb P a O.X * g O.X)
      P.dataMeasure := by
    refine Integrable.of_bound (C := B) ?_ ?_
    · simpa only [Pi.mul_apply, Function.comp_apply] using
        harmX.mul (hgmeas.comp measurable_CateObs_X).aestronglyMeasurable
    · filter_upwards [hbounds] with O hO
      change |armProb P a O.X * g O.X| ≤ B
      have hg0 : 0 ≤ g O.X := by
        change 0 ≤ gramQuad h x0 expo K z O.X
        exact gramQuad_nonneg hh hK0 z O.X
      rw [abs_mul, abs_of_nonneg (he0.le.trans hO.1)]
      rw [abs_of_nonneg hg0]
      calc
        armProb P a O.X * g O.X ≤ 1 * g O.X := by
          exact mul_le_mul_of_nonneg_right hO.2 hg0
        _ ≤ B := by simpa [B, g] using gramQuad_le hh hK0 hKmax hKsupp z O.X
  have hrightint : Integrable (T.indicator fun _ : CateObs d ↦ B) P.dataMeasure :=
    (integrable_const B).indicator hTmeas
  have hpoint : ∀ᵐ O ∂P.dataMeasure,
      armProb P a O.X * g O.X ≤ T.indicator (fun _ ↦ B) O := by
    filter_upwards [hbounds] with O hO
    by_cases hx : O.X ∈ S
    · rw [Set.indicator_of_mem (show O ∈ T from hx)]
      calc
        armProb P a O.X * g O.X ≤ 1 * g O.X := by
          apply mul_le_mul_of_nonneg_right hO.2
          change 0 ≤ gramQuad h x0 expo K z O.X
          exact gramQuad_nonneg hh hK0 z O.X
        _ ≤ B := by simpa [B, g] using gramQuad_le hh hK0 hKmax hKsupp z O.X
    · rw [show T.indicator (fun _ ↦ B) O = 0 by simp [T, Set.indicator, hx]]
      rw [show g O.X = 0 by
        change gramQuad h x0 expo K z O.X = 0
        exact gramQuad_eq_zero_of_not_mem hh hKsupp z hx]
      simp
  have hmass : (P.dataMeasure.map (fun O ↦ O.X)).real S ≤ f1 * (2 * h)^d := by
    have hrstar_r0 : rStar r0 x0 ≤ r0 := by
      unfold rStar
      have hm : min r0 (⨅ i : Fin d, min (x0 i) (1 - x0 i)) ≤ r0 := min_le_left _ _
      have hr0 : 0 < r0 := hreg.2.2.2.2.2.2.2.1.1
      nlinarith
    exact design_mass_le P f0 f1 r0 x0 hiid hP.pxDens hP.localDensity hf1 hh
      (hhr.trans hrstar_r0)
  rw [popGram_quadForm_eq hiid hP.piProp hh hK0 hKmax hKsupp hKmeas a z]
  calc
    ∫ O, armProb P a O.X * g O.X ∂P.dataMeasure ≤
        ∫ O, T.indicator (fun _ ↦ B) O ∂P.dataMeasure :=
      integral_mono_ae harmgint hrightint hpoint
    _ = B * (P.dataMeasure.map (fun O ↦ O.X)).real S := by
      rw [integral_indicator hTmeas]
      rw [setIntegral_const]
      have hm : P.dataMeasure.real T =
          (P.dataMeasure.map (fun O ↦ O.X)).real S := by
        rw [Measure.real, Measure.real,
          Measure.map_apply measurable_CateObs_X hSmeas]
        rfl
      rw [hm]
      simp [smul_eq_mul, mul_comm]
    _ ≤ B * (f1 * (2 * h)^d) := mul_le_mul_of_nonneg_left hmass hB0
    _ = Kmax * (p : ℝ) * f1 * 2 ^ d * (∑ k, (z k)^2) := by
      unfold B
      rw [show h ^ (-(d : ℝ)) * Kmax * ((p : ℝ) * ∑ k, (z k)^2) *
        (f1 * (2 * h)^d) = Kmax * (p : ℝ) * f1 * (∑ k, (z k)^2) *
        (h ^ (-(d : ℝ)) * (2 * h)^d) by ring,
        bandwidth_mass_cancel_active hh]
      ring

private theorem popGram_isHermitian {d p : ℕ} (P : CateLaw d) (h : ℝ)
    (x0 : Fin d → ℝ) (expo : Fin p → (Fin d → ℕ)) (K : (Fin d → ℝ) → ℝ)
    (a : Fin 2) : (popGram P h x0 expo K a).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro k l
  simp only [star_trivial, popGram, Matrix.of_apply]
  apply integral_congr_ae
  filter_upwards with O
  unfold gramSummand
  ring

private theorem smul_one_isHermitian {p : ℕ} (c : ℝ) :
    (c • (1 : Matrix (Fin p) (Fin p) ℝ)).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro k l
  by_cases h : k = l
  · subst l
    simp
  · simp [h, Ne.symm h]

private theorem dotProduct_sub_smul_one {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ)
    (c : ℝ) (z : Fin p → ℝ) :
    star z ⬝ᵥ ((M - c • (1 : Matrix (Fin p) (Fin p) ℝ)) *ᵥ z) =
      (∑ k, ∑ l, z k * M k l * z l) - c * ∑ k, (z k)^2 := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul]
  congr 1
  · simp only [dotProduct, mulVec, star_trivial]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  · simp [dotProduct, pow_two, smul_eq_mul]

private theorem dotProduct_smul_one_sub {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ)
    (C : ℝ) (z : Fin p → ℝ) :
    star z ⬝ᵥ ((C • (1 : Matrix (Fin p) (Fin p) ℝ) - M) *ᵥ z) =
      C * ∑ k, (z k)^2 - ∑ k, ∑ l, z k * M k l * z l := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul]
  congr 1
  · simp [dotProduct, pow_two, smul_eq_mul]
  · simp only [dotProduct, mulVec, star_trivial]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring

set_option maxHeartbeats 1000000 in
/-- The population Gram matrix lies in a law- and bandwidth-uniform Loewner interval. -/
theorem popGram_mem_loewnerSet {d p : ℕ}
    {alpha beta gamma L e0 f0 f1 r0 h Kmax Kmin rinner cmin : ℝ}
    {x0 : Fin d → ℝ} {P : CateLaw d} {expo : Fin p → (Fin d → ℕ)}
    {K : (Fin d → ℝ) → ℝ} {a : Fin 2}
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P)
    (hiid : IidSampling P) (hexpo : Function.Injective expo)
    (hK0 : ∀ u, 0 ≤ K u) (hKmax : ∀ u, K u ≤ Kmax)
    (hKsupp : ∀ u, (∃ j, 1 < |u j|) → K u = 0)
    (hKmin : ∀ u, (∀ j, |u j| ≤ rinner) → Kmin ≤ K u)
    (hKmeas : Measurable K) (hKminpos : 0 < Kmin)
    (hrin : 0 < rinner) (hrin1 : rinner < 1) (hp : 0 < p)
    (hh : 0 < h) (hhr : h ≤ rStar r0 x0) (hcmin : 0 < cmin)
    (hcoer : ∀ z : Fin p → ℝ, cmin * (∑ k, (z k)^2) ≤
      ∑ k, ∑ l, z k * monomialGram expo rinner k l * z l) :
    popGram P h x0 expo K a ∈
      loewnerSet p (e0 * f0 * Kmin * cmin)
        (Kmax * (p : ℝ) * f1 * 2^d + e0 * f0 * Kmin * cmin) := by
  have _hexpo := hexpo
  have _hp := hp
  have _hcmin := hcmin
  let c := e0 * f0 * Kmin * cmin
  let U := Kmax * (p : ℝ) * f1 * 2^d
  let G := popGram P h x0 expo K a
  have hG : G.IsHermitian := popGram_isHermitian P h x0 expo K a
  have hcI : (c • (1 : Matrix (Fin p) (Fin p) ℝ)).IsHermitian :=
    smul_one_isHermitian c
  have hUI : ((U + c) • (1 : Matrix (Fin p) (Fin p) ℝ)).IsHermitian :=
    smul_one_isHermitian (U + c)
  change (G - c • (1 : Matrix (Fin p) (Fin p) ℝ)).PosSemidef ∧
    ((U + c) • (1 : Matrix (Fin p) (Fin p) ℝ) - G).PosSemidef
  constructor
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hG.sub hcI)
    intro z
    rw [dotProduct_sub_smul_one]
    apply sub_nonneg.mpr
    change c * ∑ k, (z k)^2 ≤ ∑ k, ∑ l, z k * G k l * z l
    exact popGram_quadForm_lower hreg hP hiid hK0 hKmax hKsupp hKmin hKmeas
      hKminpos hrin hrin1 hh hhr hcoer a z
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hUI.sub hG)
    intro z
    rw [dotProduct_smul_one_sub]
    apply sub_nonneg.mpr
    change ∑ k, ∑ l, z k * G k l * z l ≤ (U + c) * ∑ k, (z k)^2
    have hu := popGram_quadForm_upper (expo := expo) hreg hP hiid hK0 hKmax hKsupp
      hKmeas hh hhr a z
    have hs : 0 ≤ ∑ k, (z k)^2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    change (∑ k, ∑ l, z k * popGram P h x0 expo K a k l * z l) ≤
      (Kmax * (p : ℝ) * f1 * 2^d + e0 * f0 * Kmin * cmin) * ∑ k, (z k)^2
    calc
      _ ≤ U * ∑ k, (z k)^2 := by simpa [U] using hu
      _ ≤ (U + c) * ∑ k, (z k)^2 := by
        apply mul_le_mul_of_nonneg_right _ hs
        have he0 : 0 < e0 := hreg.2.2.2.2.1.1
        have hf0 : 0 < f0 := hreg.2.2.2.2.2.1
        have hc0 : 0 ≤ c := by
          dsimp [c]
          positivity
        linarith
      _ = _ := by rfl

end CausalSmith.Stat.DpCateMinimax
