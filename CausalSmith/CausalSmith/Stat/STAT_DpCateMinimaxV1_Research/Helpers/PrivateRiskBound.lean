/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PopulationGram
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PrivateRisk
import Causalean.Mathlib.Probability.IidMeanVariance

/-!
# Integrated risk bound for the private local-polynomial release

This file integrates the deterministic release error estimate first over the
Laplace noise and then over the i.i.d. sample.  The constants in the final
bound depend only on the dimension, polynomial degree, and density envelope.
-/

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory Set Matrix
open scoped BigOperators ENNReal
open Causalean.Mathlib.Probability
open Causalean.Mathlib.Analysis
open Causalean.Stat.Privacy

noncomputable section

private lemma measurable_uCoord_obs {d : ℕ} (h : ℝ) (x0 : Fin d → ℝ) :
    Measurable (fun O : CateObs d ↦ uCoord h x0 O.X) := by
  rw [measurable_pi_iff]
  intro j
  exact (((measurable_pi_apply j).comp measurable_CateObs_X).sub measurable_const).div_const h

private lemma measurable_gramSummand' {d m : ℕ} (h : ℝ) (x0 : Fin d → ℝ)
    (a : Fin 2) (k l : Fin (pDim d m)) :
    Measurable (fun O : CateObs d ↦
      gramSummand h x0 (expoOf d m) (unifKernel d) a O k l) := by
  unfold gramSummand
  have hi : Measurable (fun O : CateObs d ↦
      if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0) := Measurable.ite
    (measurableSet_eq_fun measurable_CateObs_A measurable_const)
    measurable_const measurable_const
  have hK := (measurable_unifKernel d).comp (measurable_uCoord_obs h x0)
  have hk := ((measurable_pi_iff.mp (measurable_featOf d m)) k).comp
    (measurable_uCoord_obs h x0)
  have hl := ((measurable_pi_iff.mp (measurable_featOf d m)) l).comp
    (measurable_uCoord_obs h x0)
  simpa [featOf] using ((((hi.mul measurable_const).mul hK).mul hk).mul hl)

private lemma measurable_momSummand' {d m : ℕ} (h : ℝ) (x0 : Fin d → ℝ)
    (a : Fin 2) (k : Fin (pDim d m)) :
    Measurable (fun O : CateObs d ↦
      momSummand h x0 (expoOf d m) (unifKernel d) a O k) := by
  unfold momSummand
  have hi : Measurable (fun O : CateObs d ↦
      if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0) := Measurable.ite
    (measurableSet_eq_fun measurable_CateObs_A measurable_const)
    measurable_const measurable_const
  have hK := (measurable_unifKernel d).comp (measurable_uCoord_obs h x0)
  have hk := ((measurable_pi_iff.mp (measurable_featOf d m)) k).comp
    (measurable_uCoord_obs h x0)
  simpa [featOf] using ((((hi.mul measurable_const).mul hK).mul
    (measurable_const.max (measurable_const.min measurable_CateObs_Y))).mul hk)

private lemma integral_sq_le_ball_mass' {d : ℕ} (P : CateLaw d) (hiid : IidSampling P)
    {h B : ℝ} {x0 : Fin d → ℝ} {q : CateObs d → ℝ}
    (hq : Measurable q) (hB : 0 ≤ B) (hqB : ∀ O, |q O| ≤ B)
    (hqsupp : ∀ O, O.X ∉ supBall x0 h → q O = 0) :
    ∫ O, (q O) ^ 2 ∂P.dataMeasure ≤
      B ^ 2 * (P.dataMeasure.map (fun O ↦ O.X)).real (supBall x0 h) := by
  letI : IsProbabilityMeasure P.dataMeasure := hiid.1
  let S : Set (CateObs d) := {O | O.X ∈ supBall x0 h}
  have hball : MeasurableSet (supBall x0 h) := by
    rw [show supBall x0 h = ⋂ i : Fin d, {x | |x i - x0 i| ≤ h} by
      ext x
      simp [supBall]]
    apply MeasurableSet.iInter
    intro i
    change MeasurableSet ((fun x : Fin d → ℝ ↦ |x i - x0 i|) ⁻¹' Set.Iic h)
    apply measurableSet_Iic.preimage
    simpa only [Real.norm_eq_abs] using
      (((measurable_pi_apply i).sub measurable_const).norm)
  have hS : MeasurableSet S := hball.preimage measurable_CateObs_X
  have hpoint : ∀ O, (q O) ^ 2 ≤ (S.indicator fun _ ↦ B ^ 2) O := by
    intro O
    by_cases hO : O ∈ S
    · rw [Set.indicator_of_mem hO]
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hB).mpr (hqB O)
    · simp [S, hO, hqsupp O hO]
  have hleft : Integrable (fun O ↦ (q O) ^ 2) P.dataMeasure := by
    apply Integrable.of_bound (C := B ^ 2) (hq.pow_const 2).aestronglyMeasurable
    filter_upwards with O
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hB).mpr (hqB O)
  have hright : Integrable (S.indicator fun _ ↦ B ^ 2) P.dataMeasure :=
    (integrable_const (B ^ 2)).indicator hS
  calc
    _ ≤ ∫ O, S.indicator (fun _ ↦ B ^ 2) O ∂P.dataMeasure :=
      integral_mono hleft hright hpoint
    _ = B ^ 2 * P.dataMeasure.real S := by
      rw [integral_indicator hS]
      simp [Measure.real, mul_comm]
    _ = _ := by
      congr 1
      rw [Measure.real, Measure.real, Measure.map_apply measurable_CateObs_X
        hball]
      rfl

private lemma bandwidth_square_mass_cancel' {d : ℕ} {h : ℝ} (hh : 0 < h) :
    (h ^ (-(d : ℝ))) ^ 2 * (2 * h) ^ d = (2 : ℝ) ^ d * h ^ (-(d : ℝ)) := by
  rw [Real.rpow_neg hh.le, Real.rpow_natCast]
  field_simp [hh.ne']
  ring

private lemma rpow_neg_div_nat {d n : ℕ} {h : ℝ} (hh : 0 < h) :
    h ^ (-(d : ℝ)) / (n : ℝ) = 1 / ((n : ℝ) * h ^ (d : ℝ)) := by
  rw [Real.rpow_neg (le_of_lt hh)]
  field_simp

private lemma sqrt_sum_sq_le_sum_abs {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    Real.sqrt (∑ i, (v i) ^ 2) ≤ ∑ i, |v i| := by
  rw [Real.sqrt_le_iff]
  constructor
  · exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  · simpa [sq_abs] using Finset.sum_sq_le_sq_sum_of_nonneg
      (s := Finset.univ) (f := fun i ↦ |v i|) (fun _ _ ↦ abs_nonneg _)

private lemma integrable_euclidean_of_integrable
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω}
    (v : Ω → ι → ℝ) (hv : ∀ i, Integrable (fun ω ↦ v ω i) μ) :
    Integrable (fun ω ↦ Real.sqrt (∑ i, (v ω i) ^ 2)) μ := by
  have hsum : Integrable (fun ω ↦ ∑ i, |v ω i|) μ :=
    integrable_finset_sum _ fun i _ ↦ (hv i).abs
  have hmeas : AEStronglyMeasurable (fun ω ↦ Real.sqrt (∑ i, (v ω i) ^ 2)) μ := by
    fun_prop
  refine hsum.mono' hmeas (ae_of_all _ fun ω ↦ ?_)
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact sqrt_sum_sq_le_sum_abs (v ω)

private lemma integrable_iid_mean_euclidean
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (ξ : ι → Ω → ℝ) (hξ : ∀ k, Measurable (ξ k))
    (B : ℝ) (hbounded : ∀ k ω, |ξ k ω| ≤ B) :
    Integrable (fun s ↦ Real.sqrt (∑ k,
      ((n : ℝ)⁻¹ * ∑ i : Fin n, ξ k (s i) - ∫ ω, ξ k ω ∂μ) ^ 2))
      (Measure.pi fun _ : Fin n ↦ μ) := by
  apply integrable_euclidean_of_integrable
  intro k
  have hk : Integrable (ξ k) μ :=
    Integrable.of_bound (hξ k).aestronglyMeasurable B (ae_of_all μ (hbounded k))
  apply Integrable.sub
  · apply Integrable.const_mul
    exact integrable_finset_sum _ fun i _ ↦
      (measurePreserving_eval (fun _ : Fin n ↦ μ) i).integrable_comp_of_integrable hk
  · exact integrable_const _

private lemma empMom_eq_mean_momSummand {d n m : ℕ} (h : ℝ) (x0 : Fin d → ℝ)
    (a : Fin 2) (s : Fin n → CateObs d) (hn : 0 < n) (k : Fin (pDim d m)) :
    empMom m h x0 a s k = (n : ℝ)⁻¹ * ∑ i,
      momSummand h x0 (expoOf d m) (unifKernel d) a (s i) k := by
  simp [empMom, momSummand, featOf, hn.ne']
  rfl

private lemma empGram_eq_mean_gramSummand {d n m : ℕ} (h : ℝ) (x0 : Fin d → ℝ)
    (a : Fin 2) (s : Fin n → CateObs d) (hn : 0 < n) (k l : Fin (pDim d m)) :
    empGram m h x0 a s k l = (n : ℝ)⁻¹ * ∑ i,
      gramSummand h x0 (expoOf d m) (unifKernel d) a (s i) k l := by
  simp [empGram, gramSummand, featOf, hn.ne']
  rfl

/-- Expected moment-vector sampling error for one treatment arm. -/
private lemma integral_empMom_sub_popMom_le {d n m : ℕ}
    {alpha beta gamma L e0 f0 f1 r0 h : ℝ} {x0 : Fin d → ℝ} {P : CateLaw d}
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P)
    (hiid : IidSampling P) (hn : 0 < n) (hh : 0 < h) (hhr : h ≤ r0)
    (a : Fin 2) :
    ∫ s, Real.sqrt (∑ k, (empMom m h x0 a s k -
        popMom P h x0 (expoOf d m) (unifKernel d) a k) ^ 2)
        ∂(Measure.pi fun _ : Fin n ↦ P.dataMeasure) ≤
      Real.sqrt (((pDim d m : ℝ) * f1 * 2 ^ d * h ^ (-(d : ℝ))) / (n : ℝ)) := by
  letI : IsProbabilityMeasure P.dataMeasure := hiid.1
  let ξ : Fin (pDim d m) → CateObs d → ℝ := fun k O ↦
    momSummand h x0 (expoOf d m) (unifKernel d) a O k
  have hb := iid_mean_euclidean_abs_le P.dataMeasure hn ξ
    (fun k ↦ measurable_momSummand' h x0 a k)
    (h ^ (-(d : ℝ))) (fun k O ↦ by
      simpa using abs_momSummand_le hh (unifKernel_nonneg d) (unifKernel_le_one d)
        (unifKernel_eq_zero d) a O k)
  calc
    _ = ∫ s, Real.sqrt (∑ k, ((n : ℝ)⁻¹ * ∑ i, ξ k (s i) -
          ∫ O, ξ k O ∂P.dataMeasure) ^ 2)
          ∂(Measure.pi fun _ : Fin n ↦ P.dataMeasure) := by
      apply integral_congr_ae
      apply ae_of_all
      intro s
      congr 1
    _ ≤ Real.sqrt ((∑ k, ∫ O, (ξ k O) ^ 2 ∂P.dataMeasure) / (n : ℝ)) := hb
    _ ≤ _ := by
      apply Real.sqrt_le_sqrt
      calc
        (∑ k, ∫ O, (ξ k O) ^ 2 ∂P.dataMeasure) / (n : ℝ) ≤
            (∑ _k : Fin (pDim d m),
              (f1 * 2 ^ d) * h ^ (-(d : ℝ))) / (n : ℝ) := by
          apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ (n : ℝ))
          exact Finset.sum_le_sum fun k _ ↦ by
            have hb := integral_sq_le_ball_mass' P hiid
              (h := h) (x0 := x0) (B := h ^ (-(d : ℝ))) (q := fun O ↦ ξ k O)
              (measurable_momSummand' h x0 a k)
              (Real.rpow_nonneg hh.le _)
              (fun O ↦ by simpa using (abs_momSummand_le hh (unifKernel_nonneg d)
                (unifKernel_le_one d) (unifKernel_eq_zero d) a O k))
              (fun O hO ↦ momSummand_eq_zero_of_not_mem hh
                (unifKernel_eq_zero d) a O k hO)
            have hm := design_mass_le P f0 f1 r0 x0 hiid hP.pxDens hP.localDensity
              (hreg.2.2.2.2.2.1.le.trans hreg.2.2.2.2.2.2.1) hh hhr
            calc
              _ ≤ (h ^ (-(d : ℝ))) ^ 2 *
                  (P.dataMeasure.map (fun O ↦ O.X)).real (supBall x0 h) := by
                    simpa [ξ] using hb
              _ ≤ (h ^ (-(d : ℝ))) ^ 2 * (f1 * (2 * h) ^ d) := by gcongr
              _ = (f1 * 2 ^ d) * h ^ (-(d : ℝ)) := by
                calc
                  _ = f1 * ((h ^ (-(d : ℝ))) ^ 2 * (2 * h) ^ d) := by ring
                  _ = _ := by rw [bandwidth_square_mass_cancel' hh]; ring
        _ = _ := by simp; ring

/-- Expected Gram-matrix Frobenius sampling error for one treatment arm. -/
private lemma integral_empGram_sub_popGram_le {d n m : ℕ}
    {alpha beta gamma L e0 f0 f1 r0 h : ℝ} {x0 : Fin d → ℝ} {P : CateLaw d}
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (hP : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P)
    (hiid : IidSampling P) (hn : 0 < n) (hh : 0 < h) (hhr : h ≤ r0)
    (a : Fin 2) :
    ∫ s, frobDist (empGram m h x0 a s)
        (popGram P h x0 (expoOf d m) (unifKernel d) a)
        ∂(Measure.pi fun _ : Fin n ↦ P.dataMeasure) ≤
      Real.sqrt ((((pDim d m : ℝ) ^ 2) * f1 * 2 ^ d * h ^ (-(d : ℝ))) /
        (n : ℝ)) := by
  letI : IsProbabilityMeasure P.dataMeasure := hiid.1
  let ξ : (Fin (pDim d m) × Fin (pDim d m)) → CateObs d → ℝ := fun q O ↦
    gramSummand h x0 (expoOf d m) (unifKernel d) a O q.1 q.2
  have hb := iid_mean_euclidean_abs_le P.dataMeasure hn ξ
    (fun q ↦ measurable_gramSummand' h x0 a q.1 q.2)
    (h ^ (-(d : ℝ))) (fun q O ↦ by
      simpa using abs_gramSummand_le hh (unifKernel_nonneg d) (unifKernel_le_one d)
        (unifKernel_eq_zero d) a O q.1 q.2)
  calc
    _ = ∫ s, Real.sqrt (∑ q, ((n : ℝ)⁻¹ * ∑ i, ξ q (s i) -
          ∫ O, ξ q O ∂P.dataMeasure) ^ 2)
          ∂(Measure.pi fun _ : Fin n ↦ P.dataMeasure) := by
      apply integral_congr_ae
      apply ae_of_all
      intro s
      simp only [frobDist, Fintype.sum_prod_type]
      congr 1
    _ ≤ Real.sqrt ((∑ q, ∫ O, (ξ q O) ^ 2 ∂P.dataMeasure) / (n : ℝ)) := hb
    _ ≤ _ := by
      apply Real.sqrt_le_sqrt
      calc
        (∑ q, ∫ O, (ξ q O) ^ 2 ∂P.dataMeasure) / (n : ℝ) ≤
            (∑ _q : Fin (pDim d m) × Fin (pDim d m),
              (f1 * 2 ^ d) * h ^ (-(d : ℝ))) / (n : ℝ) := by
          apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ (n : ℝ))
          exact Finset.sum_le_sum fun q _ ↦ by
            have hb := integral_sq_le_ball_mass' P hiid
              (h := h) (x0 := x0) (B := h ^ (-(d : ℝ))) (q := fun O ↦ ξ q O)
              (measurable_gramSummand' h x0 a q.1 q.2)
              (Real.rpow_nonneg hh.le _)
              (fun O ↦ by simpa using (abs_gramSummand_le hh (unifKernel_nonneg d)
                (unifKernel_le_one d) (unifKernel_eq_zero d) a O q.1 q.2))
              (fun O hO ↦ gramSummand_eq_zero_of_not_mem hh
                (unifKernel_eq_zero d) a O q.1 q.2 hO)
            have hm := design_mass_le P f0 f1 r0 x0 hiid hP.pxDens hP.localDensity
              (hreg.2.2.2.2.2.1.le.trans hreg.2.2.2.2.2.2.1) hh hhr
            calc
              _ ≤ (h ^ (-(d : ℝ))) ^ 2 *
                  (P.dataMeasure.map (fun O ↦ O.X)).real (supBall x0 h) := by
                    simpa [ξ] using hb
              _ ≤ (h ^ (-(d : ℝ))) ^ 2 * (f1 * (2 * h) ^ d) := by gcongr
              _ = (f1 * 2 ^ d) * h ^ (-(d : ℝ)) := by
                calc
                  _ = f1 * ((h ^ (-(d : ℝ))) ^ 2 * (2 * h) ^ d) := by ring
                  _ = _ := by rw [bandwidth_square_mass_cancel' hh]; ring
        _ = _ := by simp; ring

set_option maxHeartbeats 1000000 in
/-- The private release has the usual bias, sampling-variance, and privacy-noise
decomposition, with constants uniform over the model class and bandwidth. -/
theorem mechOf_risk_bound (d : ℕ) (beta f1 : ℝ) :
    ∃ Cv1 Cv2 Cw : ℝ, 0 ≤ Cv1 ∧ 0 ≤ Cv2 ∧ 0 ≤ Cw ∧
      ∀ {n : ℕ} {alpha gamma L e0 f0 r0 h epsN cstar Cstar Bg Cbias : ℝ}
        {x0 : Fin d → ℝ} {P : CateLaw d},
        RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0 →
        HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P → IidSampling P →
        0 < n → 0 < h → h < rStar r0 x0 → 0 < epsN →
        0 < cstar → cstar ≤ Cstar →
        (∀ a : Fin 2, popGram P h x0 (expoOf d (⌈beta⌉₊ - 1)) (unifKernel d) a
          ∈ loewnerSet (pDim d (⌈beta⌉₊ - 1)) cstar Cstar) →
        (∀ a : Fin 2, Real.sqrt (∑ k,
          (popMom P h x0 (expoOf d (⌈beta⌉₊ - 1)) (unifKernel d) a k) ^ 2) ≤ Bg) →
        0 ≤ Bg →
        (∀ a : Fin 2,
          |((popGram P h x0 (expoOf d (⌈beta⌉₊ - 1)) (unifKernel d) a)⁻¹.mulVec
              (popMom P h x0 (expoOf d (⌈beta⌉₊ - 1)) (unifKernel d) a))
                (icptOf d (⌈beta⌉₊ - 1)) - armMu P a x0| ≤ Cbias * h ^ beta) →
        |P.mu1 x0 - P.mu0 x0| ≤ 2 →
        ∫ s, (∫ z, |z - (P.mu1 x0 - P.mu0 x0)|
            ∂(mechOf (⌈beta⌉₊ - 1) h cstar Cstar epsN x0 s))
            ∂(Measure.pi fun _ : Fin n ↦ P.dataMeasure) ≤
          2 * Cbias * h ^ beta +
            (Cv1 / cstar + Cv2 * Bg / cstar ^ 2) *
              Real.sqrt (1 / ((n : ℝ) * h ^ (d : ℝ))) +
            Cw * (1 / cstar + Bg / cstar ^ 2) *
              (1 / ((n : ℝ) * epsN * h ^ (d : ℝ))) := by
  let m := ⌈beta⌉₊ - 1
  let p : ℝ := pDim d m
  let Cv1 := 2 * Real.sqrt (p * f1 * 2 ^ d)
  let Cv2 := 2 * Real.sqrt (p ^ 2 * f1 * 2 ^ d)
  let Cw := 2 * (Nq d m : ℝ) * Cs d m
  refine ⟨Cv1, Cv2, Cw, ?_, ?_, ?_, ?_⟩
  · exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  · exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  · dsimp [Cw]
    have hCs0 : 0 ≤ Cs d m := by unfold Cs; positivity
    positivity
  intro n alpha gamma L e0 f0 r0 h epsN cstar Cstar Bg Cbias x0 P
    hreg hP hiid hn hh hhr heps hcstar hcC hloew hBg hBg0 hbias htau
  letI : IsProbabilityMeasure P.dataMeasure := hiid.1
  have hhr0 : h ≤ r0 := by
    have hrs : rStar r0 x0 ≤ r0 := by
      unfold rStar
      have := min_le_left r0 (⨅ i : Fin d, min (x0 i) (1 - x0 i))
      have hr0 : 0 < r0 := hreg.2.2.2.2.2.2.2.1.1
      linarith
    exact (le_of_lt hhr).trans hrs
  have hf1 : 0 ≤ f1 := hreg.2.2.2.2.2.1.le.trans hreg.2.2.2.2.2.2.1
  let b := (Cs d m / ((n : ℝ) * h ^ (d : ℝ))) / epsN
  have hCs : 0 < Cs d m := by
    unfold Cs
    have hp : 0 < (pDim d m : ℝ) := by exact_mod_cast pDim_pos d m
    positivity
  have hb : 0 < b := by
    dsimp [b]
    positivity
  letI (i : Fin (Nq d m)) : IsProbabilityMeasure (laplaceMeasure b) :=
    laplaceMeasure_isProbabilityMeasure b hb
  let W : (Fin (Nq d m) → ℝ) → ℝ := fun w ↦
    Real.sqrt (∑ i, (w i) ^ 2)
  let Mom : (Fin n → CateObs d) → Fin 2 → ℝ := fun s a ↦
    Real.sqrt (∑ k, (empMom m h x0 a s k -
      popMom P h x0 (expoOf d m) (unifKernel d) a k) ^ 2)
  let Gram : (Fin n → CateObs d) → Fin 2 → ℝ := fun s a ↦
    frobDist (empGram m h x0 a s)
      (popGram P h x0 (expoOf d m) (unifKernel d) a)
  let q := 1 / cstar + Bg / cstar ^ 2
  let A : (Fin n → CateObs d) → ℝ := fun s ↦
    ∑ a : Fin 2, ((1 / cstar) * Mom s a + (Bg / cstar ^ 2) * Gram s a)
  have hWint : Integrable W (Measure.pi fun _ : Fin (Nq d m) ↦ laplaceMeasure b) :=
    laplacePi_integrable_euclidean_norm b hb
  have hWbound : (∫ w, W w ∂(Measure.pi fun _ : Fin (Nq d m) ↦ laplaceMeasure b)) ≤
      (Nq d m : ℝ) * b := by
    simpa [W] using (laplacePi_integral_euclidean_norm_le
      (ι := Fin (Nq d m)) b hb)
  have hinner (s : Fin n → CateObs d) :
      (∫ z, |z - (P.mu1 x0 - P.mu0 x0)|
          ∂(mechOf m h cstar Cstar epsN x0 s)) ≤
        A s + 2 * q * ((Nq d m : ℝ) * b) + 2 * Cbias * h ^ beta := by
    rw [integral_mechOf_eq_integral_laplace]
    let D : (Fin (Nq d m) → ℝ) → ℝ := fun w ↦
      A s + 2 * q * W w + 2 * Cbias * h ^ beta
    have hDint : Integrable D (Measure.pi fun _ : Fin (Nq d m) ↦ laplaceMeasure b) := by
      dsimp [D]
      fun_prop
    calc
      _ ≤ ∫ w, D w ∂(Measure.pi fun _ : Fin (Nq d m) ↦ laplaceMeasure b) := by
        apply integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _ ) hDint
        apply ae_of_all
        intro w
        have hr := releaseOf_error_le (m := m) hcstar hcC htau hloew hBg hBg0 hbias s w
        dsimp [D, A, Mom, Gram, W, q]
        rw [Fin.sum_univ_two]
        rw [Fin.sum_univ_two] at hr
        linarith
      _ = A s + 2 * q * (∫ w, W w
            ∂(Measure.pi fun _ : Fin (Nq d m) ↦ laplaceMeasure b)) +
          2 * Cbias * h ^ beta := by
        have hfirst := integral_add (integrable_const (A s)) (hWint.const_mul (2 * q))
        have hall := integral_add
          ((integrable_const (A s)).add (hWint.const_mul (2 * q)))
          (integrable_const (2 * Cbias * h ^ beta))
        calc
          _ = (∫ w, A s + 2 * q * W w
                ∂(Measure.pi fun _ : Fin (Nq d m) ↦ laplaceMeasure b)) +
              ∫ _w, 2 * Cbias * h ^ beta
                ∂(Measure.pi fun _ : Fin (Nq d m) ↦ laplaceMeasure b) := by
                  simpa [D] using hall
          _ = ((∫ _w, A s ∂(Measure.pi fun _ : Fin (Nq d m) ↦ laplaceMeasure b)) +
                ∫ w, 2 * q * W w
                  ∂(Measure.pi fun _ : Fin (Nq d m) ↦ laplaceMeasure b)) +
              ∫ _w, 2 * Cbias * h ^ beta
                ∂(Measure.pi fun _ : Fin (Nq d m) ↦ laplaceMeasure b) := by rw [hfirst]
          _ = _ := by simp [integral_const_mul]
      _ ≤ _ := by
        gcongr
  have hMomInt (a : Fin 2) : Integrable (fun s ↦ Mom s a)
      (Measure.pi fun _ : Fin n ↦ P.dataMeasure) := by
    let ξ : Fin (pDim d m) → CateObs d → ℝ := fun k O ↦
      momSummand h x0 (expoOf d m) (unifKernel d) a O k
    have hi := integrable_iid_mean_euclidean P.dataMeasure (n := n) ξ
      (fun k ↦ measurable_momSummand' h x0 a k)
      (h ^ (-(d : ℝ))) (fun k O ↦ by
        simpa using abs_momSummand_le hh (unifKernel_nonneg d) (unifKernel_le_one d)
          (unifKernel_eq_zero d) a O k)
    convert hi using 1
  have hGramInt (a : Fin 2) : Integrable (fun s ↦ Gram s a)
      (Measure.pi fun _ : Fin n ↦ P.dataMeasure) := by
    let ξ : (Fin (pDim d m) × Fin (pDim d m)) → CateObs d → ℝ := fun q O ↦
      gramSummand h x0 (expoOf d m) (unifKernel d) a O q.1 q.2
    have hi := integrable_iid_mean_euclidean P.dataMeasure (n := n) ξ
      (fun q ↦ measurable_gramSummand' h x0 a q.1 q.2)
      (h ^ (-(d : ℝ))) (fun q O ↦ by
        simpa using abs_gramSummand_le hh (unifKernel_nonneg d) (unifKernel_le_one d)
          (unifKernel_eq_zero d) a O q.1 q.2)
    convert hi using 1
    funext s
    dsimp [Gram, frobDist]
    rw [Fintype.sum_prod_type]
    congr 1
  have hAint : Integrable A (Measure.pi fun _ : Fin n ↦ P.dataMeasure) := by
    dsimp [A]
    apply integrable_finset_sum
    intro a _
    exact ((hMomInt a).const_mul _).add ((hGramInt a).const_mul _)
  have houter :
      (∫ s, (∫ z, |z - (P.mu1 x0 - P.mu0 x0)|
          ∂(mechOf m h cstar Cstar epsN x0 s))
          ∂(Measure.pi fun _ : Fin n ↦ P.dataMeasure)) ≤
        (∫ s, A s ∂(Measure.pi fun _ : Fin n ↦ P.dataMeasure)) +
          2 * q * ((Nq d m : ℝ) * b) + 2 * Cbias * h ^ beta := by
    calc
      _ ≤ ∫ s, (A s + 2 * q * ((Nq d m : ℝ) * b) + 2 * Cbias * h ^ beta)
          ∂(Measure.pi fun _ : Fin n ↦ P.dataMeasure) := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ fun s ↦ integral_nonneg fun _ ↦ abs_nonneg _
        · fun_prop
        · exact ae_of_all _ hinner
      _ = _ := by
        have hfirst := integral_add hAint
          (integrable_const (2 * q * ((Nq d m : ℝ) * b)))
        have hall := integral_add
          (hAint.add (integrable_const (2 * q * ((Nq d m : ℝ) * b))))
          (integrable_const (2 * Cbias * h ^ beta))
        calc
          _ = (∫ s, A s + 2 * q * ((Nq d m : ℝ) * b)
                ∂(Measure.pi fun _ : Fin n ↦ P.dataMeasure)) +
              ∫ _s, 2 * Cbias * h ^ beta
                ∂(Measure.pi fun _ : Fin n ↦ P.dataMeasure) := by
                  simpa using hall
          _ = ((∫ s, A s ∂(Measure.pi fun _ : Fin n ↦ P.dataMeasure)) +
                ∫ _s, 2 * q * ((Nq d m : ℝ) * b)
                  ∂(Measure.pi fun _ : Fin n ↦ P.dataMeasure)) +
              ∫ _s, 2 * Cbias * h ^ beta
                ∂(Measure.pi fun _ : Fin n ↦ P.dataMeasure) := by rw [hfirst]
          _ = _ := by simp
  have hMomBound (a : Fin 2) := integral_empMom_sub_popMom_le
    hreg hP hiid hn hh hhr0 (m := m) a
  have hGramBound (a : Fin 2) := integral_empGram_sub_popGram_le
    hreg hP hiid hn hh hhr0 (m := m) a
  have hrate : h ^ (-(d : ℝ)) / (n : ℝ) =
      1 / ((n : ℝ) * h ^ (d : ℝ)) := rpow_neg_div_nat hh
  have hMomRate (a : Fin 2) :
      (∫ s, Mom s a ∂(Measure.pi fun _ : Fin n ↦ P.dataMeasure)) ≤
        Real.sqrt (p * f1 * 2 ^ d) *
          Real.sqrt (1 / ((n : ℝ) * h ^ (d : ℝ))) := by
    calc
      _ ≤ Real.sqrt ((p * f1 * 2 ^ d * h ^ (-(d : ℝ))) / (n : ℝ)) := hMomBound a
      _ = _ := by
        rw [show (p * f1 * 2 ^ d * h ^ (-(d : ℝ))) / (n : ℝ) =
          (p * f1 * 2 ^ d) * (h ^ (-(d : ℝ)) / (n : ℝ)) by ring, hrate,
          Real.sqrt_mul (by positivity : 0 ≤ p * f1 * 2 ^ d)]
  have hGramRate (a : Fin 2) :
      (∫ s, Gram s a ∂(Measure.pi fun _ : Fin n ↦ P.dataMeasure)) ≤
        Real.sqrt (p ^ 2 * f1 * 2 ^ d) *
          Real.sqrt (1 / ((n : ℝ) * h ^ (d : ℝ))) := by
    calc
      _ ≤ Real.sqrt ((p ^ 2 * f1 * 2 ^ d * h ^ (-(d : ℝ))) / (n : ℝ)) := hGramBound a
      _ = _ := by
        rw [show (p ^ 2 * f1 * 2 ^ d * h ^ (-(d : ℝ))) / (n : ℝ) =
          (p ^ 2 * f1 * 2 ^ d) * (h ^ (-(d : ℝ)) / (n : ℝ)) by ring, hrate,
          Real.sqrt_mul (by positivity : 0 ≤ p ^ 2 * f1 * 2 ^ d)]
  calc
    _ ≤ (∫ s, A s ∂(Measure.pi fun _ : Fin n ↦ P.dataMeasure)) +
        2 * q * ((Nq d m : ℝ) * b) + 2 * Cbias * h ^ beta := houter
    _ ≤ 2 * Cbias * h ^ beta +
        (Cv1 / cstar + Cv2 * Bg / cstar ^ 2) *
          Real.sqrt (1 / ((n : ℝ) * h ^ (d : ℝ))) +
        Cw * q * (1 / ((n : ℝ) * epsN * h ^ (d : ℝ))) := by
      rw [show (∫ s, A s ∂(Measure.pi fun _ : Fin n ↦ P.dataMeasure)) =
          ∑ a : Fin 2, ((1 / cstar) * ∫ s, Mom s
              a ∂(Measure.pi fun _ : Fin n ↦ P.dataMeasure) +
            (Bg / cstar ^ 2) * ∫ s, Gram s
              a ∂(Measure.pi fun _ : Fin n ↦ P.dataMeasure)) by
        dsimp [A]
        have ha0 := integral_add ((hMomInt 0).const_mul (1 / cstar))
          ((hGramInt 0).const_mul (Bg / cstar ^ 2))
        have ha1 := integral_add ((hMomInt 1).const_mul (1 / cstar))
          ((hGramInt 1).const_mul (Bg / cstar ^ 2))
        have hsum := integral_add
          (((hMomInt 0).const_mul (1 / cstar)).add
            ((hGramInt 0).const_mul (Bg / cstar ^ 2)))
          (((hMomInt 1).const_mul (1 / cstar)).add
            ((hGramInt 1).const_mul (Bg / cstar ^ 2)))
        calc
          _ = (∫ s, (1 / cstar) * Mom s 0 + (Bg / cstar ^ 2) * Gram s 0
                ∂(Measure.pi fun _ : Fin n ↦ P.dataMeasure)) +
              ∫ s, (1 / cstar) * Mom s 1 + (Bg / cstar ^ 2) * Gram s 1
                ∂(Measure.pi fun _ : Fin n ↦ P.dataMeasure) := by
                  simpa [Fin.sum_univ_two] using hsum
          _ = _ := by
            rw [ha0, ha1]
            simp [Fin.sum_univ_two, integral_const_mul]]
      rw [Fin.sum_univ_two]
      dsimp [Cv1, Cv2, Cw, q, b, p]
      have hnoise : ((Nq d m : ℝ) * ((Cs d m / ((n : ℝ) * h ^ (d : ℝ))) / epsN)) =
          (Nq d m : ℝ) * Cs d m *
            (1 / ((n : ℝ) * epsN * h ^ (d : ℝ))) := by
        field_simp
      rw [hnoise]
      have hm0 := hMomRate 0
      have hm1 := hMomRate 1
      have hg0 := hGramRate 0
      have hg1 := hGramRate 1
      dsimp [Mom, Gram, p] at hm0 hm1 hg0 hg1
      have hc0 : 0 ≤ 1 / cstar := by positivity
      have hbgc : 0 ≤ Bg / cstar ^ 2 := by positivity
      calc
        _ ≤ ((1 / cstar) * (Real.sqrt ((pDim d m : ℝ) * f1 * 2 ^ d) *
                Real.sqrt (1 / ((n : ℝ) * h ^ (d : ℝ)))) +
              (Bg / cstar ^ 2) * (Real.sqrt ((pDim d m : ℝ) ^ 2 * f1 * 2 ^ d) *
                Real.sqrt (1 / ((n : ℝ) * h ^ (d : ℝ))))) +
            ((1 / cstar) * (Real.sqrt ((pDim d m : ℝ) * f1 * 2 ^ d) *
                Real.sqrt (1 / ((n : ℝ) * h ^ (d : ℝ)))) +
              (Bg / cstar ^ 2) * (Real.sqrt ((pDim d m : ℝ) ^ 2 * f1 * 2 ^ d) *
                Real.sqrt (1 / ((n : ℝ) * h ^ (d : ℝ))))) +
            2 * (1 / cstar + Bg / cstar ^ 2) *
              ((Nq d m : ℝ) * Cs d m * (1 / ((n : ℝ) * epsN * h ^ (d : ℝ)))) +
            2 * Cbias * h ^ beta := by
              gcongr
        _ = _ := by ring
    _ = _ := by rfl

end

end CausalSmith.Stat.DpCateMinimax
