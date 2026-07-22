/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Core.Rate
import Causalean.ML.Ridge.Population
import Causalean.Stat.Sample
import Causalean.Stat.Limit.WLLN
import Causalean.Stat.EmpiricalProcess.CrossFitRate
import Causalean.Stat.Limit.ContinuousMapping
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Instances.Matrix

/-! # Ridge regression — estimation rate (root-n)

This file builds the sample ridge estimator from the first `n` points of an
i.i.d. sample and proves a root-n L²-estimation rate toward the population ridge
minimizer.  It defines the empirical Gram `empiricalGram`, empirical cross
moment `empiricalCross`, sample coefficient `sampleRidgeCoef`, sample predictor
`sampleRidgePredictor`, and population feature Gram `populationGram`.

The main algebraic step is `sampleRidgeCoef_sub_eq`: the coefficient error
factors through `(Ĝₙ + λI)⁻¹` times the centered empirical score
`(Ĉₙ - Ĝₙ β⋆) - λ β⋆`.  The population ridge normal equation centers that score;
`centered_score_mean_isBigOp` gives its `O_p(n^{-1/2})` rate, while
`sampleRidgeCoef_isBigOp` combines this with entrywise convergence of the
regularized Gram inverse.  The final theorem `ridge_achievesL2Rate` transfers the
coefficient rate to an L²-rate for the sample ridge predictor.
-/

namespace Causalean.ML

open MeasureTheory Matrix BigOperators Causalean.Stat

variable {Ω γ K : Type*} [MeasurableSpace Ω] [MeasurableSpace γ]
  [Fintype K] [DecidableEq K] {μ : Measure Ω}

/-- Empirical feature Gram over the first `n` sample points:
`Ĝₙ = n⁻¹ Σ_{i<n} φ(xᵢ) φ(xᵢ)ᵀ`. -/
noncomputable def empiricalGram (φ : FeatureMap γ K) (Z : ℕ → Ω → γ × ℝ)
    (n : ℕ) (ω : Ω) : Matrix K K ℝ :=
  (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
    Matrix.vecMulVec (φ.φ (Z i ω).1) (φ.φ (Z i ω).1)

/-- Empirical feature–response cross moment: `Ĉₙ = n⁻¹ Σ_{i<n} yᵢ φ(xᵢ)`. -/
noncomputable def empiricalCross (φ : FeatureMap γ K) (Z : ℕ → Ω → γ × ℝ)
    (n : ℕ) (ω : Ω) : K → ℝ :=
  (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, (Z i ω).2 • φ.φ (Z i ω).1

/-- The sample ridge coefficient `β̂ₙ = (Ĝₙ + λI)⁻¹ Ĉₙ`. -/
noncomputable def sampleRidgeCoef (φ : FeatureMap γ K) (Z : ℕ → Ω → γ × ℝ)
    (lam : ℝ) (n : ℕ) (ω : Ω) : K → ℝ :=
  (empiricalGram φ Z n ω + lam • (1 : Matrix K K ℝ))⁻¹ *ᵥ empiricalCross φ Z n ω

/-- The sample ridge predictor `x ↦ ⟨β̂ₙ, φ(x)⟩`. -/
noncomputable def sampleRidgePredictor (φ : FeatureMap γ K) (Z : ℕ → Ω → γ × ℝ)
    (lam : ℝ) (n : ℕ) (ω : Ω) : γ → ℝ :=
  fun x => ∑ k, sampleRidgeCoef φ Z lam n ω k * φ.φ x k

/-- The population feature Gram, defined entrywise (avoids matrix-valued Bochner
integration): `Gₖₗ = ∫ φ(x)ₖ φ(x)ₗ dP`. -/
noncomputable def populationGram (φ : FeatureMap γ K) (P : Measure (γ × ℝ)) :
    Matrix K K ℝ :=
  Matrix.of fun k l => ∫ z, φ.φ z.1 k * φ.φ z.1 l ∂P

/-- The population feature Gram is positive semidefinite whenever the feature
coordinates are measurable and the fourth moment of the feature norm is finite. -/
theorem populationGram_posSemidef (φ : FeatureMap γ K) (P : Measure (γ × ℝ))
    [IsFiniteMeasure P]
    (hφ : ∀ k, Measurable (fun x => φ.φ x k))
    (h4 : Integrable (fun z => (∑ k, (φ.φ z.1 k) ^ 2) ^ 2) P) :
    (populationGram φ P).PosSemidef := by
  classical
  have hφ_prod : ∀ k, Measurable (fun z : γ × ℝ => φ.φ z.1 k) := fun k =>
    (hφ k).comp measurable_fst
  have hsum_meas : Measurable (fun z : γ × ℝ => ∑ k, (φ.φ z.1 k) ^ 2) :=
    Finset.measurable_sum _ (fun k _ => (hφ_prod k).pow_const 2)
  have hsumsq_int : Integrable (fun z : γ × ℝ => ∑ k, (φ.φ z.1 k) ^ 2) P := by
    refine Integrable.mono' (g := fun z => 1 + (∑ k, (φ.φ z.1 k) ^ 2) ^ 2)
      ((integrable_const (1 : ℝ)).add h4) hsum_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun z => ?_)
    have hnn : (0 : ℝ) ≤ ∑ k, (φ.φ z.1 k) ^ 2 :=
      Finset.sum_nonneg (fun k _ => sq_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    nlinarith [sq_nonneg ((∑ k, (φ.φ z.1 k) ^ 2) - 1)]
  have hprod_int : ∀ i j,
      Integrable (fun z : γ × ℝ => φ.φ z.1 i * φ.φ z.1 j) P := by
    intro i j
    refine Integrable.mono hsumsq_int
      ((hφ_prod i).mul (hφ_prod j)).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun z => ?_)
    let a : ℝ := φ.φ z.1 i
    let b : ℝ := φ.φ z.1 j
    let s : ℝ := ∑ k, (φ.φ z.1 k) ^ 2
    have hs_nonneg : 0 ≤ s := by
      dsimp [s]
      exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
    rw [Real.norm_eq_abs, Real.norm_of_nonneg hs_nonneg]
    have hi_le : a ^ 2 ≤ s := by
      dsimp [a, s]
      exact Finset.single_le_sum (f := fun k => (φ.φ z.1 k) ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ i)
    have hj_le : b ^ 2 ≤ s := by
      dsimp [b, s]
      exact Finset.single_le_sum (f := fun k => (φ.φ z.1 k) ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    have hab_half : |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2 := by
      have h := two_mul_le_add_sq |a| |b|
      have hsqa : |a| ^ 2 = a ^ 2 := by rw [sq_abs]
      have hsqb : |b| ^ 2 = b ^ 2 := by rw [sq_abs]
      nlinarith
    have hab_sum : (a ^ 2 + b ^ 2) / 2 ≤ s := by
      nlinarith
    calc
      |φ.φ z.1 i * φ.φ z.1 j| = |a| * |b| := by
        dsimp [a, b]
        rw [abs_mul]
      _ ≤ (a ^ 2 + b ^ 2) / 2 := hab_half
      _ ≤ s := hab_sum
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · apply Matrix.IsHermitian.ext
    intro i j
    simp [populationGram, mul_comm]
  · intro x
    have hterm_int : ∀ i j,
        Integrable
          (fun z : γ × ℝ => (x i * x j) * (φ.φ z.1 i * φ.φ z.1 j)) P := by
      intro i j
      simpa [mul_assoc] using (hprod_int i j).const_mul (x i * x j)
    have hquad :
        star x ⬝ᵥ (populationGram φ P *ᵥ x)
          = ∫ z, (∑ i, x i * φ.φ z.1 i) ^ 2 ∂P := by
      calc
        star x ⬝ᵥ (populationGram φ P *ᵥ x)
            = ∑ i, ∑ j,
                x i * ((∫ z, φ.φ z.1 i * φ.φ z.1 j ∂P) * x j) := by
              simp [dotProduct, Matrix.mulVec, populationGram, Finset.mul_sum]
        _ = ∑ i, ∑ j,
                ∫ z, (x i * x j) * (φ.φ z.1 i * φ.φ z.1 j) ∂P := by
              refine Finset.sum_congr rfl ?_
              intro i _
              refine Finset.sum_congr rfl ?_
              intro j _
              calc
                x i * ((∫ z, φ.φ z.1 i * φ.φ z.1 j ∂P) * x j)
                    = (x i * x j) * ∫ z, φ.φ z.1 i * φ.φ z.1 j ∂P := by
                      ring
                _ = ∫ z, (x i * x j) * (φ.φ z.1 i * φ.φ z.1 j) ∂P := by
                      rw [integral_const_mul]
        _ = ∫ z, ∑ i, ∑ j,
                (x i * x j) * (φ.φ z.1 i * φ.φ z.1 j) ∂P := by
              rw [integral_finset_sum Finset.univ]
              · refine Finset.sum_congr rfl ?_
                intro i _
                rw [integral_finset_sum Finset.univ]
                intro j _
                exact hterm_int i j
              · intro i _
                exact integrable_finset_sum Finset.univ (fun j _ => hterm_int i j)
        _ = ∫ z, (∑ i, x i * φ.φ z.1 i) ^ 2 ∂P := by
              congr 1
              funext z
              rw [sq, Finset.sum_mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i _
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
    rw [hquad]
    exact integral_nonneg fun z => sq_nonneg _

/-- The empirical Gram is positive semidefinite (average of rank-one `φφᵀ`). -/
theorem empiricalGram_posSemidef (φ : FeatureMap γ K) (Z : ℕ → Ω → γ × ℝ)
    (n : ℕ) (ω : Ω) : (empiricalGram φ Z n ω).PosSemidef := by
  unfold empiricalGram
  apply Matrix.PosSemidef.smul
  · refine Finset.sum_induction
      (fun i => Matrix.vecMulVec (φ.φ (Z i ω).1) (φ.φ (Z i ω).1))
      (fun A : Matrix K K ℝ => A.PosSemidef)
      (fun _ _ hA hB => hA.add hB) Matrix.PosSemidef.zero ?_
    intro i _
    simpa using
      (Matrix.posSemidef_vecMulVec_self_star (φ.φ (Z i ω).1) :
        (Matrix.vecMulVec (φ.φ (Z i ω).1) (star (φ.φ (Z i ω).1))).PosSemidef)
  · exact inv_nonneg.mpr (Nat.cast_nonneg n)

/-- The ridge coefficient error factors through the regularized empirical Gram
inverse and the centered empirical score
`Ŝₙ − λ β⋆ = (Ĉₙ − Ĝₙ β⋆) − λ β⋆`. -/
theorem sampleRidgeCoef_sub_eq (φ : FeatureMap γ K) (Z : ℕ → Ω → γ × ℝ)
    {lam : ℝ} (hlam : 0 < lam) (βstar : K → ℝ) (n : ℕ) (ω : Ω) :
    sampleRidgeCoef φ Z lam n ω - βstar
      = (empiricalGram φ Z n ω + lam • (1 : Matrix K K ℝ))⁻¹ *ᵥ
          (empiricalCross φ Z n ω - empiricalGram φ Z n ω *ᵥ βstar - lam • βstar) := by
  let G : Matrix K K ℝ := empiricalGram φ Z n ω + lam • (1 : Matrix K K ℝ)
  have hGpos : G.PosDef := by
    dsimp [G]
    exact Matrix.PosDef.posSemidef_add (empiricalGram_posSemidef φ Z n ω)
      (Matrix.PosDef.smul Matrix.PosDef.one hlam)
  have hGdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hGpos.isUnit
  have hG_mul :
      empiricalGram φ Z n ω *ᵥ βstar + lam • βstar = G *ᵥ βstar := by
    dsimp [G]
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  calc
    sampleRidgeCoef φ Z lam n ω - βstar
        = G⁻¹ *ᵥ empiricalCross φ Z n ω - βstar := by
          rfl
    _ = G⁻¹ *ᵥ empiricalCross φ Z n ω - G⁻¹ *ᵥ (G *ᵥ βstar) := by
          rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hGdet, Matrix.one_mulVec]
    _ = G⁻¹ *ᵥ (empiricalCross φ Z n ω - G *ᵥ βstar) := by
          rw [Matrix.mulVec_sub]
    _ = G⁻¹ *ᵥ
          (empiricalCross φ Z n ω - empiricalGram φ Z n ω *ᵥ βstar - lam • βstar) := by
          rw [← hG_mul]
          abel

/-- The centered empirical score mean
`Ŝₙ − λβ⋆ = (Ĉₙ − Ĝₙβ⋆) − λβ⋆ = n⁻¹ Σ (φᵢ(yᵢ−⟨β⋆,φᵢ⟩) − λβ⋆)`
is `O_p(n^{-1/2})`.  The population normal equations make the summands centered. -/
theorem centered_score_mean_isBigOp (φ : FeatureMap γ K) (P : Measure (γ × ℝ))
    [IsProbabilityMeasure P] (S : IIDSample Ω (γ × ℝ) μ P) [IsProbabilityMeasure μ]
    {lam : ℝ} (βstar : K → ℝ) (hpop : IsPopulationRidge P φ lam βstar)
    (hφ : ∀ k, Measurable (fun x => φ.φ x k))
    (hscore : ∀ k, MemLp
      (fun z => (z.2 - ∑ j, βstar j * φ.φ z.1 j) * φ.φ z.1 k) 2 P) :
    Causalean.Stat.IsBigOp
      (fun n ω => ‖empiricalCross φ S.Z n ω - empiricalGram φ S.Z n ω *ᵥ βstar
        - lam • βstar‖) (fun n => (Real.sqrt (n : ℝ))⁻¹) μ := by
  classical
  let g : K → γ × ℝ → ℝ :=
    fun k z => (z.2 - ∑ j, βstar j * φ.φ z.1 j) * φ.φ z.1 k
  let D : ℕ → Ω → K → ℝ :=
    fun n ω => empiricalCross φ S.Z n ω - empiricalGram φ S.Z n ω *ᵥ βstar
      - lam • βstar
  have hφ_prod : ∀ k, Measurable (fun z : γ × ℝ => φ.φ z.1 k) := fun k =>
    (hφ k).comp measurable_fst
  have hg_meas : ∀ k, Measurable (g k) := by
    intro k
    dsimp [g]
    exact (measurable_snd.sub
      (Finset.measurable_sum _ fun j _ => measurable_const.mul (hφ_prod j))).mul
      (hφ_prod k)
  have hcoord : ∀ n ω k,
      D n ω k = S.sampleMean (g k) n ω - ∫ z, g k z ∂P := by
    intro n ω k
    dsimp [D, g, IIDSample.sampleMean, empiricalCross, empiricalGram]
    rw [hpop k]
    simp only [smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.smul_apply,
      Matrix.sum_apply, Matrix.vecMulVec_apply]
    simp [Finset.sum_apply]
    have hgram_sum :
        (∑ x, (((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
            φ.φ (S.Z i ω).1 k * φ.φ (S.Z i ω).1 x) * βstar x))
          = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
              (∑ x, βstar x * φ.φ (S.Z i ω).1 x) * φ.φ (S.Z i ω).1 k := by
      calc
        (∑ x, (((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
            φ.φ (S.Z i ω).1 k * φ.φ (S.Z i ω).1 x) * βstar x))
            = ∑ x, (n : ℝ)⁻¹ * ((∑ i ∈ Finset.range n,
                φ.φ (S.Z i ω).1 k * φ.φ (S.Z i ω).1 x) * βstar x) := by
              refine Finset.sum_congr rfl ?_
              intro x _
              ring
        _ = (n : ℝ)⁻¹ * ∑ x, (∑ i ∈ Finset.range n,
                φ.φ (S.Z i ω).1 k * φ.φ (S.Z i ω).1 x) * βstar x := by
              rw [Finset.mul_sum]
        _ = (n : ℝ)⁻¹ * ∑ x, ∑ i ∈ Finset.range n,
                (φ.φ (S.Z i ω).1 k * φ.φ (S.Z i ω).1 x) * βstar x := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro x _
              rw [Finset.sum_mul]
        _ = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∑ x,
                (φ.φ (S.Z i ω).1 k * φ.φ (S.Z i ω).1 x) * βstar x := by
              congr 1
              rw [Finset.sum_comm]
        _ = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
              (∑ x, βstar x * φ.φ (S.Z i ω).1 x) * φ.φ (S.Z i ω).1 k := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl ?_
              intro x _
              ring
    rw [hgram_sum]
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    refine congrArg (fun t : ℝ => (n : ℝ)⁻¹ * t) ?_
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  have hcoord_big :
      ∀ k, Causalean.Stat.IsBigOp (fun n ω => D n ω k)
        (fun n => (Real.sqrt (n : ℝ))⁻¹) μ := by
    intro k
    have hk0 := S.sampleMean_sub_isBigOp (hg_meas k) (by simpa [g] using hscore k)
    let A : ℝ := ∫ z, (g k z) ^ 2 ∂P
    have hA_nonneg : 0 ≤ A := by
      dsimp [A]
      exact integral_nonneg fun z => sq_nonneg _
    have hrate_le : ∀ n : ℕ,
        Real.sqrt (A / (n : ℝ)) ≤
          (Real.sqrt A + 1) * (Real.sqrt (n : ℝ))⁻¹ := by
      intro n
      calc
        Real.sqrt (A / (n : ℝ))
            = Real.sqrt A * (Real.sqrt (n : ℝ))⁻¹ := by
              rw [Real.sqrt_div hA_nonneg, div_eq_mul_inv]
        _ ≤ (Real.sqrt A + 1) * (Real.sqrt (n : ℝ))⁻¹ := by
              exact mul_le_mul_of_nonneg_right
                (by linarith [Real.sqrt_nonneg A])
                (inv_nonneg.mpr (Real.sqrt_nonneg (n : ℝ)))
    have hk1 : Causalean.Stat.IsBigOp
        (fun n ω => S.sampleMean (g k) n ω - ∫ z, g k z ∂P)
        (fun n => (Real.sqrt A + 1) * (Real.sqrt (n : ℝ))⁻¹) μ := by
      exact Causalean.Stat.IsBigOp.mono_rate
        (fun n => Real.sqrt_nonneg (A / (n : ℝ))) hrate_le hk0
    have hk2 : Causalean.Stat.IsBigOp
        (fun n ω => S.sampleMean (g k) n ω - ∫ z, g k z ∂P)
        (fun n => (Real.sqrt (n : ℝ))⁻¹) μ := by
      exact Causalean.Stat.IsBigOp.scale_rate
        (rn := fun n => (Real.sqrt (n : ℝ))⁻¹)
        (by linarith [Real.sqrt_nonneg A]) hk1
    have hfun :
        (fun n ω => D n ω k) =
          (fun n ω => S.sampleMean (g k) n ω - ∫ z, g k z ∂P) := by
      funext n ω
      exact hcoord n ω k
    rw [hfun]
    exact hk2
  have hcoord_abs :
      ∀ k, Causalean.Stat.IsBigOp (fun n ω => |D n ω k|)
        (fun n => (Real.sqrt (n : ℝ))⁻¹) μ := by
    intro k
    simpa [Causalean.Stat.IsBigOp, abs_abs] using hcoord_big k
  have hsum_abs : Causalean.Stat.IsBigOp
      (fun n ω => ∑ k, |D n ω k|) (fun n => (Real.sqrt (n : ℝ))⁻¹) μ := by
    simpa using
      (IsBigOp.finset_sum (μ := μ) (s := (Finset.univ : Finset K))
        (X := fun k n ω => |D n ω k|)
        (fun k _ => hcoord_abs k))
  refine IsBigOp.of_abs_le
    (Xn := fun n ω => ‖empiricalCross φ S.Z n ω -
      empiricalGram φ S.Z n ω *ᵥ βstar - lam • βstar‖)
    (Yn := fun n ω => ∑ k, |D n ω k|) ?_ hsum_abs
  intro n ω
  have hD_eq :
      D n ω = empiricalCross φ S.Z n ω - empiricalGram φ S.Z n ω *ᵥ βstar
        - lam • βstar := rfl
  have hsum_nonneg : 0 ≤ ∑ k, |D n ω k| :=
    Finset.sum_nonneg fun k _ => abs_nonneg _
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hsum_nonneg, ← hD_eq]
  refine (pi_norm_le_iff_of_nonneg hsum_nonneg).2 (fun k => ?_)
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun j => |D n ω j|)
    (fun j _ => abs_nonneg _) (Finset.mem_univ k)

/-- **Continuity of an inverse-matrix entry.**  At any matrix with nonzero
determinant, the map `M ↦ (M⁻¹)ₖₗ` is continuous. -/
theorem continuousAt_matrixInv_entry {G₀ : Matrix K K ℝ} (hdet : G₀.det ≠ 0) (k l : K) :
    ContinuousAt (fun M : Matrix K K ℝ => (M⁻¹) k l) G₀ := by
  have hdet_cont : ContinuousAt (fun M : Matrix K K ℝ => M.det) G₀ :=
    (Continuous.matrix_det continuous_id).continuousAt
  have hadj : ContinuousAt (fun M : Matrix K K ℝ => M.adjugate k l) G₀ :=
    (Continuous.matrix_elem (Continuous.matrix_adjugate continuous_id) k l).continuousAt
  have hfun : ContinuousAt
      (fun M : Matrix K K ℝ => (M.det)⁻¹ * M.adjugate k l) G₀ :=
    (hdet_cont.inv₀ hdet).mul hadj
  convert hfun using 1
  funext M
  rw [Matrix.inv_def]
  simp [smul_eq_mul]

/-- The ridge coefficient error is `O_p(n^{-1/2})`:
the regularized empirical-Gram inverse is `O_p(1)` (entrywise matrix LLN + inverse
continuity at the PosDef limit) times the centered score mean `O_p(n^{-1/2})`. -/
theorem sampleRidgeCoef_isBigOp (φ : FeatureMap γ K) (P : Measure (γ × ℝ))
    [IsProbabilityMeasure P] (S : IIDSample Ω (γ × ℝ) μ P) [IsProbabilityMeasure μ]
    {lam : ℝ} (hlam : 0 < lam) (βstar : K → ℝ)
    (hpop : IsPopulationRidge P φ lam βstar)
    (hφ : ∀ k, Measurable (fun x => φ.φ x k))
    (h4 : Integrable (fun z => (∑ k, (φ.φ z.1 k) ^ 2) ^ 2) P)
    (hscore : ∀ k, MemLp
      (fun z => (z.2 - ∑ j, βstar j * φ.φ z.1 j) * φ.φ z.1 k) 2 P)
    (hGramPosDef : (populationGram φ P + lam • (1 : Matrix K K ℝ)).PosDef) :
    Causalean.Stat.IsBigOp
      (fun n ω => ‖sampleRidgeCoef φ S.Z lam n ω - βstar‖)
      (fun n => (Real.sqrt (n : ℝ))⁻¹) μ := by
  classical
  let rn : ℕ → ℝ := fun n => (Real.sqrt (n : ℝ))⁻¹
  let D : ℕ → Ω → K → ℝ :=
    fun n ω => empiricalCross φ S.Z n ω - empiricalGram φ S.Z n ω *ᵥ βstar
      - lam • βstar
  let Inv : ℕ → Ω → Matrix K K ℝ :=
    fun n ω => (empiricalGram φ S.Z n ω + lam • (1 : Matrix K K ℝ))⁻¹
  have hrn_nonneg : ∀ n, 0 ≤ rn n := fun n =>
    inv_nonneg.mpr (Real.sqrt_nonneg (n : ℝ))
  have hDnorm : Causalean.Stat.IsBigOp (fun n ω => ‖D n ω‖) rn μ := by
    simpa [D, rn] using
      (centered_score_mean_isBigOp φ P S βstar hpop hφ hscore)
  have hDcoord : ∀ l, Causalean.Stat.IsBigOp (fun n ω => D n ω l) rn μ := by
    intro l
    refine IsBigOp.of_abs_le (Yn := fun n ω => ‖D n ω‖) ?_ hDnorm
    intro n ω
    have hcoord := norm_le_pi_norm (D n ω) l
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hcoord
  have hφ_prod : ∀ k, Measurable (fun z : γ × ℝ => φ.φ z.1 k) := fun k =>
    (hφ k).comp measurable_fst
  have hsum_meas : Measurable (fun z : γ × ℝ => ∑ k, (φ.φ z.1 k) ^ 2) :=
    Finset.measurable_sum _ (fun k _ => (hφ_prod k).pow_const 2)
  have hsumsq_int : Integrable (fun z : γ × ℝ => ∑ k, (φ.φ z.1 k) ^ 2) P := by
    refine Integrable.mono' (g := fun z => 1 + (∑ k, (φ.φ z.1 k) ^ 2) ^ 2)
      ((integrable_const (1 : ℝ)).add h4) hsum_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun z => ?_)
    have hnn : (0 : ℝ) ≤ ∑ k, (φ.φ z.1 k) ^ 2 :=
      Finset.sum_nonneg (fun k _ => sq_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    nlinarith [sq_nonneg ((∑ k, (φ.φ z.1 k) ^ 2) - 1)]
  have hprod_int : ∀ i j,
      Integrable (fun z : γ × ℝ => φ.φ z.1 i * φ.φ z.1 j) P := by
    intro i j
    refine Integrable.mono hsumsq_int
      ((hφ_prod i).mul (hφ_prod j)).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun z => ?_)
    let a : ℝ := φ.φ z.1 i
    let b : ℝ := φ.φ z.1 j
    let s : ℝ := ∑ k, (φ.φ z.1 k) ^ 2
    have hs_nonneg : 0 ≤ s := by
      dsimp [s]
      exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
    rw [Real.norm_eq_abs, Real.norm_of_nonneg hs_nonneg]
    have hi_le : a ^ 2 ≤ s := by
      dsimp [a, s]
      exact Finset.single_le_sum (f := fun k => (φ.φ z.1 k) ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ i)
    have hj_le : b ^ 2 ≤ s := by
      dsimp [b, s]
      exact Finset.single_le_sum (f := fun k => (φ.φ z.1 k) ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    have hab_half : |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2 := by
      have h := two_mul_le_add_sq |a| |b|
      have hsqa : |a| ^ 2 = a ^ 2 := by rw [sq_abs]
      have hsqb : |b| ^ 2 = b ^ 2 := by rw [sq_abs]
      nlinarith
    have hab_sum : (a ^ 2 + b ^ 2) / 2 ≤ s := by
      nlinarith
    calc
      |φ.φ z.1 i * φ.φ z.1 j| = |a| * |b| := by
        dsimp [a, b]
        rw [abs_mul]
      _ ≤ (a ^ 2 + b ^ 2) / 2 := hab_half
      _ ≤ s := hab_sum
  have hGram_entry : ∀ i j,
      Tendsto_inProb (fun n ω => empiricalGram φ S.Z n ω i j)
        (fun _ => populationGram φ P i j) μ := by
    intro i j
    have hcomp_int :
        Integrable (fun ω => φ.φ (S.Z 0 ω).1 i * φ.φ (S.Z 0 ω).1 j) μ := by
      let g : γ × ℝ → ℝ := fun z => φ.φ z.1 i * φ.φ z.1 j
      have hg_meas : Measurable g := (hφ_prod i).mul (hφ_prod j)
      have hmap : Integrable g (μ.map (S.Z 0)) := by
        rw [S.law]
        exact hprod_int i j
      simpa [g] using
        (MeasureTheory.integrable_map_measure hg_meas.aestronglyMeasurable
          (S.meas 0).aemeasurable).1 hmap
    have hmean := S.sampleMean_tendsto_inProb
      ((hφ_prod i).mul (hφ_prod j)) hcomp_int
    have hfun :
        (fun n ω => empiricalGram φ S.Z n ω i j) =
          S.sampleMean (fun z : γ × ℝ => φ.φ z.1 i * φ.φ z.1 j) := by
      funext n ω
      simp [empiricalGram, IIDSample.sampleMean, smul_eq_mul, Matrix.smul_apply,
        Matrix.sum_apply, Matrix.vecMulVec_apply, Finset.mul_sum]
    rw [hfun]
    simpa [populationGram] using hmean
  have hInv_entry : ∀ k l,
      Causalean.Stat.IsBigOp (fun n ω => Inv n ω k l) (fun _ => (1 : ℝ)) μ := by
    intro k l
    have hconv : Tendsto_inProb (fun n ω => Inv n ω k l)
        (fun _ => ((populationGram φ P + lam • (1 : Matrix K K ℝ))⁻¹) k l) μ := by
      simpa [Inv] using
        (Tendsto_inProb.matrix_comp_continuousAt
          (Mn := fun n ω => empiricalGram φ S.Z n ω)
          (M₀ := populationGram φ P)
          (g := fun M : Matrix K K ℝ =>
            ((M + lam • (1 : Matrix K K ℝ))⁻¹) k l)
          (by
            have hshift : ContinuousAt
                (fun M : Matrix K K ℝ => M + lam • (1 : Matrix K K ℝ))
                (populationGram φ P) :=
              (continuous_id.add continuous_const).continuousAt
            have hbase : ContinuousAt (fun A : Matrix K K ℝ => (A⁻¹) k l)
                (populationGram φ P + lam • (1 : Matrix K K ℝ)) :=
              continuousAt_matrixInv_entry
                (hdet := (Matrix.PosDef.det_pos hGramPosDef).ne') k l
            simpa [Function.comp_def] using
              (ContinuousAt.comp
                (f := fun M : Matrix K K ℝ => M + lam • (1 : Matrix K K ℝ))
                (g := fun A : Matrix K K ℝ => (A⁻¹) k l)
                hbase hshift))
          hGram_entry)
    exact Tendsto_inProb.isBigOp_one hconv
  have hcoef_coord : ∀ k,
      Causalean.Stat.IsBigOp
        (fun n ω => (sampleRidgeCoef φ S.Z lam n ω - βstar) k) rn μ := by
    intro k
    have hsummand : ∀ l ∈ (Finset.univ : Finset K),
        Causalean.Stat.IsBigOp (fun n ω => Inv n ω k l * D n ω l) rn μ := by
      intro l _
      simpa [rn] using
        (IsBigOp.mul (μ := μ) (rn := fun _ => (1 : ℝ)) (sn := rn)
          (Xn := fun n ω => Inv n ω k l) (Yn := fun n ω => D n ω l)
          (fun _ => zero_le_one) hrn_nonneg (hInv_entry k l) (hDcoord l))
    have hsum : Causalean.Stat.IsBigOp
        (fun n ω => ∑ l ∈ (Finset.univ : Finset K), Inv n ω k l * D n ω l) rn μ :=
      IsBigOp.finset_sum (μ := μ) (s := (Finset.univ : Finset K))
        (X := fun l n ω => Inv n ω k l * D n ω l) hsummand
    refine IsBigOp.of_abs_le
      (Yn := fun n ω => ∑ l ∈ (Finset.univ : Finset K), Inv n ω k l * D n ω l) ?_
      hsum
    intro n ω
    have hsub := sampleRidgeCoef_sub_eq φ S.Z hlam βstar n ω
    have hcoord :
        (sampleRidgeCoef φ S.Z lam n ω - βstar) k =
          ∑ l ∈ (Finset.univ : Finset K), Inv n ω k l * D n ω l := by
      rw [hsub]
      dsimp [Inv, D]
      simp [Matrix.mulVec, dotProduct]
    rw [hcoord]
  have hcoord_abs : ∀ k,
      Causalean.Stat.IsBigOp
        (fun n ω => |(sampleRidgeCoef φ S.Z lam n ω - βstar) k|) rn μ := by
    intro k
    simpa [Causalean.Stat.IsBigOp, abs_abs] using hcoef_coord k
  have hsum_abs : Causalean.Stat.IsBigOp
      (fun n ω => ∑ k, |(sampleRidgeCoef φ S.Z lam n ω - βstar) k|) rn μ := by
    simpa using
      (IsBigOp.finset_sum (μ := μ) (s := (Finset.univ : Finset K))
        (X := fun k n ω => |(sampleRidgeCoef φ S.Z lam n ω - βstar) k|)
        (fun k _ => hcoord_abs k))
  refine IsBigOp.of_abs_le
    (Xn := fun n ω => ‖sampleRidgeCoef φ S.Z lam n ω - βstar‖)
    (Yn := fun n ω => ∑ k, |(sampleRidgeCoef φ S.Z lam n ω - βstar) k|)
    ?_ hsum_abs
  intro n ω
  let v : K → ℝ := sampleRidgeCoef φ S.Z lam n ω - βstar
  have hsum_nonneg : 0 ≤ ∑ k, |v k| :=
    Finset.sum_nonneg fun k _ => abs_nonneg _
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hsum_nonneg]
  change ‖v‖ ≤ ∑ k, |v k|
  refine (pi_norm_le_iff_of_nonneg hsum_nonneg).2 (fun k => ?_)
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun j => |v j|)
    (fun j _ => abs_nonneg _) (Finset.mem_univ k)

/-- A finite linear combination of features has finite L² norm under the
covariate marginal whenever the feature vector has a finite fourth moment under
the joint law. -/
lemma linear_predictor_sub_memLp_of_l4 (φ : FeatureMap γ K) (P : Measure (γ × ℝ))
    [IsProbabilityMeasure P]
    (hφ : ∀ k, Measurable (fun x => φ.φ x k))
    (h4 : Integrable (fun z => (∑ k, (φ.φ z.1 k) ^ 2) ^ 2) P)
    (β βstar : K → ℝ) :
    MemLp (fun x : γ => (∑ k, β k * φ.φ x k) - ∑ k, βstar k * φ.φ x k) 2
      (P.map Prod.fst) := by
  classical
  have hmeasP : ∀ k, Measurable (fun z : γ × ℝ => φ.φ z.1 k) := fun k =>
    (hφ k).comp measurable_fst
  have hsum_meas : Measurable (fun z : γ × ℝ => ∑ k, (φ.φ z.1 k) ^ 2) :=
    Finset.measurable_sum _ (fun k _ => (hmeasP k).pow_const 2)
  have hsumsq_int : Integrable (fun z : γ × ℝ => ∑ k, (φ.φ z.1 k) ^ 2) P := by
    refine Integrable.mono' (g := fun z => 1 + (∑ k, (φ.φ z.1 k) ^ 2) ^ 2)
      ((integrable_const (1 : ℝ)).add h4) hsum_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun z => ?_)
    have hnn : (0 : ℝ) ≤ ∑ k, (φ.φ z.1 k) ^ 2 :=
      Finset.sum_nonneg (fun k _ => sq_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    nlinarith [sq_nonneg ((∑ k, (φ.φ z.1 k) ^ 2) - 1)]
  have hphisq_int : ∀ k, Integrable (fun z : γ × ℝ => (φ.φ z.1 k) ^ 2) P := by
    intro k
    refine Integrable.mono hsumsq_int ((hmeasP k).pow_const 2).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun z => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg
      (Finset.sum_nonneg (fun k _ => sq_nonneg _))]
    exact Finset.single_le_sum (f := fun k => (φ.φ z.1 k) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ k)
  have hmemLp : ∀ k, MemLp (fun z : γ × ℝ => φ.φ z.1 k) 2 P := fun k =>
    (memLp_two_iff_integrable_sq (hmeasP k).aestronglyMeasurable).mpr (hphisq_int k)
  set δ : K → ℝ := β - βstar with hδ
  have hlin_mem : MemLp (fun z : γ × ℝ => ∑ k, δ k * φ.φ z.1 k) 2 P := by
    exact memLp_finset_sum (s := (Finset.univ : Finset K))
      (fun k _ => (hmemLp k).const_mul (δ k))
  have hF_meas : Measurable
      (fun x : γ => (∑ k, β k * φ.φ x k) - ∑ k, βstar k * φ.φ x k) :=
    (Finset.measurable_sum _ (fun k _ => measurable_const.mul (hφ k))).sub
      (Finset.measurable_sum _ (fun k _ => measurable_const.mul (hφ k)))
  have hmap :
      (fun z : γ × ℝ =>
          (∑ k, β k * φ.φ z.1 k) - ∑ k, βstar k * φ.φ z.1 k)
        = fun z : γ × ℝ => ∑ k, δ k * φ.φ z.1 k := by
    funext z
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by rw [hδ]; simp [sub_mul])
  rw [memLp_map_measure_iff hF_meas.aestronglyMeasurable measurable_fst.aemeasurable]
  simpa [Function.comp_def, hmap] using hlin_mem

/-- **Deterministic predictor Lipschitz bound.** The prediction L²(P_X) error is
bounded by a finite constant times the coefficient error:
`‖∑ₖ δₖ φ·ₖ‖_{L²} ≤ C ‖δ‖`. -/
theorem eLpNorm_predictor_sub_le (φ : FeatureMap γ K) (P : Measure (γ × ℝ))
    [IsProbabilityMeasure P]
    (hφ : ∀ k, Measurable (fun x => φ.φ x k))
    (h4 : Integrable (fun z => (∑ k, (φ.φ z.1 k) ^ 2) ^ 2) P) (βstar : K → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : K → ℝ),
      (eLpNorm (fun x => (∑ k, β k * φ.φ x k) - ∑ k, βstar k * φ.φ x k) 2
        (P.map Prod.fst)).toReal ≤ C * ‖β - βstar‖ := by
  classical
  -- Coordinate measurability on the product space.
  have hmeasP : ∀ k, Measurable (fun z : γ × ℝ => φ.φ z.1 k) := fun k =>
    (hφ k).comp measurable_fst
  -- Features are square-integrable under `P` (from the L⁴ feature moment `h4`).
  have hsum_meas : Measurable (fun z : γ × ℝ => ∑ k, (φ.φ z.1 k) ^ 2) :=
    Finset.measurable_sum _ (fun k _ => (hmeasP k).pow_const 2)
  have hsumsq_int : Integrable (fun z : γ × ℝ => ∑ k, (φ.φ z.1 k) ^ 2) P := by
    refine Integrable.mono' (g := fun z => 1 + (∑ k, (φ.φ z.1 k) ^ 2) ^ 2)
      ((integrable_const (1 : ℝ)).add h4) hsum_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun z => ?_)
    have hnn : (0 : ℝ) ≤ ∑ k, (φ.φ z.1 k) ^ 2 :=
      Finset.sum_nonneg (fun k _ => sq_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    nlinarith [sq_nonneg ((∑ k, (φ.φ z.1 k) ^ 2) - 1)]
  have hphisq_int : ∀ k, Integrable (fun z : γ × ℝ => (φ.φ z.1 k) ^ 2) P := by
    intro k
    refine Integrable.mono hsumsq_int ((hmeasP k).pow_const 2).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun z => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg
      (Finset.sum_nonneg (fun k _ => sq_nonneg _))]
    exact Finset.single_le_sum (f := fun k => (φ.φ z.1 k) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ k)
  have hmemLp : ∀ k, MemLp (fun z : γ × ℝ => φ.φ z.1 k) 2 P := fun k =>
    (memLp_two_iff_integrable_sq (hmeasP k).aestronglyMeasurable).mpr (hphisq_int k)
  have hCk_ne_top : ∀ k, eLpNorm (fun z : γ × ℝ => φ.φ z.1 k) 2 P ≠ ⊤ :=
    fun k => (hmemLp k).2.ne
  refine ⟨∑ k, (eLpNorm (fun z : γ × ℝ => φ.φ z.1 k) 2 P).toReal, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun k _ => ENNReal.toReal_nonneg)
  intro β
  set δ : K → ℝ := β - βstar with hδ
  -- Push the L²(P_X) norm back to `P` via the coordinate projection.
  have hF_meas : Measurable
      (fun x : γ => (∑ k, β k * φ.φ x k) - ∑ k, βstar k * φ.φ x k) :=
    (Finset.measurable_sum _ (fun k _ => measurable_const.mul (hφ k))).sub
      (Finset.measurable_sum _ (fun k _ => measurable_const.mul (hφ k)))
  have hmap :
      eLpNorm (fun x => (∑ k, β k * φ.φ x k) - ∑ k, βstar k * φ.φ x k) 2
          (P.map Prod.fst)
        = eLpNorm (fun z : γ × ℝ => ∑ k, δ k * φ.φ z.1 k) 2 P := by
    rw [eLpNorm_map_measure hF_meas.aestronglyMeasurable measurable_fst.aemeasurable]
    congr 1
    funext z
    simp only [Function.comp_apply]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by rw [hδ]; simp [sub_mul])
  -- Triangle inequality + scalar pull-out, coordinatewise.
  have hsum_le :
      eLpNorm (fun z : γ × ℝ => ∑ k, δ k * φ.φ z.1 k) 2 P
        ≤ ∑ k, ‖δ k‖ₑ * eLpNorm (fun z : γ × ℝ => φ.φ z.1 k) 2 P := by
    have hbound :
        eLpNorm (fun z : γ × ℝ => ∑ k, δ k * φ.φ z.1 k) 2 P
          ≤ ∑ k, eLpNorm (fun z : γ × ℝ => δ k * φ.φ z.1 k) 2 P := by
      have hfun : (fun z : γ × ℝ => ∑ k, δ k * φ.φ z.1 k)
          = ∑ k, (fun z : γ × ℝ => δ k * φ.φ z.1 k) := by
        funext z; rw [Finset.sum_apply]
      rw [hfun]
      exact eLpNorm_sum_le (μ := P) (p := 2)
        (f := fun k => fun z : γ × ℝ => δ k * φ.φ z.1 k)
        (s := (Finset.univ : Finset K))
        (fun k _ => ((hmeasP k).const_mul (δ k)).aestronglyMeasurable) (by norm_num)
    refine hbound.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show (fun z : γ × ℝ => δ k * φ.φ z.1 k)
        = δ k • (fun z : γ × ℝ => φ.φ z.1 k) from rfl,
      eLpNorm_const_smul]
  -- Replace each coordinate factor by the sup norm `‖δ‖`.
  have hcoord_le : ∀ k,
      ‖δ k‖ₑ * eLpNorm (fun z : γ × ℝ => φ.φ z.1 k) 2 P
        ≤ ‖δ‖ₑ * eLpNorm (fun z : γ × ℝ => φ.φ z.1 k) 2 P := by
    intro k
    have hk : ‖δ k‖ₑ ≤ ‖δ‖ₑ := by
      have : ‖δ k‖ ≤ ‖δ‖ := norm_le_pi_norm δ k
      simpa [enorm_eq_nnnorm] using ENNReal.coe_le_coe.mpr (by exact_mod_cast this)
    gcongr
  have hfinal_le :
      eLpNorm (fun x => (∑ k, β k * φ.φ x k) - ∑ k, βstar k * φ.φ x k) 2
          (P.map Prod.fst)
        ≤ ‖δ‖ₑ * ∑ k, eLpNorm (fun z : γ × ℝ => φ.φ z.1 k) 2 P := by
    rw [hmap, Finset.mul_sum]
    exact hsum_le.trans (Finset.sum_le_sum (fun k _ => hcoord_le k))
  have hrhs_ne_top : ‖δ‖ₑ * ∑ k, eLpNorm (fun z : γ × ℝ => φ.φ z.1 k) 2 P ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact enorm_ne_top
    · exact (ENNReal.sum_ne_top).mpr (fun k _ => hCk_ne_top k)
  calc
    (eLpNorm (fun x => (∑ k, β k * φ.φ x k) - ∑ k, βstar k * φ.φ x k) 2
        (P.map Prod.fst)).toReal
        ≤ (‖δ‖ₑ * ∑ k, eLpNorm (fun z : γ × ℝ => φ.φ z.1 k) 2 P).toReal :=
          ENNReal.toReal_mono hrhs_ne_top hfinal_le
    _ = ‖δ‖ * ∑ k, (eLpNorm (fun z : γ × ℝ => φ.φ z.1 k) 2 P).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_sum (fun k _ => hCk_ne_top k)]
          congr 1
    _ = (∑ k, (eLpNorm (fun z : γ × ℝ => φ.φ z.1 k) 2 P).toReal) * ‖β - βstar‖ := by
          rw [hδ]; ring

/-- **Ridge root-n estimation rate.** Under the population ridge normal equation,
a positive regularization parameter, and the required feature and score moment
conditions, the sample ridge predictor attains the root-n L²-rate toward the
population ridge minimizer. The regularized population Gram is positive definite
because the population feature Gram is positive semidefinite and `λI` is positive
definite when `λ > 0`. -/
theorem ridge_achievesL2Rate (φ : FeatureMap γ K) (P : Measure (γ × ℝ))
    [IsProbabilityMeasure P] (S : IIDSample Ω (γ × ℝ) μ P) [IsProbabilityMeasure μ]
    {lam : ℝ} (hlam : 0 < lam) (βstar : K → ℝ)
    (hpop : IsPopulationRidge P φ lam βstar)
    (hφ : ∀ k, Measurable (fun x => φ.φ x k))
    (h4 : Integrable (fun z => (∑ k, (φ.φ z.1 k) ^ 2) ^ 2) P)
    (hscore : ∀ k, MemLp
      (fun z => (z.2 - ∑ j, βstar j * φ.φ z.1 j) * φ.φ z.1 k) 2 P) :
    AchievesL2Rate (sampleRidgePredictor φ S.Z lam)
      (fun x => ∑ k, βstar k * φ.φ x k) P (fun n => (Real.sqrt (n : ℝ))⁻¹) μ := by
  classical
  rcases eLpNorm_predictor_sub_le φ P hφ h4 βstar with ⟨C, hC_nonneg, hC_bound⟩
  have hGramPosDef : (populationGram φ P + lam • (1 : Matrix K K ℝ)).PosDef :=
    Matrix.PosDef.posSemidef_add (populationGram_posSemidef φ P hφ h4)
      (Matrix.PosDef.smul Matrix.PosDef.one hlam)
  have hcoef := sampleRidgeCoef_isBigOp φ P S hlam βstar hpop hφ h4 hscore hGramPosDef
  unfold AchievesL2Rate
  constructor
  · intro n ω
    simpa [sampleRidgePredictor] using
      (linear_predictor_sub_memLp_of_l4 φ P hφ h4
        (sampleRidgeCoef φ S.Z lam n ω) βstar).eLpNorm_ne_top
  intro ε hε
  rcases hcoef ε hε with ⟨M0, hM0⟩
  let M : ℝ := max M0 0
  have hM0_le_M : M0 ≤ M := le_max_left M0 0
  have hM_nonneg : 0 ≤ M := le_max_right M0 0
  refine ⟨C * M, ?_⟩
  have hlim_M :
      Filter.limsup
          (fun n : ℕ =>
            μ {ω | M * (Real.sqrt (n : ℝ))⁻¹ <
              |‖sampleRidgeCoef φ S.Z lam n ω - βstar‖|}) Filter.atTop
        ≤ ENNReal.ofReal ε := by
    refine le_trans (Filter.limsup_le_limsup (Filter.Eventually.of_forall ?_)) hM0
    intro n
    apply measure_mono
    intro ω hω
    have hr_nonneg : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ :=
      inv_nonneg.mpr (Real.sqrt_nonneg _)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hM0_le_M hr_nonneg) hω
  refine le_trans (Filter.limsup_le_limsup (Filter.Eventually.of_forall ?_)) hlim_M
  intro n
  apply measure_mono
  intro ω hω
  by_cases hC_zero : C = 0
  · have hpred_le_zero :
        (eLpNorm
          (fun x =>
            sampleRidgePredictor φ S.Z lam n ω x -
              ∑ k, βstar k * φ.φ x k) 2 (P.map Prod.fst)).toReal ≤ 0 := by
      simpa [sampleRidgePredictor, hC_zero] using
        hC_bound (sampleRidgeCoef φ S.Z lam n ω)
    have hpred_nonneg :
        0 ≤ (eLpNorm
          (fun x =>
            sampleRidgePredictor φ S.Z lam n ω x -
              ∑ k, βstar k * φ.φ x k) 2 (P.map Prod.fst)).toReal :=
      ENNReal.toReal_nonneg
    have hpred_abs :
        |(eLpNorm
          (fun x =>
            sampleRidgePredictor φ S.Z lam n ω x -
              ∑ k, βstar k * φ.φ x k) 2 (P.map Prod.fst)).toReal| = 0 := by
      rw [abs_of_nonneg hpred_nonneg]
      exact le_antisymm hpred_le_zero hpred_nonneg
    rw [hC_zero, zero_mul, zero_mul] at hω
    have hpred_abs' :
        |(fun n ω =>
            (eLpNorm
              (fun x =>
                sampleRidgePredictor φ S.Z lam n ω x -
                  (fun x => ∑ k, βstar k * φ.φ x k) x) 2
              (P.map Prod.fst)).toReal) n ω| = 0 := by
      simpa using hpred_abs
    exfalso
    have hωlt :
        0 <
          |(fun n ω =>
              (eLpNorm
                (fun x =>
                  sampleRidgePredictor φ S.Z lam n ω x -
                    (fun x => ∑ k, βstar k * φ.φ x k) x) 2
                (P.map Prod.fst)).toReal) n ω| := by
      simpa using hω
    rw [hpred_abs'] at hωlt
    exact (lt_irrefl (0 : ℝ)) hωlt
  · have hC_pos : 0 < C := lt_of_le_of_ne hC_nonneg (Ne.symm hC_zero)
    have hpred_bound :
        (eLpNorm
          (fun x =>
            sampleRidgePredictor φ S.Z lam n ω x -
              ∑ k, βstar k * φ.φ x k) 2 (P.map Prod.fst)).toReal
          ≤ C * ‖sampleRidgeCoef φ S.Z lam n ω - βstar‖ := by
      simpa [sampleRidgePredictor] using
        hC_bound (sampleRidgeCoef φ S.Z lam n ω)
    have hpred_nonneg :
        0 ≤ (eLpNorm
          (fun x =>
            sampleRidgePredictor φ S.Z lam n ω x -
              ∑ k, βstar k * φ.φ x k) 2 (P.map Prod.fst)).toReal :=
      ENNReal.toReal_nonneg
    have hnorm_nonneg : 0 ≤ ‖sampleRidgeCoef φ S.Z lam n ω - βstar‖ := norm_nonneg _
    have hr_nonneg : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ :=
      inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hlt :
        C * (M * (Real.sqrt (n : ℝ))⁻¹) <
          C * ‖sampleRidgeCoef φ S.Z lam n ω - βstar‖ := by
      calc
        C * (M * (Real.sqrt (n : ℝ))⁻¹)
            = (C * M) * (Real.sqrt (n : ℝ))⁻¹ := by ring
        _ < |(eLpNorm
              (fun x =>
                sampleRidgePredictor φ S.Z lam n ω x -
                  ∑ k, βstar k * φ.φ x k) 2 (P.map Prod.fst)).toReal| := hω
        _ = (eLpNorm
              (fun x =>
                sampleRidgePredictor φ S.Z lam n ω x -
                  ∑ k, βstar k * φ.φ x k) 2 (P.map Prod.fst)).toReal := by
              rw [abs_of_nonneg hpred_nonneg]
        _ ≤ C * ‖sampleRidgeCoef φ S.Z lam n ω - βstar‖ := hpred_bound
    have hlt' : M * (Real.sqrt (n : ℝ))⁻¹ <
        ‖sampleRidgeCoef φ S.Z lam n ω - βstar‖ := by
      nlinarith [hC_pos, hlt]
    simpa [abs_of_nonneg hnorm_nonneg] using hlt'

end Causalean.ML
