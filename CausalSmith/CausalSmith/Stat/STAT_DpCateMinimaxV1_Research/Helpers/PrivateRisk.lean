/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Risk of the private local-polynomial release

Auxiliary deterministic and measure-theoretic estimates for the uniform absolute-risk
bound of the projected, Laplace-privatized local-polynomial CATE mechanism.
-/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PrivateMechanism
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PopulationBias
import Causalean.Mathlib.Probability.IidMeanVariance
import Causalean.Stat.Privacy.LaplaceMechanism
import Causalean.Mathlib.Analysis.ConvexProjection

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory Set Matrix
open scoped BigOperators ENNReal
open Causalean.Mathlib.Analysis
open Causalean.Mathlib.Probability
open Causalean.Stat.Privacy

/-! ## Elementary deterministic estimates -/

/-- Clipping to `[-2,2]` cannot increase distance from a point of that interval. -/
private theorem abs_clip_two_sub_le {z tau : ℝ} (htau : |tau| ≤ 2) :
    |max (-2) (min 2 z) - tau| ≤ |z - tau| := by
  have hlo : (-2 : ℝ) ≤ tau := by linarith [neg_le_abs tau]
  have hhi : tau ≤ 2 := le_trans (le_abs_self tau) htau
  by_cases hzlo : z < -2
  · have hmin : min 2 z = z := min_eq_right (le_trans (le_of_lt hzlo) (by norm_num))
    have hmax : max (-2) z = -2 := max_eq_left (le_of_lt hzlo)
    rw [hmin, hmax, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · have hzlo' : (-2 : ℝ) ≤ z := le_of_not_gt hzlo
    by_cases hzhi : z ≤ 2
    · rw [min_eq_right hzhi, max_eq_right hzlo']
    · have hzhi' : 2 < z := lt_of_not_ge hzhi
      rw [min_eq_left (le_of_lt hzhi'), max_eq_right (by norm_num),
        abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith

/-- The algebraic inverse-perturbation identity used to compare two normal-equation solves. -/
private theorem matrix_inv_sub_inv {p : ℕ}
    (U V : Matrix (Fin p) (Fin p) ℝ)
    (hUleft : U⁻¹ * U = 1) (hVright : V * V⁻¹ = 1) :
    U⁻¹ - V⁻¹ = U⁻¹ * (V - U) * V⁻¹ := by
  calc
    U⁻¹ - V⁻¹ = U⁻¹ * V * V⁻¹ - U⁻¹ * U * V⁻¹ := by
      simp [mul_assoc, hUleft, hVright]
    _ = U⁻¹ * (V - U) * V⁻¹ := by noncomm_ring

/-- A coordinate is bounded in absolute value by the Euclidean norm of a finite vector. -/
private theorem abs_apply_le_euclidean {p : ℕ} (v : Fin p → ℝ) (i : Fin p) :
    |v i| ≤ Real.sqrt (∑ k, (v k) ^ 2) := by
  have hi : (v i) ^ 2 ≤ ∑ k, (v k) ^ 2 :=
    Finset.single_le_sum (fun k _ ↦ sq_nonneg (v k)) (Finset.mem_univ i)
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hi

/-- Pointwise, the final clipping in `releaseOf` can be discarded when bounding error
toward an estimand in `[-2,2]`. -/
theorem releaseOf_error_le_unclipped {d n : ℕ} (m : ℕ)
    (h cstar Cstar : ℝ) (x0 : Fin d → ℝ) (s : Fin n → CateObs d)
    (w : Fin (Nq d m) → ℝ) (tau : ℝ) (htau : |tau| ≤ 2) :
    |releaseOf m h cstar Cstar x0 s w - tau| ≤
      |((((loewnerProj (pDim d m) cstar Cstar
          (Matrix.of (fun k l : Fin (pDim d m) ↦
            empGram m h x0 1 s k l + w (gramIdxOf d m 1 k l))))⁻¹.mulVec
        (fun k : Fin (pDim d m) ↦ empMom m h x0 1 s k + w (momIdxOf d m 1 k)))
          (icptOf d m)) -
        (((loewnerProj (pDim d m) cstar Cstar
          (Matrix.of (fun k l : Fin (pDim d m) ↦
            empGram m h x0 0 s k l + w (gramIdxOf d m 0 k l))))⁻¹.mulVec
        (fun k : Fin (pDim d m) ↦ empMom m h x0 0 s k + w (momIdxOf d m 0 k)))
          (icptOf d m))) - tau| := by
  unfold releaseOf
  exact abs_clip_two_sub_le htau

/-- The release integral is the corresponding integral over the product Laplace noise law. -/
theorem integral_mechOf_eq_integral_laplace {d n : ℕ} (m : ℕ)
    (h cstar Cstar epsN : ℝ) (x0 : Fin d → ℝ)
    (s : Fin n → CateObs d) (tau : ℝ) :
    ∫ z, |z - tau| ∂(mechOf m h cstar Cstar epsN x0 s) =
      ∫ w, |releaseOf m h cstar Cstar x0 s w - tau|
        ∂(Measure.pi fun _ : Fin (Nq d m) ↦
          laplaceMeasure (((Cs d m) / ((n : ℝ) * h ^ (d : ℝ))) / epsN)) := by
  rw [mechOf, laplaceVecKernel_eq_pi_laplaceMeasure]
  exact integral_map (measurable_releaseOf_noise m h cstar Cstar x0 s).aemeasurable
    (continuous_abs.measurable.comp (measurable_id.sub measurable_const)).aestronglyMeasurable

/-- The coordinate formula for the Euclidean norm inherits the triangle inequality. -/
private theorem euclidean_add_le {p : ℕ} (u v : Fin p → ℝ) :
    Real.sqrt (∑ k, (u k + v k) ^ 2) ≤
      Real.sqrt (∑ k, (u k) ^ 2) + Real.sqrt (∑ k, (v k) ^ 2) := by
  let u' : EuclideanSpace ℝ (Fin p) :=
    (EuclideanSpace.equiv (Fin p) ℝ).symm u
  let v' : EuclideanSpace ℝ (Fin p) :=
    (EuclideanSpace.equiv (Fin p) ℝ).symm v
  simpa [u', v', EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs] using
    (norm_add_le u' v')

/-- Pulling back nonnegative squared coordinates along an injection cannot increase their sum. -/
private theorem sum_sq_comp_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (f : ι → κ) (hf : Function.Injective f)
    (w : κ → ℝ) :
    ∑ i, (w (f i)) ^ 2 ≤ ∑ j, (w j) ^ 2 := by
  calc
    ∑ i, (w (f i)) ^ 2 = ∑ j ∈ Finset.univ.image f, (w j) ^ 2 := by
      rw [Finset.sum_image]
      intro x _ y _ hxy
      exact hf hxy
    _ ≤ ∑ j, (w j) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ ↦ sq_nonneg (w j))

/-- Noise coordinates belonging to one arm's moment vector are dominated by the full noise norm. -/
private theorem mom_noise_norm_le {d m : ℕ} (a : Fin 2) (w : Fin (Nq d m) → ℝ) :
    Real.sqrt (∑ k, (w (momIdxOf d m a k)) ^ 2) ≤
      Real.sqrt (∑ i, (w i) ^ 2) := by
  apply Real.sqrt_le_sqrt
  apply sum_sq_comp_le
  intro k l hkl
  have h : (a, k) = (a, l) := momIdxOf_injective d m hkl
  exact congrArg Prod.snd h

/-- Noise coordinates belonging to one arm's Gram matrix are dominated by the full noise norm. -/
private theorem gram_noise_norm_le {d m : ℕ} (a : Fin 2) (w : Fin (Nq d m) → ℝ) :
    Real.sqrt (∑ k, ∑ l, (w (gramIdxOf d m a k l)) ^ 2) ≤
      Real.sqrt (∑ i, (w i) ^ 2) := by
  apply Real.sqrt_le_sqrt
  simpa only [Fintype.sum_prod_type] using
    (sum_sq_comp_le (fun q : Fin (pDim d m) × Fin (pDim d m) ↦
        gramIdxOf d m a q.1 q.2) (by
      intro q r hqr
      have h : (a, q.1, q.2) = (a, r.1, r.2) := gramIdxOf_injective d m hqr
      exact congrArg Prod.snd h) w)

set_option maxHeartbeats 1000000 in
/-- Deterministic pointwise error bound for the projected noisy local-polynomial release. -/
theorem releaseOf_error_le {d n m : ℕ} {h cstar Cstar : ℝ} {x0 : Fin d → ℝ}
    {P : CateLaw d} {Bg Cbias beta : ℝ}
    (hcstar : 0 < cstar) (hcC : cstar ≤ Cstar)
    (htau : |P.mu1 x0 - P.mu0 x0| ≤ 2)
    (hloew : ∀ a : Fin 2, popGram P h x0 (expoOf d m) (unifKernel d) a
      ∈ loewnerSet (pDim d m) cstar Cstar)
    (hBg : ∀ a : Fin 2,
      Real.sqrt (∑ k, (popMom P h x0 (expoOf d m) (unifKernel d) a k) ^ 2) ≤ Bg)
    (hBg0 : 0 ≤ Bg)
    (hbias : ∀ a : Fin 2,
      |((popGram P h x0 (expoOf d m) (unifKernel d) a)⁻¹.mulVec
          (popMom P h x0 (expoOf d m) (unifKernel d) a)) (icptOf d m) -
        armMu P a x0| ≤ Cbias * h ^ beta)
    (s : Fin n → CateObs d) (w : Fin (Nq d m) → ℝ) :
    |releaseOf m h cstar Cstar x0 s w - (P.mu1 x0 - P.mu0 x0)| ≤
      ∑ a : Fin 2,
        ((1 / cstar) *
            (Real.sqrt (∑ k, (empMom m h x0 a s k -
                popMom P h x0 (expoOf d m) (unifKernel d) a k) ^ 2) +
              Real.sqrt (∑ i : Fin (Nq d m), (w i) ^ 2)) +
          (Bg / cstar ^ 2) *
            (frobDist (empGram m h x0 a s)
                (popGram P h x0 (expoOf d m) (unifKernel d) a) +
              Real.sqrt (∑ i : Fin (Nq d m), (w i) ^ 2)) +
          Cbias * h ^ beta) := by
  let Gbar (a : Fin 2) := popGram P h x0 (expoOf d m) (unifKernel d) a
  let gbar (a : Fin 2) := popMom P h x0 (expoOf d m) (unifKernel d) a
  let Ghat (a : Fin 2) := empGram m h x0 a s
  let ghat (a : Fin 2) := empMom m h x0 a s
  let noisyG (a : Fin 2) : Matrix (Fin (pDim d m)) (Fin (pDim d m)) ℝ :=
    Matrix.of fun k l ↦ Ghat a k l + w (gramIdxOf d m a k l)
  let U (a : Fin 2) := loewnerProj (pDim d m) cstar Cstar (noisyG a)
  let noisyg (a : Fin 2) : Fin (pDim d m) → ℝ :=
    fun k ↦ ghat a k + w (momIdxOf d m a k)
  let thetaHat (a : Fin 2) := (U a)⁻¹.mulVec (noisyg a)
  let thetaBar (a : Fin 2) := (Gbar a)⁻¹.mulVec (gbar a)
  let wn := Real.sqrt (∑ i : Fin (Nq d m), (w i) ^ 2)
  have hUmem (a : Fin 2) : U a ∈ loewnerSet (pDim d m) cstar Cstar := by
    exact loewnerProj_mem hcstar hcC (noisyG a)
  have hGmem (a : Fin 2) : Gbar a ∈ loewnerSet (pDim d m) cstar Cstar := hloew a
  have hUdet (a : Fin 2) : IsUnit (U a).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (loewnerSet_posDef hcstar hcC (hUmem a)).isUnit
  have hGdet (a : Fin 2) : IsUnit (Gbar a).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (loewnerSet_posDef hcstar hcC (hGmem a)).isUnit
  have hmomNoise (a : Fin 2) :
      Real.sqrt (∑ k, (noisyg a k - gbar a k) ^ 2) ≤
        Real.sqrt (∑ k, (ghat a k - gbar a k) ^ 2) + wn := by
    have htri := euclidean_add_le
      (fun k ↦ ghat a k - gbar a k) (fun k ↦ w (momIdxOf d m a k))
    have hn := mom_noise_norm_le a w
    dsimp only [noisyg, wn]
    calc
      Real.sqrt (∑ k, (ghat a k + w (momIdxOf d m a k) - gbar a k) ^ 2) =
          Real.sqrt (∑ k, ((ghat a k - gbar a k) + w (momIdxOf d m a k)) ^ 2) := by
            congr 1
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ ≤ Real.sqrt (∑ k, (ghat a k - gbar a k) ^ 2) +
          Real.sqrt (∑ k, (w (momIdxOf d m a k)) ^ 2) := htri
      _ ≤ Real.sqrt (∑ k, (ghat a k - gbar a k) ^ 2) +
          Real.sqrt (∑ i, (w i) ^ 2) := add_le_add_right hn _
  have hgramNoise (a : Fin 2) : frobDist (noisyG a) (Ghat a) ≤ wn := by
    dsimp only [noisyG, wn]
    simpa [frobDist] using gram_noise_norm_le a w
  have hproj (a : Fin 2) :
      frobDist (Gbar a) (U a) ≤ frobDist (Ghat a) (Gbar a) + wn := by
    calc
      frobDist (Gbar a) (U a) = frobDist (U a) (Gbar a) := frobDist_comm _ _
      _ ≤ frobDist (noisyG a) (Gbar a) :=
        loewnerProj_frobDist_le hcstar hcC (noisyG a) (Gbar a) (hGmem a)
      _ ≤ frobDist (noisyG a) (Ghat a) + frobDist (Ghat a) (Gbar a) :=
        frobDist_triangle _ _ _
      _ ≤ frobDist (Ghat a) (Gbar a) + wn := by
        linarith [hgramNoise a]
  have hthetaEq (a : Fin 2) :
      thetaHat a - thetaBar a =
        (U a)⁻¹.mulVec (noisyg a - gbar a) +
          (U a)⁻¹.mulVec ((Gbar a - U a).mulVec (thetaBar a)) := by
    have hinv := matrix_inv_sub_inv (U a) (Gbar a)
      (Matrix.nonsing_inv_mul _ (hUdet a)) (Matrix.mul_nonsing_inv _ (hGdet a))
    rw [show thetaHat a - thetaBar a =
        ((U a)⁻¹ - (Gbar a)⁻¹).mulVec (gbar a) +
          (U a)⁻¹.mulVec (noisyg a - gbar a) by
      simp only [thetaHat, thetaBar]
      rw [Matrix.sub_mulVec, Matrix.mulVec_sub]
      abel]
    rw [hinv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    abel
  have hthetaNorm (a : Fin 2) :
      Real.sqrt (∑ k, (thetaHat a k - thetaBar a k) ^ 2) ≤
        (1 / cstar) *
            (Real.sqrt (∑ k, (ghat a k - gbar a k) ^ 2) + wn) +
          (Bg / cstar ^ 2) * (frobDist (Ghat a) (Gbar a) + wn) := by
    have htri := euclidean_add_le
      ((U a)⁻¹.mulVec (noisyg a - gbar a))
      ((U a)⁻¹.mulVec ((Gbar a - U a).mulVec (thetaBar a)))
    have htri' : Real.sqrt (∑ k, (thetaHat a k - thetaBar a k) ^ 2) ≤
        Real.sqrt (∑ k, ((U a)⁻¹.mulVec (noisyg a - gbar a) k) ^ 2) +
          Real.sqrt (∑ k,
            ((U a)⁻¹.mulVec ((Gbar a - U a).mulVec (thetaBar a)) k) ^ 2) := by
      change Real.sqrt (∑ k, ((thetaHat a - thetaBar a) k) ^ 2) ≤ _
      rw [hthetaEq a]
      exact htri
    have hfirst := loewnerSet_inv_mulVec_norm_le hcstar hcC (hUmem a)
      (noisyg a - gbar a)
    have houter := loewnerSet_inv_mulVec_norm_le hcstar hcC (hUmem a)
      ((Gbar a - U a).mulVec (thetaBar a))
    have hinner := mulVec_sub_norm_le (Gbar a) (U a) (thetaBar a)
    have hbar := loewnerSet_inv_mulVec_norm_le hcstar hcC (hGmem a) (gbar a)
    have hbarBg : Real.sqrt (∑ k, (thetaBar a k) ^ 2) ≤ Bg / cstar := by
      exact hbar.trans (div_le_div_of_nonneg_right (hBg a) (le_of_lt hcstar))
    have hinnerBg : Real.sqrt (∑ k, ((Gbar a - U a).mulVec (thetaBar a) k) ^ 2) ≤
        frobDist (Gbar a) (U a) * (Bg / cstar) :=
      hinner.trans (mul_le_mul_of_nonneg_left hbarBg (frobDist_nonneg _ _))
    have hfirst' : Real.sqrt (∑ k, ((U a)⁻¹.mulVec (noisyg a - gbar a) k) ^ 2) ≤
        (Real.sqrt (∑ k, (ghat a k - gbar a k) ^ 2) + wn) / cstar :=
      hfirst.trans (div_le_div_of_nonneg_right (hmomNoise a) (le_of_lt hcstar))
    have houter' : Real.sqrt (∑ k,
        ((U a)⁻¹.mulVec ((Gbar a - U a).mulVec (thetaBar a)) k) ^ 2) ≤
        (frobDist (Gbar a) (U a) * (Bg / cstar)) / cstar :=
      houter.trans (div_le_div_of_nonneg_right hinnerBg (le_of_lt hcstar))
    calc
      _ ≤ Real.sqrt (∑ k, ((U a)⁻¹.mulVec (noisyg a - gbar a) k) ^ 2) +
          Real.sqrt (∑ k,
            ((U a)⁻¹.mulVec ((Gbar a - U a).mulVec (thetaBar a)) k) ^ 2) := htri'
      _ ≤ (Real.sqrt (∑ k, (ghat a k - gbar a k) ^ 2) + wn) / cstar +
          (frobDist (Gbar a) (U a) * (Bg / cstar)) / cstar :=
        add_le_add hfirst' houter'
      _ ≤ (Real.sqrt (∑ k, (ghat a k - gbar a k) ^ 2) + wn) / cstar +
          ((frobDist (Ghat a) (Gbar a) + wn) * (Bg / cstar)) / cstar := by
        gcongr
        exact hproj a
      _ = _ := by
        field_simp
  have harm (a : Fin 2) :
      |thetaHat a (icptOf d m) - armMu P a x0| ≤
        (1 / cstar) *
            (Real.sqrt (∑ k, (ghat a k - gbar a k) ^ 2) + wn) +
          (Bg / cstar ^ 2) * (frobDist (Ghat a) (Gbar a) + wn) +
          Cbias * h ^ beta := by
    calc
      _ ≤ |thetaHat a (icptOf d m) - thetaBar a (icptOf d m)| +
          |thetaBar a (icptOf d m) - armMu P a x0| := abs_sub_le _ _ _
      _ ≤ Real.sqrt (∑ k, (thetaHat a k - thetaBar a k) ^ 2) +
          Cbias * h ^ beta := add_le_add
            (abs_apply_le_euclidean (thetaHat a - thetaBar a) (icptOf d m)) (hbias a)
      _ ≤ _ := add_le_add (hthetaNorm a) (le_refl _)
  apply (releaseOf_error_le_unclipped m h cstar Cstar x0 s w
    (P.mu1 x0 - P.mu0 x0) htau).trans
  have hsplit :
      |thetaHat 1 (icptOf d m) - thetaHat 0 (icptOf d m) -
          (P.mu1 x0 - P.mu0 x0)| ≤
        |thetaHat 1 (icptOf d m) - armMu P 1 x0| +
          |thetaHat 0 (icptOf d m) - armMu P 0 x0| := by
    calc
      _ = |(thetaHat 1 (icptOf d m) - P.mu1 x0) -
          (thetaHat 0 (icptOf d m) - P.mu0 x0)| := by congr 1; ring
      _ ≤ |thetaHat 1 (icptOf d m) - P.mu1 x0| +
          |thetaHat 0 (icptOf d m) - P.mu0 x0| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (thetaHat 1 (icptOf d m) - P.mu1 x0) 0
            (thetaHat 0 (icptOf d m) - P.mu0 x0))
      _ = _ := by simp [armMu]
  change |thetaHat 1 (icptOf d m) - thetaHat 0 (icptOf d m) -
      (P.mu1 x0 - P.mu0 x0)| ≤ _
  rw [Fin.sum_univ_two]
  exact hsplit.trans (add_le_add (harm 1) (harm 0) |>.trans_eq (by ring))

end CausalSmith.Stat.DpCateMinimax
