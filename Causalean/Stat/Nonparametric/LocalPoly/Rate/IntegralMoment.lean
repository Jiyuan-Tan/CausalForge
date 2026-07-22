/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.Basic

/-!
# Positive-definiteness of the integral (population) moment matrix

Positive-definiteness criteria for integral Gram matrices of centered monomials, supplying
invertibility of local-polynomial population moment matrices.

The population analogue of the empirical design moment matrix is the **integral Gram matrix** of
the centered monomials `φ_j(a) = (a − t)^j` against a positive measure `ν` (for the
local-polynomial fit, `ν` is the kernel-weighted design law `K((·−t)/h)·μ_A`):

`S_{jk} = ∫ (a − t)^j · (a − t)^k dν`.

Its quadratic form is `vᵀ S v = ∫ (∑ⱼ vⱼ (a−t)^j)² dν ≥ 0`, so with a finite second moment it is
positive semidefinite, and positive definite — hence **invertible** — exactly when the design law
`ν` is non-degenerate (no nonzero degree-`p` polynomial of the centered argument vanishes `ν`-almost
everywhere; e.g. `ν` is not supported on `≤ p` points). This is the integral transport of
`designMatrix_posDef` and discharges the `IsUnit S.det` hypothesis for the bandwidth-free shape
matrix `T` feeding the `Θ(Nh)` leverage rate.
-/

namespace Causalean.Stat.Nonparametric

open MeasureTheory
open scoped BigOperators
open Matrix

/-- The integral (population) moment matrix `S_{jk} = ∫ (a − t)^j (a − t)^k dν` of the centered
monomials against a measure `ν`. -/
noncomputable def intMomentMatrix (p : ℕ) (ν : Measure ℝ) (t : ℝ) :
    Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ :=
  Matrix.of (fun j k => ∫ a, (a - t) ^ (j : ℕ) * (a - t) ^ (k : ℕ) ∂ν)

/-- **Gram quadratic form of the integral moment matrix.** `vᵀ S v = ∫ (∑ⱼ vⱼ (a−t)^j)² dν` —
the population moment matrix is the integral Gram matrix of the centered monomial features. -/
theorem intMomentMatrix_quadForm {p : ℕ} {ν : Measure ℝ} {t : ℝ}
    (hint : ∀ j k : Fin (p + 1),
      Integrable (fun a => (a - t) ^ (j : ℕ) * (a - t) ^ (k : ℕ)) ν)
    (v : Fin (p + 1) → ℝ) :
    v ⬝ᵥ (intMomentMatrix p ν t *ᵥ v)
      = ∫ a, (∑ j, v j * (a - t) ^ (j : ℕ)) ^ 2 ∂ν := by
  simp only [dotProduct, Matrix.mulVec, intMomentMatrix, Matrix.of_apply]
  calc
    ∑ j : Fin (p + 1), v j * ∑ k : Fin (p + 1),
          (∫ a, (a - t) ^ (j : ℕ) * (a - t) ^ (k : ℕ) ∂ν) * v k
        = ∑ j : Fin (p + 1), ∑ k : Fin (p + 1),
            (v j * v k) * ∫ a, (a - t) ^ (j : ℕ) * (a - t) ^ (k : ℕ) ∂ν := by
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro k _
          ring
    _ = ∑ j : Fin (p + 1), ∑ k : Fin (p + 1),
            ∫ a, (v j * v k) * ((a - t) ^ (j : ℕ) * (a - t) ^ (k : ℕ)) ∂ν := by
          refine Finset.sum_congr rfl ?_
          intro j _
          refine Finset.sum_congr rfl ?_
          intro k _
          exact (MeasureTheory.integral_const_mul (v j * v k)
            (fun a => (a - t) ^ (j : ℕ) * (a - t) ^ (k : ℕ))).symm
    _ = ∑ j : Fin (p + 1),
            ∫ a, ∑ k : Fin (p + 1),
              (v j * v k) * ((a - t) ^ (j : ℕ) * (a - t) ^ (k : ℕ)) ∂ν := by
          refine Finset.sum_congr rfl ?_
          intro j _
          symm
          rw [MeasureTheory.integral_finset_sum]
          intro k _
          exact (hint j k).const_mul (v j * v k)
    _ = ∫ a, ∑ j : Fin (p + 1), ∑ k : Fin (p + 1),
            (v j * v k) * ((a - t) ^ (j : ℕ) * (a - t) ^ (k : ℕ)) ∂ν := by
          symm
          rw [MeasureTheory.integral_finset_sum]
          intro j _
          exact integrable_finset_sum _ (fun k _ => (hint j k).const_mul (v j * v k))
    _ = ∫ a, (∑ j, v j * (a - t) ^ (j : ℕ)) ^ 2 ∂ν := by
          exact MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall (fun a => by
              change (∑ j : Fin (p + 1), ∑ k : Fin (p + 1),
                  (v j * v k) * ((a - t) ^ (j : ℕ) * (a - t) ^ (k : ℕ)))
                = (∑ j : Fin (p + 1), v j * (a - t) ^ (j : ℕ)) ^ 2
              rw [pow_two, Finset.sum_mul_sum]
              refine Finset.sum_congr rfl ?_
              intro j _
              refine Finset.sum_congr rfl ?_
              intro k _
              ring))

/-- The integral moment matrix is symmetric. -/
theorem intMomentMatrix_isHermitian {p : ℕ} {ν : Measure ℝ} {t : ℝ} :
    (intMomentMatrix p ν t).IsHermitian := by
  ext j k
  simp only [Matrix.conjTranspose_apply, intMomentMatrix, Matrix.of_apply, star_trivial]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun a => by ring))

/-- **The integral moment matrix is positive semidefinite** (a Gram matrix of an `L²` family). -/
theorem intMomentMatrix_posSemidef {p : ℕ} {ν : Measure ℝ} {t : ℝ}
    (hint : ∀ j k : Fin (p + 1),
      Integrable (fun a => (a - t) ^ (j : ℕ) * (a - t) ^ (k : ℕ)) ν) :
    (intMomentMatrix p ν t).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg intMomentMatrix_isHermitian (fun v => ?_)
  have hstar : star v = v := funext (fun i => star_trivial _)
  rw [hstar, intMomentMatrix_quadForm hint]
  exact integral_nonneg (fun a => sq_nonneg _)

/-- **The integral moment matrix is positive definite** under non-degeneracy of the design law:
no nonzero coefficient vector `v` makes the centered polynomial `∑ⱼ vⱼ (a−t)^j` vanish `ν`-almost
everywhere. -/
theorem intMomentMatrix_posDef {p : ℕ} {ν : Measure ℝ} {t : ℝ}
    (hint : ∀ j k : Fin (p + 1),
      Integrable (fun a => (a - t) ^ (j : ℕ) * (a - t) ^ (k : ℕ)) ν)
    (hnd : ∀ v : Fin (p + 1) → ℝ, v ≠ 0 →
        ¬ (∀ᵐ a ∂ν, (∑ j, v j * (a - t) ^ (j : ℕ)) = 0)) :
    (intMomentMatrix p ν t).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos intMomentMatrix_isHermitian (fun v hv => ?_)
  have hstar : star v = v := funext (fun i => star_trivial _)
  rw [hstar, intMomentMatrix_quadForm hint]
  have hnn : 0 ≤ ∫ a, (∑ j : Fin (p + 1), v j * (a - t) ^ (j : ℕ)) ^ 2 ∂ν :=
    integral_nonneg (fun a => sq_nonneg _)
  have hq2 : Integrable (fun a => (∑ j : Fin (p + 1),
      v j * (a - t) ^ (j : ℕ)) ^ 2) ν := by
    have e : (fun a => (∑ j : Fin (p + 1), v j * (a - t) ^ (j : ℕ)) ^ 2)
        = (fun a => ∑ j : Fin (p + 1), ∑ k : Fin (p + 1),
            (v j * v k) * ((a - t) ^ (j : ℕ) * (a - t) ^ (k : ℕ))) := by
      funext a
      rw [pow_two, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      refine Finset.sum_congr rfl ?_
      intro k _
      ring
    rw [e]
    exact integrable_finset_sum _ (fun j _ =>
      integrable_finset_sum _ (fun k _ => (hint j k).const_mul (v j * v k)))
  cases lt_or_eq_of_le hnn with
  | inl h =>
      exact h
  | inr h =>
      exfalso
      have hz := (MeasureTheory.integral_eq_zero_iff_of_nonneg
        (fun a => sq_nonneg ((∑ j : Fin (p + 1), v j * (a - t) ^ (j : ℕ)))) hq2).mp h.symm
      apply hnd v hv
      filter_upwards [hz] with a ha
      exact sq_eq_zero_iff.mp ha

/-- **Invertibility of the integral moment matrix** from design non-degeneracy: a positive
definite matrix has a unit determinant, discharging the `IsUnit S.det` hypothesis for the
population shape matrix. -/
theorem intMomentMatrix_isUnit_det {p : ℕ} {ν : Measure ℝ} {t : ℝ}
    (hint : ∀ j k : Fin (p + 1),
      Integrable (fun a => (a - t) ^ (j : ℕ) * (a - t) ^ (k : ℕ)) ν)
    (hnd : ∀ v : Fin (p + 1) → ℝ, v ≠ 0 →
        ¬ (∀ᵐ a ∂ν, (∑ j, v j * (a - t) ^ (j : ℕ)) = 0)) :
    IsUnit (intMomentMatrix p ν t).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (intMomentMatrix_posDef hint hnd).isUnit

end Causalean.Stat.Nonparametric
