/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.LocalPoly.Weights
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Polynomial.Roots

/-!
# Positive-definiteness and invertibility of the design moment matrix

Positive-definiteness criteria for local-polynomial weighted design moment matrices, viewed as
Gram matrices of centered monomial vectors.

The weighted design moment matrix `M_{jk} = ∑ᵢ wᵢ xᵢʲ xᵢᵏ` of a degree-`p` local-polynomial
fit is a **weighted Gram matrix** of the monomial vectors `(1, xᵢ, …, xᵢᵖ)`: its quadratic
form is `vᵀ M v = ∑ᵢ wᵢ (∑ⱼ vⱼ xᵢʲ)²`. Hence with nonnegative weights it is positive
semidefinite, and it is positive definite — therefore **invertible** — exactly when the
design is non-degenerate (no nonzero degree-`p` polynomial vanishes at all positively
weighted design points; e.g. there are `p+1` distinct points with positive weight, by
Vandermonde). This discharges the `IsUnit (designMatrix p x w).det` hypothesis used
throughout the local-polynomial analysis from a concrete condition on the design.
-/

namespace Causalean.Stat.Nonparametric

open scoped BigOperators
open Matrix

/-- **Gram quadratic form of the design moment matrix.** `vᵀ M v = ∑ᵢ wᵢ (∑ⱼ vⱼ xᵢʲ)²` —
the design moment matrix is the weighted Gram matrix of the monomial feature vectors. -/
theorem designMatrix_quadForm {N p : ℕ} (x w : Fin N → ℝ) (v : Fin (p + 1) → ℝ) :
    v ⬝ᵥ (designMatrix p x w *ᵥ v)
      = ∑ i, w i * (∑ j, v j * x i ^ (j : ℕ)) ^ 2 := by
  simp only [dotProduct, Matrix.mulVec, designMatrix]
  calc
    (∑ j : Fin (p + 1), v j * ∑ k : Fin (p + 1),
        (∑ i : Fin N, w i * x i ^ (j : ℕ) * x i ^ (k : ℕ)) * v k)
        = ∑ j : Fin (p + 1), ∑ k : Fin (p + 1), ∑ i : Fin N,
            v j * (w i * x i ^ (j : ℕ) * x i ^ (k : ℕ)) * v k := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    _ = ∑ j : Fin (p + 1), ∑ i : Fin N, ∑ k : Fin (p + 1),
            v j * (w i * x i ^ (j : ℕ) * x i ^ (k : ℕ)) * v k := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ i : Fin N, ∑ j : Fin (p + 1), ∑ k : Fin (p + 1),
            v j * (w i * x i ^ (j : ℕ) * x i ^ (k : ℕ)) * v k := by
      rw [Finset.sum_comm]
    _ = ∑ i, w i * (∑ j, v j * x i ^ (j : ℕ)) ^ 2 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by ring)

/-- The design moment matrix is symmetric. -/
theorem designMatrix_isHermitian {N p : ℕ} (x w : Fin N → ℝ) :
    (designMatrix p x w).IsHermitian := by
  ext j k
  simp only [Matrix.conjTranspose_apply, designMatrix, star_trivial]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- **The design moment matrix is positive semidefinite** when the weights are nonnegative
(a sum of weighted rank-one squares). -/
theorem designMatrix_posSemidef {N p : ℕ} {x w : Fin N → ℝ} (hw : ∀ i, 0 ≤ w i) :
    (designMatrix p x w).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (designMatrix_isHermitian x w) ?_
  intro v
  have hstar : star v = v := by
    funext i
    exact star_trivial _
  rw [hstar, designMatrix_quadForm]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))

/-- **The design moment matrix is positive definite** under a non-degeneracy condition on the
design: no nonzero coefficient vector `v` yields a polynomial `∑ⱼ vⱼ xᵢʲ` that vanishes at
every positively weighted design point. (Implied by the existence of `p+1` distinct design
points with positive weight, via Vandermonde.) -/
theorem designMatrix_posDef {N p : ℕ} {x w : Fin N → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hnd : ∀ v : Fin (p + 1) → ℝ, v ≠ 0 →
        ∃ i, 0 < w i ∧ (∑ j, v j * x i ^ (j : ℕ)) ≠ 0) :
    (designMatrix p x w).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (designMatrix_isHermitian x w) ?_
  intro v hv
  have hstar : star v = v := by
    funext i
    exact star_trivial _
  rw [hstar, designMatrix_quadForm]
  obtain ⟨i₀, hwi₀, hpoly⟩ := hnd v hv
  refine Finset.sum_pos' (fun i _ => mul_nonneg (hw i) (sq_nonneg _)) ?_
  refine ⟨i₀, Finset.mem_univ _, ?_⟩
  exact mul_pos hwi₀ (sq_pos_of_ne_zero hpoly)

/-- **Invertibility of the design moment matrix** from design non-degeneracy: a positive
definite matrix has a unit determinant, discharging the `IsUnit (designMatrix p x w).det`
hypothesis used throughout the local-polynomial analysis. -/
theorem designMatrix_isUnit_det {N p : ℕ} {x w : Fin N → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hnd : ∀ v : Fin (p + 1) → ℝ, v ≠ 0 →
        ∃ i, 0 < w i ∧ (∑ j, v j * x i ^ (j : ℕ)) ≠ 0) :
    IsUnit (designMatrix p x w).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (designMatrix_posDef hw hnd).isUnit

/-- **Design non-degeneracy from distinct positively-weighted points (Vandermonde).** If a set
`S` of design indices all carry positive weight and the design points `xᵢ` take at least `p+1`
distinct values on `S`, then the non-degeneracy condition holds: no nonzero degree-`p`
polynomial vanishes at every positively weighted point. (A nonzero polynomial of degree `≤ p`
has at most `p` roots, but it would vanish at the `≥ p+1` distinct points of `S`.) Hence the
design moment matrix is invertible. -/
theorem nondegenerate_of_distinct_points {N p : ℕ} {x w : Fin N → ℝ}
    (S : Finset (Fin N)) (hpos : ∀ i ∈ S, 0 < w i)
    (hdistinct : p + 1 ≤ (S.image x).card) :
    ∀ v : Fin (p + 1) → ℝ, v ≠ 0 →
      ∃ i, 0 < w i ∧ (∑ j, v j * x i ^ (j : ℕ)) ≠ 0 := by
  classical
  intro v hv
  by_contra hcon
  push_neg at hcon
  let P : Polynomial ℝ :=
    ∑ j : Fin (p + 1), Polynomial.C (v j) * Polynomial.X ^ (j : ℕ)
  have hP_eval : ∀ a : ℝ, P.eval a = ∑ j : Fin (p + 1), v j * a ^ (j : ℕ) := by
    intro a
    simp only [P, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
  have hP_coeff : ∀ j₀ : Fin (p + 1), P.coeff (j₀ : ℕ) = v j₀ := by
    intro j₀
    simp only [P, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single j₀]
    · simp
    · intro j _ hj
      by_cases hval : (j₀ : ℕ) = (j : ℕ)
      · exact (hj (Fin.ext hval.symm)).elim
      · simp [hval]
    · intro hj₀
      simp at hj₀
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hv
  have hcoeff_ne : P.coeff (j₀ : ℕ) ≠ 0 := by
    simpa [hP_coeff j₀] using hj₀
  have hP_ne : P ≠ 0 := by
    intro hzero
    exact hcoeff_ne (by simp [hzero])
  have hP_natDegree : P.natDegree ≤ p := by
    simpa [P] using
      (Polynomial.natDegree_sum_le_of_forall_le
        (s := Finset.univ)
        (f := fun j : Fin (p + 1) => Polynomial.C (v j) * Polynomial.X ^ (j : ℕ))
        (n := p)
        (by
          intro j _
          exact (Polynomial.natDegree_C_mul_X_pow_le (v j) (j : ℕ)).trans
            (Nat.lt_succ_iff.mp j.isLt)))
  let Z : Finset ℝ := S.image x
  have hsubset : Z.val ⊆ P.roots := by
    intro a ha
    have haZ : a ∈ Z := by
      simpa using ha
    obtain ⟨i, hiS, hxi⟩ := Finset.mem_image.mp haZ
    have hroot_eval : P.eval a = 0 := by
      rw [hP_eval, ← hxi]
      exact hcon i (hpos i hiS)
    exact (Polynomial.mem_roots hP_ne).mpr (by
      simpa [Polynomial.IsRoot] using hroot_eval)
  have hZ_le_degree : Z.card ≤ P.natDegree :=
    Polynomial.card_le_degree_of_subset_roots (p := P) (Z := Z) hsubset
  have hZ_le_p : Z.card ≤ p := hZ_le_degree.trans hP_natDegree
  have hZ_ge : p + 1 ≤ Z.card := by
    simpa [Z] using hdistinct
  omega

end Causalean.Stat.Nonparametric
