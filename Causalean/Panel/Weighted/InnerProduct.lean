/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Weighted inner product on arrays over a weighted support

For `c : WeightedSupport R` (see `Causalean/Panel/Weighted/Support.lean`) and scalar
arrays `A B : R → ℝ`, this file defines the weighted inner product

    ⟨A, B⟩_ω  :=  ∑_{r ∈ observed} ω_r · A_r · B_r

(`WeightedSupport.ip`), and its matrix-valued lift to vector arrays
`A B : Fin K → (R → ℝ)`,

    (⟨A, B⟩_ω)_{j,k}  :=  ⟨A_j, B_k⟩_ω

(`WeightedSupport.ipMat`).

This is the WLS inner product underpinning Frisch–Waugh–Lovell: the
weighted projections of `Causalean/Panel/Weighted/Subspace.lean` are orthogonal in
this inner product, and the WLS-optimality characterization in
`Causalean/Panel/Weighted/WLS.lean` rests on its bilinearity / positive-semidefiniteness.

## Main definitions

* `WeightedSupport.ip` — the scalar weighted inner product.
* `WeightedSupport.ipMat` — the matrix-valued vector inner product.

## Main lemmas

* `WeightedSupport.ip_symm`, `ip_add_left`, `ip_smul_left`
* `WeightedSupport.ip_self_nonneg`
* `WeightedSupport.ip_self_eq_zero_iff` — definiteness on the observed support.
* `WeightedSupport.ipMat_apply`, `ipMat_transpose`,
  `ipMat_add_left`, `ipMat_smul_left`.
-/

import Causalean.Panel.Weighted.Support
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Weighted inner products over a finite support

This file defines the scalar weighted inner product over observed records and
its matrix-valued lift to tuples of arrays.

The inner product is the WLS pairing used by the weighted projection,
WLS-optimality, and Frisch-Waugh-Lovell layers. It is bilinear,
positive-semidefinite, definite on the observed support, and symmetric after
matrix transposition. -/

open scoped BigOperators

namespace Causalean
namespace Panel.Weighted
namespace WeightedSupport

variable {R : Type*}
variable [Fintype R] [DecidableEq R]

/-! ### Scalar weighted inner product -/

/-- The weighted inner product multiplies two arrays record by record and sums
the products with the support weights over observed records. -/
def ip (c : WeightedSupport R) (A B : R → ℝ) : ℝ :=
  ∑ r ∈ c.observed, c.weight r * A r * B r

/-- The weighted inner product unfolds to its finite weighted sum over observed
records. -/
@[simp] lemma ip_def (c : WeightedSupport R) (A B : R → ℝ) :
    c.ip A B = ∑ r ∈ c.observed, c.weight r * A r * B r := rfl

/-- Symmetry of the weighted inner product. -/
lemma ip_symm (c : WeightedSupport R) (A B : R → ℝ) :
    c.ip A B = c.ip B A := by
  unfold ip
  refine Finset.sum_congr rfl ?_
  intro r _
  ring

/-- Additivity in the left argument. -/
lemma ip_add_left (c : WeightedSupport R) (A A' B : R → ℝ) :
    c.ip (A + A') B = c.ip A B + c.ip A' B := by
  unfold ip
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro r _
  simp [Pi.add_apply]; ring

/-- Additivity in the right argument. -/
lemma ip_add_right (c : WeightedSupport R) (A B B' : R → ℝ) :
    c.ip A (B + B') = c.ip A B + c.ip A B' := by
  rw [ip_symm, ip_add_left, ip_symm c A B, ip_symm c A B']

/-- Scalar homogeneity in the left argument. -/
lemma ip_smul_left (c : WeightedSupport R) (s : ℝ) (A B : R → ℝ) :
    c.ip (s • A) B = s * c.ip A B := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro r _
  simp [Pi.smul_apply]; ring

/-- Scalar homogeneity in the right argument. -/
lemma ip_smul_right (c : WeightedSupport R) (s : ℝ) (A B : R → ℝ) :
    c.ip A (s • B) = s * c.ip A B := by
  rw [ip_symm, ip_smul_left, ip_symm c A B]

/-- Each summand of `⟨A, A⟩_ω` is nonnegative. -/
lemma ip_self_summand_nonneg (c : WeightedSupport R) (A : R → ℝ) :
    ∀ r ∈ c.observed, 0 ≤ c.weight r * A r * A r := by
  intro r hr
  have hw : 0 ≤ c.weight r := (c.weight_pos r hr).le
  have hsq : 0 ≤ A r * A r := mul_self_nonneg (A r)
  have : 0 ≤ c.weight r * (A r * A r) := mul_nonneg hw hsq
  simpa [mul_assoc] using this

/-- Positivity: `⟨A, A⟩_ω ≥ 0`. -/
lemma ip_self_nonneg (c : WeightedSupport R) (A : R → ℝ) :
    0 ≤ c.ip A A := by
  unfold ip
  exact Finset.sum_nonneg (c.ip_self_summand_nonneg A)

/-- Definiteness on the support: `⟨A, A⟩_ω = 0` iff `A` vanishes on every
observed index.  Arrays that differ only off `c.observed` are identified. -/
lemma ip_self_eq_zero_iff (c : WeightedSupport R) (A : R → ℝ) :
    c.ip A A = 0 ↔ ∀ r ∈ c.observed, A r = 0 := by
  unfold ip
  rw [Finset.sum_eq_zero_iff_of_nonneg (c.ip_self_summand_nonneg A)]
  constructor
  · -- From `ω_r · A_r · A_r = 0` and `ω_r > 0`, deduce `A_r = 0`.
    intro h r hr
    have hwpos : 0 < c.weight r := c.weight_pos r hr
    have hsum : c.weight r * A r * A r = 0 := h r hr
    have hsum' : c.weight r * (A r * A r) = 0 := by
      rw [← mul_assoc]; exact hsum
    have hne : c.weight r ≠ 0 := ne_of_gt hwpos
    have hsq : A r * A r = 0 := (mul_eq_zero.mp hsum').resolve_left hne
    exact mul_self_eq_zero.mp hsq
  · -- `A_r = 0` ⇒ `ω_r · A_r · A_r = 0`.
    intro h r hr
    have hAr : A r = 0 := h r hr
    rw [hAr]; ring

/-! ### Matrix-valued vector inner product

Vector arrays are modeled as `K`-tuples of scalar arrays:
`A : Fin K → (R → ℝ)`.  The matrix-valued inner product is the entrywise
scalar inner product. -/

variable {K : ℕ}

/-- The matrix-valued inner product takes the scalar weighted inner product
between each pair of columns. -/
def ipMat (c : WeightedSupport R) (A B : Fin K → R → ℝ) :
    Matrix (Fin K) (Fin K) ℝ :=
  fun j k => c.ip (A j) (B k)

/-- Each entry of the matrix-valued inner product is the scalar weighted inner
product of the corresponding two columns. -/
@[simp] lemma ipMat_apply (c : WeightedSupport R) (A B : Fin K → R → ℝ)
    (j k : Fin K) :
    c.ipMat A B j k = c.ip (A j) (B k) := rfl

/-- The transpose of `⟨A, B⟩_ω` is `⟨B, A⟩_ω`. -/
lemma ipMat_transpose (c : WeightedSupport R) (A B : Fin K → R → ℝ) :
    (c.ipMat A B).transpose = c.ipMat B A := by
  ext j k
  rw [Matrix.transpose_apply, ipMat_apply, ipMat_apply, ip_symm]

/-- Additivity in the left tuple argument (entrywise). -/
lemma ipMat_add_left (c : WeightedSupport R) (A A' B : Fin K → R → ℝ) :
    c.ipMat (A + A') B = c.ipMat A B + c.ipMat A' B := by
  ext j k
  change c.ip ((A + A') j) (B k) = c.ipMat A B j k + c.ipMat A' B j k
  rw [Pi.add_apply, ip_add_left]
  simp [ipMat_apply]

/-- Additivity in the right tuple argument (entrywise). -/
lemma ipMat_add_right (c : WeightedSupport R) (A B B' : Fin K → R → ℝ) :
    c.ipMat A (B + B') = c.ipMat A B + c.ipMat A B' := by
  ext j k
  change c.ip (A j) ((B + B') k) = c.ipMat A B j k + c.ipMat A B' j k
  rw [Pi.add_apply, ip_add_right]
  simp [ipMat_apply]

/-- Scalar homogeneity in the left tuple argument (entrywise). -/
lemma ipMat_smul_left (c : WeightedSupport R) (s : ℝ) (A B : Fin K → R → ℝ) :
    c.ipMat (s • A) B = s • c.ipMat A B := by
  ext j k
  change c.ip ((s • A) j) (B k) = s • (c.ipMat A B) j k
  rw [Pi.smul_apply, ip_smul_left]
  simp [ipMat_apply, smul_eq_mul]

/-- Scalar homogeneity in the right tuple argument (entrywise). -/
lemma ipMat_smul_right (c : WeightedSupport R) (s : ℝ) (A B : Fin K → R → ℝ) :
    c.ipMat A (s • B) = s • c.ipMat A B := by
  ext j k
  change c.ip (A j) ((s • B) k) = s • (c.ipMat A B) j k
  rw [Pi.smul_apply, ip_smul_right]
  simp [ipMat_apply, smul_eq_mul]

end WeightedSupport
end Panel.Weighted
end Causalean
