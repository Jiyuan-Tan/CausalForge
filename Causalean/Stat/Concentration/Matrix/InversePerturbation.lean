/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Causalean.Stat.Concentration.Matrix.Resolvent

/-!
# Entrywise perturbation of the inverse design moment matrix

Deterministic inverse-perturbation bounds that transport entrywise matrix deviations into control
of a design inverse.

The interior local-polynomial variance rate `(M⁻¹)₀₀ = O(1/(Nh))` is obtained by transporting
an *entrywise* concentration bound on the random design moment matrix `M` (each entry close to
the corresponding entry of a fixed, invertible population matrix `S`) through the matrix
inverse. This file develops the deterministic perturbation step:

if every entry of `M` is within `η` of the corresponding entry of an invertible matrix `S`, and
the rows of `S⁻¹` have absolute sums bounded by `c`, with `c·(p+1)·η ≤ 1/2`, then `M` is
invertible and

`|(M⁻¹)₀₀ − (S⁻¹)₀₀| ≤ 2 c² (p+1) η`.

The argument is the operator (`ℓ∞`-operator, i.e. max-row-sum) norm Neumann/resolvent bound:
`M = S(1 − u)` with `u = S⁻¹(S − M)`, `‖u‖ ≤ ‖S⁻¹‖·‖S − M‖ ≤ 1/2`, so `1 − u` is a unit
(`Units.oneSub`) with `‖(1−u)⁻¹‖ ≤ (1−‖u‖)⁻¹ ≤ 2` (geometric series), hence `M` is a unit with
`‖M⁻¹‖ ≤ 2‖S⁻¹‖`, and the resolvent identity `M⁻¹ − S⁻¹ = M⁻¹(S − M)S⁻¹`
(`norm_unitInv_sub_unitInv_le`) gives `‖M⁻¹ − S⁻¹‖ ≤ 2‖S⁻¹‖²‖S − M‖`. The entry bound follows
since each entry is dominated by the operator norm. The public statement carries only entrywise
hypotheses, so it composes with the iid Chebyshev union bound (for `M` close to `𝔼 M = S`) and
the population positive-definiteness (`designMatrix_posDef`) without exposing the matrix norm.
-/

namespace Causalean.Stat.Concentration

open scoped BigOperators
open Matrix

section LinftyOp

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing

variable {p : ℕ}

/-- Completeness of the matrix ring under the `ℓ∞`-operator norm (it shares the product
uniformity, so it inherits completeness from the coordinatewise reshaping `Fin (p+1) → Fin (p+1)
→ ℝ`). Needed to invoke the Neumann/geometric-series unit API. -/
theorem completeSpace_matrix_linftyOp :
    CompleteSpace (Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ) :=
  inferInstanceAs (CompleteSpace (Fin (p + 1) → Fin (p + 1) → ℝ))

/-- Each absolute entry is dominated by the `ℓ∞`-operator (max-row-sum) norm. -/
theorem linftyOp_abs_entry_le (A : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ) (i j : Fin (p + 1)) :
    |A i j| ≤ ‖A‖ := by
  rw [← Real.norm_eq_abs, Matrix.linfty_opNorm_def]
  have hrow : ‖A i j‖₊ ≤ ∑ k, ‖A i k‖₊ :=
    Finset.single_le_sum (s := Finset.univ) (f := fun k => ‖A i k‖₊)
      (fun _ _ => zero_le _) (Finset.mem_univ j)
  have hsup : (∑ k, ‖A i k‖₊) ≤
      Finset.univ.sup (fun i => ∑ k, ‖A i k‖₊) :=
    Finset.le_sup (s := Finset.univ) (f := fun i => ∑ k, ‖A i k‖₊)
      (Finset.mem_univ i)
  exact_mod_cast le_trans hrow hsup

/-- A row-sum upper bound for the `ℓ∞`-operator norm: if every row's absolute sum is `≤ c`,
then `‖A‖ ≤ c`. -/
theorem linftyOp_norm_le_of_rowsum {A : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ} {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ i, (∑ j, |A i j|) ≤ c) : ‖A‖ ≤ c := by
  rw [Matrix.linfty_opNorm_def]
  have hsup : Finset.univ.sup (fun i => ∑ j, ‖A i j‖₊) ≤ c.toNNReal := by
    refine Finset.sup_le ?_
    intro i _
    exact NNReal.coe_le_coe.mp (by
      rw [NNReal.coe_sum, Real.coe_toNNReal c hc]
      simpa [Real.norm_eq_abs] using h i)
  calc
    ↑(Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ (c.toNNReal : ℝ) :=
      NNReal.coe_le_coe.mpr hsup
    _ = c := Real.coe_toNNReal c hc

/-- The `ℓ∞`-operator norm of an entrywise-`η`-bounded matrix is `≤ (p+1)·η`. -/
theorem linftyOp_norm_le_of_entry {A : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ} {η : ℝ}
    (hη : 0 ≤ η) (h : ∀ i j, |A i j| ≤ η) : ‖A‖ ≤ (p + 1 : ℕ) * η := by
  apply linftyOp_norm_le_of_rowsum (by positivity)
  intro i
  calc
    ∑ j, |A i j| ≤ ∑ _j : Fin (p + 1), η :=
      Finset.sum_le_sum (fun j _ => h i j)
    _ = (p + 1 : ℕ) * η := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Entrywise perturbation of the `(0,0)` inverse entry.** Let `S` be an invertible
`(p+1)×(p+1)` real matrix whose inverse has rows with absolute sums bounded by `c`, and let `M`
be a matrix all of whose entries are within `η` of `S` (`|Mⱼₖ − Sⱼₖ| ≤ η`). If
`c·(p+1)·η ≤ 1/2`, then `M` is invertible and the `(0,0)` entries of the inverses satisfy

`|(M⁻¹)₀₀ − (S⁻¹)₀₀| ≤ 2 c² (p+1) η`.

This is the deterministic transport step turning an entrywise design concentration bound into a
bound on the leverage quantity `(M⁻¹)₀₀`; combined with the population positive-definiteness it
discharges both invertibility and the `O(1/(Nh))` leverage rate on the good event. -/
theorem designInv00_perturb (S M : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ)
    (hS : IsUnit S.det) {η c : ℝ} (hc : 0 ≤ c) (hη : 0 ≤ η)
    (hSrow : ∀ i, (∑ j, |S⁻¹ i j|) ≤ c)
    (hclose : ∀ j k, |M j k - S j k| ≤ η)
    (hsmall : c * ((p + 1 : ℕ) * η) ≤ 1 / 2) :
    IsUnit M.det ∧
      |M⁻¹ 0 0 - S⁻¹ 0 0| ≤ 2 * c ^ 2 * ((p + 1 : ℕ) * η) := by
  haveI : CompleteSpace (Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ) :=
    completeSpace_matrix_linftyOp
  let R := Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ
  have hSu : IsUnit S := (Matrix.isUnit_iff_isUnit_det S).mpr hS
  set Su : Rˣ := hSu.unit with hSu_def
  have hval : (↑Su : R) = S := by
    rw [hSu_def]
    exact hSu.unit_spec
  have hinv : (↑Su⁻¹ : R) = S⁻¹ := by
    rw [Matrix.coe_units_inv, hval]
  have hSinv_norm : ‖(↑Su⁻¹ : R)‖ ≤ c := by
    rw [hinv]
    exact linftyOp_norm_le_of_rowsum hc hSrow
  have hMS_norm : ‖M - S‖ ≤ (p + 1 : ℕ) * η :=
    linftyOp_norm_le_of_entry hη (by
      intro i j
      simpa [Matrix.sub_apply] using hclose i j)
  set u : R := (↑Su⁻¹ : R) * (S - M) with hu_def
  have hu_le : ‖u‖ ≤ c * ((p + 1 : ℕ) * η) := by
    calc
      ‖u‖ = ‖(↑Su⁻¹ : R) * (S - M)‖ := by rw [hu_def]
      _ ≤ ‖(↑Su⁻¹ : R)‖ * ‖S - M‖ := norm_mul_le _ _
      _ = ‖(↑Su⁻¹ : R)‖ * ‖M - S‖ := by rw [norm_sub_rev S M]
      _ ≤ c * ((p + 1 : ℕ) * η) := by
        gcongr
  have huhalf : ‖u‖ ≤ 1 / 2 := le_trans hu_le hsmall
  have hu1 : ‖u‖ < 1 := by
    have hunonneg : 0 ≤ ‖u‖ := norm_nonneg u
    nlinarith
  set v : Rˣ := Units.oneSub u hu1 with hv_def
  have hinvS : (↑Su⁻¹ : R) * S = 1 := by
    rw [← hval]
    exact_mod_cast Su.inv_mul
  have hSmulinv : S * (↑Su⁻¹ : R) = 1 := by
    rw [← hval]
    exact Su.mul_inv
  have hvval : (↑v : R) = (↑Su⁻¹ : R) * M := by
    rw [hv_def]
    change (1 : R) - u = (↑Su⁻¹ : R) * M
    rw [hu_def]
    calc
      (1 : R) - (↑Su⁻¹ : R) * (S - M)
          = (↑Su⁻¹ : R) * S - (↑Su⁻¹ : R) * (S - M) := by
              rw [hinvS]
      _ = (↑Su⁻¹ : R) * (S - (S - M)) := by
              rw [← mul_sub]
      _ = (↑Su⁻¹ : R) * M := by
              simp
  set Munit : Rˣ := Su * v with hM_def
  have hMval : (↑Munit : R) = M := by
    rw [hM_def]
    change ((↑Su : R) * (↑v : R)) = M
    rw [hval, hvval, ← mul_assoc, hSmulinv, one_mul]
  have hMunit : IsUnit M := hMval ▸ Munit.isUnit
  have hMdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hMunit
  have hMinv_eq : (↑Munit⁻¹ : R) = M⁻¹ := by
    rw [Matrix.coe_units_inv, hMval]
  have hvinv_norm : ‖(↑v⁻¹ : R)‖ ≤ (1 - ‖u‖)⁻¹ := by
    rw [hv_def]
    change ‖∑' n : ℕ, u ^ n‖ ≤ (1 - ‖u‖)⁻¹
    simpa [norm_one] using tsum_geometric_le_of_norm_lt_one u hu1
  have hvinv2 : ‖(↑v⁻¹ : R)‖ ≤ 2 := by
    have hhalf_le : (1 / 2 : ℝ) ≤ 1 - ‖u‖ := by linarith
    have hhalf_pos : 0 < (1 / 2 : ℝ) := by norm_num
    have hinv_le : (1 - ‖u‖)⁻¹ ≤ 2 := by
      have hden_pos : 0 < 1 - ‖u‖ := by linarith
      calc
        (1 - ‖u‖)⁻¹ ≤ ((1 / 2 : ℝ)⁻¹) :=
          (inv_le_inv₀ hden_pos hhalf_pos).mpr hhalf_le
        _ = 2 := by norm_num
    exact le_trans hvinv_norm hinv_le
  have hMunitinv_norm : ‖(↑Munit⁻¹ : R)‖ ≤ 2 * c := by
    calc
      ‖(↑Munit⁻¹ : R)‖ = ‖(↑v⁻¹ : R) * (↑Su⁻¹ : R)‖ := by
        rw [hM_def]
        rw [_root_.mul_inv_rev]
        rfl
      _ ≤ ‖(↑v⁻¹ : R)‖ * ‖(↑Su⁻¹ : R)‖ := norm_mul_le _ _
      _ ≤ 2 * c := by
        exact mul_le_mul hvinv2 hSinv_norm (norm_nonneg _) (by norm_num)
  have hdiff_norm :
      ‖(↑Munit⁻¹ : R) - ↑Su⁻¹‖ ≤ 2 * c ^ 2 * ((p + 1 : ℕ) * η) := by
    have hres := norm_unitInv_sub_unitInv_le Munit Su
    calc
      ‖(↑Munit⁻¹ : R) - ↑Su⁻¹‖
          ≤ ‖(↑Munit⁻¹ : R)‖ * ‖(↑Su⁻¹ : R)‖ * ‖(↑Munit : R) - ↑Su‖ :=
            hres
      _ ≤ (2 * c) * c * ((p + 1 : ℕ) * η) := by
            have hdiff_mat : ‖(↑Munit : R) - ↑Su‖ ≤ (p + 1 : ℕ) * η := by
              simpa [hMval, hval] using hMS_norm
            have hAB :
                ‖(↑Munit⁻¹ : R)‖ * ‖(↑Su⁻¹ : R)‖ ≤ (2 * c) * c :=
              mul_le_mul hMunitinv_norm hSinv_norm (norm_nonneg _) (by positivity)
            have hD_nonneg : 0 ≤ ‖(↑Munit : R) - ↑Su‖ := norm_nonneg _
            have hC_nonneg : 0 ≤ (2 * c) * c := by positivity
            exact le_trans
              (mul_le_mul_of_nonneg_right hAB hD_nonneg)
              (mul_le_mul_of_nonneg_left hdiff_mat hC_nonneg)
      _ = 2 * c ^ 2 * ((p + 1 : ℕ) * η) := by ring
  refine ⟨hMdet, ?_⟩
  calc
    |M⁻¹ 0 0 - S⁻¹ 0 0|
        = |(((↑Munit⁻¹ : R) - ↑Su⁻¹) 0 0)| := by
            rw [← hMinv_eq, ← hinv, Matrix.sub_apply]
    _ ≤ ‖(↑Munit⁻¹ : R) - ↑Su⁻¹‖ :=
        linftyOp_abs_entry_le ((↑Munit⁻¹ : R) - ↑Su⁻¹) 0 0
    _ ≤ 2 * c ^ 2 * ((p + 1 : ℕ) * η) := hdiff_norm

end LinftyOp

end Causalean.Stat.Concentration
