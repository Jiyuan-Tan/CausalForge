/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Causalean.Stat.Nonparametric.LeastSquares.NormalEquations

/-!
# Polynomial reproduction of the local-polynomial equivalent kernel

Equivalent-kernel weights for local-polynomial weighted least squares and their
polynomial-reproduction property.

The degree-`p` local-polynomial weighted least-squares fit at a point has, when the
weighted design moment matrix is invertible, an explicit **equivalent-kernel** weight
`Sᵢ = ∑ₖ (M⁻¹)₀ₖ wᵢ xᵢᵏ`, where `M_{jk} = ∑ᵢ wᵢ xᵢʲ xᵢᵏ` is the weighted design moment
matrix (`xᵢ = aᵢ − t`). This file proves the defining **polynomial-reproduction**
property of these weights:

`∑ᵢ Sᵢ xᵢᵐ = [m = 0]`  for `m ≤ p`,

i.e. the equivalent kernel reproduces polynomials up to degree `p`. This is exactly the
hypothesis `hrep` consumed by `linearSmoother_bias_of_reproduces`, so it converts the
abstract bias bound into the concrete local-polynomial bias estimate. The reproduction is
pure linear algebra: `∑ᵢ Sᵢ xᵢᵐ = ∑ₖ (M⁻¹)₀ₖ M_{km} = (M⁻¹ M)₀ₘ = I₀ₘ` (Fan–Gijbels 1996
§3.1).
-/

namespace Causalean.Stat.Nonparametric

open scoped BigOperators
open Matrix

/-- The weighted design moment matrix `M_{jk} = ∑ᵢ wᵢ xᵢʲ xᵢᵏ` of a degree-`p`
local-polynomial fit with design points `xᵢ` (typically `aᵢ − t`) and weights `wᵢ`. -/
noncomputable def designMatrix (p : ℕ) {N : ℕ} (x w : Fin N → ℝ) :
    Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ :=
  fun j k => ∑ i, w i * x i ^ (j : ℕ) * x i ^ (k : ℕ)

/-- The local-polynomial equivalent-kernel weight `Sᵢ = ∑ₖ (M⁻¹)₀ₖ wᵢ xᵢᵏ` extracting the
fitted intercept: the degree-`p` WLS intercept equals `∑ᵢ Sᵢ Yᵢ`. -/
noncomputable def equivKernelWeight (p : ℕ) {N : ℕ} (x w : Fin N → ℝ) (i : Fin N) : ℝ :=
  ∑ k, (designMatrix p x w)⁻¹ 0 k * (w i * x i ^ (k : ℕ))

/-- **Polynomial reproduction of the equivalent kernel.** If the weighted design moment
matrix is invertible, the local-polynomial equivalent-kernel weights reproduce polynomials
up to degree `p`: `∑ᵢ Sᵢ xᵢᵐ = [m = 0]` for every `m ≤ p`. This discharges the reproduction
hypothesis of `linearSmoother_bias_of_reproduces`. -/
theorem equivKernelWeight_reproduces {N p : ℕ} {x w : Fin N → ℝ}
    (hM : IsUnit (designMatrix p x w).det) :
    ∀ m : ℕ, m ≤ p →
      (∑ i, equivKernelWeight p x w i * x i ^ m) = if m = 0 then 1 else 0 := by
  intro m hm
  let M : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ := designMatrix p x w
  let m' : Fin (p + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
  calc
    (∑ i, equivKernelWeight p x w i * x i ^ m)
        = ∑ i, (∑ k, M⁻¹ 0 k * (w i * x i ^ (k : ℕ))) * x i ^ m := by
          simp only [equivKernelWeight, M]
    _ = ∑ k, M⁻¹ 0 k * M k m' := by
          simp only [Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k hk
          calc
            (∑ i, M⁻¹ 0 k * (w i * x i ^ (k : ℕ)) * x i ^ m)
                = ∑ i, M⁻¹ 0 k * (w i * x i ^ (k : ℕ) * x i ^ m) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
            _ = M⁻¹ 0 k * (∑ i, w i * x i ^ (k : ℕ) * x i ^ m) := by
                  rw [Finset.mul_sum]
            _ = M⁻¹ 0 k * M k m' := by
                  simp only [M, m', designMatrix]
    _ = (M⁻¹ * M) 0 m' := by
          rw [Matrix.mul_apply]
    _ = (1 : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ) 0 m' := by
          rw [Matrix.nonsing_inv_mul]
          simpa only [M] using hM
    _ = if m = 0 then 1 else 0 := by
          by_cases hm0 : m = 0
          · subst m
            have hfin : (0 : Fin (p + 1)) = m' := by
              ext
              simp only [Fin.val_zero, m']
            simp only [Matrix.one_apply, hfin, ↓reduceIte]
          · simp only [Matrix.one_apply, hm0, ↓reduceIte]
            rw [if_neg]
            intro h
            apply hm0
            have hval := congrArg Fin.val h
            simpa only [Fin.val_zero, m', Fin.val_mk] using hval.symm

/-- **The local-polynomial WLS intercept is the equivalent-kernel linear smoother.** If the
weighted design moment matrix is invertible and `c` minimizes the weighted sum of squares,
then the fitted intercept `c 0` equals the linear smoother `∑ᵢ Sᵢ Yᵢ` with the
equivalent-kernel weights `Sᵢ = equivKernelWeight p x w i`. Combined with
`equivKernelWeight_reproduces` and `linearSmoother_bias_of_reproduces`, this yields the
interior local-polynomial bias estimate. -/
theorem wls_intercept_eq_equivKernelSmoother {N p : ℕ} {x w Y : Fin N → ℝ}
    {c : Fin (p + 1) → ℝ}
    (hw : ∀ i, 0 ≤ w i)
    (hM : IsUnit (designMatrix p x w).det)
    (hmin : ∀ c' : Fin (p + 1) → ℝ,
        (∑ i, w i * (Y i - ∑ j, c j * x i ^ (j : ℕ)) ^ 2)
          ≤ ∑ i, w i * (Y i - ∑ j, c' j * x i ^ (j : ℕ)) ^ 2) :
    c 0 = ∑ i, equivKernelWeight p x w i * Y i := by
  let M : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ := designMatrix p x w
  let b : Fin (p + 1) → ℝ := fun k => ∑ i, w i * x i ^ (k : ℕ) * Y i
  have hnormal_scalar :
      ∀ k : Fin (p + 1),
        b k = ∑ i, w i * x i ^ (k : ℕ) *
          (∑ j, c j * x i ^ (j : ℕ)) := by
    intro k
    have hne := wls_normal_equations (x := x) (w := w) (Y := Y) (c := c) hw hmin k
    have hdiff :
        b k - ∑ i, w i * x i ^ (k : ℕ) *
            (∑ j, c j * x i ^ (j : ℕ)) = 0 := by
      rw [← Finset.sum_sub_distrib]
      calc
        (∑ i, (w i * x i ^ (k : ℕ) * Y i -
            w i * x i ^ (k : ℕ) *
              (∑ j, c j * x i ^ (j : ℕ))))
            = ∑ i, w i * (Y i - ∑ j, c j * x i ^ (j : ℕ)) *
                x i ^ (k : ℕ) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = 0 := hne
    exact sub_eq_zero.mp hdiff
  have hnormal : M *ᵥ c = b := by
    funext k
    calc
      (M *ᵥ c) k = ∑ j, M k j * c j := by
        simp [Matrix.mulVec, dotProduct]
      _ = ∑ j : Fin (p + 1), (∑ i, w i * x i ^ (k : ℕ) *
          x i ^ (j : ℕ)) * c j := by
        simp only [M, designMatrix]
      _ = ∑ i, w i * x i ^ (k : ℕ) *
          (∑ j : Fin (p + 1), c j * x i ^ (j : ℕ)) := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = b k := (hnormal_scalar k).symm
  have hMinv : M⁻¹ * M = 1 := by
    rw [Matrix.nonsing_inv_mul]
    simpa only [M] using hM
  have hc_eq : c = M⁻¹ *ᵥ b := by
    calc
      c = (1 : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ) *ᵥ c := by
        simp
      _ = (M⁻¹ * M) *ᵥ c := by
        simp only [hMinv]
      _ = M⁻¹ *ᵥ (M *ᵥ c) := by
        rw [Matrix.mulVec_mulVec]
      _ = M⁻¹ *ᵥ b := by
        rw [hnormal]
  calc
    c 0 = (M⁻¹ *ᵥ b) 0 := by
      rw [hc_eq]
    _ = ∑ k, M⁻¹ 0 k * b k := by
      simp [Matrix.mulVec, dotProduct]
    _ = ∑ k, M⁻¹ 0 k * (∑ i, w i * x i ^ (k : ℕ) * Y i) := by
      simp only [b]
    _ = ∑ i, (∑ k, M⁻¹ 0 k * (w i * x i ^ (k : ℕ))) * Y i := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ i, equivKernelWeight p x w i * Y i := by
      simp only [equivKernelWeight, M]

/-- **Leverage identity for the equivalent kernel.** Writing the equivalent-kernel weight as
`Sᵢ = wᵢ · gᵢ` with `gᵢ = ∑ₖ (M⁻¹)₀ₖ xᵢᵏ` the unweighted kernel, the weighted leverage equals
the `(0,0)` entry of the inverse moment matrix:
`∑ᵢ wᵢ gᵢ² = (M⁻¹)₀₀`. (Algebraically `e₀ᵀ M⁻¹ M M⁻¹ e₀ = e₀ᵀ M⁻¹ e₀`.) -/
theorem equivKernel_weighted_sq_sum {N p : ℕ} {x w : Fin N → ℝ}
    (hM : IsUnit (designMatrix p x w).det) :
    (∑ i, w i * (∑ k, (designMatrix p x w)⁻¹ 0 k * x i ^ (k : ℕ)) ^ 2)
      = (designMatrix p x w)⁻¹ 0 0 := by
  let M : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ := designMatrix p x w
  have hMinv : M⁻¹ * M = 1 := by
    rw [Matrix.nonsing_inv_mul]
    simpa only [M] using hM
  calc
    (∑ i, w i * (∑ k, (designMatrix p x w)⁻¹ 0 k * x i ^ (k : ℕ)) ^ 2)
        = ∑ i, w i * ((∑ k, M⁻¹ 0 k * x i ^ (k : ℕ)) *
            (∑ l, M⁻¹ 0 l * x i ^ (l : ℕ))) := by
          simp only [M]
          apply Finset.sum_congr rfl
          intro i hi
          rw [sq]
    _ = ∑ k, ∑ l, M⁻¹ 0 k * M⁻¹ 0 l * M k l := by
          calc
            (∑ i, w i * ((∑ k, M⁻¹ 0 k * x i ^ (k : ℕ)) *
                (∑ l, M⁻¹ 0 l * x i ^ (l : ℕ))))
                = ∑ i, ∑ k, ∑ l,
                    w i * ((M⁻¹ 0 k * x i ^ (k : ℕ)) *
                      (M⁻¹ 0 l * x i ^ (l : ℕ))) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [Finset.sum_mul_sum]
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro k hk
                  rw [Finset.mul_sum]
            _ = ∑ k, ∑ i, ∑ l,
                    w i * ((M⁻¹ 0 k * x i ^ (k : ℕ)) *
                      (M⁻¹ 0 l * x i ^ (l : ℕ))) := by
                  rw [Finset.sum_comm]
            _ = ∑ k, ∑ l, ∑ i,
                    w i * ((M⁻¹ 0 k * x i ^ (k : ℕ)) *
                      (M⁻¹ 0 l * x i ^ (l : ℕ))) := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  rw [Finset.sum_comm]
            _ = ∑ k, ∑ l, M⁻¹ 0 k * M⁻¹ 0 l * M k l := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  apply Finset.sum_congr rfl
                  intro l hl
                  calc
                    (∑ i, w i * ((M⁻¹ 0 k * x i ^ (k : ℕ)) *
                        (M⁻¹ 0 l * x i ^ (l : ℕ))))
                        = ∑ i, (M⁻¹ 0 k * M⁻¹ 0 l) *
                            (w i * x i ^ (k : ℕ) * x i ^ (l : ℕ)) := by
                          apply Finset.sum_congr rfl
                          intro i hi
                          ring
                    _ = (M⁻¹ 0 k * M⁻¹ 0 l) *
                        (∑ i, w i * x i ^ (k : ℕ) * x i ^ (l : ℕ)) := by
                          rw [Finset.mul_sum]
                    _ = M⁻¹ 0 k * M⁻¹ 0 l * M k l := by
                          simp only [M, designMatrix]
    _ = ∑ l, (∑ k, M⁻¹ 0 k * M k l) * M⁻¹ 0 l := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro l hl
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = ∑ l, (M⁻¹ * M) 0 l * M⁻¹ 0 l := by
          apply Finset.sum_congr rfl
          intro l hl
          rw [Matrix.mul_apply]
    _ = ∑ l, (1 : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ) 0 l * M⁻¹ 0 l := by
          simp only [hMinv]
    _ = M⁻¹ 0 0 := by
          simp [Matrix.one_apply]

/-- **Leverage bound for the equivalent kernel.** With nonnegative weights bounded by `W`, the
local-polynomial equivalent-kernel weights satisfy `∑ᵢ Sᵢ² ≤ W · (M⁻¹)₀₀`. Combined with
`linearSmoother_variance_le`, this reduces the interior `O((Nh)^{−1/2})` stochastic-error rate
to the single concentration bound `(M⁻¹)₀₀ = O(1/(Nh))`. -/
theorem equivKernelWeight_sq_sum_le {N p : ℕ} {x w : Fin N → ℝ} {W : ℝ}
    (hM : IsUnit (designMatrix p x w).det)
    (hw : ∀ i, 0 ≤ w i) (hwW : ∀ i, w i ≤ W) :
    (∑ i, equivKernelWeight p x w i ^ 2) ≤ W * (designMatrix p x w)⁻¹ 0 0 := by
  let M : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ := designMatrix p x w
  let g : Fin N → ℝ := fun i => ∑ k, M⁻¹ 0 k * x i ^ (k : ℕ)
  have hfactor : ∀ i, equivKernelWeight p x w i = w i * g i := by
    intro i
    calc
      equivKernelWeight p x w i
          = ∑ k, M⁻¹ 0 k * (w i * x i ^ (k : ℕ)) := by
            simp only [equivKernelWeight, M]
      _ = ∑ k, w i * (M⁻¹ 0 k * x i ^ (k : ℕ)) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = w i * g i := by
            simp only [g]
            rw [Finset.mul_sum]
  have hterm :
      ∀ i, equivKernelWeight p x w i ^ 2 ≤ W * (w i * g i ^ 2) := by
    intro i
    have hsq_le : w i ^ 2 ≤ W * w i := by
      nlinarith [hw i, hwW i]
    have hg_nonneg : 0 ≤ g i ^ 2 := sq_nonneg (g i)
    calc
      equivKernelWeight p x w i ^ 2 = (w i * g i) ^ 2 := by
        rw [hfactor i]
      _ = w i ^ 2 * g i ^ 2 := by
        ring
      _ ≤ (W * w i) * g i ^ 2 := by
        exact mul_le_mul_of_nonneg_right hsq_le hg_nonneg
      _ = W * (w i * g i ^ 2) := by
        ring
  have hweighted : (∑ i, w i * g i ^ 2) = M⁻¹ 0 0 := by
    simpa only [g, M] using
      (equivKernel_weighted_sq_sum (N := N) (p := p) (x := x) (w := w) hM)
  calc
    (∑ i, equivKernelWeight p x w i ^ 2)
        ≤ ∑ i, W * (w i * g i ^ 2) := by
          exact Finset.sum_le_sum (fun i hi => hterm i)
    _ = W * (∑ i, w i * g i ^ 2) := by
          rw [Finset.mul_sum]
    _ = W * M⁻¹ 0 0 := by
          rw [hweighted]
    _ = W * (designMatrix p x w)⁻¹ 0 0 := by
          simp only [M]

/-- **Cauchy–Schwarz leverage bound for the equivalent kernel.** The `ℓ¹` leverage of the
equivalent-kernel weights is controlled by the product of the `(0,0)` entries of the design
moment matrix and its inverse:
`(∑ᵢ |Sᵢ|)² ≤ M₀₀ · (M⁻¹)₀₀`,
where `M₀₀ = ∑ᵢ wᵢ` is the total weight. (Cauchy–Schwarz on `Sᵢ = wᵢ gᵢ` split as
`√wᵢ · √wᵢ gᵢ`, using `∑ᵢ wᵢ gᵢ² = (M⁻¹)₀₀`.) Together with `equivKernelWeight_sq_sum_le` this
reduces *both* the bias leverage `∑ᵢ|Sᵢ|` and the variance leverage `∑ᵢ Sᵢ²` to the design
quantities `M₀₀` and `(M⁻¹)₀₀`. -/
theorem equivKernelWeight_abs_sum_sq_le {N p : ℕ} {x w : Fin N → ℝ}
    (hM : IsUnit (designMatrix p x w).det) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, |equivKernelWeight p x w i|) ^ 2
      ≤ (designMatrix p x w) 0 0 * (designMatrix p x w)⁻¹ 0 0 := by
  let M : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ := designMatrix p x w
  let g : Fin N → ℝ := fun i => ∑ k, M⁻¹ 0 k * x i ^ (k : ℕ)
  have hfactor : ∀ i, equivKernelWeight p x w i = w i * g i := by
    intro i
    calc
      equivKernelWeight p x w i
          = ∑ k, M⁻¹ 0 k * (w i * x i ^ (k : ℕ)) := by
            simp only [equivKernelWeight, M]
      _ = ∑ k, w i * (M⁻¹ 0 k * x i ^ (k : ℕ)) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = w i * g i := by
            simp only [g]
            rw [Finset.mul_sum]
  have habs : ∀ i, |equivKernelWeight p x w i| = w i * |g i| := by
    intro i
    rw [hfactor i, abs_mul, abs_of_nonneg (hw i)]
  have hM00 : M 0 0 = ∑ i, w i := by
    simp [M, designMatrix]
  have hweighted : (∑ i, w i * g i ^ 2) = M⁻¹ 0 0 := by
    simpa only [g, M] using
      (equivKernel_weighted_sq_sum (N := N) (p := p) (x := x) (w := w) hM)
  have hleft :
      (∑ i, Real.sqrt (w i) * (Real.sqrt (w i) * |g i|))
        = ∑ i, |equivKernelWeight p x w i| := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      Real.sqrt (w i) * (Real.sqrt (w i) * |g i|)
          = (Real.sqrt (w i) * Real.sqrt (w i)) * |g i| := by
            ring
      _ = w i * |g i| := by
            rw [Real.mul_self_sqrt (hw i)]
      _ = |equivKernelWeight p x w i| := (habs i).symm
  have hfirst :
      (∑ i, Real.sqrt (w i) ^ 2) = M 0 0 := by
    calc
      (∑ i, Real.sqrt (w i) ^ 2) = ∑ i, w i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Real.sq_sqrt (hw i)
      _ = M 0 0 := hM00.symm
  have hsecond :
      (∑ i, (Real.sqrt (w i) * |g i|) ^ 2) = M⁻¹ 0 0 := by
    calc
      (∑ i, (Real.sqrt (w i) * |g i|) ^ 2)
          = ∑ i, w i * g i ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            calc
              (Real.sqrt (w i) * |g i|) ^ 2
                  = Real.sqrt (w i) ^ 2 * |g i| ^ 2 := by
                    ring
              _ = w i * g i ^ 2 := by
                    rw [Real.sq_sqrt (hw i), sq_abs]
      _ = M⁻¹ 0 0 := hweighted
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin N => Real.sqrt (w i))
    (fun i : Fin N => Real.sqrt (w i) * |g i|)
  rw [hleft, hfirst, hsecond] at hcs
  simpa only [M] using hcs

end Causalean.Stat.Nonparametric
