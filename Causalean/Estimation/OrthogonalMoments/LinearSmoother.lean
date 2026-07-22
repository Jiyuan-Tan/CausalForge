/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Linear-smoother specialisation of the abstract second-stage regression operator

This file specialises `SecondStageOperator` to *linear smoothers*, i.e.
operators with the concrete form

  `̂E_{n,B}{f(Z) | X = x} = Σ_{i ∈ B(n)} w_{n,i}(x; X_{B(n)}) · f(Z_i)`

(see `def:est-cate-second-stage`). The bundle adds an abstract weight
function; the linear-combination identity is encoded as a separate `Prop`
predicate `IsLinearSmoother` parameterised by the index type, the index set
`B`, the weights `w`, and the data tuples `xs`.

The two main statements proved here are:

* `smoother_bias_holder` — single-function Hölder bound for the smoothed
  bias of `g ∘ z.1`, controlled by the absolute-weight envelope `c_n` and
  the weighted L¹ norm of `g`.
* `smoother_bias_product_holder` — product Hölder bound for cross-product
  bias terms `(g₁ · g₂) ∘ z.1`, with conjugate exponents `1/p + 1/q = 1`.
  Matches Prop `prop:est-cate-linear-smoother-bound`.
-/

import Causalean.Estimation.OrthogonalMoments.SecondStageOperator
import Mathlib.Analysis.MeanInequalities

/-! # Linear Smoother Second-Stage Operators

This file specializes the abstract second-stage regression operator to weighted
linear smoothers. It records the weighted-sum representation and proves
Hölder-type bias bounds for smoothed single functions and products of functions. -/

namespace Causalean
namespace Estimation
namespace OrthogonalMoments

open MeasureTheory Filter Topology Causalean.Stat

/-- Linear-smoother operator (Def `def:est-cate-second-stage`, smoother form).

Extends `SecondStageOperator` with an abstract weight function

  `weights n ω x z = w_{n,i}(x; X_{B(n)})`

where `n : ℕ` is the sample size, `ω : Ω` is the randomness scope (encoding
the data fold), `x : γ` is the query point, and `(z.1, z.2.1, z.2.2)` is the
data tuple `(X_i, A_i, Y_i)`. The third argument is the evaluation point
and the fourth is the data point.

The linear-combination identity `evalAt n ω f x = Σ weights · f(Z_i)` is
NOT enforced as a structure field; see `IsLinearSmoother` below for the
predicate form. -/
structure LinearSmootherOp
    (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    (γ : Type*) [MeasurableSpace γ]
    extends SecondStageOperator Ω μ γ where
  weights : ℕ → Ω → γ → (γ × Bool × ℝ) → ℝ

namespace LinearSmootherOp

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {γ : Type*} [MeasurableSpace γ]

/-- Predicate witnessing that the operator is genuinely a linear smoother:
the value of `evalAt n ω f x` is the weighted sum `Σ_{i ∈ B} w i · f (xs i)`,
where `B : Finset ι` enumerates the data fold, `w : ι → ℝ` provides the
weights, and `xs : ι → γ × Bool × ℝ` provides the data tuples.  The exact
relationship between `w` and `op.weights` is left to the caller.

This is the explicit weighted-sum identity from Def `def:est-cate-second-stage`. -/
def IsLinearSmoother {ι : Type*} (op : LinearSmootherOp Ω μ γ)
    (n : ℕ) (ω : Ω) (x : γ)
    (B : Finset ι) (w : ι → ℝ) (xs : ι → γ × Bool × ℝ) : Prop :=
  ∀ f : γ × Bool × ℝ → ℝ,
    op.evalAt n ω f x = ∑ i ∈ B, w i * f (xs i)

end LinearSmootherOp

/-! ## Weighted empirical norms

The weighted L^p norm `‖g‖_{w,p}` from Prop `prop:est-cate-linear-smoother-bound`:

  `‖g‖_{w,p} = (Σ_{i ∈ B} (|w_i| / Σ_j |w_j|) · |g(X_i)|^p)^{1/p}`.

We parametrize over an abstract index type `ι`, a finset `B : Finset ι`, a
weight function `w : ι → ℝ`, and a function-on-data `g : ι → ℝ`. The exponent
is a real number `p`. Real exponentiation `^` is used (Mathlib's
`Real.rpow`). The factor `|w i| / Σ_j |w_j|` is the normalised weight; the
identity collapses if all weights are zero, which is the trivial regime we
handle at the abstract layer via Mathlib's convention `0 / 0 = 0`. -/

/-- The weighted norm is the normalized absolute-weight empirical norm of a
real-valued function on the sample indices.

$\left(\sum_{i \in B} |w_i|/(\sum_{j \in B}|w_j|)\, |g_i|^p\right)^{1/p}$.
There are no positivity or nonzero-denominator hypotheses in the definition.

This is the weighted L^p norm `‖g‖_{w,p}` from Prop
`prop:est-cate-linear-smoother-bound`. Real exponentiation `^` is Mathlib's
`Real.rpow`. The factor `|w i| / Σ_j |w_j|` is the normalised weight; the
identity collapses if all weights are zero, which is the trivial regime handled
at the abstract layer via Mathlib's convention `0 / 0 = 0`. -/
noncomputable def WeightedNorm
    {ι : Type*} (B : Finset ι) (w : ι → ℝ) (g : ι → ℝ) (p : ℝ) : ℝ :=
  (∑ i ∈ B, |w i| / (∑ j ∈ B, |w j|) * |g i| ^ p) ^ (1 / p)

/-- The weighted norm is non-negative.

Each summand `|w i|/Σ|w_j| * |g i|^p` is non-negative (Real.rpow of a
non-negative base), so the sum is non-negative; rpow of a non-negative base
is non-negative. -/
lemma WeightedNorm_nonneg
    {ι : Type*} (B : Finset ι) (w : ι → ℝ) (g : ι → ℝ) (p : ℝ) :
    0 ≤ WeightedNorm B w g p := by
  unfold WeightedNorm
  refine Real.rpow_nonneg ?_ _
  refine Finset.sum_nonneg ?_
  intro i _
  refine mul_nonneg ?_ (Real.rpow_nonneg (abs_nonneg _) _)
  exact div_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- **Single-function Hölder bound for a linear smoother**.

If the linear-smoother weights have absolute-weight envelope `Σ |w_i| ≤ c_n`,
then for any query point `x : γ` the smoothed bias `op.evalAt n ω (g ∘ z.1) x`
is dominated by `c_n · ‖g ∘ xs.1‖_{w,1}`.

The LaTeX statement is

  ̂E_{n,B}{g(Z) | X = x} ≤ c_n · ‖g‖_{w,1}.

The `g` argument in `evalAt` lives on data tuples `γ × Bool × ℝ`; here we
look at its `γ`-component, hence `(fun z => g z.1)`. -/
theorem smoother_bias_holder
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {γ : Type*} [MeasurableSpace γ] {ι : Type*}
    (op : LinearSmootherOp Ω μ γ)
    (n : ℕ) (ω : Ω) (x : γ) (g : γ → ℝ)
    (B : Finset ι) (w : ι → ℝ) (xs : ι → γ × Bool × ℝ) (c_n : ℝ)
    (hLin : LinearSmootherOp.IsLinearSmoother op n ω x B w xs)
    (hWeights : ∑ i ∈ B, |w i| ≤ c_n) :
    |op.evalAt n ω (fun z => g z.1) x|
      ≤ c_n * WeightedNorm B w (fun i => g (xs i).1) 1 := by
  let S : ℝ := ∑ j ∈ B, |w j|
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hNorm_nonneg : 0 ≤ WeightedNorm B w (fun i => g (xs i).1) 1 :=
    WeightedNorm_nonneg B w (fun i => g (xs i).1) 1
  by_cases hS : S = 0
  · have hw_zero : ∀ i ∈ B, w i = 0 := by
      intro i hi
      have h_abs_zero : |w i| = 0 := by
        have h_each :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (s := B) (f := fun i => |w i|)
            (fun _ _ => abs_nonneg _)).mp hS
        exact h_each i hi
      exact abs_eq_zero.mp h_abs_zero
    have hEval_zero : op.evalAt n ω (fun z => g z.1) x = 0 := by
      rw [hLin (fun z => g z.1)]
      apply Finset.sum_eq_zero
      intro i hi
      simp [hw_zero i hi]
    rw [hEval_zero, abs_zero]
    exact mul_nonneg (le_trans (by simpa [S] using hS_nonneg) hWeights) hNorm_nonneg
  · have hS_pos : 0 < S := lt_of_le_of_ne hS_nonneg (Ne.symm hS)
    have hAbsEval :
        |op.evalAt n ω (fun z => g z.1) x|
          ≤ ∑ i ∈ B, |w i| * |g (xs i).1| := by
      rw [hLin (fun z => g z.1)]
      calc
        |∑ i ∈ B, w i * g (xs i).1|
            ≤ ∑ i ∈ B, |w i * g (xs i).1| :=
          Finset.abs_sum_le_sum_abs (fun i => w i * g (xs i).1) B
        _ = ∑ i ∈ B, |w i| * |g (xs i).1| := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [abs_mul]
    have hWeighted :
        ∑ i ∈ B, |w i| * |g (xs i).1|
          = S * WeightedNorm B w (fun i => g (xs i).1) 1 := by
      unfold WeightedNorm
      simp only [Real.rpow_one, div_one]
      calc
        ∑ i ∈ B, |w i| * |g (xs i).1|
            = ∑ i ∈ B, S * (|w i| / S * |g (xs i).1|) := by
          apply Finset.sum_congr rfl
          intro i hi
          field_simp [hS]
        _ = S * ∑ i ∈ B, |w i| / S * |g (xs i).1| := by
          rw [Finset.mul_sum]
    calc
      |op.evalAt n ω (fun z => g z.1) x|
          ≤ S * WeightedNorm B w (fun i => g (xs i).1) 1 := by
        simpa [hWeighted] using hAbsEval
      _ ≤ c_n * WeightedNorm B w (fun i => g (xs i).1) 1 :=
        mul_le_mul_of_nonneg_right (by simpa [S] using hWeights) hNorm_nonneg

/-- **Product Hölder bound for a linear smoother** (Prop
`prop:est-cate-linear-smoother-bound`).

For `g(z) = g₁(z.1) · g₂(z.1)` and conjugate exponents `1/p + 1/q = 1` (in the
form `Real.HolderConjugate p q`), the smoothed bias of the product is
bounded by

  c_n · ‖g₁‖_{w,p} · ‖g₂‖_{w,q}.

In the DR-Learner application, `g₁` is the propensity error
`hat π_n - π` and `g₂` is the outcome-regression error `hat μ_{a,n} - μ_a`. -/
theorem smoother_bias_product_holder
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {γ : Type*} [MeasurableSpace γ] {ι : Type*}
    (op : LinearSmootherOp Ω μ γ)
    (n : ℕ) (ω : Ω) (x : γ) (g₁ g₂ : γ → ℝ)
    (B : Finset ι) (w : ι → ℝ) (xs : ι → γ × Bool × ℝ) (c_n p q : ℝ)
    (hLin : LinearSmootherOp.IsLinearSmoother op n ω x B w xs)
    (hWeights : ∑ i ∈ B, |w i| ≤ c_n)
    (hConj : Real.HolderConjugate p q) :
    |op.evalAt n ω (fun z => g₁ z.1 * g₂ z.1) x|
      ≤ c_n
        * WeightedNorm B w (fun i => g₁ (xs i).1) p
        * WeightedNorm B w (fun i => g₂ (xs i).1) q := by
  let S : ℝ := ∑ j ∈ B, |w j|
  let α : ι → ℝ := fun i => |w i| / S
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hc_nonneg : 0 ≤ c_n := le_trans (by simpa [S] using hS_nonneg) hWeights
  have hα_nonneg : ∀ i ∈ B, 0 ≤ α i := by
    intro i hi
    exact div_nonneg (abs_nonneg _) hS_nonneg
  have hpq_one : 1 / p + 1 / q = 1 := by
    simpa using hConj.one_div_add_one_div
  have hNormHolder :
      WeightedNorm B w (fun i => g₁ (xs i).1 * g₂ (xs i).1) 1
        ≤ WeightedNorm B w (fun i => g₁ (xs i).1) p
          * WeightedNorm B w (fun i => g₂ (xs i).1) q := by
    have hHolder :=
      Real.inner_le_Lp_mul_Lq_of_nonneg
        (s := B)
        (f := fun i => (α i) ^ (1 / p) * |g₁ (xs i).1|)
        (g := fun i => (α i) ^ (1 / q) * |g₂ (xs i).1|)
        hConj
        (by
          intro i hi
          exact mul_nonneg (Real.rpow_nonneg (hα_nonneg i hi) _) (abs_nonneg _))
        (by
          intro i hi
          exact mul_nonneg (Real.rpow_nonneg (hα_nonneg i hi) _) (abs_nonneg _))
    have hLeft :
        (∑ i ∈ B,
            ((α i) ^ (1 / p) * |g₁ (xs i).1|)
              * ((α i) ^ (1 / q) * |g₂ (xs i).1|))
          = ∑ i ∈ B, α i * |g₁ (xs i).1 * g₂ (xs i).1| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul]
      calc
        ((α i) ^ (1 / p) * |g₁ (xs i).1|)
              * ((α i) ^ (1 / q) * |g₂ (xs i).1|)
            = ((α i) ^ (1 / p) * (α i) ^ (1 / q))
                * (|g₁ (xs i).1| * |g₂ (xs i).1|) := by
          ring
        _ = (α i) ^ (1 / p + 1 / q)
                * (|g₁ (xs i).1| * |g₂ (xs i).1|) := by
          rw [Real.rpow_add_of_nonneg (hα_nonneg i hi)
            hConj.one_div_nonneg hConj.symm.one_div_nonneg]
        _ = α i * (|g₁ (xs i).1| * |g₂ (xs i).1|) := by
          rw [hpq_one, Real.rpow_one]
    have hRight₁ :
        (∑ i ∈ B, ((α i) ^ (1 / p) * |g₁ (xs i).1|) ^ p)
          = ∑ i ∈ B, α i * |g₁ (xs i).1| ^ p := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Real.mul_rpow (Real.rpow_nonneg (hα_nonneg i hi) _) (abs_nonneg _)]
      rw [one_div, Real.rpow_inv_rpow (hα_nonneg i hi) hConj.ne_zero]
    have hRight₂ :
        (∑ i ∈ B, ((α i) ^ (1 / q) * |g₂ (xs i).1|) ^ q)
          = ∑ i ∈ B, α i * |g₂ (xs i).1| ^ q := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Real.mul_rpow (Real.rpow_nonneg (hα_nonneg i hi) _) (abs_nonneg _)]
      rw [one_div, Real.rpow_inv_rpow (hα_nonneg i hi) hConj.symm.ne_zero]
    unfold WeightedNorm
    simp only [Real.rpow_one, div_one]
    change
      (∑ i ∈ B, α i * |g₁ (xs i).1 * g₂ (xs i).1|)
        ≤ (∑ i ∈ B, α i * |g₁ (xs i).1| ^ p) ^ (1 / p)
          * (∑ i ∈ B, α i * |g₂ (xs i).1| ^ q) ^ (1 / q)
    rw [← hLeft, ← hRight₁, ← hRight₂]
    simpa [mul_assoc] using hHolder
  calc
    |op.evalAt n ω (fun z => g₁ z.1 * g₂ z.1) x|
        ≤ c_n * WeightedNorm B w
            (fun i => g₁ (xs i).1 * g₂ (xs i).1) 1 :=
      smoother_bias_holder op n ω x (fun y => g₁ y * g₂ y) B w xs c_n hLin hWeights
    _ ≤ c_n
          * WeightedNorm B w (fun i => g₁ (xs i).1) p
          * WeightedNorm B w (fun i => g₂ (xs i).1) q := by
      have :=
        mul_le_mul_of_nonneg_left hNormHolder hc_nonneg
      simpa [mul_assoc] using this

end OrthogonalMoments
end Estimation
end Causalean
