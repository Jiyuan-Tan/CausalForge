/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Experimentation.DesignBased.DesignCore

/-!
# Finite-sample delta-method identities for the design-based layer

Exact design-mean identities for mean-normalized (Horvitz–Thompson / Hájek) ratio statistics
and their products, computed directly from `FiniteDesign.E`.

These are the finite-design counterpart of the measure-theoretic ratio delta method
(`Causalean.Stat`'s `deltaMethod_ratio`): rather than a limiting distributional statement, they
give the *exact finite-`n`* linearization kernel of a ratio estimator, so a design-based variance
computation never has to leave the `FiniteDesign` world.

* `E_centered_ratio` — a plug-in ratio `X / E[X]` is exactly centered.
* `E_centered_ratio_mul` — the exact covariance of two normalized ratios; the linearization
  kernel for any ratio / Hájek variance.
* `E_lin_expand` — distributes the design mean over a product of two two-term linear forms, the
  bilinear bookkeeping step for a two-arm linearized variance.
* `ratio_remainder_capped_bound` — the capped second-order remainder of a single scaled ratio
  estimator, the per-arm building block of a ratio/Hájek CLT's asymptotic-linearity argument.
-/

open scoped BigOperators

namespace Causalean
namespace Experimentation
namespace DesignBased

/-- **Capped ratio-remainder bound.** Consider a ratio estimator `A / D` of a target `μ`, scaled by
`√n` (here `sn` with `sn² = n`), and let `G = A − μ·D` be the centered numerator. The scaled
second-order remainder `√n·(A/D − μ) − √n⁻¹·G` equals `√n⁻¹·G·(n/D − 1)`, and on the event where the
denominator is at least half its target (equivalently `n/D ≤ 2`) it is bounded by
`2·|√n⁻¹·G|·|n⁻¹·D − 1|`. This is the per-arm remainder control a design-based ratio / Hájek CLT
uses to reduce the studentized estimator to its linear score. -/
lemma ratio_remainder_capped_bound {n sn A D μ G : ℝ}
    (hn : 0 < n) (hsn_sq : sn ^ 2 = n) (hD : 0 < D) (hcap : n / D ≤ 2)
    (hG : G = A - μ * D) :
    |sn * (A / D - μ) - sn⁻¹ * G| ≤ 2 * |sn⁻¹ * G| * |n⁻¹ * D - 1| := by
  have hsn0 : sn ≠ 0 := by
    intro h
    rw [h, pow_two, mul_zero] at hsn_sq
    exact absurd hsn_sq.symm (ne_of_gt hn)
  have hD0 : D ≠ 0 := ne_of_gt hD
  have hrem : sn * (A / D - μ) - sn⁻¹ * G = sn⁻¹ * G * (n / D - 1) := by
    have hquot : A / D - μ = G / D := by
      rw [hG]; field_simp
    rw [hquot]
    field_simp
    rw [hsn_sq]
  have hbound : |sn⁻¹ * G * (n / D - 1)| ≤ 2 * |sn⁻¹ * G| * |n⁻¹ * D - 1| := by
    have hid : n / D - 1 = -((n / D) * (n⁻¹ * D - 1)) := by
      field_simp; ring
    have hnonneg : 0 ≤ n / D := le_of_lt (div_pos hn hD)
    have hratio : |n / D - 1| ≤ 2 * |n⁻¹ * D - 1| := by
      rw [hid, abs_neg, abs_mul, abs_of_nonneg hnonneg]
      exact mul_le_mul_of_nonneg_right hcap (abs_nonneg _)
    rw [abs_mul]
    calc
      |sn⁻¹ * G| * |n / D - 1| ≤ |sn⁻¹ * G| * (2 * |n⁻¹ * D - 1|) :=
        mul_le_mul_of_nonneg_left hratio (abs_nonneg _)
      _ = 2 * |sn⁻¹ * G| * |n⁻¹ * D - 1| := by ring
  rw [hrem]
  exact hbound

namespace FiniteDesign

variable {Ω : Type*} [Fintype Ω] (D : FiniteDesign Ω)

/-- **Centering of a plug-in ratio.** In a finite design, the mean-normalized ratio
`X / E[X] − 1` has design mean zero whenever the mean `E[X]` is nonzero — the first-order
(linearization) fact that a ratio statistic is exactly centered at its plug-in point. -/
lemma E_centered_ratio (X : Ω → ℝ) (a : ℝ) (ha : a ≠ 0) (hEX : D.E X = a) :
    D.E (fun z => X z / a - 1) = 0 := by
  have hpoint : (fun z => X z / a - 1) = (fun z => (1 / a) * X z - 1) := by
    funext z
    ring
  rw [D.E_congr (by intro z; exact congrFun hpoint z)]
  rw [D.E_sub, D.E_const_mul, D.E_const, hEX]
  field_simp [ha]
  ring

/-- **Covariance of two normalized ratios (the ratio linearization kernel).** In a finite design,
the mean of the product of two mean-normalized ratios `(X/E[X] − 1)(Y/E[Y] − 1)` equals
`E[XY] / (E[X]·E[Y]) − 1`. This is the exact second cross-moment at the heart of every
Horvitz–Thompson / Hájek ratio-variance linearization. -/
lemma E_centered_ratio_mul (X Y : Ω → ℝ) (a b c : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hEX : D.E X = a) (hEY : D.E Y = b) (hEXY : D.E (fun z => X z * Y z) = c) :
    D.E (fun z => (X z / a - 1) * (Y z / b - 1)) = c / (a * b) - 1 := by
  have hpoint : (fun z => (X z / a - 1) * (Y z / b - 1)) =
      (fun z => ((1 / (a * b)) * (X z * Y z) - (1 / a) * X z) -
        (1 / b) * Y z + 1) := by
    funext z
    field_simp [ha, hb]
    ring
  rw [D.E_congr (by intro z; exact congrFun hpoint z)]
  rw [D.E_add, D.E_sub, D.E_sub, D.E_const_mul, D.E_const_mul, D.E_const_mul, D.E_const]
  rw [hEX, hEY, hEXY]
  field_simp [ha, hb]
  ring

/-- **Bilinear expansion of a design mean.** In a finite design, the mean of a product of two
two-term linear forms `(A·ai − B·bi)(C·aj − F·bj)` expands, via the four pairwise cross-moments
`E[AC], E[AF], E[BC], E[BF]`, to `AA·ai·aj − AB·ai·bj − BA·bi·aj + BB·bi·bj`. This is the generic
bookkeeping step assembling a two-arm (e.g. treated/control) linearized variance from its
component moments. -/
lemma E_lin_expand (A B C F : Ω → ℝ) (ai bi aj bj AA AB BA BB : ℝ)
    (hAA : D.E (fun z => A z * C z) = AA)
    (hAB : D.E (fun z => A z * F z) = AB)
    (hBA : D.E (fun z => B z * C z) = BA)
    (hBB : D.E (fun z => B z * F z) = BB) :
    D.E (fun z => (A z * ai - B z * bi) * (C z * aj - F z * bj))
      = AA * ai * aj - AB * ai * bj - BA * bi * aj + BB * bi * bj := by
  have hpoint : (fun z => (A z * ai - B z * bi) * (C z * aj - F z * bj)) =
      (fun z => ((ai * aj) * (A z * C z) - (ai * bj) * (A z * F z)) -
        (bi * aj) * (B z * C z) + (bi * bj) * (B z * F z)) := by
    funext z
    ring
  rw [D.E_congr (by intro z; exact congrFun hpoint z)]
  rw [D.E_add, D.E_sub, D.E_sub]
  repeat rw [D.E_const_mul]
  rw [hAA, hAB, hBA, hBB]
  ring

end FiniteDesign
end DesignBased
end Experimentation
end Causalean
