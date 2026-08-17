/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.Approximation.HolderTaylor

/-!
# Bias of a polynomial-reproducing linear smoother

Bias bounds for polynomial-reproducing linear smoothers, converting Hölder–Taylor remainders into
pointwise nonparametric smoothing error bounds.

A *linear smoother* estimates the value of a regression function `f` at a point `t`
by a weighted sum `∑ᵢ Sᵢ f(aᵢ)` of its values at finitely many design points `aᵢ`,
with weights `Sᵢ` that depend only on the design (e.g. the local-polynomial /
Nadaraya–Watson "equivalent kernel" weights). This file proves the deterministic
bias estimate that turns the pointwise Hölder–Taylor remainder
(`holder_taylor_remainder`) into a bias bound for the whole smoother:

if the weights *reproduce polynomials up to degree `p = holderDerivOrder β`* in the sense
`∑ᵢ Sᵢ (aᵢ − t)ᵏ = [k = 0]` for `k ≤ p`, then for a `β`-Hölder `f`

`|∑ᵢ Sᵢ f(aᵢ) − f t| ≤ (M/p!) · ∑ᵢ |Sᵢ| · |aᵢ − t|^β`.

The reproduction hypothesis is exactly the property satisfied by the local-polynomial
weighted-least-squares weights (it is the first block of the normal equations); the
factors `∑ᵢ |Sᵢ| |aᵢ − t|^β` are later bounded via the design density. This lemma is
thus the bias half of the interior local-polynomial estimator analysis
(Fan–Gijbels 1996; Tsybakov 2009 Ch. 1), kept design-agnostic.
-/

namespace Causalean.Stat.Nonparametric

open scoped BigOperators

/-- A linear smoother whose weights reproduce polynomials up to degree `p`
(`∑ᵢ Sᵢ (aᵢ − t)ᵏ = [k = 0]` for `k ≤ p`) reproduces the degree-`p` Taylor polynomial
of `f` at `t` exactly: `∑ᵢ Sᵢ · T_p(aᵢ; t) = f t`. Only the constant term of the Taylor
polynomial survives the reproduction identities. -/
theorem linearSmoother_reproduces_taylorPoly {f : ℝ → ℝ} {t : ℝ} {N : ℕ}
    {a S : Fin N → ℝ} (p : ℕ)
    (hrep : ∀ k : ℕ, k ≤ p → (∑ i, S i * (a i - t) ^ k) = if k = 0 then 1 else 0) :
    (∑ i, S i * taylorPoly p f t (a i)) = f t := by
  have key : (∑ i, S i * taylorPoly p f t (a i))
      = ∑ k ∈ Finset.range (p + 1),
          (iteratedDeriv k f t / (k.factorial : ℝ)) * (∑ i, S i * (a i - t) ^ k) := by
    simp_rw [taylorPoly, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [key]
  have step : (∑ k ∈ Finset.range (p + 1),
        (iteratedDeriv k f t / (k.factorial : ℝ)) * (∑ i, S i * (a i - t) ^ k))
      = ∑ k ∈ Finset.range (p + 1),
          (iteratedDeriv k f t / (k.factorial : ℝ)) * (if k = 0 then (1 : ℝ) else 0) :=
    Finset.sum_congr rfl (fun k hk => by
      rw [hrep k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))])
  rw [step, Finset.sum_eq_single 0]
  · simp [iteratedDeriv_zero]
  · intro k _ hk0; simp [hk0]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos p)) h

/-- **Bias of a polynomial-reproducing linear smoother.** If the weights `Sᵢ` reproduce
polynomials up to degree `p = holderDerivOrder β` at `t`
(`∑ᵢ Sᵢ (aᵢ − t)ᵏ = [k = 0]` for `k ≤ p`), the design points `aᵢ` and `t` lie in a
window `[lo, hi]`, and `f` is `β`-Hölder there (`p`-times continuously
differentiable with `(β−p)`-Hölder top derivative, constant `M`), then the
smoother's bias is controlled by the weighted spread of the design:
`|∑ᵢ Sᵢ f(aᵢ) − f t| ≤ (M/p!) · ∑ᵢ |Sᵢ| · |aᵢ − t|^β`. (Tsybakov 2009, Ch. 1.) -/
theorem linearSmoother_bias_of_reproduces {f : ℝ → ℝ} {β M lo hi t : ℝ} {N : ℕ}
    {a S : Fin N → ℝ}
    (hβ : 0 < β) (hM : 0 ≤ M)
    (ht : t ∈ Set.Icc lo hi) (ha : ∀ i, a i ∈ Set.Icc lo hi)
    (hf : ContDiff ℝ (holderDerivOrder β) f)
    (hb : ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
            |iteratedDeriv (holderDerivOrder β) f x - iteratedDeriv (holderDerivOrder β) f y|
              ≤ M * |x - y| ^ (β - ((holderDerivOrder β) : ℝ)))
    (hrep : ∀ k : ℕ, k ≤ (holderDerivOrder β) →
      (∑ i, S i * (a i - t) ^ k) = if k = 0 then 1 else 0) :
    |∑ i, S i * f (a i) - f t|
      ≤ (M / ((holderDerivOrder β)).factorial) * ∑ i, |S i| * |a i - t| ^ β := by
  have hrep_tay : (∑ i, S i * taylorPoly (holderDerivOrder β) f t (a i)) = f t :=
    linearSmoother_reproduces_taylorPoly (holderDerivOrder β) hrep
  have hdiff : (∑ i, S i * f (a i)) - f t
      = ∑ i, S i * (f (a i) - taylorPoly (holderDerivOrder β) f t (a i)) := by
    rw [← hrep_tay, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_sub]
  rw [hdiff]
  calc |∑ i, S i * (f (a i) - taylorPoly (holderDerivOrder β) f t (a i))|
      ≤ ∑ i, |S i * (f (a i) - taylorPoly (holderDerivOrder β) f t (a i))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |S i| * (M / ((holderDerivOrder β)).factorial * |a i - t| ^ β) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (holder_taylor_remainder hβ hM ht (ha i) hf hb) (abs_nonneg _)
    _ = (M / ((holderDerivOrder β)).factorial) * ∑ i, |S i| * |a i - t| ^ β := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring

/-- **Interior `O(h^β)` bias of a polynomial-reproducing linear smoother.** Let `p` denote
the largest natural number strictly below the smoothness index `β`. If [`β` is
positive](hyp:hβ), [the Hölder constant `M` is nonnegative](hyp:hM), [the target point `t`
lies in a window `[lo,hi]`](hyp:ht), [every design point `aᵢ` lies in the same
window](hyp:ha), [every design point is within bandwidth `h` of `t`](hyp:hwin), [`f` is
`p` times continuously differentiable](hyp:hf), [its `p`-th derivative is `(β−p)`-Hölder
with constant `M` on the window](hyp:hb), and [the smoother weights `S` reproduce
polynomials of degree up to `p` at `t`](hyp:hrep), then [the smoother's bias collapses to
the standard rate `|∑ᵢ Sᵢ f(aᵢ) − f t| ≤ (M/p!) · (∑ᵢ |Sᵢ|) · h^β`](goal).

Bounding the leverage `∑ᵢ |Sᵢ|` by a constant (from the design density) then yields the
textbook `O(h^β)` local-polynomial bias. -/
theorem linearSmoother_bias_window {f : ℝ → ℝ} {β M lo hi t h : ℝ} {N : ℕ}
    {a S : Fin N → ℝ}
    (hβ : 0 < β) (hM : 0 ≤ M)
    (ht : t ∈ Set.Icc lo hi) (ha : ∀ i, a i ∈ Set.Icc lo hi)
    (hwin : ∀ i, |a i - t| ≤ h)
    (hf : ContDiff ℝ (holderDerivOrder β) f)
    (hb : ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
            |iteratedDeriv (holderDerivOrder β) f x - iteratedDeriv (holderDerivOrder β) f y|
              ≤ M * |x - y| ^ (β - ((holderDerivOrder β) : ℝ)))
    (hrep : ∀ k : ℕ, k ≤ (holderDerivOrder β) →
      (∑ i, S i * (a i - t) ^ k) = if k = 0 then 1 else 0) :
    |∑ i, S i * f (a i) - f t|
      ≤ (M / ((holderDerivOrder β)).factorial) * (∑ i, |S i|) * h ^ β := by
  refine le_trans (linearSmoother_bias_of_reproduces hβ hM ht ha hf hb hrep) ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hM (by positivity))
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun i _ => ?_)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (abs_nonneg _) (hwin i) hβ.le) (abs_nonneg _)

end Causalean.Stat.Nonparametric
