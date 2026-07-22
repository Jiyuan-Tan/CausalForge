/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.LeastSquares.SmootherBias
import Causalean.Stat.Nonparametric.LocalPoly.Weights

/-!
# Interior local-polynomial bias `O(h^β)`

Bias bounds for interior local-polynomial regression, combining equivalent-kernel polynomial
reproduction with the Hölder–Taylor remainder.

This file assembles the deterministic bias estimate for the interior local-polynomial
regression estimator (Fan–Gijbels 1996 §3.1; Tsybakov 2009 Ch. 1) from its building blocks:

* `wls_intercept_eq_equivKernelSmoother` — the fitted intercept is the equivalent-kernel
  linear smoother `c₀ = ∑ᵢ Sᵢ f(aᵢ)`;
* `equivKernelWeight_reproduces` — those weights reproduce polynomials up to degree
  `p = holderDerivOrder β`;
* `linearSmoother_bias_window` — a polynomial-reproducing smoother whose design lies within
  bandwidth `h` has bias `≤ (M/p!)·(∑ᵢ|Sᵢ|)·h^β`.

The result: the degree-`p` local-polynomial intercept fitted to a `β`-Hölder regression
function `f` (noise-free responses `Yᵢ = f(aᵢ)`), with an invertible weighted design moment
matrix and design points within bandwidth `h` of the target `t`, has bias

`|c₀ − f t| ≤ (M/p!)·(∑ᵢ |Sᵢ|)·h^β`,

i.e. `O(h^β)` once the leverage `∑ᵢ|Sᵢ|` is controlled by the design density.
-/

namespace Causalean.Stat.Nonparametric

open scoped BigOperators

/-- **Interior local-polynomial bias is `O(h^β)`.** Let `c` be the degree
`p = holderDerivOrder β` weighted
least-squares fit (weights `wᵢ ≥ 0`) of a `β`-Hölder function `f` at noise-free responses
`f(aᵢ)`, with an invertible weighted design moment matrix and all design points within the
bandwidth `h` of `t` (`|aᵢ − t| ≤ h`). Then the fitted intercept `c 0` estimates `f t` with
bias `|c 0 − f t| ≤ (M/p!)·(∑ᵢ |Sᵢ|)·h^β`, where `Sᵢ` are the local-polynomial
equivalent-kernel weights. Bounding the leverage `∑ᵢ|Sᵢ|` by a design-density constant gives
the textbook `O(h^β)` interior bias. -/
theorem localPoly_intercept_bias {N : ℕ} {β M lo hi t h : ℝ} {a w : Fin N → ℝ}
    {f : ℝ → ℝ} {c : Fin ((holderDerivOrder β) + 1) → ℝ}
    (hβ : 0 < β) (hM : 0 ≤ M)
    (hw : ∀ i, 0 ≤ w i)
    (ht : t ∈ Set.Icc lo hi) (ha : ∀ i, a i ∈ Set.Icc lo hi)
    (hwin : ∀ i, |a i - t| ≤ h)
    (hf : ContDiff ℝ (holderDerivOrder β) f)
    (hb : ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
            |iteratedDeriv (holderDerivOrder β) f x - iteratedDeriv (holderDerivOrder β) f y|
              ≤ M * |x - y| ^ (β - ((holderDerivOrder β) : ℝ)))
    (hMdet : IsUnit (designMatrix (holderDerivOrder β) (fun i => a i - t) w).det)
    (hmin : ∀ c' : Fin ((holderDerivOrder β) + 1) → ℝ,
        (∑ i, w i * (f (a i) - ∑ j, c j * (a i - t) ^ (j : ℕ)) ^ 2)
          ≤ ∑ i, w i * (f (a i) - ∑ j, c' j * (a i - t) ^ (j : ℕ)) ^ 2) :
    |c 0 - f t|
      ≤ (M / ((holderDerivOrder β)).factorial)
          * (∑ i, |equivKernelWeight (holderDerivOrder β) (fun i => a i - t) w i|) * h ^ β := by
  have hc0 : c 0 = ∑ i, equivKernelWeight (holderDerivOrder β) (fun i => a i - t) w i * f (a i) :=
    wls_intercept_eq_equivKernelSmoother (x := fun i => a i - t) (w := w)
      (Y := fun i => f (a i)) hw hMdet hmin
  have hrep : ∀ k : ℕ, k ≤ (holderDerivOrder β) →
      (∑ i, equivKernelWeight (holderDerivOrder β) (fun i => a i - t) w i * (a i - t) ^ k)
        = if k = 0 then 1 else 0 :=
    equivKernelWeight_reproduces hMdet
  rw [hc0]
  exact linearSmoother_bias_window hβ hM ht ha hwin hf hb hrep

end Causalean.Stat.Nonparametric
