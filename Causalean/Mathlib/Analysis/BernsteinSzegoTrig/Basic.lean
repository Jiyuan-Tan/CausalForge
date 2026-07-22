/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib

/-!
# Bernstein / Szegő trigonometric transform: definitions and derivative

For a real polynomial `R` the function `t ↦ R(cos t)` is the *even trigonometric
transform* of `R`.  This file records the elementary, fully-proved facts about
this transform that feed the sharp Szegő differential inequality
(`Causalean.Mathlib.Analysis.BernsteinSzegoTrig.Szego`):

* `hasDerivAt_cosComp`, `deriv_cosComp` — the chain-rule derivative
  `d/dt R(cos t) = R'(cos t) · (-sin t)`.

Everything here is a direct consequence of `Polynomial.hasDerivAt`,
`Real.hasDerivAt_cos` and the composition rule; no deep input is used.

## Standard reference
Szegő's / Bernstein's inequality for trigonometric polynomials; Rivlin,
*The Chebyshev Polynomials* (1974); DeVore–Lorentz, *Constructive Approximation*
Ch. 4.
-/

open Real Polynomial

namespace Causalean.Mathlib.Analysis.BernsteinSzegoTrig

/-- The composite `t ↦ R(cos t)` has derivative `R'(cos t) · (-sin t)` at every
point `t`.  This is the chain rule for the polynomial evaluation `x ↦ R.eval x`
(whose derivative is `R.derivative.eval x`) composed with `Real.cos` (whose
derivative is `-Real.sin`). -/
theorem hasDerivAt_cosComp (R : Polynomial ℝ) (t : ℝ) :
    HasDerivAt (fun s => R.eval (Real.cos s))
      (R.derivative.eval (Real.cos t) * (-Real.sin t)) t := by
  have h1 : HasDerivAt (fun x => Polynomial.eval x R)
      (R.derivative.eval (Real.cos t)) (Real.cos t) := R.hasDerivAt (Real.cos t)
  have h2 : HasDerivAt Real.cos (-Real.sin t) t := Real.hasDerivAt_cos t
  exact h1.comp t h2

/-- The pointwise derivative of `t ↦ R(cos t)` is `R'(cos t) · (-sin t)`. -/
theorem deriv_cosComp (R : Polynomial ℝ) (t : ℝ) :
    deriv (fun s => R.eval (Real.cos s)) t
      = R.derivative.eval (Real.cos t) * (-Real.sin t) :=
  (hasDerivAt_cosComp R t).deriv

end Causalean.Mathlib.Analysis.BernsteinSzegoTrig
