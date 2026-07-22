/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Coordinates of a Euclidean gradient as directional derivatives

A single bridge lemma: the `a`-th coordinate of the (Riesz) gradient of a real-valued function on a
finite-dimensional Euclidean space equals the ordinary one-variable derivative of the function along
the `a`-th coordinate line. This is the standard tool for computing a gradient coordinate by
coordinate — reduce each entry to a `deriv` of a one-parameter restriction, which the univariate
calculus API can then evaluate.
-/

open InnerProductSpace

namespace Causalean.Mathlib

/-- **Gradient coordinate as a directional derivative.** For a function `f` on a finite-dimensional
Euclidean space that is differentiable at `x`, the `a`-th coordinate of its gradient at `x` equals
the derivative at `0` of the one-variable restriction `t ↦ f(x + t · eₐ)` along the `a`-th standard
basis direction. -/
lemma gradient_coord_eq_deriv {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (a : Fin n)
    (hf : DifferentiableAt ℝ f x) :
    (gradient f x) a =
      deriv (fun t : ℝ => f (x + t • EuclideanSpace.single a (1 : ℝ))) 0 := by
  have hinner : ⟪EuclideanSpace.single a (1 : ℝ), gradient f x⟫_ℝ =
      fderiv ℝ f x (EuclideanSpace.single a (1 : ℝ)) := by
    rw [real_inner_comm]
    exact inner_gradient_left (𝕜 := ℝ) (f := f) (x := x)
      (y := EuclideanSpace.single a (1 : ℝ)) hf
  have hline :
      HasDerivAt
        (fun t : ℝ => x + t • EuclideanSpace.single a (1 : ℝ))
        (EuclideanSpace.single a (1 : ℝ)) 0 := by
    simpa using
      (((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single a (1 : ℝ))).const_add x)
  have hderiv :
      HasDerivAt
        (fun t : ℝ => f (x + t • EuclideanSpace.single a (1 : ℝ)))
        (fderiv ℝ f x (EuclideanSpace.single a (1 : ℝ))) 0 := by
    have hf' :
        HasFDerivAt f (fderiv ℝ f x)
          (x + (0 : ℝ) • EuclideanSpace.single a (1 : ℝ)) := by
      simpa using hf.hasFDerivAt
    exact hf'.comp_hasDerivAt (0 : ℝ) hline
  calc
    (gradient f x) a = ⟪EuclideanSpace.single a (1 : ℝ), gradient f x⟫_ℝ := by
      have hs :
          ⟪EuclideanSpace.single a (1 : ℝ), gradient f x⟫_ℝ = (gradient f x) a := by
        simpa using EuclideanSpace.inner_single_left a (1 : ℝ) (gradient f x)
      exact hs.symm
    _ = fderiv ℝ f x (EuclideanSpace.single a (1 : ℝ)) := hinner
    _ = deriv (fun t : ℝ => f (x + t • EuclideanSpace.single a (1 : ℝ))) 0 :=
      hderiv.deriv.symm

end Causalean.Mathlib
