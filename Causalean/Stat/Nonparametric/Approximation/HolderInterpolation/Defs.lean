/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Generic multivariate Hölder ball and moment-cancelling product kernel — definitions

This module fixes the *generic* (estimand-agnostic) vocabulary for the Tsybakov
nonparametric-minimax lower-bound primitive
`holder_point_l1_interpolation`: for a function in a multivariate Hölder ball, a
pointwise value forces a local `L¹` mass lower bound via a moment-cancelling
kernel.

The definitions are estimand-agnostic: they apply to any regression or response
function and carry no dependency on a causal-law or treatment-effect type. This
makes the primitive reusable in every Hölder-class two-point or Assouad lower bound.

* `supBall x0 r` — the sup-norm `r`-neighbourhood (closed cube) around `x0`.
* `HolderBallStd f γ M S` — the standard `⌈γ⌉-1`-convention multivariate Hölder
  ball of order `γ`, radius `M`, on `S`.
* `prodKernel k d` — the tensorized product kernel `u ↦ ∏ᵢ k (u i)`.
-/

namespace Causalean.Stat.Nonparametric

open MeasureTheory
open scoped BigOperators

/-- The closed coordinatewise neighbourhood of radius `r` around a point: the cube
containing exactly the covariate values whose every coordinate is within `r` of the
corresponding coordinate of the centre. -/
def supBall {d : ℕ} (x0 : Fin d → ℝ) (r : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, |x i - x0 i| ≤ r}

/-- The standard multivariate Hölder ball of a given smoothness order and radius on
a region: derivatives through the conventional highest order are continuous and
bounded, and the highest derivative changes at the Hölder rate set by that order. -/
def HolderBallStd {d : ℕ} (f : (Fin d → ℝ) → ℝ) (order M : ℝ)
    (S : Set (Fin d → ℝ)) : Prop :=
  ContDiffOn ℝ (⌈order⌉₊ - 1) f S ∧
    (∀ j : ℕ, j ≤ ⌈order⌉₊ - 1 → ∀ x ∈ S, ‖iteratedFDeriv ℝ j f x‖ ≤ M) ∧
    (∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ (⌈order⌉₊ - 1) f x - iteratedFDeriv ℝ (⌈order⌉₊ - 1) f y‖
        ≤ M * ‖x - y‖ ^ (order - ((⌈order⌉₊ - 1 : ℕ) : ℝ)))

/-- The multivariate product kernel obtained by multiplying the same one-dimensional
kernel across all covariate coordinates. -/
def prodKernel (k : ℝ → ℝ) (d : ℕ) : (Fin d → ℝ) → ℝ :=
  fun u => ∏ i : Fin d, k (u i)

end Causalean.Stat.Nonparametric
