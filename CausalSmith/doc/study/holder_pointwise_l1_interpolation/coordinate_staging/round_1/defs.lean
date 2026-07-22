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
# Definitions for multivariate Hölder interpolation

This file supplies the estimand-agnostic objects used by the multivariate Hölder
pointwise-to-local-mass inequality. They can therefore be used in any nonparametric
two-point or Assouad lower bound, independently of a particular causal estimand.

It defines closed sup-norm neighbourhoods, the standard integer-order Hölder-ball
regularity convention, and tensor-product kernels.
-/

namespace Causalean.Stat.Nonparametric

open MeasureTheory
open scoped BigOperators

/-- The closed coordinatewise neighbourhood of radius `r` around a point: every
coordinate differs from its center by at most `r`. -/
def supBall {d : ℕ} (x0 : Fin d → ℝ) (r : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, |x i - x0 i| ≤ r}

/-- The standard multivariate Hölder ball of smoothness `order` and radius `M` on
a domain: derivatives through the highest integer strictly below the smoothness
are continuous and uniformly bounded, and the top derivative has the remaining
Hölder regularity. At an integer smoothness level, this convention requires a
Lipschitz top derivative of one order lower. -/
def HolderBallStd {d : ℕ} (f : (Fin d → ℝ) → ℝ) (order M : ℝ)
    (S : Set (Fin d → ℝ)) : Prop :=
  ContDiffOn ℝ (⌈order⌉₊ - 1) f S ∧
    (∀ j : ℕ, j ≤ ⌈order⌉₊ - 1 → ∀ x ∈ S, ‖iteratedFDeriv ℝ j f x‖ ≤ M) ∧
    (∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ (⌈order⌉₊ - 1) f x - iteratedFDeriv ℝ (⌈order⌉₊ - 1) f y‖
        ≤ M * ‖x - y‖ ^ (order - ((⌈order⌉₊ - 1 : ℕ) : ℝ)))

/-- The multivariate product kernel obtained by multiplying one one-dimensional
kernel factor in each coordinate. -/
def prodKernel (k : ℝ → ℝ) (d : ℕ) : (Fin d → ℝ) → ℝ :=
  fun u => ∏ i : Fin d, k (u i)

end Causalean.Stat.Nonparametric
