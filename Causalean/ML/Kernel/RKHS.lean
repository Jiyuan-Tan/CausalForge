/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Reproducing-kernel Hilbert spaces (abstract interface)

Mathlib has no RKHS hierarchy, so `IsRKHS` uses a minimal abstract interface: a
real inner-product space `H` of functions on `X` with an evaluation map and a
representer map satisfying the reproducing property `f x = ⟪f, kₓ⟫`.  This is
the interface consumed by the representer theorem and RKHS Rademacher bounds.
-/

namespace Causalean.ML

/-- The candidate reproducing-kernel Hilbert space structure on a real inner-product space `H` of
functions on `X`, given an evaluation map and a representer map, satisfies the reproducing
property: [evaluating any function of `H` at a point equals its inner product with the
representer of that point](hyp:reproducing). -/
structure IsRKHS (X H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (feval : H → X → ℝ) (representer : X → H) : Prop where
  /-- The reproducing identity `f x = ⟪f, kₓ⟫`. -/
  reproducing : ∀ (f : H) (x : X), feval f x = inner ℝ f (representer x)

end Causalean.ML
