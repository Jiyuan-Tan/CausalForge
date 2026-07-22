/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Restricted strong convexity (RSC)

`RestrictedStrongConvexity` packages the σₙ-RSC predicate at the truth `θ₀`
over a support `S₀`: for every `ν` in the restricted cone,

  `empRiskFn (θ₀ + ν) - empRiskFn θ₀ - ⟪∇emp θ₀, ν⟫ ≥ (σₙ/2) * ‖ν‖²`.

The positivity of `σn` is a separate hypothesis that callers thread into
the headline theorem; it is *not* part of this predicate.

See `doc/basic_concepts/po/estimation/orthogonal_statistical_learning.tex`,
`def:est-osl-rsc`.
-/

import Causalean.Estimation.OrthogonalLearning.Sparse.Setup

/-! # Restricted Strong Convexity

This file defines restricted strong convexity for a finite-dimensional empirical
risk at the population target over the restricted cone associated with a support
set. The condition supplies the curvature input in the sparse plug-in
estimation guarantee.

The exported predicate `RestrictedStrongConvexity` states that the empirical
risk lies above its first-order approximation at `θ₀` by a quadratic margin on
`RestrictedCone S₀`; positivity of the curvature parameter is supplied by
callers. -/

namespace Causalean
namespace Estimation
namespace OrthogonalLearning
namespace Sparse

open scoped BigOperators RealInnerProductSpace

variable {p : ℕ}

/-- σₙ-restricted strong convexity of `empRiskFn` at `θ₀` over `S₀`.

For every `ν ∈ RestrictedCone S₀`,
`empRiskFn (θ₀ + ν) - empRiskFn θ₀ - ⟪∇emp θ₀, ν⟫ ≥ (σn/2) * ‖ν‖²`. -/
def RestrictedStrongConvexity
    (empRiskFn : EuclideanSpace ℝ (Fin p) → ℝ)
    (gradEmp : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (θ₀ : EuclideanSpace ℝ (Fin p))
    (S₀ : Finset (Fin p))
    (σn : ℝ) : Prop :=
  ∀ ν ∈ RestrictedCone S₀,
    empRiskFn (θ₀ + ν) - empRiskFn θ₀ - inner ℝ (gradEmp θ₀) ν
      ≥ (σn / 2) * ‖ν‖ ^ 2

end Sparse
end OrthogonalLearning
end Estimation
end Causalean
