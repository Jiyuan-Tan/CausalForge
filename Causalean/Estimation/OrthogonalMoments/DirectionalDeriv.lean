/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Directional derivative data for an abstract `GeneralMoment`

The `HasDirDeriv` structure packages a pointwise directional derivative
`dM η z` of `m(·, z, θ₀)` along the segment from `η₀` to `η`, together
with the convergence and measurability witnesses required by the DCT
bridge in `NeymanOrthogonal.lean`.

See `docs/superpowers/specs/2026-05-06-general-dml-framework-design.md` §4.2.
-/

import Causalean.Estimation.OrthogonalMoments.MomentFunctional

/-! # Directional Derivatives for Abstract Moments

This file packages the pointwise nuisance directional derivative data required
by the abstract double machine learning framework. The data include convergence
of difference quotients along nuisance line segments and measurability of the
derivative functions. -/

namespace Causalean
namespace Estimation
namespace OrthogonalMoments

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- Pointwise directional derivative of `m(·, z, θ₀)` along the segment from
`η₀` to `η`, packaged with the pointwise tendsto witness and the
measurability of `dM η`. -/
structure HasDirDeriv (M : GeneralMoment Ω μ Z P_Z H) where
  dM : H → Z → ℝ
  pointwise_tendsto  : ∀ η ∈ M.H_ε, ∀ z,
    Tendsto (fun t : ℝ =>
      (M.m (M.η₀ + t • (η - M.η₀)) z M.θ₀ - M.m M.η₀ z M.θ₀) / t)
      (𝓝[≠] 0) (𝓝 (dM η z))
  dM_meas            : ∀ η, Measurable (dM η)

end OrthogonalMoments
end Estimation
end Causalean
