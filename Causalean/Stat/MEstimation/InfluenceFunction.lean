/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Influence Functions (data layer)

Light data structure packaging the three properties an influence function
must satisfy: measurability, mean-zero, and finite second moment.  Mirrors
`def:sp-pathwise-diff` from `doc/basic_concepts/Semi-parametric Inference/
semi_parametric_inference.tex` at the *assumption* level: pathwise
differentiability and efficient-influence-function derivations are supplied by
the caller rather than derived in this data-layer structure.

This is the input expected by downstream estimator wrappers when they ask
for an "influence function ψ".  Concrete instances live next to their
estimator (e.g., `Estimation/ATE/AIPWMoment.lean`'s `ψ_AIPW`).
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Influence-function data layer

This module defines `InfluenceFunction`, the basic data-layer predicate for an
influence function under a sampling law.  It records exactly the public
requirements needed by downstream asymptotic-linearity wrappers: measurability,
mean zero, and an integrable squared norm.
-/

namespace Causalean.Stat

open MeasureTheory

variable {X : Type*} [MeasurableSpace X]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- An *influence function* for a parameter `θ ∈ E` under the law `P : Measure X`
is a measurable, mean-zero, square-integrable function `ψ : X → E`.

This is a data structure, not a derivation: the user supplies `ψ` and the
witnesses, and the structure provides a uniform input to estimator
asymptotic-linearity wrappers.  Pathwise differentiability and the EIF
characterisation are deferred. -/
structure InfluenceFunction (P : Measure X) (ψ : X → E) : Prop where
  /-- `ψ` is measurable. -/
  measurable : Measurable ψ
  /-- `ψ` has mean zero under `P`. -/
  mean_zero  : ∫ x, ψ x ∂P = 0
  /-- `ψ` has finite second moment: `‖ψ‖² ∈ L¹(P)`. -/
  finite_var : Integrable (fun x => ‖ψ x‖^2) P

end Causalean.Stat
