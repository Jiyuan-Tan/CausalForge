/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Neyman orthogonality of moment functionals

The `NeymanOrthogonal` predicate matching `def:est-neyman` in
`doc/basic_concepts/po/estimation.tex`: a moment functional
`m : H × X × ℝ → ℝ` is Neyman-orthogonal at `(η₀, θ₀)` if (a) the moment
condition `∫ m(η₀, x, θ₀) dP = 0` holds and (b) the Gâteaux derivative of
`η ↦ ∫ m(η, x, θ₀) dP` at `η₀` vanishes in every direction.

The nuisance space `H` is treated abstractly as a real vector space; concrete
instantiations are deferred to the project-specific estimation files
(`Causalean/Estimation/...`).
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-! # Neyman Orthogonality

This file defines Neyman orthogonality for population moment functionals with an
abstract nuisance space. The condition combines the population moment equation
at the target value with the requirement that every nuisance-direction
derivative of the population moment vanishes at the reference nuisance value. -/

namespace Causalean.Stat

open MeasureTheory Filter Topology

variable {H X : Type*} [AddCommGroup H] [Module ℝ H] [MeasurableSpace X]

/-- Neyman orthogonality of a moment functional `m : H → X → ℝ → ℝ` at
nuisance value `η₀ : H` and target value `θ₀ : ℝ`, with respect to the
population measure `P : Measure X`.

Two conjuncts:

1. **Moment condition.** `∫ m η₀ x θ₀ dP = 0`.
2. **Vanishing Gâteaux derivative.** For every direction `η : H`, the
   one-dimensional curve `t ↦ η₀ + t • (η − η₀)` perturbs the population
   moment only at second order in `t`:
   `lim_{t → 0, t ≠ 0} (∫ m (η₀ + t • (η − η₀)) x θ₀ dP) / t = 0`. -/
def NeymanOrthogonal
    (m : H → X → ℝ → ℝ) (η₀ : H) (θ₀ : ℝ) (P : Measure X) : Prop :=
  (∫ x, m η₀ x θ₀ ∂P) = 0 ∧
  ∀ η : H,
    Tendsto
      (fun t : ℝ => (∫ x, m (η₀ + t • (η - η₀)) x θ₀ ∂P) / t)
      (𝓝[≠] 0) (𝓝 0)

end Causalean.Stat
