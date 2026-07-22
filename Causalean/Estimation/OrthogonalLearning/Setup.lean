/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Orthogonal Statistical Learning system bundle

`LearningSystem` is the analytic core of the orthogonal statistical-learning
framework: a measurable loss `ℓ : Z → Θ → G → ℝ`, a convex target class with a
distinguished target `θ₀ ∈ Θ_set`, an admissible nuisance class with a
distinguished nuisance `g₀ ∈ G_set`, and the population-risk condition saying
that `θ₀` minimizes the true-nuisance risk over `Θ_set`.  This is the
statistical-learning parallel of `Estimation.OrthogonalMoments.GeneralMoment`:
the identification object is a *loss* (population risk minimization), not a
*moment* (population root finding).

See `doc/basic_concepts/po/estimation/orthogonal_statistical_learning.tex`,
`def:est-osl-system`.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Orthogonal Statistical Learning Setup

This file defines the basic population system for orthogonal statistical
learning: a measurable loss, a convex target class in a Hilbert space, an
admissible nuisance class, and distinguished target and nuisance elements. It
is the loss-based analogue of an orthogonal-moment model.

The central structure is `LearningSystem`. Its namespace provides the population
risk `LearningSystem.L`, and the file also exposes the segment-closure predicates
`Θ_PerturbClosed` and `G_PerturbClosed` used by later directional-derivative
modules. -/

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory

/-- Orthogonal statistical-learning system.

This structure bundles the population law, a convex target class, a nuisance
class, distinguished target and nuisance elements, a measurable loss, and the
condition that the distinguished target minimizes the population risk at the
true nuisance over the target class.

* `Ω, μ`        — ambient probability space carrying the i.i.d. sample.
* `Z, P_Z`      — observation type and population law.
* `Θ, Θ_set`    — target space; `Θ_set` is a convex subset containing `θ₀`.
* `G, G_set`    — nuisance space; `G_set` contains `g₀`.
* `ℓ z θ g`     — loss evaluated at observation `z`, target `θ`,
                  nuisance `g` (note `Z` first, matching the `.tex` file's
                  `ℓ(z; θ, g)`).
* `ℓ_meas`      — joint measurability of `ℓ · θ g` in `z`.
* `θ₀_minimizes` — population-risk minimization of `θ₀` over `Θ_set` at
                   the true nuisance `g₀`. -/
structure LearningSystem
    (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (Z : Type*) [MeasurableSpace Z] (P_Z : MeasureTheory.Measure Z)
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
    (G : Type*) [AddCommGroup G] [Module ℝ G] where
  Θ_set : Set Θ
  Θ_convex  : Convex ℝ Θ_set
  θ₀        : Θ
  θ₀_mem    : θ₀ ∈ Θ_set
  G_set     : Set G
  g₀        : G
  g₀_mem    : g₀ ∈ G_set
  ℓ         : Z → Θ → G → ℝ
  ℓ_meas    : ∀ θ g, Measurable (fun z => ℓ z θ g)
  θ₀_minimizes :
    ∀ θ ∈ Θ_set, ∫ z, ℓ z θ₀ g₀ ∂P_Z ≤ ∫ z, ℓ z θ g₀ ∂P_Z

namespace LearningSystem

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
         {G : Type*} [AddCommGroup G] [Module ℝ G]

/-- Population risk: `L(θ, g) := ∫ ℓ(z; θ, g) dP_Z`. -/
noncomputable def L (S : LearningSystem Ω μ Z P_Z Θ G) (θ : Θ) (g : G) : ℝ :=
  ∫ z, S.ℓ z θ g ∂P_Z

end LearningSystem

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
         {G : Type*} [AddCommGroup G] [Module ℝ G]

/-- Closure-under-perturbation predicate for `Θ_set`: every line segment
between `θ₀` and `θ ∈ Θ_set` stays in `Θ_set`.  Strictly weaker than
convexity; useful for stating directional-derivative hypotheses without
requiring the whole set to be convex. -/
def Θ_PerturbClosed (S : LearningSystem Ω μ Z P_Z Θ G) : Prop :=
  ∀ θ ∈ S.Θ_set, ∀ t ∈ Set.Icc (0 : ℝ) 1, S.θ₀ + t • (θ - S.θ₀) ∈ S.Θ_set

/-- Closure-under-perturbation predicate for `G_set`. -/
def G_PerturbClosed (S : LearningSystem Ω μ Z P_Z Θ G) : Prop :=
  ∀ g ∈ S.G_set, ∀ t ∈ Set.Icc (0 : ℝ) 1, S.g₀ + t • (g - S.g₀) ∈ S.G_set

end OrthogonalLearning
end Estimation
end Causalean
