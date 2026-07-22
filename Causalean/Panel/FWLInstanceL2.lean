/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# L²(μ) instantiation of the abstract Frisch–Waugh–Lovell theorem

This file instantiates the abstract, panel-agnostic FWL development of
`Causalean/Mathlib/FWL.lean` on the genuine inner-product space `Lp ℝ 2 μ`
(square-integrable real functions modulo a.e. equality), with a
finite-dimensional nuisance subspace `H`.

It is the **measure-theoretic instance** of the canonical projection layer
(see `doc/basic_concepts/po/estimand_characterization/INTERFACE_canonical_projection.md`):
the cell-indicator nuisance classes used by the conditional-mean estimand
papers (Goodman-Bacon, Sun-Abraham, MTW, Słoczyński) are finite-dimensional
subspaces of `Lp ℝ 2 μ`, so the abstract FWL coefficient, residualized normal
equations, and least-squares optimality apply directly.

Concretely this file:

* provides the `HasOrthogonalProjection` instance for finite-dimensional
  subspaces of `Lp ℝ 2 μ` (free, via completeness of finite-dimensional spaces);
* re-exports the abstract FWL results (`gramResid_mulVec_fwlCoef`,
  `fwlCoef_original_minimizes`, `original_minimizer_eq_fwlCoef_projection`)
  specialized to `Lp ℝ 2 μ`;
* records the `L²` inner-product ↔ integral bridge `inner f g = ∫ f·g dμ`,
  so the abstract `⟨X̃, Y⟩` reads as the population second moment `∫ X̃·Y dμ`
  that the papers manipulate.

This file is the reusable `L²` interface for applying the abstract FWL theorem
to population regression problems: downstream raw-function developments can use
these facts once they have supplied the required bridge from concrete functions
to `Lp` equivalence classes.
-/

import Causalean.Mathlib.FWL
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! # L2 Frisch-Waugh-Lovell Instance

This file instantiates the abstract Frisch-Waugh-Lovell development on
square-integrable real functions under a probability measure. It supplies
orthogonal projections for finite-dimensional nuisance subspaces, identifies
the `Lp` inner product with the corresponding population integral, and exposes
the residualized normal equations, least-squares optimality, and uniqueness
statements for the `L²(μ)` specialization. -/

namespace Causalean
namespace Panel
namespace FWLInstanceL2

open MeasureTheory
open scoped InnerProductSpace BigOperators

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A finite-dimensional subspace of `Lp ℝ 2 μ` admits an orthogonal
projection: it is complete (finite-dimensional over the complete field `ℝ`),
so Mathlib's completeness instance applies. -/
instance hasOrthogonalProjection_of_finiteDimensional
    (H : Submodule ℝ (Lp ℝ 2 μ)) [FiniteDimensional ℝ H] :
    H.HasOrthogonalProjection :=
  inferInstance

/-- **L² inner product = integral pairing.** For two square-integrable real
random variables, the Hilbert-space inner product equals the integral of their
product, independent of the chosen representatives. This is the bridge between
abstract FWL inner products and the population second moments used in estimand
papers. -/
theorem inner_eq_integral (f g : Lp ℝ 2 μ) :
    inner ℝ f g = ∫ a, f a * g a ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
  change inner ℝ (f a) (g a) = f a * g a
  exact mul_comm _ _

section FWL

variable {K : ℕ} (H : Submodule ℝ (Lp ℝ 2 μ)) [FiniteDimensional ℝ H]
  (X : Fin K → Lp ℝ 2 μ) (Y : Lp ℝ 2 μ)

/-- **Residualized normal equations on `L²(μ)`.** The FWL coefficient solves
`gramResid H X *ᵥ fwlCoef H X Y = residInnerVec H X Y` whenever the
residualized Gram matrix is invertible. Specialization of
`Causalean.Mathlib.FWL.gramResid_mulVec_fwlCoef`. -/
theorem gramResid_mulVec_fwlCoef
    (hQ : IsUnit (Causalean.Mathlib.FWL.gramResid H X).det) :
    (Causalean.Mathlib.FWL.gramResid H X).mulVec (Causalean.Mathlib.FWL.fwlCoef H X Y)
      = Causalean.Mathlib.FWL.residInnerVec H X Y :=
  Causalean.Mathlib.FWL.gramResid_mulVec_fwlCoef H X Y hQ

/-- **FWL least-squares optimality on `L²(μ)`.** The FWL coefficient (paired
with the nuisance projection of its raw residual) minimizes the original
least-squares objective over coefficients and nuisance terms in `H`.
Specialization of `Causalean.Mathlib.FWL.fwlCoef_original_minimizes`. -/
theorem fwlCoef_original_minimizes
    (hQ : IsUnit (Causalean.Mathlib.FWL.gramResid H X).det)
    (β : Fin K → ℝ) {h : Lp ℝ 2 μ} (hh : h ∈ H) :
    Causalean.Mathlib.FWL.originalObjective X Y (Causalean.Mathlib.FWL.fwlCoef H X Y)
        (H.orthogonalProjectionFn
          (Y - Causalean.Mathlib.FWL.fittedValue X (Causalean.Mathlib.FWL.fwlCoef H X Y)))
      ≤ Causalean.Mathlib.FWL.originalObjective X Y β h :=
  Causalean.Mathlib.FWL.fwlCoef_original_minimizes H X Y hQ β hh

/-- **FWL uniqueness on `L²(μ)`.** Every minimizer of the original
least-squares problem has its coefficient block equal to the FWL coefficient.
Specialization of `Causalean.Mathlib.FWL.fwlCoef_eq_of_original_minimizer`. -/
theorem fwlCoef_eq_of_original_minimizer
    (hQ : IsUnit (Causalean.Mathlib.FWL.gramResid H X).det)
    (β : Fin K → ℝ) {h : Lp ℝ 2 μ} (hh : h ∈ H)
    (hmin : ∀ (γ : Fin K → ℝ) {g : Lp ℝ 2 μ}, g ∈ H →
      Causalean.Mathlib.FWL.originalObjective X Y β h
        ≤ Causalean.Mathlib.FWL.originalObjective X Y γ g) :
    β = Causalean.Mathlib.FWL.fwlCoef H X Y :=
  Causalean.Mathlib.FWL.fwlCoef_eq_of_original_minimizer H X Y hQ β hh hmin

end FWL

end FWLInstanceL2
end Panel
end Causalean
