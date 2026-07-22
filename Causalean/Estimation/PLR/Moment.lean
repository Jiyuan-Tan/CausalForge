/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The partially linear (Robinson partialling-out) orthogonal score

This file defines the Neyman-orthogonal moment for the partially linear model —
the Robinson (1988) partialling-out score — over the observed-data triple
`z = (x, d, y) : γ × ℝ × ℝ`, with nuisance `η = (ℓ, m)` a pair of measurable
covariate functions (outcome regression `ℓ` and treatment regression `m`):

    ψ(η, z, θ) = (y − ℓ(x) − θ·(d − m(x)))·(d − m(x)).

It is a *linear score* in the target `θ`: with the treatment residual
`v = d − m(x)`,

    ψ(η, z, θ) = m_a(η, z)·θ + m_b(η, z),   m_a = −v²,  m_b = (y − ℓ(x))·v.

* `plrResidual` — the treatment residual `d − m(x)`.
* `plrMomentFunctional`, `plrMomentA`, `plrMomentB` — the score and its linear
  decomposition; `plrMoment_decomp` is `ψ = m_a·θ + m_b`.
* `measurable_plrMomentFunctional`, `measurable_plrMomentA/B` — measurability in
  the data (the nuisance carries its own measurability).
-/

import Causalean.Estimation.PLR.Nuisance

/-! # Partially linear orthogonal score

This file provides the partialling-out moment functional for the partially
linear model, its decomposition into the linear-in-parameter form, and the
measurability of these maps in the data. The score is linear in the structural
slope, with coefficient minus the squared treatment residual and constant term
given by the residualized outcome times the treatment residual. -/

namespace Causalean
namespace Estimation
namespace PLR

open MeasureTheory

variable {γ : Type*} [MeasurableSpace γ]

/-- The treatment residual subtracts the nuisance treatment regression from the
observed treatment value. -/
def plrResidual (η : PLRNuisance γ) (z : γ × ℝ × ℝ) : ℝ := z.2.1 - η.mFn z.1

/-- The Robinson partialling-out score multiplies the structural residualized
outcome by the treatment residual. -/
def plrMomentFunctional (η : PLRNuisance γ) (z : γ × ℝ × ℝ) (θ : ℝ) : ℝ :=
  (z.2.2 - η.lFn z.1 - θ * plrResidual η z) * plrResidual η z

/-- The linear-score coefficient is minus the squared treatment residual. -/
def plrMomentA (η : PLRNuisance γ) (z : γ × ℝ × ℝ) : ℝ :=
  -(plrResidual η z) ^ 2

/-- The linear-score constant term is the residualized outcome times the
treatment residual. -/
def plrMomentB (η : PLRNuisance γ) (z : γ × ℝ × ℝ) : ℝ :=
  (z.2.2 - η.lFn z.1) * plrResidual η z

/-- The Robinson score decomposes into a coefficient times the target parameter
plus a constant term. -/
lemma plrMoment_decomp (η : PLRNuisance γ) (z : γ × ℝ × ℝ) (θ : ℝ) :
    plrMomentFunctional η z θ = plrMomentA η z * θ + plrMomentB η z := by
  simp only [plrMomentFunctional, plrMomentA, plrMomentB]
  ring

/-- The treatment residual is measurable as a function of the observed data. -/
lemma measurable_plrResidual (η : PLRNuisance γ) :
    Measurable (fun z : γ × ℝ × ℝ => plrResidual η z) :=
  (measurable_fst.comp measurable_snd).sub (η.mMeas.comp measurable_fst)

/-- The Robinson partialling-out score is measurable in the observed data. -/
lemma measurable_plrMomentFunctional (η : PLRNuisance γ) (θ : ℝ) :
    Measurable (fun z : γ × ℝ × ℝ => plrMomentFunctional η z θ) := by
  have hv := measurable_plrResidual η
  have hy : Measurable (fun z : γ × ℝ × ℝ => z.2.2) :=
    measurable_snd.comp measurable_snd
  exact (((hy.sub (η.lMeas.comp measurable_fst)).sub (hv.const_mul θ)).mul hv)

/-- The linear-score coefficient is measurable in the observed data. -/
lemma measurable_plrMomentA (η : PLRNuisance γ) :
    Measurable (fun z : γ × ℝ × ℝ => plrMomentA η z) := by
  have hv := measurable_plrResidual η
  exact (hv.pow_const 2).neg

/-- The linear-score constant term is measurable in the observed data. -/
lemma measurable_plrMomentB (η : PLRNuisance γ) :
    Measurable (fun z : γ × ℝ × ℝ => plrMomentB η z) := by
  have hv := measurable_plrResidual η
  have hy : Measurable (fun z : γ × ℝ × ℝ => z.2.2) :=
    measurable_snd.comp measurable_snd
  exact (hy.sub (η.lMeas.comp measurable_fst)).mul hv

end PLR
end Estimation
end Causalean
