/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# TRAE-DR estimator (one-shot split)

The one-shot TRAE doubly robust estimator from `def:est-trae-dr-estimator`
in `doc/basic_concepts/po/estimation/trae_inverse_problems.tex`:

    θ̂ⁿ_TRAE-DR := (1/|B(n)|) Σ_{i ∈ B(n)} φ_{ĥ_n, q̂_n}(W_i),

where `(ĥ_n, q̂_n)` are nuisances trained only on the fold-A subsample
`A(n)`, and `φ_{h, q}(w) := m_e(w; h) + m(w; q) - q(z) h(x)` is the
pointwise pseudo-outcome from `InverseProblemSystem.phiVal`
(`Causalean/Estimation/NPIV/Setup.lean`).

This file defines only the estimator.  Asymptotic linearity is in
`AsymptoticLinear.lean`; asymptotic normality + Wald coverage are in
`AsymptoticNormal.lean`.
-/

import Causalean.Estimation.NPIV.Setup
import Causalean.Stat.Sample
import Causalean.Stat.SampleSplit

/-!
Defines estimator-level helpers and local instances for the doubly robust NPIV
development. The module exposes sample, measure, and inverse-problem-system
fields in the form used by the DR rate and limit theorems.
-/

namespace Causalean
namespace Estimation
namespace NPIV
namespace DR

open MeasureTheory Causalean.Stat

/-! ## Local instance helpers

Expose the `InverseProblemSystem` measurable-space fields as scoped
instances so the rest of the `DR` namespace can use plain (non-`@`)
syntax for `Measure S.𝒲`, `Integrable`, `IIDSample`, `OneShotSplit`,
`IsAsymLinear`, and `IsProbabilityMeasure`. -/

/-- The observation space carries the measurable space stored in the inverse
problem system. -/
scoped instance instMeasurableSpace_𝒲
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : InverseProblemSystem Ω μ) : MeasurableSpace S.𝒲 := S.inst𝒲

/-- The covariate space carries the measurable space stored in the inverse
problem system. -/
scoped instance instMeasurableSpace_𝒳
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : InverseProblemSystem Ω μ) : MeasurableSpace S.𝒳 := S.inst𝒳

/-- The instrument space carries the measurable space stored in the inverse
problem system. -/
scoped instance instMeasurableSpace_𝒵
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : InverseProblemSystem Ω μ) : MeasurableSpace S.𝒵 := S.inst𝒵

/-- One-shot **TRAE doubly robust estimator** (`def:est-trae-dr-estimator`):

    θ̂ⁿ_TRAE-DR := (1/|B(n)|) Σ_{i ∈ B(n)} φ_{ĥ_n, q̂_n}(W_i),

where `W_i = sample.Z i ω` and `φ_{h, q}` is `InverseProblemSystem.phiVal`.
The nuisances `ĥ_n n ω : 𝒳 → ℝ` and `q̂_n n ω : 𝒵 → ℝ` are random
functions (depending on `(n, ω)`) that, in applications, are trained only
on `A(n)`. -/
noncomputable def trae_dr_estimator
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : InverseProblemSystem Ω μ)
    {P_W : Measure S.𝒲}
    (sample : IIDSample Ω S.𝒲 μ P_W)
    (split : OneShotSplit sample)
    (h_hat : ℕ → Ω → (S.𝒳 → ℝ))
    (q_hat : ℕ → Ω → (S.𝒵 → ℝ))
    (n : ℕ) (ω : Ω) : ℝ :=
  ((split.foldB n).card : ℝ)⁻¹ *
    ∑ i ∈ split.foldB n, S.phiVal (h_hat n ω) (q_hat n ω) (sample.Z i ω)

/-- The estimator equals the average of `φ_{ĥ_n, q̂_n}` over `B(n)`. -/
lemma trae_dr_estimator_eq_avg_phi
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : InverseProblemSystem Ω μ)
    {P_W : Measure S.𝒲}
    (sample : IIDSample Ω S.𝒲 μ P_W)
    (split : OneShotSplit sample)
    (h_hat : ℕ → Ω → (S.𝒳 → ℝ))
    (q_hat : ℕ → Ω → (S.𝒵 → ℝ))
    (n : ℕ) (ω : Ω) :
    trae_dr_estimator S sample split h_hat q_hat n ω
      = ((split.foldB n).card : ℝ)⁻¹ *
          ∑ i ∈ split.foldB n,
            S.phiVal (h_hat n ω) (q_hat n ω) (sample.Z i ω) := rfl

end DR
end NPIV
end Estimation
end Causalean
