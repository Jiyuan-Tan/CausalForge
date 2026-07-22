/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Automatic debiasing — general moment layer

This file develops the general-moment automatic-debiasing layer for
`doc/basic_concepts/po/estimation/automatic_debiasing.tex`:

* `RegNuisanceMomentSys` — regression-nuisance moment system (extends the
  data + regression infrastructure of `LinRegFnSys` to a general moment
  functional `M` with a precomputed Gateaux derivative `D_g_M`).
* `AutoDebiasRepresenter` — the automatic-debiasing representer
  `α₀ : X → ℝ` characterised by `D_g M(θ₀, g₀)[ν] = ∫ α₀ · γ_target ν dP_X`.
* `autoDebiasedScore`, `autoDebiasedMoment` — the debiased score and its
  population moment.
* Three orthogonality lemmas: mean-zero plus two directional zeros.
* `genRieszLoss`, `finDiffRieszLoss` — population and finite-difference
  Riesz objectives for fitting the automatic-debiasing representer.

The structure mirrors `LinRegFnSys` (defined in `AutoDebias/Linear.lean`)
but with `m_lin → m` (a moment depending on `θ` as well) and
`L_of_m → D_g_M`.
-/

import Causalean.Estimation.OrthogonalMoments.MomentFunctional
import Causalean.Estimation.OrthogonalMoments.AutoDebias.Linear

/-! # Automatic Debiasing for General Moments

This file extends the automatic-debiasing construction from linear regression
functionals to general scalar moment equations with a regression nuisance. It
packages the moment system, the Riesz-representer correction, and the resulting
orthogonality identities used to build debiased scores, together with
population and finite-difference Riesz objectives for representer fitting. -/

namespace Causalean.Estimation.OrthogonalMoments.AutoDebias

open MeasureTheory

/-- **Regression-nuisance moment system.**

A bundle packaging the data + regression infrastructure of `LinRegFnSys`
together with:

* a scalar parameter truth `θ₀ : ℝ`;
* a population moment functional `M : ℝ × H → ℝ` satisfying
  `M(θ₀, g₀) = 0`;
* a precomputed Gateaux derivative `D_g_M : H → ℝ` representing
  `D_g M(θ₀, g₀)[ν]`;
* an observation-level kernel `m : H → Z → ℝ → ℝ` satisfying
  `M(θ, g) = ∫ m(g, z, θ) dP_Z`.

To keep universe parameters tame, every type, instance, and function is
declared as a field of the structure. -/
structure RegNuisanceMomentSys where
  Z : Type*
  [Z_meas : MeasurableSpace Z]
  P_Z : Measure Z
  [P_Z_prob : IsProbabilityMeasure P_Z]
  X : Type*
  [X_meas : MeasurableSpace X]
  P_X : Measure X
  H : Type*
  [H_addCommGroup : AddCommGroup H]
  [H_module : Module ℝ H]
  proj_X : Z → X
  proj_X_meas : Measurable proj_X
  Y_obs : Z → ℝ
  Y_obs_meas : Measurable Y_obs
  γ_target : H → X → ℝ
  γ_target_add : ∀ (γ₁ γ₂ : H) (x : X),
    γ_target (γ₁ + γ₂) x = γ_target γ₁ x + γ_target γ₂ x
  γ_target_smul : ∀ (c : ℝ) (γ : H) (x : X),
    γ_target (c • γ) x = c * γ_target γ x
  g₀ : H
  θ₀ : ℝ
  M : ℝ → H → ℝ
  M_truth : M θ₀ g₀ = 0
  D_g_M : H → ℝ
  D_g_M_add : ∀ (ν₁ ν₂ : H), D_g_M (ν₁ + ν₂) = D_g_M ν₁ + D_g_M ν₂
  D_g_M_smul : ∀ (c : ℝ) (ν : H), D_g_M (c • ν) = c * D_g_M ν
  m : H → Z → ℝ → ℝ
  m_meas : ∀ g θ, Measurable (fun z => m g z θ)
  m_population : ∀ g θ, M θ g = ∫ z, m g z θ ∂P_Z
  pushforward : P_X = P_Z.map proj_X
  regression_resid_orthog :
    ∀ α : X → ℝ, Measurable α →
      Integrable (fun z => α (proj_X z) * (Y_obs z - γ_target g₀ (proj_X z))) P_Z →
      ∫ z, α (proj_X z) * (Y_obs z - γ_target g₀ (proj_X z)) ∂P_Z = 0

attribute [instance] RegNuisanceMomentSys.Z_meas RegNuisanceMomentSys.P_Z_prob
  RegNuisanceMomentSys.X_meas RegNuisanceMomentSys.H_addCommGroup
  RegNuisanceMomentSys.H_module

/-- **Automatic debiasing representer.**

A measurable, integrable `α₀ : X → ℝ` representing the Gateaux derivative
`D_g M(θ₀, g₀)[ν]` as the `L²(P_X)` inner product
`∫ α₀ · γ_target ν dP_X`. -/
structure AutoDebiasRepresenter (S : RegNuisanceMomentSys) where
  α₀ : S.X → ℝ
  α₀_meas : Measurable α₀
  α₀_integrable : Integrable α₀ S.P_X
  representation : ∀ ν : S.H, S.D_g_M ν = ∫ x, α₀ x * S.γ_target ν x ∂S.P_X

/-- **Automatically debiased score** (observation-level form):

  `m(g, z, θ) + α(proj_X z) · (Y_obs z − γ_target g (proj_X z))`. -/
noncomputable def autoDebiasedScore (S : RegNuisanceMomentSys)
    (g : S.H) (α : S.X → ℝ) (θ : ℝ) (z : S.Z) : ℝ :=
  S.m g z θ + α (S.proj_X z) * (S.Y_obs z - S.γ_target g (S.proj_X z))

/-- **Automatically debiased moment** (population form):

  `∫ z, autoDebiasedScore S g α θ z ∂P_Z`,

equivalently `M(θ, g) + ∫ α(X) · (Y − g(X)) dP_Z`. -/
noncomputable def autoDebiasedMoment (S : RegNuisanceMomentSys)
    (g : S.H) (α : S.X → ℝ) (θ : ℝ) : ℝ :=
  ∫ z, autoDebiasedScore S g α θ z ∂S.P_Z

/-- **Mean-zero of the debiased moment at the truth.** -/
theorem autoDebiasedMoment_meanZero_at_truth (S : RegNuisanceMomentSys)
    (rep : AutoDebiasRepresenter S)
    (h_α₀_resid_int :
      Integrable
        (fun z => rep.α₀ (S.proj_X z) * (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z)))
        S.P_Z)
    (h_int_m_truth : Integrable (fun z => S.m S.g₀ z S.θ₀) S.P_Z) :
    autoDebiasedMoment S S.g₀ rep.α₀ S.θ₀ = 0 := by
  unfold autoDebiasedMoment autoDebiasedScore
  rw [integral_add h_int_m_truth h_α₀_resid_int]
  rw [show ∫ z, S.m S.g₀ z S.θ₀ ∂S.P_Z = 0 by
    have h := S.m_population S.g₀ S.θ₀
    rw [← h, S.M_truth]]
  rw [S.regression_resid_orthog rep.α₀ rep.α₀_meas h_α₀_resid_int]
  ring

/-- **Directional zero in the regression direction.**

The Gateaux derivative of the population debiased moment in the
`g`-direction at the truth equals zero — equivalently, the representer
identity for the perturbation `ν_g`. -/
theorem autoDebiasedMoment_directional_g_zero (S : RegNuisanceMomentSys)
    (rep : AutoDebiasRepresenter S) (ν_g : S.H) :
    S.D_g_M ν_g - ∫ x, rep.α₀ x * S.γ_target ν_g x ∂S.P_X = 0 := by
  have h := rep.representation ν_g
  linarith

/-- **Directional zero in the representer direction.**

For any measurable perturbation `ν_α : X → ℝ` with integrable residual
product, the directional derivative of the population debiased moment in
the `α`-direction at the truth vanishes. -/
theorem autoDebiasedMoment_directional_α_zero (S : RegNuisanceMomentSys)
    (ν_α : S.X → ℝ) (hν_α_meas : Measurable ν_α)
    (h_int :
      Integrable
        (fun z => ν_α (S.proj_X z) * (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z)))
        S.P_Z) :
    ∫ z, ν_α (S.proj_X z) * (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z)) ∂S.P_Z = 0 := by
  exact S.regression_resid_orthog ν_α hν_α_meas h_int

/-- **General Riesz loss.**

The loss is `L_M(α) := ∫ (γ_target α x)² dP_X − 2 · D_g_M α`.

The first-order-condition characterisation follows the same representer
geometry as the linear-functional case in `Linear.lean`; this definition is the
general-moment population objective used by downstream automatic-debiasing
instances. -/
noncomputable def genRieszLoss (S : RegNuisanceMomentSys) (α : S.H) : ℝ :=
  ∫ x, (S.γ_target α x) ^ 2 ∂S.P_X - 2 * S.D_g_M α

/-- **Finite-difference representer loss.**

Pure-empirical analogue of `genRieszLoss`, intended as the loss minimised
by Chernozhukov–Newey–Singh "RieszNet"-type estimators. The first term is
the empirical second moment of `γ_target α` on the training fold `C n`;
the second term is a centred finite-difference approximation of
`D_g M(θ̂_n, ĝ_n)[α]` using perturbation scale `ε n`. -/
noncomputable def finDiffRieszLoss (S : RegNuisanceMomentSys)
    {Ω : Type*} (Z_data : ℕ → Ω → S.Z)
    (θ_hat : ℕ → Ω → ℝ) (g_hat : ℕ → Ω → S.H)
    (ε : ℕ → ℝ) (α : S.H) (C : ℕ → Finset ℕ)
    (n : ℕ) (ω : Ω) : ℝ :=
  ((C n).card : ℝ)⁻¹ *
    ∑ i ∈ C n, (S.γ_target α (S.proj_X (Z_data i ω))) ^ 2
  - 2 * (
      ((C n).card : ℝ)⁻¹ *
        ∑ i ∈ C n, S.m (g_hat n ω + ε n • α) (Z_data i ω) (θ_hat n ω)
      - ((C n).card : ℝ)⁻¹ *
        ∑ i ∈ C n, S.m (g_hat n ω - ε n • α) (Z_data i ω) (θ_hat n ω)
    ) / (2 * ε n)

end Causalean.Estimation.OrthogonalMoments.AutoDebias
