/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Partialling-out identification of the partially linear treatment effect

For the partially linear model under the backdoor PO framework
(`POPartialLinearModel`), this file identifies the structural slope `θ` as the
Robinson partialling-out estimand:

    θ = E[(Y − ℓ₀(X))·(D − m₀(X))] / E[(D − m₀(X))²],

where `m₀(X) = E[D | σ(X)]` and `ℓ₀(X) = E[Y | σ(X)]` are the treatment and
outcome regressions on the covariate.  This is the *causal bridge*: the purely
statistical partialling-out estimand equals the causal parameter `θ`.

Key population facts (the Neyman-orthogonality content):
* `condExp_U_sigmaX` — `E[U | σ(X)] = 0`.
* `condExp_resid_sigmaX` — `E[D − m₀(X) | σ(X)] = 0` (the treatment residual is
  conditionally mean-zero).
* `integral_U_resid` — `E[U·(D − m₀(X))] = 0`.
* `lReg_eq` — `ℓ₀(X) = b(X) + θ·m₀(X)`.
* `robinson_estimand_eq_theta` — the bridge `θ₀ = θ`.
-/

import Causalean.PO.ID.Exact.PartialLinear.Setup
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Partialling-out identification

This file proves the population partialling-out bridge for the partially
linear potential-outcome model. It defines the covariate regressions `mReg` and
`lReg`, the treatment residual `resid`, and then proves the conditional
mean-zero and orthogonality identities that drive Robinson's identification
argument.

The important lemmas are `condExp_U_sigmaX`, `condExp_resid_sigmaX`,
`integral_U_resid`, `lReg_eq`, `factualY_sub_lReg`, and `integral_partialled`.
The main theorem `robinson_estimand_eq_theta` states that the population
Robinson ratio
`E[(Y - lReg(X)) * (D - mReg(X))] / E[(D - mReg(X))^2]` equals the structural
slope `theta` when the residual second moment is nonzero. -/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POPartialLinearModel

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable [IsFiniteMeasure P.μ]
variable (M : POPartialLinearModel P γ)

/-- The treatment regression `m₀(X) = E[D | σ(X)]` (the conditional mean of the
treatment given the covariate). -/
noncomputable def mReg : P.Ω → ℝ := P.μ[M.factualD | M.sigmaX]

/-- The outcome regression `ℓ₀(X) = E[Y | σ(X)]` (the conditional mean of the
outcome given the covariate). -/
noncomputable def lReg : P.Ω → ℝ := P.μ[M.factualY | M.sigmaX]

/-- The treatment residual `V = D − m₀(X)` (treatment with its covariate
prediction partialled out). -/
noncomputable def resid : P.Ω → ℝ := fun ω => M.factualD ω - M.mReg ω

/-- The structural error has zero conditional mean given the covariate.  Follows
from the backdoor assumption `E[U | σ(X,D)] = 0` by the tower property, since
`σ(X) ⊆ σ(X,D)`. -/
lemma condExp_U_sigmaX : P.μ[M.U | M.sigmaX] =ᵐ[P.μ] 0 := by
  have htower :
      P.μ[P.μ[M.U | M.sigmaXD] | M.sigmaX] =ᵐ[P.μ] P.μ[M.U | M.sigmaX] :=
    MeasureTheory.condExp_condExp_of_le M.sigmaX_le_sigmaXD M.sigmaXD_le
  have hinner :
      P.μ[P.μ[M.U | M.sigmaXD] | M.sigmaX] =ᵐ[P.μ] P.μ[(0 : P.Ω → ℝ) | M.sigmaX] :=
    MeasureTheory.condExp_congr_ae M.backdoor
  refine htower.symm.trans (hinner.trans ?_)
  simp [MeasureTheory.condExp_zero]

/-- The treatment residual is conditionally mean-zero given the covariate:
`E[D − m₀(X) | σ(X)] = 0`.  Immediate from `condExp_sub` and idempotence of the
conditional expectation. -/
lemma condExp_resid_sigmaX
    (hD : Integrable M.factualD P.μ) :
    P.μ[M.resid | M.sigmaX] =ᵐ[P.μ] 0 := by
  have hresid_eq : M.resid = M.factualD - M.mReg := rfl
  rw [hresid_eq]
  have hsub :
      P.μ[M.factualD - M.mReg | M.sigmaX]
        =ᵐ[P.μ] P.μ[M.factualD | M.sigmaX] - P.μ[M.mReg | M.sigmaX] :=
    MeasureTheory.condExp_sub hD MeasureTheory.integrable_condExp M.sigmaX
  have hidem : P.μ[M.mReg | M.sigmaX] =ᵐ[P.μ] M.mReg := by
    unfold mReg
    exact MeasureTheory.condExp_condExp_of_le le_rfl M.sigmaX_le
  refine hsub.trans ?_
  have : P.μ[M.factualD | M.sigmaX] = M.mReg := rfl
  rw [this]
  filter_upwards [hidem] with ω hω
  simp [Pi.sub_apply, hω]

/-- Orthogonality of the structural error to the covariate-treatment residual:
`E[U·(D − m₀(X))] = 0`.  Since the residual is `σ(X,D)`-measurable and
`E[U | σ(X,D)] = 0`, the product integrates to zero (pull the residual out of the
conditional expectation, then integrate). -/
lemma integral_U_resid
    (hU : Integrable M.U P.μ)
    (hUV : Integrable (fun ω => M.U ω * M.resid ω) P.μ) :
    ∫ ω, M.U ω * M.resid ω ∂P.μ = 0 := by
  -- `resid = D − mReg` is `σ(X,D)`-strongly-measurable.
  have hD_sm : StronglyMeasurable[M.sigmaXD] M.factualD := by
    have heq : M.factualD = Prod.snd ∘ M.factualXD := rfl
    rw [heq]
    exact (measurable_snd.comp (comap_measurable M.factualXD)).stronglyMeasurable
  have hmReg_sm : StronglyMeasurable[M.sigmaXD] M.mReg := by
    refine MeasureTheory.stronglyMeasurable_condExp.mono M.sigmaX_le_sigmaXD
  have hresid_sm : StronglyMeasurable[M.sigmaXD] M.resid := by
    have : M.resid = fun ω => M.factualD ω - M.mReg ω := rfl
    rw [this]
    exact hD_sm.sub hmReg_sm
  -- Rewrite `U·resid` as `resid·U` (integrable up to commutativity).
  have hVU_int : Integrable (fun ω => M.resid ω * M.U ω) P.μ := by
    simpa [mul_comm] using hUV
  -- `∫ U·resid = ∫ resid·U = ∫ μ[resid·U | σ(X,D)] = ∫ resid·μ[U|σ(X,D)] = ∫ resid·0 = 0`.
  have hpull :
      P.μ[fun ω => M.resid ω * M.U ω | M.sigmaXD]
        =ᵐ[P.μ] M.resid * P.μ[M.U | M.sigmaXD] :=
    MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (μ := P.μ) (m := M.sigmaXD) hresid_sm hVU_int hU
  have hce_zero : P.μ[fun ω => M.resid ω * M.U ω | M.sigmaXD] =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
    refine hpull.trans ?_
    filter_upwards [M.backdoor] with ω hω
    rw [Pi.mul_apply, hω, Pi.zero_apply, mul_zero]
  calc ∫ ω, M.U ω * M.resid ω ∂P.μ
      = ∫ ω, M.resid ω * M.U ω ∂P.μ := by simp_rw [mul_comm]
    _ = ∫ ω, P.μ[fun ω => M.resid ω * M.U ω | M.sigmaXD] ω ∂P.μ := by
        rw [MeasureTheory.integral_condExp M.sigmaXD_le]
    _ = ∫ _, (0 : ℝ) ∂P.μ := MeasureTheory.integral_congr_ae hce_zero
    _ = 0 := MeasureTheory.integral_zero _ _

/-- The outcome regression decomposes as `ℓ₀(X) = b(X) + θ·m₀(X)`.  Apply the
conditional expectation given `σ(X)` to the observed-data form
`Y = b(X) + θ·D + U`: the covariate term is `σ(X)`-measurable, the treatment term
contributes `θ·m₀(X)`, and the error term vanishes by `condExp_U_sigmaX`. -/
lemma lReg_eq
    (hD : Integrable M.factualD P.μ)
    (hbX : Integrable (fun ω => M.b (M.factualX ω)) P.μ)
    (hU : Integrable M.U P.μ) :
    M.lReg =ᵐ[P.μ] fun ω => M.b (M.factualX ω) + M.θ * M.mReg ω := by
  have hbX_int : Integrable (fun ω => M.b (M.factualX ω)) P.μ := hbX
  have hθD_int : Integrable (fun ω => M.θ * M.factualD ω) P.μ := hD.const_mul M.θ
  -- σ(X)-strong-measurability of the covariate term.
  have hbX_sm : StronglyMeasurable[M.sigmaX] (fun ω => M.b (M.factualX ω)) := by
    change StronglyMeasurable[MeasurableSpace.comap M.factualX inferInstance]
      (fun ω => M.b (M.factualX ω))
    exact (M.b_meas.comp
      (comap_measurable M.factualX)).stronglyMeasurable
  -- Rewrite Y by the observed-data form, then split the conditional expectation.
  have hY :
      M.lReg =ᵐ[P.μ]
        P.μ[fun ω => (M.b (M.factualX ω) + M.θ * M.factualD ω) + M.U ω | M.sigmaX] := by
    unfold lReg
    refine MeasureTheory.condExp_congr_ae ?_
    filter_upwards [M.factualY_eq] with ω hω
    simpa using hω
  have hsplit1 :
      P.μ[fun ω => (M.b (M.factualX ω) + M.θ * M.factualD ω) + M.U ω | M.sigmaX]
        =ᵐ[P.μ]
        P.μ[fun ω => M.b (M.factualX ω) + M.θ * M.factualD ω | M.sigmaX]
          + P.μ[M.U | M.sigmaX] :=
    MeasureTheory.condExp_add (hbX_int.add hθD_int) hU M.sigmaX
  have hsplit2 :
      P.μ[fun ω => M.b (M.factualX ω) + M.θ * M.factualD ω | M.sigmaX]
        =ᵐ[P.μ]
        P.μ[fun ω => M.b (M.factualX ω) | M.sigmaX]
          + P.μ[fun ω => M.θ * M.factualD ω | M.sigmaX] :=
    MeasureTheory.condExp_add hbX_int hθD_int M.sigmaX
  have hbXce : P.μ[fun ω => M.b (M.factualX ω) | M.sigmaX]
      = fun ω => M.b (M.factualX ω) :=
    MeasureTheory.condExp_of_stronglyMeasurable M.sigmaX_le hbX_sm hbX_int
  have hθDce : P.μ[fun ω => M.θ * M.factualD ω | M.sigmaX]
      =ᵐ[P.μ] fun ω => M.θ * M.mReg ω := by
    have hsmul : P.μ[fun ω => M.θ • M.factualD ω | M.sigmaX]
        =ᵐ[P.μ] M.θ • P.μ[M.factualD | M.sigmaX] :=
      MeasureTheory.condExp_smul M.θ M.factualD M.sigmaX
    refine hsmul.trans ?_
    filter_upwards with ω
    simp [Pi.smul_apply, mReg, smul_eq_mul]
  rw [hbXce] at hsplit2
  refine hY.trans (hsplit1.trans ?_)
  filter_upwards [hsplit2, hθDce, M.condExp_U_sigmaX] with ω h2 hθd hu
  rw [Pi.add_apply, h2, Pi.add_apply, hθd, hu]
  simp

/-- Partialling-out identity (observed data): `Y − ℓ₀(X) = θ·(D − m₀(X)) + U`.
Algebraic consequence of `factualY_eq` and `lReg_eq`. -/
lemma factualY_sub_lReg
    (hD : Integrable M.factualD P.μ)
    (hbX : Integrable (fun ω => M.b (M.factualX ω)) P.μ)
    (hU : Integrable M.U P.μ) :
    (fun ω => M.factualY ω - M.lReg ω)
      =ᵐ[P.μ] fun ω => M.θ * M.resid ω + M.U ω := by
  filter_upwards [M.factualY_eq, M.lReg_eq hD hbX hU] with ω hY hl
  rw [hY, hl]
  simp only [resid]
  ring

/-- The Robinson numerator equals `θ` times the residual second moment:
`E[(Y − ℓ₀(X))·(D − m₀(X))] = θ·E[(D − m₀(X))²]`.  Expand `Y − ℓ₀ = θ·V + U` and
use `E[U·V] = 0`. -/
lemma integral_partialled
    (hD : Integrable M.factualD P.μ)
    (hbX : Integrable (fun ω => M.b (M.factualX ω)) P.μ)
    (hU : Integrable M.U P.μ)
    (hVsq : Integrable (fun ω => M.resid ω ^ 2) P.μ)
    (hUV : Integrable (fun ω => M.U ω * M.resid ω) P.μ) :
    ∫ ω, (M.factualY ω - M.lReg ω) * M.resid ω ∂P.μ
      = M.θ * ∫ ω, M.resid ω ^ 2 ∂P.μ := by
  rw [integral_congr_ae
    (g := fun ω => M.θ * M.resid ω ^ 2 + M.U ω * M.resid ω) ?_]
  · rw [integral_add (hVsq.const_mul M.θ) hUV, integral_const_mul,
      M.integral_U_resid hU hUV, add_zero]
  · filter_upwards [M.factualY_sub_lReg hD hbX hU] with ω h
    rw [h]; ring

/-- **The causal bridge.**  The Robinson partialling-out estimand equals the
structural treatment effect `θ`, provided the treatment has residual variation
(`E[(D − m₀(X))²] ≠ 0`).  This is what makes the partially linear DML estimator
target the causal parameter. -/
theorem robinson_estimand_eq_theta
    (hD : Integrable M.factualD P.μ)
    (hbX : Integrable (fun ω => M.b (M.factualX ω)) P.μ)
    (hU : Integrable M.U P.μ)
    (hVsq : Integrable (fun ω => M.resid ω ^ 2) P.μ)
    (hUV : Integrable (fun ω => M.U ω * M.resid ω) P.μ)
    (hV : ∫ ω, M.resid ω ^ 2 ∂P.μ ≠ 0) :
    (∫ ω, (M.factualY ω - M.lReg ω) * M.resid ω ∂P.μ)
        / (∫ ω, M.resid ω ^ 2 ∂P.μ) = M.θ := by
  rw [M.integral_partialled hD hbX hU hVsq hUV, mul_div_assoc, div_self hV,
    mul_one]

end POPartialLinearModel

end PO
end Causalean
