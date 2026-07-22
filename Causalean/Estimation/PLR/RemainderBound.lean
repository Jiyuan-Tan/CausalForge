/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Doubly-robust bilinear remainder of the partially linear score

The Neyman-orthogonality payoff for the partially linear model: the population
moment evaluated at any nuisance `η = (ℓ̂, m̂)` (but at the true target `θ₀`) is
controlled by the *product* of the two L²(P_X) nuisance errors.  With
`Δℓ = ℓ₀ − ℓ̂`, `Δm = m₀ − m̂`, the cross terms vanish (by `integral_U_resid` and
the conditional-mean-zero facts `condExp_U_sigmaX` / `condExp_resid_sigmaX`),
leaving

    E[ψ(η, ·, θ₀)] = E[Δℓ·Δm] − θ₀·E[Δm²],
    |E[ψ(η, ·, θ₀)]| ≤ (1 + |θ₀|)·max(‖Δℓ‖₂, ‖Δm‖₂)².

This is the product-rate structure the DML engine needs: it makes the
`o_p(n^{-1/2})` requirement the textbook "both nuisances at `o_p(n^{-1/4})`."
-/

import Causalean.Estimation.PLR.Setup
import Causalean.Stat.Orthogonality.ConditionalOp

/-! # Doubly-robust remainder for the partially linear score

This file proves the doubly-robust bilinear bound on the population moment at an
estimated nuisance, the analytic heart of the partially linear DML guarantee.
The helper `integral_condExpZero_mul_comp_factualX` turns conditional
mean-zero-with-respect-to-`σ(X)` into orthogonality against covariate functions,
and `plr_remainder_bound` applies that orthogonality to bound the partially
linear population score by the product of outcome- and treatment-regression
L²(P_X) errors. -/

namespace Causalean
namespace Estimation
namespace PLR

open MeasureTheory ProbabilityTheory Causalean.PO Causalean.Stat
open Causalean.Estimation.OrthogonalMoments

namespace PLRSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ] [IsFiniteMeasure P.μ]
variable (S : PLRSystem P γ)

/-- Orthogonality of a `σ(X)`-conditionally-mean-zero variable `w` to any
covariate function `h(X)`: `E[w·h(X)] = 0`.  Mirrors `integral_U_resid`, but the
σ-algebra is `σ(X)` (so `h(X)` pulls out of the conditional expectation) instead
of `σ(X,D)`.  Used to kill the three orthogonal cross terms `U·Δm`, `Δℓ·V`,
`V·Δm` in the doubly-robust remainder. -/
lemma integral_condExpZero_mul_comp_factualX
    {w : P.Ω → ℝ} {h : γ → ℝ} (hh : Measurable h)
    (hwz : P.μ[w | S.sigmaX] =ᵐ[P.μ] 0)
    (hw : Integrable w P.μ)
    (hwg : Integrable (fun ω => w ω * h (S.factualX ω)) P.μ) :
    ∫ ω, w ω * h (S.factualX ω) ∂P.μ = 0 := by
  -- `h(X)` is `σ(X)`-strongly-measurable.
  have hg_sm : StronglyMeasurable[S.sigmaX] (fun ω => h (S.factualX ω)) := by
    change StronglyMeasurable[MeasurableSpace.comap S.factualX inferInstance]
      (fun ω => h (S.factualX ω))
    exact (hh.comp (comap_measurable S.factualX)).stronglyMeasurable
  -- `w·h(X) = h(X)·w` is integrable up to commutativity.
  have hgw_int : Integrable (fun ω => h (S.factualX ω) * w ω) P.μ := by
    simpa [mul_comm] using hwg
  -- Pull `h(X)` out of the conditional expectation, then `E[w|σX] = 0`.
  have hpull :
      P.μ[fun ω => h (S.factualX ω) * w ω | S.sigmaX]
        =ᵐ[P.μ] (fun ω => h (S.factualX ω)) * P.μ[w | S.sigmaX] :=
    MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (μ := P.μ) (m := S.sigmaX) hg_sm hgw_int hw
  have hce_zero :
      P.μ[fun ω => h (S.factualX ω) * w ω | S.sigmaX] =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
    refine hpull.trans ?_
    filter_upwards [hwz] with ω hω
    rw [Pi.mul_apply, hω, Pi.zero_apply, mul_zero]
  calc ∫ ω, w ω * h (S.factualX ω) ∂P.μ
      = ∫ ω, h (S.factualX ω) * w ω ∂P.μ := by simp_rw [mul_comm]
    _ = ∫ ω, P.μ[fun ω => h (S.factualX ω) * w ω | S.sigmaX] ω ∂P.μ := by
        rw [MeasureTheory.integral_condExp S.sigmaX_le]
    _ = ∫ _, (0 : ℝ) ∂P.μ := MeasureTheory.integral_congr_ae hce_zero
    _ = 0 := MeasureTheory.integral_zero _ _

/-- **Doubly-robust bilinear remainder.**  For any nuisance `η`, the population
moment at the true target is bounded by the product of the two L²(P_X) nuisance
errors:

    |E[ψ(η, ·, θ₀)]| ≤ (1 + |θ₀|)·max(‖Δℓ‖₂, ‖Δm‖₂)². -/
lemma plr_remainder_bound (η : PLRNuisance γ)
    (hD : Integrable S.factualD P.μ)
    (hbX : Integrable (fun ω => S.b (S.factualX ω)) P.μ)
    (hU : Integrable S.U P.μ)
    (hΔl : MemLp (fun x => η.lFn x - S.lVal x) 2 S.P_X)
    (hΔm : MemLp (fun x => η.mFn x - S.mVal x) 2 S.P_X)
    (hV : MemLp S.resid 2 P.μ)
    -- L¹ control of the orthogonal cross terms (each derivable from the above
    -- by Cauchy–Schwarz, but kept as explicit integrability hypotheses).
    (hUΔm : Integrable
      (fun ω => S.U ω * (η.mFn (S.factualX ω) - S.mVal (S.factualX ω))) P.μ)
    (hΔlV : Integrable
      (fun ω => (η.lFn (S.factualX ω) - S.lVal (S.factualX ω)) * S.resid ω) P.μ)
    (hVΔm : Integrable
      (fun ω => S.resid ω * (η.mFn (S.factualX ω) - S.mVal (S.factualX ω))) P.μ)
    (hUV : Integrable (fun ω => S.U ω * S.resid ω) P.μ) :
    |∫ z, plrMomentFunctional η z S.θ₀ ∂S.P_Z|
      ≤ (1 + |S.θ₀|)
          * ((S.plrGeneralMoment.ρ₁ η S.η₀ : NNReal) : ℝ)
          * ((S.plrGeneralMoment.ρ₂ η S.η₀ : NNReal) : ℝ) := by
  -- Notation for the two pulled-back nuisance errors.
  set δl : P.Ω → ℝ := fun ω => η.lFn (S.factualX ω) - S.lVal (S.factualX ω) with hδl_def
  set δm : P.Ω → ℝ := fun ω => η.mFn (S.factualX ω) - S.mVal (S.factualX ω) with hδm_def
  -- L²(μ) membership of the pulled-back errors, transported from L²(P_X).
  have hδl : MemLp δl 2 P.μ :=
    hΔl.comp_of_map (f := S.factualX) S.measurable_factualX.aemeasurable
  have hδm : MemLp δm 2 P.μ :=
    hΔm.comp_of_map (f := S.factualX) S.measurable_factualX.aemeasurable
  -- Step 1: change of variables to the `μ`-level integral.
  rw [S.integral_P_Z (measurable_plrMomentFunctional η S.θ₀)]
  -- Step 2: pointwise-a.e. rewrite of the integrand.
  have hae :
      (fun ω => plrMomentFunctional η (S.factualZ ω) S.θ₀)
        =ᵐ[P.μ] fun ω => (S.U ω - δl ω + S.θ * δm ω) * (S.resid ω - δm ω) := by
    filter_upwards [S.lVal_compat, S.mVal_compat, S.factualY_sub_lReg hD hbX hU]
      with ω hl hm hY
    simp only [plrMomentFunctional, plrResidual, hδl_def, hδm_def]
    change (S.factualY ω - η.lFn (S.factualX ω)
            - S.θ₀ * (S.factualD ω - η.mFn (S.factualX ω)))
          * (S.factualD ω - η.mFn (S.factualX ω))
        = (S.U ω - (η.lFn (S.factualX ω) - S.lVal (S.factualX ω))
            + S.θ * (η.mFn (S.factualX ω) - S.mVal (S.factualX ω)))
          * (S.resid ω - (η.mFn (S.factualX ω) - S.mVal (S.factualX ω)))
    have hr : S.resid ω = S.factualD ω - S.mReg ω := rfl
    have ht : S.θ₀ = S.θ := rfl
    rw [ht]
    rw [hr] at hY ⊢
    rw [hl, hm]
    linear_combination (S.factualD ω - η.mFn (S.factualX ω)) * hY
  rw [integral_congr_ae hae]
  -- `δl, δm` are σ(X)-pullbacks, hence orthogonal to `U` and `resid`.
  have hδl_meas : Measurable (fun x => η.lFn x - S.lVal x) := η.lMeas.sub S.lVal_meas
  have hδm_meas : Measurable (fun x => η.mFn x - S.mVal x) := η.mMeas.sub S.mVal_meas
  -- Step 3: the three orthogonal cross terms vanish.
  have h_U_resid : ∫ ω, S.U ω * S.resid ω ∂P.μ = 0 := S.integral_U_resid hU hUV
  have h_U_δm : ∫ ω, S.U ω * δm ω ∂P.μ = 0 := by
    rw [hδm_def]
    exact S.integral_condExpZero_mul_comp_factualX hδm_meas
      S.condExp_U_sigmaX hU hUΔm
  have h_δl_resid : ∫ ω, δl ω * S.resid ω ∂P.μ = 0 := by
    have hcomm : (fun ω => δl ω * S.resid ω)
        = fun ω => S.resid ω * (η.lFn (S.factualX ω) - S.lVal (S.factualX ω)) := by
      funext ω; rw [hδl_def]; ring
    rw [hcomm]
    exact S.integral_condExpZero_mul_comp_factualX hδl_meas
      (S.condExp_resid_sigmaX hD) (hV.integrable (by norm_num))
      (by simpa [mul_comm] using hΔlV)
  have h_δm_resid : ∫ ω, δm ω * S.resid ω ∂P.μ = 0 := by
    have hcomm : (fun ω => δm ω * S.resid ω)
        = fun ω => S.resid ω * (η.mFn (S.factualX ω) - S.mVal (S.factualX ω)) := by
      funext ω; rw [hδm_def]; ring
    rw [hcomm]
    exact S.integral_condExpZero_mul_comp_factualX hδm_meas
      (S.condExp_resid_sigmaX hD) (hV.integrable (by norm_num)) hVΔm
  -- Cauchy–Schwarz integrability of the two surviving (`δl·δm`, `δm²`) terms.
  haveI : ENNReal.HolderTriple (2 : ENNReal) (2 : ENNReal) (1 : ENNReal) := by
    constructor; simpa using ENNReal.inv_two_add_inv_two
  have hδlδm_memLp : MemLp (fun ω => δl ω * δm ω) 1 P.μ := MemLp.mul' hδm hδl
  have hδmsq_memLp : MemLp (fun ω => δm ω * δm ω) 1 P.μ := MemLp.mul' hδm hδm
  have hδlδm_int : Integrable (fun ω => δl ω * δm ω) P.μ :=
    hδlδm_memLp.integrable le_rfl
  have hδmsq_int : Integrable (fun ω => δm ω * δm ω) P.μ :=
    hδmsq_memLp.integrable le_rfl
  -- Integrability of every product term in the expansion.
  have hUδm_int : Integrable (fun ω => S.U ω * δm ω) P.μ := by
    rw [hδm_def]; exact hUΔm
  have hδlresid_int : Integrable (fun ω => δl ω * S.resid ω) P.μ := by
    rw [hδl_def]; exact hΔlV
  have hδmresid_int : Integrable (fun ω => δm ω * S.resid ω) P.μ := by
    rw [hδm_def]; simpa [mul_comm] using hVΔm
  -- Step 3 (cont.): expand the integral; only `∫δl·δm − θ·∫δm²` survives.
  -- Integrability of the grouped sub-expressions, stated in pointwise form so
  -- the `integral_add` / `integral_sub` rewrites match the integrand.
  have hA1 : Integrable (fun ω => S.U ω * S.resid ω - S.U ω * δm ω) P.μ :=
    hUV.sub hUδm_int
  have hA2 :
      Integrable
        (fun ω => S.U ω * S.resid ω - S.U ω * δm ω - δl ω * S.resid ω) P.μ :=
    hA1.sub hδlresid_int
  have hA3 :
      Integrable
        (fun ω => S.U ω * S.resid ω - S.U ω * δm ω - δl ω * S.resid ω
          + δl ω * δm ω) P.μ :=
    hA2.add hδlδm_int
  have hB :
      Integrable
        (fun ω => S.θ * (δm ω * S.resid ω) - S.θ * (δm ω * δm ω)) P.μ :=
    (hδmresid_int.const_mul S.θ).sub (hδmsq_int.const_mul S.θ)
  have hint_eq :
      ∫ ω, (S.U ω - δl ω + S.θ * δm ω) * (S.resid ω - δm ω) ∂P.μ
        = ∫ ω, δl ω * δm ω ∂P.μ - S.θ * ∫ ω, δm ω * δm ω ∂P.μ := by
    have hexp :
        (fun ω => (S.U ω - δl ω + S.θ * δm ω) * (S.resid ω - δm ω))
          = fun ω =>
              (S.U ω * S.resid ω - S.U ω * δm ω - δl ω * S.resid ω
                + δl ω * δm ω)
                + (S.θ * (δm ω * S.resid ω) - S.θ * (δm ω * δm ω)) := by
      funext ω; ring
    rw [hexp, integral_add hA3 hB, integral_add hA2 hδlδm_int,
      integral_sub hA1 hδlresid_int, integral_sub hUV hUδm_int,
      integral_sub (hδmresid_int.const_mul S.θ) (hδmsq_int.const_mul S.θ),
      integral_const_mul, integral_const_mul,
      h_U_resid, h_U_δm, h_δl_resid, h_δm_resid]
    ring
  rw [hint_eq]
  -- Step 4: the bound.  Abbreviate the two L²(P_X) nuisance errors.
  set a : ℝ := (eLpNorm (fun x => η.lFn x - S.lVal x) 2 S.P_X).toReal with ha_def
  set b : ℝ := (eLpNorm (fun x => η.mFn x - S.mVal x) 2 S.P_X).toReal with hb_def
  have ha_nonneg : 0 ≤ a := ENNReal.toReal_nonneg
  have hb_nonneg : 0 ≤ b := ENNReal.toReal_nonneg
  -- The right-hand side is `(1 + |θ₀|)·(max a b)·(max a b)`.
  have hrhs1 : ((S.plrGeneralMoment.ρ₁ η S.η₀ : NNReal) : ℝ) = max a b := by
    simp only [plrGeneralMoment, η₀, NNReal.coe_mk, ← ha_def, ← hb_def]
  have hrhs2 : ((S.plrGeneralMoment.ρ₂ η S.η₀ : NNReal) : ℝ) = max a b := by
    simp only [plrGeneralMoment, η₀, NNReal.coe_mk, ← ha_def, ← hb_def]
  rw [hrhs1, hrhs2]
  -- L²(μ) ↔ L²(P_X) bridge for the two pulled-back nuisance errors.
  have hbridge_l : (eLpNorm δl 2 P.μ).toReal = a := by
    rw [ha_def, hδl_def, P_X,
      eLpNorm_map_measure hδl_meas.aestronglyMeasurable
        S.measurable_factualX.aemeasurable]
    rfl
  have hbridge_m : (eLpNorm δm 2 P.μ).toReal = b := by
    rw [hb_def, hδm_def, P_X,
      eLpNorm_map_measure hδm_meas.aestronglyMeasurable
        S.measurable_factualX.aemeasurable]
    rfl
  -- Cauchy–Schwarz on `δl·δm` and on `δm²` (over `μ`).
  have hCS_lm : ∫ ω, |δl ω * δm ω| ∂P.μ ≤ a * b := by
    have h := integral_abs_mul_le_eLpNorm_mul_eLpNorm (ν := P.μ) hδl hδm
    rwa [hbridge_l, hbridge_m] at h
  have hCS_mm : ∫ ω, |δm ω * δm ω| ∂P.μ ≤ b * b := by
    have h := integral_abs_mul_le_eLpNorm_mul_eLpNorm (ν := P.μ) hδm hδm
    rwa [hbridge_m] at h
  -- `∫ δm² = ∫ |δm·δm| ≥ 0`.
  have hδmsq_abs : (fun ω => δm ω * δm ω) = fun ω => |δm ω * δm ω| := by
    funext ω; rw [abs_of_nonneg (mul_self_nonneg (δm ω))]
  have hδmsq_nonneg : 0 ≤ ∫ ω, δm ω * δm ω ∂P.μ :=
    integral_nonneg fun ω => mul_self_nonneg (δm ω)
  -- `|∫ δl·δm| ≤ ∫ |δl·δm| ≤ a·b`.
  have hbound_lm : |∫ ω, δl ω * δm ω ∂P.μ| ≤ a * b :=
    (abs_integral_le_integral_abs).trans hCS_lm
  -- `∫ δm² ≤ b²`.
  have hbound_mm : ∫ ω, δm ω * δm ω ∂P.μ ≤ b * b := by
    calc ∫ ω, δm ω * δm ω ∂P.μ = ∫ ω, |δm ω * δm ω| ∂P.μ := by rw [hδmsq_abs]
      _ ≤ b * b := hCS_mm
  -- Triangle inequality and the `max` bound.
  have hθ : S.θ₀ = S.θ := rfl
  have ha_le : a ≤ max a b := le_max_left a b
  have hb_le : b ≤ max a b := le_max_right a b
  have hmax_nonneg : 0 ≤ max a b := le_trans ha_nonneg ha_le
  calc |∫ ω, δl ω * δm ω ∂P.μ - S.θ * ∫ ω, δm ω * δm ω ∂P.μ|
      ≤ |∫ ω, δl ω * δm ω ∂P.μ| + |S.θ * ∫ ω, δm ω * δm ω ∂P.μ| :=
        abs_sub _ _
    _ = |∫ ω, δl ω * δm ω ∂P.μ| + |S.θ| * (∫ ω, δm ω * δm ω ∂P.μ) := by
        rw [abs_mul, abs_of_nonneg hδmsq_nonneg]
    _ ≤ a * b + |S.θ| * (b * b) :=
        add_le_add hbound_lm
          (mul_le_mul_of_nonneg_left hbound_mm (abs_nonneg _))
    _ ≤ max a b * max a b + |S.θ| * (max a b * max a b) := by
        gcongr
    _ = (1 + |S.θ₀|) * max a b * max a b := by rw [hθ]; ring

end PLRSystem

end PLR
end Estimation
end Causalean
