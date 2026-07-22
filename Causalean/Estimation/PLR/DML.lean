/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Headline partially linear DML: asymptotic linearity and normality

Assembles the two flagship results for the one-step double-machine-learning
estimator of the structural slope `θ` in the partially linear model, directly
mirroring the AIPW back-door development:

* `plr_dml_isAsymLinear`  — the Robinson partialling-out DML estimator is
  asymptotically linear at `θ` with influence function
  `−J₀⁻¹ · ψ(η₀, ·, θ)`, derived from the abstract Chernozhukov engine
  `dml_chernozhukov_asymptoticLinear` fed with the three partially linear
  facts (`plr_meanZero`, `plr_finite_var`, `plr_remainder_bound`).
* `plr_dml_tendstoNormal` — √|B(n)|-asymptotic normality of the rescaled
  estimator, obtained from the generic CLT bridge
  `IsAsymLinear.tendsto_normal_foldB`.

This is the partially linear analogue of `Estimation/OrthogonalMoments/
AIPWInstance.lean` (`aipw_dml_isAsymLinear`) and `Estimation/ATE/DML.lean`
(`dml_ATE_tendstoNormal`).
-/

import Causalean.Estimation.PLR.MeanZero
import Causalean.Estimation.PLR.RemainderBound
import Causalean.Estimation.OrthogonalMoments.DMLChernozhukov
import Causalean.Stat.SampleSplit.PartialFoldCLT

/-! # Headline partially linear DML theorems

This file delivers the asymptotic linearity and √n-asymptotic normality of the
one-step double-machine-learning estimator of the structural slope in the
partially linear model, by composing the abstract Chernozhukov-form engine with
the three model-specific analytic facts (mean-zero, finite-variance,
doubly-robust remainder) and the generic asymptotic-linearity ⇒ normality
bridge. -/

namespace Causalean
namespace Estimation
namespace PLR

open MeasureTheory ProbabilityTheory Causalean.Stat Causalean.PO
open Causalean.Estimation.OrthogonalMoments
open Filter Topology

namespace PLRSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ] [IsProbabilityMeasure P.μ]

/-- **Headline partially linear DML asymptotic-linearity theorem.**  The
one-step double-machine-learning estimator of the structural slope, which
recenters the empirical Robinson partialling-out score by the inverse
partialling-out Jacobian, is asymptotically linear at the true slope.  Its
influence function is the inverse-Jacobian-scaled partialling-out score
evaluated at the true regressions, the standard partially linear influence
function, which is mean-zero at the truth.

The result is obtained by feeding the abstract Chernozhukov double-machine-learning
engine the three partially linear analytic facts — the score is mean-zero at the
truth, has finite variance, and admits a doubly-robust product bound on its
population bias at any estimated nuisance — together with the engine's
measurability and rate bundle, all supplied by the caller exactly as in the
AIPW development. -/
theorem plr_dml_isAsymLinear
    (S : PLRSystem P γ)
    (sample : IIDSample P.Ω (γ × ℝ × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (hc_pos : 0 < c)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (η_hat : ℕ → P.Ω → PLRNuisance γ)
    -- Model-level integrability facts feeding the three PLR lemmas.
    (hU : Integrable S.U P.μ)
    (hUV : Integrable (fun ω => S.U ω * S.toPOPartialLinearModel.resid ω) P.μ)
    (hbX : Integrable (fun ω => S.b (S.factualX ω)) P.μ)
    (hD : Integrable S.factualD P.μ)
    (hV : MemLp S.resid 2 P.μ)
    (hsq : Integrable
      (fun ω => (plrMomentFunctional S.η₀ (S.factualZ ω) S.θ₀) ^ 2) P.μ)
    -- Per-`(n, ω)` remainder regularity, so `plr_remainder_bound` applies at
    -- each estimated nuisance `η_hat n ω`.
    (hΔl : ∀ n ω, MemLp (fun x => (η_hat n ω).lFn x - S.lVal x) 2 S.P_X)
    (hΔm : ∀ n ω, MemLp (fun x => (η_hat n ω).mFn x - S.mVal x) 2 S.P_X)
    (hUΔm : ∀ n ω, Integrable
      (fun ω' => S.U ω' *
        ((η_hat n ω).mFn (S.factualX ω') - S.mVal (S.factualX ω'))) P.μ)
    (hΔlV : ∀ n ω, Integrable
      (fun ω' => ((η_hat n ω).lFn (S.factualX ω') - S.lVal (S.factualX ω'))
        * S.resid ω') P.μ)
    (hVΔm : ∀ n ω, Integrable
      (fun ω' => S.resid ω' *
        ((η_hat n ω).mFn (S.factualX ω') - S.mVal (S.factualX ω'))) P.μ)
    -- The abstract engine's measurability and rate bundle (copied verbatim from
    -- `dml_chernozhukov_asymptoticLinear` with `M := S.plrGeneralMoment`).
    (h_m_meas :
      ∀ n, Measurable (fun (p : P.Ω × (γ × ℝ × ℝ)) =>
        S.plrGeneralMoment.m (η_hat n p.1) p.2 S.plrGeneralMoment.θ₀))
    (h_m_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (fun ω z => S.plrGeneralMoment.m (η_hat n ω) z S.plrGeneralMoment.θ₀))
    (h_m_foldA_uncurry :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace (γ × ℝ × ℝ))]
          (fun (p : P.Ω × (γ × ℝ × ℝ)) =>
            S.plrGeneralMoment.m (η_hat n p.1) p.2 S.plrGeneralMoment.θ₀))
    (h_m_int : ∀ n ω,
      Integrable (fun z =>
        S.plrGeneralMoment.m (η_hat n ω) z S.plrGeneralMoment.θ₀) S.P_Z)
    (h_m_sq_int : ∀ n ω,
      Integrable (fun z =>
        (S.plrGeneralMoment.m (η_hat n ω) z S.plrGeneralMoment.θ₀) ^ 2) S.P_Z)
    (h_score_diff_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm
            (fun z =>
              S.plrGeneralMoment.m (η_hat n ω) z S.plrGeneralMoment.θ₀ -
                S.plrGeneralMoment.m S.plrGeneralMoment.η₀ z S.plrGeneralMoment.θ₀)
            2 S.P_Z).toReal)
        (fun _ => (1 : ℝ)) P.μ)
    (h_product_rate :
      IsLittleOp
        (fun n ω =>
          ((S.plrGeneralMoment.ρ₁ (η_hat n ω) S.plrGeneralMoment.η₀ : NNReal) : ℝ) *
            ((S.plrGeneralMoment.ρ₂ (η_hat n ω) S.plrGeneralMoment.η₀ : NNReal) : ℝ))
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ) :
    IsAsymLinear
      (Causalean.Estimation.OrthogonalMoments.dmlChernozhukovEstimator
        S.plrGeneralMoment sample split η_hat)
      S.θ₀
      (fun z => -S.plrGeneralMoment.J₀_inv * plrMomentFunctional S.η₀ z S.θ₀)
      sample
      split.foldB := by
  set Crem : ℝ := 1 + |S.θ₀| with hCrem_def
  have hMZ := S.plr_meanZero hU hUV hbX hD
  have hFV := S.plr_finite_var hsq
  have hBR_at :
      ∀ n ω,
        |∫ z, plrMomentFunctional (η_hat n ω) z S.θ₀ ∂S.P_Z| ≤
          Crem * ((S.plrGeneralMoment.ρ₁ (η_hat n ω) S.η₀ : NNReal) : ℝ) *
                 ((S.plrGeneralMoment.ρ₂ (η_hat n ω) S.η₀ : NNReal) : ℝ) :=
    fun n ω =>
      S.plr_remainder_bound (η_hat n ω) hD hbX hU (hΔl n ω) (hΔm n ω) hV
        (hUΔm n ω) (hΔlV n ω) (hVΔm n ω) hUV
  simpa [plrGeneralMoment] using
    (Causalean.Estimation.OrthogonalMoments.dml_chernozhukov_asymptoticLinear
      S.plrGeneralMoment hMZ hFV sample split hc_pos h_split_rate η_hat
      (Crem := Crem) hBR_at h_m_meas h_m_foldA h_m_foldA_uncurry h_m_int
      h_m_sq_int h_score_diff_rate h_product_rate)

/-- **Headline partially linear DML asymptotic-normality theorem.**  Under the
same hypotheses as the asymptotic-linearity result, the rescaled
double-machine-learning estimator of the structural slope, recentered at the
true slope and scaled by the square root of the fold-B sample size, converges in
distribution to a centered Gaussian whose variance is the second moment of the
inverse-Jacobian-scaled partialling-out score at the true regressions.

Combined with a fixed split ratio this yields the usual √n-rate normal limit
with the sample-splitting variance inflation; that final Slutsky rescaling is
left to the caller.  The proof composes the asymptotic-linearity theorem with
the generic central-limit bridge for fold-B asymptotically linear estimators. -/
theorem plr_dml_tendstoNormal
    (S : PLRSystem P γ)
    (sample : IIDSample P.Ω (γ × ℝ × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (hc_pos : 0 < c)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (η_hat : ℕ → P.Ω → PLRNuisance γ)
    (hU : Integrable S.U P.μ)
    (hUV : Integrable (fun ω => S.U ω * S.toPOPartialLinearModel.resid ω) P.μ)
    (hbX : Integrable (fun ω => S.b (S.factualX ω)) P.μ)
    (hD : Integrable S.factualD P.μ)
    (hV : MemLp S.resid 2 P.μ)
    (hsq : Integrable
      (fun ω => (plrMomentFunctional S.η₀ (S.factualZ ω) S.θ₀) ^ 2) P.μ)
    (hΔl : ∀ n ω, MemLp (fun x => (η_hat n ω).lFn x - S.lVal x) 2 S.P_X)
    (hΔm : ∀ n ω, MemLp (fun x => (η_hat n ω).mFn x - S.mVal x) 2 S.P_X)
    (hUΔm : ∀ n ω, Integrable
      (fun ω' => S.U ω' *
        ((η_hat n ω).mFn (S.factualX ω') - S.mVal (S.factualX ω'))) P.μ)
    (hΔlV : ∀ n ω, Integrable
      (fun ω' => ((η_hat n ω).lFn (S.factualX ω') - S.lVal (S.factualX ω'))
        * S.resid ω') P.μ)
    (hVΔm : ∀ n ω, Integrable
      (fun ω' => S.resid ω' *
        ((η_hat n ω).mFn (S.factualX ω') - S.mVal (S.factualX ω'))) P.μ)
    (h_m_meas :
      ∀ n, Measurable (fun (p : P.Ω × (γ × ℝ × ℝ)) =>
        S.plrGeneralMoment.m (η_hat n p.1) p.2 S.plrGeneralMoment.θ₀))
    (h_m_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (fun ω z => S.plrGeneralMoment.m (η_hat n ω) z S.plrGeneralMoment.θ₀))
    (h_m_foldA_uncurry :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace (γ × ℝ × ℝ))]
          (fun (p : P.Ω × (γ × ℝ × ℝ)) =>
            S.plrGeneralMoment.m (η_hat n p.1) p.2 S.plrGeneralMoment.θ₀))
    (h_m_int : ∀ n ω,
      Integrable (fun z =>
        S.plrGeneralMoment.m (η_hat n ω) z S.plrGeneralMoment.θ₀) S.P_Z)
    (h_m_sq_int : ∀ n ω,
      Integrable (fun z =>
        (S.plrGeneralMoment.m (η_hat n ω) z S.plrGeneralMoment.θ₀) ^ 2) S.P_Z)
    (h_score_diff_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm
            (fun z =>
              S.plrGeneralMoment.m (η_hat n ω) z S.plrGeneralMoment.θ₀ -
                S.plrGeneralMoment.m S.plrGeneralMoment.η₀ z S.plrGeneralMoment.θ₀)
            2 S.P_Z).toReal)
        (fun _ => (1 : ℝ)) P.μ)
    (h_product_rate :
      IsLittleOp
        (fun n ω =>
          ((S.plrGeneralMoment.ρ₁ (η_hat n ω) S.plrGeneralMoment.η₀ : NNReal) : ℝ) *
            ((S.plrGeneralMoment.ρ₂ (η_hat n ω) S.plrGeneralMoment.η₀ : NNReal) : ℝ))
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ)
    (hψ_meas :
      Measurable
        (fun z => -S.plrGeneralMoment.J₀_inv * plrMomentFunctional S.η₀ z S.θ₀))
    (hθn_meas : ∀ n, AEMeasurable
      (IsAsymLinear.rescaledEstimator
        (dmlChernozhukovEstimator S.plrGeneralMoment sample split η_hat)
        S.θ₀ split.foldB n) P.μ)
    (hSum_meas : ∀ n, AEMeasurable
      (IsAsymLinear.normalizedSum sample
        (fun z => -S.plrGeneralMoment.J₀_inv * plrMomentFunctional S.η₀ z S.θ₀)
        split.foldB n) P.μ) :
    Tendsto_dist
      (IsAsymLinear.rescaledEstimator
        (dmlChernozhukovEstimator S.plrGeneralMoment sample split η_hat)
        S.θ₀ split.foldB)
      (gaussianMeasure 0
        (∫ z, (-S.plrGeneralMoment.J₀_inv * plrMomentFunctional S.η₀ z S.θ₀) ^ 2
          ∂S.P_Z))
      P.μ
      hθn_meas := by
  have hAL :=
    S.plr_dml_isAsymLinear sample split hc_pos h_split_rate η_hat
      hU hUV hbX hD hV hsq hΔl hΔm hUΔm hΔlV hVΔm
      h_m_meas h_m_foldA h_m_foldA_uncurry h_m_int h_m_sq_int
      h_score_diff_rate h_product_rate
  exact hAL.tendsto_normal_foldB split hψ_meas hθn_meas hSum_meas

end PLRSystem

end PLR
end Estimation
end Causalean
