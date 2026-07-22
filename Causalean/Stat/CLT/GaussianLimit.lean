/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The concrete limiting Gaussian of the multivariate CLT

`Causalean/Stat/CLT/MultivariateCLT.lean` proves the Cramér–Wold reduction against an
*abstract* target `Q` carrying the hypothesis
`charFun Q t = exp(−½ ∫⟪t,ψ⟫² dP)`.  This file constructs that target
concretely and discharges the hypothesis, completing the de-abstraction.

`gaussianLimit ψ` is the centered Gaussian on `E` with covariance the
second-moment operator `Σ` of `ψ` (`Causalean/Stat/CLT/SecondMomentOperator.lean`).  It
is built as `(stdGaussian E).map √Σ` where `√Σ` is the positive operator square
root (`Causalean/Mathlib/OperatorSqrt.lean`) and `stdGaussian E` is the standard
Gaussian with identity covariance (`Causalean/Mathlib/StandardGaussian.lean`):

* `IsGaussian (gaussianLimit ψ)` — pushforward of a Gaussian by a linear map;
* `gaussianLimit_mean` — it is centered;
* `gaussianLimit_covarianceBilin` — its covariance form is `∫⟪t,ψ⟫⟪t,ψ⟫ dP`,
  via `covarianceBilin (μ.map L) = covarianceBilin μ (L† ·)(L† ·)`,
  self-adjointness `√Σ† = √Σ`, and the square law `√Σ ∘ √Σ = Σ`;
* `gaussianLimit_charFun` — the `hQ` shape `exp(−½ ∫⟪t,ψ⟫² dP)`, through the
  `charFun_isGaussian_of_cov_eq` bridge;
* `IIDSample.clt_normalizedSum_vec` — the multivariate CLT against the *concrete*
  Gaussian limit, with no abstract-`Q` / charFun hypothesis remaining.
-/
import Causalean.Stat.CLT.MultivariateCLT
import Causalean.Stat.CLT.SecondMomentOperator
import Causalean.Stat.CLT.GaussianCharFunBridge
import Causalean.Mathlib.StandardGaussian

/-! # Gaussian Limit Law

This file constructs the concrete centered Gaussian law that appears in the
multivariate central limit theorem for vector-valued influence functions. The
covariance is the second-moment operator of the influence function, so the
abstract characteristic-function target from the Cramér-Wold argument becomes an
explicit probability law.

The construction is `gaussianLimit`, with instances showing it is Gaussian and
probabilistic. Theorems `gaussianLimit_mean`,
`gaussianLimit_covarianceBilin`, and `gaussianLimit_charFun` identify its mean,
covariance, and characteristic function. The final theorem
`IIDSample.clt_normalizedSum_vec` gives the multivariate CLT against this
concrete Gaussian limit. -/

open MeasureTheory ProbabilityTheory Complex Causalean.Mathlib
open scoped RealInnerProductSpace

namespace Causalean.Stat

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
  {ψ : X → E} (hψ : Measurable ψ) (hvar : Integrable (fun x => ‖ψ x‖ ^ 2) P)

/-- The limiting Gaussian law of the multivariate CLT: the centered Gaussian on
`E` with covariance the second-moment operator of `ψ`, realised as
`(stdGaussian E).map √Σ`. -/
noncomputable def gaussianLimit : Measure E :=
  (stdGaussian E).map (secondMomentLM_isPositive hψ hvar).posSqrtCLM

/-- The limiting law is Gaussian. -/
instance : IsGaussian (gaussianLimit hψ hvar) := by
  unfold gaussianLimit; infer_instance

/-- The limiting Gaussian law is a probability law. -/
instance : IsProbabilityMeasure (gaussianLimit hψ hvar) := inferInstance

omit [IsProbabilityMeasure P] in
/-- The limiting Gaussian is centered. -/
theorem gaussianLimit_mean : ∫ x, x ∂(gaussianLimit hψ hvar) = 0 := by
  have hL : ∫ x, x ∂(gaussianLimit hψ hvar)
      = (secondMomentLM_isPositive hψ hvar).posSqrtCLM (∫ x, x ∂(stdGaussian E)) := by
    rw [gaussianLimit, integral_map (by fun_prop) (by fun_prop)]
    exact ContinuousLinearMap.integral_comp_comm _ IsGaussian.integrable_id
  rw [hL, stdGaussian_mean, map_zero]

omit [IsProbabilityMeasure P] in
/-- The covariance form of the limiting Gaussian recovers the asymptotic-variance
integral `∫⟪t,ψ⟫⟪t,ψ⟫ dP`. -/
theorem gaussianLimit_covarianceBilin (t : E) :
    covarianceBilin (gaussianLimit hψ hvar) t t = ∫ x, ⟪t, ψ x⟫ * ⟪t, ψ x⟫ ∂P := by
  set hpos := secondMomentLM_isPositive hψ hvar with hposdef
  -- `√Σ ∘ √Σ = Σ` at the point `t`
  have hcomp : hpos.posSqrtCLM (hpos.posSqrtCLM t) = secondMomentLM hψ hvar t := by
    have h := hpos.posSqrtCLM_comp_self
    calc hpos.posSqrtCLM (hpos.posSqrtCLM t)
        = (hpos.posSqrtCLM ∘L hpos.posSqrtCLM) t := rfl
      _ = ((secondMomentLM hψ hvar).toContinuousLinearMap) t := by rw [h]
      _ = secondMomentLM hψ hvar t := rfl
  -- self-adjointness turns `⟪√Σ t, √Σ t⟫` into `⟪t, Σ t⟫`
  have hsa : (⟪hpos.posSqrtCLM t, hpos.posSqrtCLM t⟫ : ℝ) = ⟪t, secondMomentLM hψ hvar t⟫ := by
    rw [(ContinuousLinearMap.adjoint_inner_right hpos.posSqrtCLM t (hpos.posSqrtCLM t)).symm,
      hpos.posSqrtCLM_adjoint, hcomp]
  rw [gaussianLimit, covarianceBilin_map IsGaussian.memLp_two_id hpos.posSqrtCLM,
    hpos.posSqrtCLM_adjoint, covarianceBilin_stdGaussian, hsa,
    show (⟪t, secondMomentLM hψ hvar t⟫ : ℝ) = ⟪secondMomentLM hψ hvar t, t⟫ from
      real_inner_comm _ _,
    secondMomentLM_inner hψ hvar t t]

omit [IsProbabilityMeasure P] in
/-- The characteristic function of the limiting Gaussian is exactly the abstract
target `exp(−½ ∫⟪t,ψ⟫² dP)` of `MultivariateCLT`. -/
theorem gaussianLimit_charFun (t : E) :
    charFun (gaussianLimit hψ hvar) t
      = Complex.exp (-(((∫ x, (⟪t, ψ x⟫) ^ 2 ∂P : ℝ)) : ℂ) / 2) := by
  refine charFun_isGaussian_of_cov_eq (ψ := ψ) (gaussianLimit hψ hvar)
    (gaussianLimit_mean hψ hvar) (fun s => ?_) t
  rw [gaussianLimit_covarianceBilin]
  exact integral_congr_ae (ae_of_all _ fun x => (pow_two (⟪s, ψ x⟫)).symm)

/-- **Multivariate CLT against the concrete Gaussian limit.**  Under integrable,
mean-zero, square-integrable `ψ`, the vector normalised sum converges in
distribution to `gaussianLimit ψ`, the centered Gaussian with covariance the
second-moment operator of `ψ`.  No abstract target or charFun hypothesis
remains. -/
theorem IIDSample.clt_normalizedSum_vec (S : IIDSample Ω X μ P)
    (hψ_int : Integrable ψ P) (hmean : ∫ x, ψ x ∂P = 0)
    (hSum_meas : ∀ n,
      AEMeasurable (IsAsymLinearVec.normalizedSum S ψ (fun m => Finset.range m) n) μ) :
    Tendsto_dist_vec (IsAsymLinearVec.normalizedSum S ψ (fun m => Finset.range m))
      (gaussianLimit hψ hvar) μ hSum_meas :=
  S.clt_normalizedSum_vec_of_charFun hψ hψ_int hmean hvar (gaussianLimit hψ hvar)
    (gaussianLimit_charFun hψ hvar) hSum_meas

end Causalean.Stat
