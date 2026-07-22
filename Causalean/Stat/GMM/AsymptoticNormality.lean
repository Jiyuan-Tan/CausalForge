/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# GMM asymptotic linearity via the combined-score Z-estimator

The asymptotic-linear representation of the GMM estimator is obtained from the
Z-estimator solving the combined estimating equation `GᵀW ḡ_n(θ) = 0`
(Newey & McFadden 1994, §3): the empirical first-order condition of the GMM
criterion `ḡ_n(θ)ᵀ W ḡ_n(θ)`, after fixing the Jacobian weight at its population
value `G`.  Thus GMM asymptotic linearity is a direct corollary of the parametric
Z-estimator linearization theorem `zEstimator_clt`
(`Causalean/Stat/MEstimation/ZEstimatorCLT.lean`)
applied to the combined score `ψ(θ,x) = GᵀW g(θ,x)` (`GMMProblem.score`).

`gmm_asymptotically_linear` instantiates that CLT and identifies the influence
function as `gmmIF = −(GᵀWG)⁻¹GᵀW g(θ₀,·)`. The separate corollary
`gmm_tendsto_normal_vec` composes this linear representation with
`IsAsymLinearVec.tendsto_normal_vec` once the caller supplies the vector-CLT
contact point and measurability obligations. Identifying that target with the
usual sandwich covariance is handled by `GMMProblem.asympVar` and
`GMMProblem.efficiency`, not by the linearity theorem itself.

The Jacobian linkage `reg.J₀_inv = breadInv` is a hypothesis: `reg.J₀` is the
Fréchet derivative of `θ ↦ ∫ GᵀW g(θ) dP`, which by the chain rule equals the
bread `GᵀWG`; we expose the identification of its inverse with the problem's
`breadInv` rather than re-deriving the derivative-through-integral here.

The `hJinv : reg.J₀_inv = prob.breadInv` link is carried as an explicit
hypothesis. It records the model-specific derivative-through-integral
calculation `D[θ ↦ ∫ GᵀW g(θ) dP] = GᵀWG`; this file then handles the generic
GMM-to-Z-estimator reduction once that Jacobian identification is supplied.
-/

import Causalean.Stat.GMM.Setup
import Causalean.Stat.MEstimation.ZEstimatorCLT
import Causalean.Stat.MEstimation.ExtremumConsistency

/-! # GMM Asymptotic Linearity

This file derives asymptotic linearity for generalized method of moments
estimators from the central limit theorem for parametric estimating equations.
The theorem `gmm_asymptotically_linear` applies the Z-estimator CLT to the
combined GMM score and identifies the influence function
`-(G^T W G)^{-1} G^T W g(θ₀, z)`.  The corollary `gmm_tendsto_normal_vec`
transfers that linear representation to a caller-supplied vector CLT target;
the concrete sandwich covariance identification is handled by the GMM setup and
efficiency modules, not by this file. -/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology ContinuousLinearMap

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}
  {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]

/-- **GMM asymptotic linearity.**  A GMM estimator that solves the combined
empirical moment equation and satisfies the Z-estimator consistency, stochastic
equicontinuity, and root-n rate conditions has the usual GMM asymptotic-linear
expansion around the target parameter.

The influence function is

    influence(z) = −(GᵀWG)⁻¹ GᵀW g(θ₀, z).
-/
theorem gmm_asymptotically_linear
    [IsProbabilityMeasure μ] (prob : GMMProblem (E := E) (F := F) P)
    (reg : ZEstimatorRegularity prob.score prob.θ₀ P)
    (hJinv : reg.J₀_inv = prob.breadInv)
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (hConsistent :
      ∀ ε > 0, Tendsto (fun n => μ {ω | ε < ‖θn n ω - prob.θ₀‖}) atTop (𝓝 0))
    (hStochEquicont : StochEquicontAt prob.score prob.θ₀ P μ S θn)
    (hRate : IsBigOp
      (fun n ω => ‖θn n ω - prob.θ₀‖) (fun n => (Real.sqrt (n : ℝ))⁻¹) μ)
    (hMoment :
      ∀ᶠ n in atTop, ∀ᵐ ω ∂μ,
        ∑ i ∈ Finset.range n, prob.score (θn n ω) (S.Z i ω) = 0) :
    IsAsymLinearVec (E := E) θn prob.θ₀ prob.influence S (fun n => Finset.range n) := by
  have h := zEstimator_clt prob.score prob.θ₀ P reg S θn
    hConsistent hStochEquicont hRate hMoment
  -- The Chernozhukov-form influence function of the combined score IS gmmIF.
  have hIF : prob.influence
      = fun z => -(reg.J₀_inv (prob.score prob.θ₀ z)) := by
    funext z
    rw [hJinv]
    simp only [GMMProblem.influence, GMMProblem.score, gmmIF, gmmScore]
  rw [hIF]
  exact h

/-- **GMM asymptotic normality from a supplied vector CLT contact.** Combining
`gmm_asymptotically_linear` with `IsAsymLinearVec.tendsto_normal_vec`, the
rescaled GMM estimator converges to the caller-supplied vector CLT target `Q`.
The theorem is parametric in the limiting law: the concrete Gaussian or sandwich
identification is supplied through `hCLT` and the target law `Q`. -/
theorem gmm_tendsto_normal_vec
    [IsProbabilityMeasure μ] (prob : GMMProblem (E := E) (F := F) P)
    (reg : ZEstimatorRegularity prob.score prob.θ₀ P)
    (hJinv : reg.J₀_inv = prob.breadInv)
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (hConsistent :
      ∀ ε > 0, Tendsto (fun n => μ {ω | ε < ‖θn n ω - prob.θ₀‖}) atTop (𝓝 0))
    (hStochEquicont : StochEquicontAt prob.score prob.θ₀ P μ S θn)
    (hRate : IsBigOp
      (fun n ω => ‖θn n ω - prob.θ₀‖) (fun n => (Real.sqrt (n : ℝ))⁻¹) μ)
    (hMoment :
      ∀ᶠ n in atTop, ∀ᵐ ω ∂μ,
        ∑ i ∈ Finset.range n, prob.score (θn n ω) (S.Z i ω) = 0)
    (Q : ProbabilityMeasure E)
    (hIF_meas : Measurable prob.influence)
    (hθn_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinearVec.rescaledEstimator θn prob.θ₀ (fun m => Finset.range m) n) μ)
    (hSum_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinearVec.normalizedSum S prob.influence (fun m => Finset.range m) n) μ)
    (hCLT : Tendsto (β := ProbabilityMeasure E)
      (fun n => ⟨μ.map
        (IsAsymLinearVec.normalizedSum S prob.influence (fun m => Finset.range m) n),
        Measure.isProbabilityMeasure_map (hSum_meas n)⟩)
      atTop (𝓝 Q)) :
    Tendsto (β := ProbabilityMeasure E)
      (fun n => ⟨μ.map
        (IsAsymLinearVec.rescaledEstimator θn prob.θ₀ (fun m => Finset.range m) n),
        Measure.isProbabilityMeasure_map (hθn_meas n)⟩)
      atTop (𝓝 Q) := by
  exact IsAsymLinearVec.tendsto_normal_vec Q
    (gmm_asymptotically_linear prob reg hJinv S θn hConsistent hStochEquicont hRate hMoment)
    hIF_meas hθn_meas hSum_meas hCLT

/-- **GMM asymptotic linearity from extremum primitives.**  The GMM analogue of
`zEstimator_clt_of_extremum`: `gmm_asymptotically_linear` with the consistency
hypothesis discharged from a Glivenko–Cantelli GMM criterion `m` with a
well-separated population maximum at `θ₀` of which `θn` is a sample maximiser.
The classical instance is `m θ = −ḡ_n(θ)ᵀ W ḡ_n(θ)` (the GMM objective), whose
score is `prob.score`. -/
theorem gmm_asymptotically_linear_of_extremum
    [IsProbabilityMeasure μ] (prob : GMMProblem (E := E) (F := F) P)
    (reg : ZEstimatorRegularity prob.score prob.θ₀ P)
    (hJinv : reg.J₀_inv = prob.breadInv)
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (m : E → X → ℝ)
    (hGC : GlivenkoCantelli S m)
    (hArgmax : ∀ n ω,
      S.sampleMean (m prob.θ₀) n ω ≤ S.sampleMean (m (θn n ω)) n ω)
    (hSep : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ θ : E, ε ≤ dist θ prob.θ₀ →
        (∫ x, m θ x ∂P) + η ≤ ∫ x, m prob.θ₀ x ∂P)
    (hStochEquicont : StochEquicontAt prob.score prob.θ₀ P μ S θn)
    (hRate : IsBigOp
      (fun n ω => ‖θn n ω - prob.θ₀‖) (fun n => (Real.sqrt (n : ℝ))⁻¹) μ)
    (hMoment :
      ∀ᶠ n in atTop, ∀ᵐ ω ∂μ,
        ∑ i ∈ Finset.range n, prob.score (θn n ω) (S.Z i ω) = 0) :
    IsAsymLinearVec (E := E) θn prob.θ₀ prob.influence S (fun n => Finset.range n) :=
  gmm_asymptotically_linear prob reg hJinv S θn
    (consistent_lt_norm_of_le_dist θn prob.θ₀
      (mEstimator_consistent_of_glivenkoCantelli S m prob.θ₀ θn hGC hArgmax hSep))
    hStochEquicont hRate hMoment

/-- **GMM asymptotic linearity with the equicontinuity hypothesis discharged.**
The GMM analogue of `zEstimator_clt_of_donsker`: `gmm_asymptotically_linear`
with the opaque modulus `hStochEquicont` replaced by the class-level Donsker
property `AsymptoticEquicont prob.score prob.θ₀ P μ S`, reconstructed via
`stochEquicontAt_of_asymptoticEquicont` from `hAEC` and consistency. -/
theorem gmm_asymptotically_linear_of_donsker
    [IsProbabilityMeasure μ] (prob : GMMProblem (E := E) (F := F) P)
    (reg : ZEstimatorRegularity prob.score prob.θ₀ P)
    (hJinv : reg.J₀_inv = prob.breadInv)
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (hConsistent :
      ∀ ε > 0, Tendsto (fun n => μ {ω | ε < ‖θn n ω - prob.θ₀‖}) atTop (𝓝 0))
    (hAEC : AsymptoticEquicont prob.score prob.θ₀ P μ S)
    (hRate : IsBigOp
      (fun n ω => ‖θn n ω - prob.θ₀‖) (fun n => (Real.sqrt (n : ℝ))⁻¹) μ)
    (hMoment :
      ∀ᶠ n in atTop, ∀ᵐ ω ∂μ,
        ∑ i ∈ Finset.range n, prob.score (θn n ω) (S.Z i ω) = 0) :
    IsAsymLinearVec (E := E) θn prob.θ₀ prob.influence S (fun n => Finset.range n) :=
  gmm_asymptotically_linear prob reg hJinv S θn hConsistent
    (stochEquicontAt_of_asymptoticEquicont prob.score prob.θ₀ S θn hAEC hConsistent)
    hRate hMoment

/-- **GMM asymptotic linearity from primitive conditions: both opaque hypotheses
discharged.**  The GMM analogue of `zEstimator_clt_of_extremum_donsker`: neither
`hConsistent` nor `hStochEquicont` is assumed.  Consistency is derived from the
Glivenko–Cantelli GMM criterion `m` with well-separated maximum, then fed to
both the linearisation and the `StochEquicontAt` reduction applied to `hAEC`. -/
theorem gmm_asymptotically_linear_of_extremum_donsker
    [IsProbabilityMeasure μ] (prob : GMMProblem (E := E) (F := F) P)
    (reg : ZEstimatorRegularity prob.score prob.θ₀ P)
    (hJinv : reg.J₀_inv = prob.breadInv)
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (m : E → X → ℝ)
    (hGC : GlivenkoCantelli S m)
    (hArgmax : ∀ n ω,
      S.sampleMean (m prob.θ₀) n ω ≤ S.sampleMean (m (θn n ω)) n ω)
    (hSep : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ θ : E, ε ≤ dist θ prob.θ₀ →
        (∫ x, m θ x ∂P) + η ≤ ∫ x, m prob.θ₀ x ∂P)
    (hAEC : AsymptoticEquicont prob.score prob.θ₀ P μ S)
    (hRate : IsBigOp
      (fun n ω => ‖θn n ω - prob.θ₀‖) (fun n => (Real.sqrt (n : ℝ))⁻¹) μ)
    (hMoment :
      ∀ᶠ n in atTop, ∀ᵐ ω ∂μ,
        ∑ i ∈ Finset.range n, prob.score (θn n ω) (S.Z i ω) = 0) :
    IsAsymLinearVec (E := E) θn prob.θ₀ prob.influence S (fun n => Finset.range n) :=
  have hcons := consistent_lt_norm_of_le_dist θn prob.θ₀
    (mEstimator_consistent_of_glivenkoCantelli S m prob.θ₀ θn hGC hArgmax hSep)
  gmm_asymptotically_linear prob reg hJinv S θn hcons
    (stochEquicontAt_of_asymptoticEquicont prob.score prob.θ₀ S θn hAEC hcons)
    hRate hMoment

end Causalean.Stat
