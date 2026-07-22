/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Discharging the consistency hypothesis of the Z- / M-estimator CLT

The headline parametric-inference theorems `zEstimator_clt`
(`Causalean/Stat/MEstimation/ZEstimatorCLT.lean`) and `gmm_asymptotically_linear`
(`Causalean/Stat/GMM/AsymptoticNormality.lean`) both *assume* the estimator is
consistent,

    hConsistent : ∀ ε > 0, Tendsto (fun n => μ {ω | ε < ‖θn n ω − θ₀‖}) atTop (𝓝 0),

as a black-box input.  Classically (Newey–McFadden 1994 Thm 2.1; van der Vaart
1998 Thm 5.7) consistency is *derived* from primitive conditions on the
optimisation problem: a **Glivenko–Cantelli** criterion class plus a
**well-separated population maximum**.  Now that the empirical-process layer
(`Causalean/Stat/EmpiricalProcess/`) provides `mEstimator_consistent_of_glivenkoCantelli`,
we can discharge `hConsistent` and expose the CLT directly in terms of those
primitives.

This file is purely additive: it imports the existing (already-proven) CLT
theorems and the consistency engine, and threads them together.  The original
`hConsistent`-taking statements are unchanged and remain available for callers
who establish consistency by other means.

* `consistent_lt_norm_of_le_dist` — format bridge: turn the consistency
  conclusion of the empirical-process layer (`ε ≤ dist (θ̂ n) θ₀`) into the
  `ε < ‖θ̂ n − θ₀‖` form the CLT layer consumes.  Pure metric/squeeze argument.
* `zEstimator_clt_of_extremum` — the Z-estimator CLT with `hConsistent`
  replaced by an extremum-consistency package `(m, hGC, hArgmax, hSep)`: the
  estimator is a sample maximiser of a Glivenko–Cantelli criterion `m` whose
  population maximum is well separated at `θ₀`.  (Typically `ψ = ∂m/∂θ`, so the
  same estimator satisfies the score FOC `hMoment` and the argmax condition
  `hArgmax`; we keep `m` and `ψ` as independent inputs so the reduction needs no
  differentiability bookkeeping.)

The parallel GMM reductions (`gmm_asymptotically_linear_of_extremum` etc.) reuse
`consistent_lt_norm_of_le_dist` from here but live beside `gmm_asymptotically_linear`
in `Causalean/Stat/GMM/AsymptoticNormality.lean`.
-/

import Causalean.Stat.MEstimation.ZEstimatorCLT
import Causalean.Stat.EmpiricalProcess.MEstimatorConsistency
import Causalean.Stat.EmpiricalProcess.Equicontinuity.Modulus

/-! # Extremum consistency for M-estimation

This module packages primitive extremum-estimation conditions that imply the
consistency assumptions used by Z-estimator and GMM central-limit theorems.  The
format bridge `consistent_lt_norm_of_le_dist` adapts the empirical-process
consistency theorem to the CLT layer, while `zEstimator_clt_of_extremum`,
`zEstimator_clt_of_donsker`, and `zEstimator_clt_of_extremum_donsker` discharge
opaque consistency and equicontinuity hypotheses from Glivenko-Cantelli,
well-separated-optimum, and class-level equicontinuity inputs.  (The parallel GMM
reductions live in `Causalean/Stat/GMM/AsymptoticNormality.lean`.)
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-- **Format bridge.**  On a normed group `dist x θ₀ = ‖x − θ₀‖`, so the
consistency statement produced by `mEstimator_consistent_of_glivenkoCantelli`
(phrased with `ε ≤ dist (θn n) θ₀`) implies the strictly-larger-radius form
`ε < ‖θn n − θ₀‖` consumed by the CLT layer.  `{ε < ‖·‖} ⊆ {ε ≤ dist}`, so the
measures are squeezed to `0`. -/
theorem consistent_lt_norm_of_le_dist {E : Type*} [NormedAddCommGroup E]
    (θn : ℕ → Ω → E) (θ₀ : E)
    (h : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ {ω | ε ≤ dist (θn n ω) θ₀}) atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun n => μ {ω | ε < ‖θn n ω - θ₀‖}) atTop (𝓝 0) := by
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (h ε hε)
    (Eventually.of_forall fun n => zero_le _)
    (Eventually.of_forall fun n => measure_mono ?_)
  intro ω hω
  simp only [Set.mem_setOf_eq, dist_eq_norm] at hω ⊢
  exact le_of_lt hω

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Z-estimator CLT from extremum primitives.**  Identical conclusion to
`zEstimator_clt`, but the opaque consistency hypothesis is replaced by the
classical extremum-estimator package:

* `hGC`     — the criterion class `{m θ : θ}` is Glivenko–Cantelli (uniform LLN);
* `hArgmax` — `θn` is a sample maximiser of the criterion (`Mₙ θ₀ ≤ Mₙ (θn)`);
* `hSep`    — the population maximum `M θ = ∫ m θ dP` is well separated at `θ₀`.

Consistency `θn →_p θ₀` is then *derived* via
`mEstimator_consistent_of_glivenkoCantelli` and fed to `zEstimator_clt`.  The
remaining inputs (`hStochEquicont` Donsker modulus, `hRate`, `hMoment` score
FOC) are unchanged. -/
theorem zEstimator_clt_of_extremum
    (ψ : E → X → E) (θ₀ : E) (P : Measure X)
    (reg : ZEstimatorRegularity ψ θ₀ P)
    [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (m : E → X → ℝ)
    (hGC : GlivenkoCantelli S m)
    (hArgmax : ∀ n ω,
      S.sampleMean (m θ₀) n ω ≤ S.sampleMean (m (θn n ω)) n ω)
    (hSep : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ θ : E, ε ≤ dist θ θ₀ → (∫ x, m θ x ∂P) + η ≤ ∫ x, m θ₀ x ∂P)
    (hStochEquicont : StochEquicontAt ψ θ₀ P μ S θn)
    (hRate : IsBigOp
      (fun n ω => ‖θn n ω - θ₀‖) (fun n => (Real.sqrt (n : ℝ))⁻¹) μ)
    (hMoment :
      ∀ᶠ n in atTop, ∀ᵐ ω ∂μ,
        ∑ i ∈ Finset.range n, ψ (θn n ω) (S.Z i ω) = 0) :
    IsAsymLinearVec (E := E) θn θ₀
      (fun z => -(reg.J₀_inv (ψ θ₀ z))) S (fun n => Finset.range n) :=
  zEstimator_clt ψ θ₀ P reg S θn
    (consistent_lt_norm_of_le_dist θn θ₀
      (mEstimator_consistent_of_glivenkoCantelli S m θ₀ θn hGC hArgmax hSep))
    hStochEquicont hRate hMoment

/-- **Z-estimator CLT with the equicontinuity hypothesis discharged.**
Identical conclusion to `zEstimator_clt`, but the opaque empirical-process
modulus `hStochEquicont : StochEquicontAt ψ θ₀ P μ S θn` is replaced by the
*class-level* Donsker / asymptotic-equicontinuity property
`AsymptoticEquicont ψ θ₀ P μ S` (a property of the score family, independent of
the estimator sequence).  `StochEquicontAt` is reconstructed from `hAEC` and the
consistency hypothesis via `stochEquicontAt_of_asymptoticEquicont`. -/
theorem zEstimator_clt_of_donsker
    (ψ : E → X → E) (θ₀ : E) (P : Measure X)
    (reg : ZEstimatorRegularity ψ θ₀ P)
    [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (hConsistent :
      ∀ ε > 0, Tendsto (fun n => μ {ω | ε < ‖θn n ω - θ₀‖}) atTop (𝓝 0))
    (hAEC : AsymptoticEquicont ψ θ₀ P μ S)
    (hRate : IsBigOp
      (fun n ω => ‖θn n ω - θ₀‖) (fun n => (Real.sqrt (n : ℝ))⁻¹) μ)
    (hMoment :
      ∀ᶠ n in atTop, ∀ᵐ ω ∂μ,
        ∑ i ∈ Finset.range n, ψ (θn n ω) (S.Z i ω) = 0) :
    IsAsymLinearVec (E := E) θn θ₀
      (fun z => -(reg.J₀_inv (ψ θ₀ z))) S (fun n => Finset.range n) :=
  zEstimator_clt ψ θ₀ P reg S θn hConsistent
    (stochEquicontAt_of_asymptoticEquicont ψ θ₀ S θn hAEC hConsistent)
    hRate hMoment

/-- **Z-estimator CLT from primitive conditions: both opaque hypotheses
discharged.**  Fuses `zEstimator_clt_of_extremum` (consistency from a
Glivenko–Cantelli criterion `m` with a well-separated population maximum) with
`zEstimator_clt_of_donsker` (equicontinuity from the class-level Donsker
property `hAEC`).  The resulting statement assumes neither `hConsistent` nor
`hStochEquicont`: the single derived consistency conclusion is threaded into
*both* the estimating-equation linearisation and the `StochEquicontAt`
reduction. -/
theorem zEstimator_clt_of_extremum_donsker
    (ψ : E → X → E) (θ₀ : E) (P : Measure X)
    (reg : ZEstimatorRegularity ψ θ₀ P)
    [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (m : E → X → ℝ)
    (hGC : GlivenkoCantelli S m)
    (hArgmax : ∀ n ω,
      S.sampleMean (m θ₀) n ω ≤ S.sampleMean (m (θn n ω)) n ω)
    (hSep : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ θ : E, ε ≤ dist θ θ₀ → (∫ x, m θ x ∂P) + η ≤ ∫ x, m θ₀ x ∂P)
    (hAEC : AsymptoticEquicont ψ θ₀ P μ S)
    (hRate : IsBigOp
      (fun n ω => ‖θn n ω - θ₀‖) (fun n => (Real.sqrt (n : ℝ))⁻¹) μ)
    (hMoment :
      ∀ᶠ n in atTop, ∀ᵐ ω ∂μ,
        ∑ i ∈ Finset.range n, ψ (θn n ω) (S.Z i ω) = 0) :
    IsAsymLinearVec (E := E) θn θ₀
      (fun z => -(reg.J₀_inv (ψ θ₀ z))) S (fun n => Finset.range n) :=
  have hcons := consistent_lt_norm_of_le_dist θn θ₀
    (mEstimator_consistent_of_glivenkoCantelli S m θ₀ θn hGC hArgmax hSep)
  zEstimator_clt ψ θ₀ P reg S θn hcons
    (stochEquicontAt_of_asymptoticEquicont ψ θ₀ S θn hAEC hcons)
    hRate hMoment

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

-- The GMM analogues of the Z-estimator CLT corollaries
-- (`gmm_asymptotically_linear_of_extremum` / `_of_donsker` / `_of_extremum_donsker`)
-- now live beside `gmm_asymptotically_linear` in
-- `Causalean/Stat/GMM/AsymptoticNormality.lean`, so this M-estimation module no
-- longer depends on the GMM layer.

end Causalean.Stat
