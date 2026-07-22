/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Z- / M-estimator regularity (parametric inference workhorse, structure layer)

Regularity bundle `ZEstimatorRegularity` for the parametric Z/M-estimator CLT
(`def:par-z-clt`).  The headline theorem `zEstimator_clt` lives downstream in
`Causalean/Stat/MEstimation/ZEstimatorCLT.lean` because its proof pulls in
`Causalean/Stat/MEstimation/EmpiricalExpansion.lean`, which in turn imports this file for
`ZEstimatorRegularity`.  Splitting the structure (here) from the theorem (in
`ZEstimatorCLT.lean`) keeps the import DAG acyclic.

Reference: van der Vaart (1998), §5.6, Theorem 5.41; Newey & McFadden (1994).
Spec: `def:par-smoothness`, `thm:par-z-clt` in
`doc/basic_concepts/Semi-parametric Inference/parametric_inference.tex`.
-/

import Causalean.Stat.CLT.AsymptoticLinearity
import Causalean.Stat.Limit.Convergence
import Causalean.Stat.Sample
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-! # Z-estimator regularity

This module records the public regularity bundle `ZEstimatorRegularity` for
parametric Z-estimator and M-estimator central limit theorems.  The structure
collects population identification, derivative invertibility, finite variance,
measurability, local integrability, continuity of the population Jacobian, and
an integrable `L2` score envelope used by the empirical-expansion and
asymptotic-linearity layers.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Regularity conditions** for the Z-estimator CLT.

Existing fields (population identification + smoothness + measurability):

* `identification`     : `∫ ψ(z; θ₀) dP = 0` (population moment vanishes at the
                          truth).
* `J₀`                 : Jacobian of the population moment at `θ₀`,
                          `J₀ := ∂_θ ∫ ψ(z; θ) dP |_{θ=θ₀}`.
* `J₀_inv`             : inverse of `J₀`.
* `J₀_inverse`         : witness `J₀ ∘ J₀_inv = id`.
* `J₀_spec`            : `J₀` is the Fréchet derivative of
                          `θ ↦ ∫ ψ(z; θ) dP` at `θ₀`.
* `finite_var`         : `∫ ‖ψ(z; θ₀)‖² dP < ∞`.
* `psi_meas`           : `ψ(·; θ)` is measurable for every `θ`.

Empirical-process / smoothness fields (added for the CLT proof,
van der Vaart 1998 §5.6, `def:par-smoothness`):

* `jacobian_continuity`  : `θ ↦ ∫ ψ(z;θ) dP` is continuous at `θ₀`.  Implied
                            by `J₀_spec`, but stated explicitly so downstream
                            CLT code does not have to redo the derivation.
* `psi_int_neighborhood` : `ψ(·;θ)` is `P`-integrable on a neighborhood of
                            `θ₀`, ensuring `∫ ψ(·;θ) dP` is well-defined for
                            all `θ` close enough to `θ₀`. -/
structure ZEstimatorRegularity
    (ψ : E → X → E) (θ₀ : E) (P : Measure X) where
  identification : ∫ z, ψ θ₀ z ∂P = 0
  J₀             : E →L[ℝ] E
  J₀_inv         : E →L[ℝ] E
  J₀_inverse     : J₀.comp J₀_inv = ContinuousLinearMap.id ℝ E
  J₀_spec        : HasFDerivAt (fun θ => ∫ z, ψ θ z ∂P) J₀ θ₀
  finite_var     : Integrable (fun z => ‖ψ θ₀ z‖^2) P
  psi_meas       : ∀ θ, Measurable (ψ θ)
  /-- `θ ↦ ∫ ψ(z;θ) dP` is continuous at `θ₀`.  Follows from `J₀_spec` but
  stated explicitly so downstream proofs can quote it directly. -/
  jacobian_continuity :
    ContinuousAt (fun θ : E => ∫ z, ψ θ z ∂P) θ₀
  /-- `ψ(·;θ)` is `P`-integrable on a neighborhood of `θ₀`. -/
  psi_int_neighborhood :
    ∃ δ : ℝ, 0 < δ ∧ ∀ θ : E, ‖θ - θ₀‖ < δ → Integrable (ψ θ) P
  /-- **Integrable almost-everywhere envelope** for the local score differences.
  Near the target parameter, outside one `P`-null observation set, every local
  score change is bounded by the parameter displacement times a nonnegative
  measurable envelope whose square is integrable under the sampling law. This is
  an `L²` envelope form of the usual local square-integrable smoothness condition
  in van der Vaart (1998), §5.6, and Newey--McFadden style Z-estimation
  arguments.

  The null set is uniform over nearby parameters, which is enough to transfer the
  bound to random sample-dependent estimators after pulling the a.e. statement
  through each IID coordinate. Used to close `score_diff_L2_isLittleOp_sqrt` in
  `EmpiricalExpansion.lean`. -/
  score_envelope :
    ∃ δ : ℝ, 0 < δ ∧ ∃ F : X → ℝ,
      Measurable F ∧ (∀ z, 0 ≤ F z) ∧ Integrable (fun z => F z ^ 2) P ∧
      ∀ᵐ z ∂P, ∀ θ : E, ‖θ - θ₀‖ < δ →
        ‖ψ θ z - ψ θ₀ z‖ ≤ ‖θ - θ₀‖ * F z

end Causalean.Stat
