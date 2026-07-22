/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Asymptotic linearity for vector-valued estimators

Companion to `Causalean/Stat/CLT/AsymptoticLinearity.lean`.  Generalises the
asymptotic-linearity predicate to a vector-valued parameter
`θ : E := EuclideanSpace ℝ (Fin d)` and a vector-valued influence
function `ψ : X → E`.  The scalar form (`IsAsymLinear`) is kept untouched
so existing AIPW/PlugIn proofs continue to compile; the vector form
(`IsAsymLinearVec`) is the input/output of the multivariate-DML theorems
in `Estimation/OrthogonalMoments/DML.lean` (Chernozhukov form, with Jacobian
`J₀ : E →L[ℝ] E`).

The headline corollary `IsAsymLinearVec.tendsto_normal_vec` packages the
multivariate CLT contact: the rescaled estimator converges in distribution
to the pushforward of the target law `Q : ProbabilityMeasure E` (typically
a multivariate Gaussian with covariance `J₀⁻¹ Σ J₀⁻ᵀ`).  Proved by
absorbing the asymptotic-linearity remainder into the partial-sum CLT
contact via `Tendsto_dist_vec.add_isLittleOp_one`.

Bridge `IsAsymLinearVec.toScalar`: when `E = ℝ`, the vector predicate
reduces to the existing scalar `IsAsymLinear`.
-/

import Causalean.Stat.CLT.AsymptoticLinearity
import Causalean.Stat.Limit.Convergence
import Causalean.Stat.Limit.ConvergenceVec
import Causalean.Stat.Sample
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! # Vector Asymptotic Linearity

This file extends scalar asymptotic linearity to finite-dimensional
vector-valued estimators. `IsAsymLinearVec` records the vector influence
function, finite second moment, and vector `o_p(1)` remainder along a finite
index family, with `IsAsymLinearVec.normalizedSum` and
`IsAsymLinearVec.rescaledEstimator` giving the associated partial sum and scaled
estimator.

The scalar bridge theorems `IsAsymLinearVec.toScalar` and `IsAsymLinear.toVec`
identify the `E = ℝ` specialization with the scalar predicate. The headline
result `IsAsymLinearVec.tendsto_normal_vec` absorbs the vector remainder into a
caller-supplied multivariate CLT contact. -/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ## Vector-valued asymptotic linearity -/

/-- `IsAsymLinearVec θn θ₀ ψ S I` says the (vector-valued) estimator sequence
`θn : ℕ → Ω → E` is asymptotically linear at `θ₀ : E` with influence function
`ψ : X → E`, indexed by the family of finite index sets `I : ℕ → Finset ℕ`.

Fields:

* `mean_zero`  : `∫ ψ dP = 0`  (Bochner integral in `E`).
* `finite_var` : `‖ψ‖² ∈ L¹(P)`.
* `remainder`  : `‖√|I n| · (θn − θ₀) − (1/√|I n|) Σ_{i ∈ I n} ψ(Z_i)‖ = o_p(1)`.

The scalar specialisation `E = ℝ` reduces to `IsAsymLinear` (see
`IsAsymLinearVec.toScalar`).  The full-sample case is `I n = Finset.range n`;
fold-B / fold-K cases are obtained by passing the corresponding fold index
families.  Mirrors `def:est-asym-linear` in
`doc/basic_concepts/po/estimation.tex` lifted to vector-valued targets. -/
structure IsAsymLinearVec
    (θn : ℕ → Ω → E) (θ₀ : E) (ψ : X → E)
    (S : IIDSample Ω X μ P) (I : ℕ → Finset ℕ) : Prop where
  /-- The influence function has Bochner mean zero under `P`. -/
  mean_zero  : ∫ x, ψ x ∂P = 0
  /-- `‖ψ‖² ∈ L¹(P)`: a finite second-moment witness. -/
  finite_var : Integrable (fun x => ‖ψ x‖^2) P
  /-- The vector remainder has norm `o_p(1)` under `μ`. -/
  remainder  :
    IsLittleOp
      (fun n ω =>
        ‖Real.sqrt ((I n).card : ℝ) • (θn n ω - θ₀)
          - (Real.sqrt ((I n).card : ℝ))⁻¹ •
            ∑ i ∈ I n, ψ (S.Z i ω)‖)
      (fun _ => (1 : ℝ)) μ

namespace IsAsymLinearVec

variable {θn : ℕ → Ω → E} {θ₀ : E} {ψ : X → E} {S : IIDSample Ω X μ P}
  {I : ℕ → Finset ℕ}

/-- Vector normalised partial sum `(1/√|I n|) Σ_{i ∈ I n} ψ(Z_i)`. -/
noncomputable def normalizedSum (S : IIDSample Ω X μ P) (ψ : X → E)
    (I : ℕ → Finset ℕ) (n : ℕ) : Ω → E :=
  fun ω => (Real.sqrt ((I n).card : ℝ))⁻¹ • ∑ i ∈ I n, ψ (S.Z i ω)

/-- Vector rescaled estimator `√|I n| · (θn n − θ₀)`. -/
noncomputable def rescaledEstimator (θn : ℕ → Ω → E) (θ₀ : E)
    (I : ℕ → Finset ℕ) (n : ℕ) : Ω → E :=
  fun ω => Real.sqrt ((I n).card : ℝ) • (θn n ω - θ₀)

end IsAsymLinearVec

/-! ## Scalar bridge: `E = ℝ` reduces to the existing `IsAsymLinear` -/

/-- When the parameter space is `ℝ`, the vector predicate `IsAsymLinearVec`
unfolds to the scalar `IsAsymLinear`.  The forward direction is a direct
field-by-field rewrite using `‖x‖ = |x|` on `ℝ` and scalar `•` = `*`. -/
theorem IsAsymLinearVec.toScalar
    {θn : ℕ → Ω → ℝ} {θ₀ : ℝ} {ψ : X → ℝ} {S : IIDSample Ω X μ P}
    {I : ℕ → Finset ℕ}
    (h : IsAsymLinearVec θn θ₀ ψ S I) :
    IsAsymLinear θn θ₀ ψ S I := by
  refine ⟨h.mean_zero, ?_, ?_⟩
  · simpa [Real.norm_eq_abs, sq_abs] using h.finite_var
  · intro ε hε
    have hrem := h.remainder ε hε
    refine hrem.congr fun n => ?_
    congr 1
    ext ω
    simp [Real.norm_eq_abs, smul_eq_mul, abs_abs]

/-- Conversely, scalar asymptotic linearity lifts to the vector predicate. -/
theorem IsAsymLinear.toVec
    {θn : ℕ → Ω → ℝ} {θ₀ : ℝ} {ψ : X → ℝ} {S : IIDSample Ω X μ P}
    {I : ℕ → Finset ℕ}
    (h : IsAsymLinear θn θ₀ ψ S I) :
    IsAsymLinearVec θn θ₀ ψ S I := by
  refine ⟨h.mean_zero, ?_, ?_⟩
  · simpa [Real.norm_eq_abs, sq_abs] using h.finite_var
  · intro ε hε
    have hrem := h.remainder ε hε
    refine hrem.congr fun n => ?_
    congr 1
    ext ω
    simp [Real.norm_eq_abs, smul_eq_mul, abs_abs]

/-! ## Headline corollary (multivariate)

Multivariate analogue of `IsAsymLinear.tendsto_normal`: combines the
caller-supplied vector CLT contact (`_hCLT`) with vector Slutsky absorption
(`Tendsto_dist_vec.add_isLittleOp_one`) to push the rescaled estimator's
pushforward to the target law `Q : ProbabilityMeasure E`. -/

variable [IsProbabilityMeasure μ]

/-- **Vector asymptotic normality.**  Given vector asymptotic linearity at
`θ₀` with influence function `ψ`, and a vector CLT contact (the partial-sum
pushforwards converge to a target law `Q : ProbabilityMeasure E`), the
rescaled estimator converges in distribution to `Q`.

For the canonical case `Q = N(0, ∫ ψ ψᵀ dP)` the conclusion specialises to
the multivariate CLT. -/
theorem IsAsymLinearVec.tendsto_normal_vec
    {θn : ℕ → Ω → E} {θ₀ : E} {ψ : X → E} {S : IIDSample Ω X μ P}
    {I : ℕ → Finset ℕ}
    (Q : ProbabilityMeasure E)
    (_h : IsAsymLinearVec θn θ₀ ψ S I)
    (_hψ_meas : Measurable ψ)
    (_hθn_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinearVec.rescaledEstimator θn θ₀ I n) μ)
    (_hSum_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinearVec.normalizedSum S ψ I n) μ)
    (_hCLT : Tendsto (β := ProbabilityMeasure E)
      (fun n => ⟨μ.map (IsAsymLinearVec.normalizedSum S ψ I n),
                  Measure.isProbabilityMeasure_map (_hSum_meas n)⟩)
      atTop (𝓝 Q)) :
    Tendsto (β := ProbabilityMeasure E)
      (fun n => ⟨μ.map (IsAsymLinearVec.rescaledEstimator θn θ₀ I n),
                  Measure.isProbabilityMeasure_map (_hθn_meas n)⟩)
      atTop (𝓝 Q) := by
  haveI : IsProbabilityMeasure (Q.toMeasure) := Q.2
  change Tendsto_dist_vec (IsAsymLinearVec.rescaledEstimator θn θ₀ I)
    Q.toMeasure μ _hθn_meas
  refine Tendsto_dist_vec.add_isLittleOp_one
    (Q := Q.toMeasure) (Xn := IsAsymLinearVec.normalizedSum S ψ I)
    (Yn := IsAsymLinearVec.rescaledEstimator θn θ₀ I)
    _hSum_meas _hθn_meas ?_ ?_
  · change Tendsto_dist_vec (IsAsymLinearVec.normalizedSum S ψ I)
      Q.toMeasure μ _hSum_meas
    exact _hCLT
  · have := _h.remainder
    simpa [IsAsymLinearVec.normalizedSum, IsAsymLinearVec.rescaledEstimator] using this

end Causalean.Stat
