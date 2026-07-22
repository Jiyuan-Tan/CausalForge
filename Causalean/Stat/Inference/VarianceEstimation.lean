/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Consistent variance / covariance estimation for the i.i.d. sample type

Consistency of empirical variance- and covariance-matrix estimators for the
`Causalean.Stat.IIDSample` model, supplying the `σ̂ →ₚ σ₀` hypothesis consumed by
the generic studentized CLT (`Causalean/Stat/Inference/Studentize.lean`,
`Tendsto_dist.div_tendsto_inProb_gaussian`).

* `IIDSample.sampleMean_mul_tendsto_inProb` — empirical mean of an arbitrary
  product `g₁ · g₂` of two measurable, jointly-integrable statistics converges
  in probability to its population integral.  Direct application of the WLLN to
  `g := g₁ · g₂`.
* `IIDSample.sampleCov_entry_tendsto_inProb` — entrywise covariance-matrix
  consistency for a vector influence function `ψ : X → E` (`E` a finite-
  dimensional inner-product space).  Coordinates are extracted by two continuous
  linear functionals `φ φ' : E →L[ℝ] ℝ` (the caller supplies the coordinate
  projections — e.g. `EuclideanSpace.proj j`); for each pair, the empirical mean
  of `φ (ψ x) * φ' (ψ x)` converges in probability to
  `∫ x, φ (ψ x) * φ' (ψ x) ∂P`.  Entrywise integrability is derived from the
  single hypothesis `Integrable (fun x => ‖ψ x‖²) P` via the operator-norm
  bound `|φ (ψ x)| ≤ ‖φ‖ · ‖ψ x‖`.  Working through abstract functionals keeps
  the statement basis-agnostic while remaining fully general.
* `sqrt_var_tendsto_inProb` (`Tendsto_inProb.sqrt`) — packaging for the
  studentized layer: from `σ̂² →ₚ σ₀²` with `σ₀ > 0`, conclude
  `√(σ̂²) →ₚ σ₀`.  Continuous mapping with `Real.sqrt` (continuous everywhere),
  reusing `Tendsto_inProb.comp_continuousAt`.
-/

import Causalean.Stat.Limit.WLLN
import Causalean.Stat.Limit.Convergence
import Causalean.Stat.Limit.ContinuousMapping
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
This file proves variance and covariance consistency tools for i.i.d. samples.
Inside `IIDSample`, `sampleMean_mul_tendsto_inProb` applies the WLLN to empirical
means of products, and `sampleCov_entry_tendsto_inProb` turns a square-integrable
vector influence function into entrywise covariance-matrix consistency for any
pair of continuous linear coordinate functionals.

The helper `abs_apply_mul_le_norm_sq` supplies the domination bound needed for
entrywise integrability.  The final packaging lemmas `Tendsto_inProb.sqrt` and
`sqrt_var_tendsto_inProb` convert variance-estimator consistency into
standard-error consistency, the input expected by the studentized CLT.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

namespace IIDSample

/-! ## Scalar product means -/

/-- **Empirical mean of a product.**  For two measurable real-valued statistics
`g₁, g₂` of an i.i.d. sample whose product is integrable, the empirical mean
`S.sampleMean (g₁ · g₂) N` converges in probability to the population integral
`∫ x, g₁ x * g₂ x ∂P`.  Direct application of the generic WLLN to the product
`g := fun x => g₁ x * g₂ x`.

Specializing `g₁ = g₂ = ψ` recovers second-moment / variance consistency
(`sampleSecondMoment_tendsto_inProb`); the general two-factor form is what the
entrywise covariance lemma below needs. -/
theorem sampleMean_mul_tendsto_inProb
    (S : IIDSample Ω X μ P) [IsProbabilityMeasure P] {g₁ g₂ : X → ℝ}
    (hg₁_meas : Measurable g₁) (hg₂_meas : Measurable g₂)
    (hint : Integrable (fun ω => g₁ (S.Z 0 ω) * g₂ (S.Z 0 ω)) μ) :
    Tendsto_inProb (S.sampleMean (fun x => g₁ x * g₂ x))
      (fun _ => ∫ x, g₁ x * g₂ x ∂P) μ :=
  S.sampleMean_tendsto_inProb (hg₁_meas.mul hg₂_meas) hint

/-! ## Covariance-matrix consistency (entrywise)

For a vector influence function `ψ : X → E` with `E` a finite-dimensional
inner-product space, each coordinate of `ψ` is recovered by a continuous linear
functional `φ : E →L[ℝ] ℝ`.  The covariance matrix `∫ ψ ψᵀ dP` is estimated
entrywise by the empirical mean of `φ (ψ ·) * φ' (ψ ·)`; consistency is a direct
WLLN application once entrywise integrability is in hand.  The natural single
hypothesis is `Integrable (fun x => ‖ψ x‖²) P`, from which each entry product is
integrable via the operator-norm bound `|φ v| ≤ ‖φ‖ · ‖v‖`.

The coordinate functionals are supplied by the caller; for
`E = EuclideanSpace ℝ (Fin d)` take `φ = EuclideanSpace.proj j`, so
`φ (ψ x) = (ψ x) j` and the conclusion is the literal entry
`(1/n) Σ (ψ Zᵢ) j (ψ Zᵢ) k →ₚ ∫ (ψ x) j (ψ x) k`. -/

section Vector

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace Ω] [MeasurableSpace X]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The pointwise product of two functional-evaluations is dominated by a
constant times `‖ψ x‖²`: `|φ (ψ x) * φ' (ψ x)| ≤ (‖φ‖ * ‖φ'‖) * ‖ψ x‖²`.
Used to derive entrywise integrability of the product from the single
hypothesis `Integrable (fun x => ‖ψ x‖²) P`. -/
theorem abs_apply_mul_le_norm_sq
    (φ φ' : E →L[ℝ] ℝ) (ψ : X → E) (x : X) :
    |φ (ψ x) * φ' (ψ x)| ≤ (‖φ‖ * ‖φ'‖) * ‖ψ x‖ ^ 2 := by
  rw [abs_mul]
  have hb1 : |φ (ψ x)| ≤ ‖φ‖ * ‖ψ x‖ :=
    (Real.norm_eq_abs _).symm.le.trans (φ.le_opNorm (ψ x))
  have hb2 : |φ' (ψ x)| ≤ ‖φ'‖ * ‖ψ x‖ :=
    (Real.norm_eq_abs _).symm.le.trans (φ'.le_opNorm (ψ x))
  calc |φ (ψ x)| * |φ' (ψ x)|
        ≤ (‖φ‖ * ‖ψ x‖) * (‖φ'‖ * ‖ψ x‖) :=
          mul_le_mul hb1 hb2 (abs_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (‖φ‖ * ‖φ'‖) * ‖ψ x‖ ^ 2 := by ring

omit [FiniteDimensional ℝ E] in
/-- **Entrywise covariance-matrix consistency.**  For a vector influence
function `ψ : X → E` that is measurable and has square-integrable norm along the
sample, and two continuous linear coordinate functionals `φ φ' : E →L[ℝ] ℝ`, the
empirical mean of the entry product `φ (ψ ·) * φ' (ψ ·)` converges in
probability to the population integral `∫ x, φ (ψ x) * φ' (ψ x) ∂P`.

For `E = EuclideanSpace ℝ (Fin d)` and `φ = EuclideanSpace.proj j`,
`φ' = EuclideanSpace.proj k` this is the literal `(j,k)` entry of the empirical
covariance matrix converging to the population covariance entry.

The single integrability hypothesis `Integrable (fun ω => ‖ψ (S.Z 0 ω)‖²) μ`
yields entrywise integrability via `abs_apply_mul_le_norm_sq`; consistency is
then `sampleMean_mul_tendsto_inProb` with `g₁ = fun x => φ (ψ x)`,
`g₂ = fun x => φ' (ψ x)`. -/
theorem sampleCov_entry_tendsto_inProb
    (S : IIDSample Ω X μ P) [IsProbabilityMeasure P]
    {ψ : X → E}
    (hψ_meas : Measurable ψ)
    (hψ_sq_int : Integrable (fun ω => ‖ψ (S.Z 0 ω)‖ ^ 2) μ)
    (φ φ' : E →L[ℝ] ℝ) :
    Tendsto_inProb
      (S.sampleMean (fun x => φ (ψ x) * φ' (ψ x)))
      (fun _ => ∫ x, φ (ψ x) * φ' (ψ x) ∂P) μ := by
  -- coordinate measurability
  have hφ : Measurable (fun x => φ (ψ x)) := φ.continuous.measurable.comp hψ_meas
  have hφ' : Measurable (fun x => φ' (ψ x)) := φ'.continuous.measurable.comp hψ_meas
  -- entrywise integrability of the product, dominated by (‖φ‖‖φ'‖)·‖ψ‖²
  have hprod_int :
      Integrable (fun ω => φ (ψ (S.Z 0 ω)) * φ' (ψ (S.Z 0 ω))) μ := by
    have hmeas :
        AEStronglyMeasurable
          (fun ω => φ (ψ (S.Z 0 ω)) * φ' (ψ (S.Z 0 ω))) μ :=
      ((hφ.comp (S.meas 0)).mul (hφ'.comp (S.meas 0))).aestronglyMeasurable
    refine Integrable.mono'
      (hψ_sq_int.const_mul (‖φ‖ * ‖φ'‖)) hmeas ?_
    filter_upwards with ω
    simpa [Real.norm_eq_abs] using abs_apply_mul_le_norm_sq φ φ' ψ (S.Z 0 ω)
  exact S.sampleMean_mul_tendsto_inProb hφ hφ' hprod_int

end Vector

end IIDSample

/-! ## Packaging for the studentized layer -/

/-- **Square root preserves convergence in probability.**  If `Vn →ₚ v₀`
under `μ`, then `√Vn →ₚ √v₀`.  Continuous mapping with the (everywhere
continuous) `Real.sqrt`, via `Tendsto_inProb.comp_continuousAt`. -/
theorem Tendsto_inProb.sqrt
    {Ω : Type*} [MeasurableSpace Ω] {Vn : ℕ → Ω → ℝ} {v₀ : ℝ} {μ : Measure Ω}
    (h : Tendsto_inProb Vn (fun _ => v₀) μ) :
    Tendsto_inProb (fun n ω => Real.sqrt (Vn n ω)) (fun _ => Real.sqrt v₀) μ :=
  Tendsto_inProb.comp_continuousAt (Real.continuous_sqrt.continuousAt) h

/-- **Standard-error consistency from variance consistency.**  If the variance
estimator `varhat →ₚ σ₀²` under `μ` and `σ₀ > 0`, then the standard-error
estimator `√varhat →ₚ σ₀`.  This is exactly the `σ̂ →ₚ σ₀` input required by the
generic studentized CLT `Tendsto_dist.div_tendsto_inProb_gaussian`; callers feed
`fun N ω => Real.sqrt (varhat N ω)` to it.

Proof: `√varhat →ₚ √(σ₀²) = |σ₀| = σ₀` by continuous mapping
(`Tendsto_inProb.sqrt`) and `√(σ₀²) = σ₀` for `σ₀ ≥ 0`. -/
theorem sqrt_var_tendsto_inProb
    {Ω : Type*} [MeasurableSpace Ω] {varhat : ℕ → Ω → ℝ} {σ₀ : ℝ}
    {μ : Measure Ω} (hσ₀_pos : 0 < σ₀)
    (h : Tendsto_inProb varhat (fun _ => σ₀ ^ 2) μ) :
    Tendsto_inProb (fun n ω => Real.sqrt (varhat n ω)) (fun _ => σ₀) μ := by
  have hsqrt := Tendsto_inProb.sqrt h
  have heq : Real.sqrt (σ₀ ^ 2) = σ₀ := by
    rw [Real.sqrt_sq (le_of_lt hσ₀_pos)]
  rwa [heq] at hsqrt

end Causalean.Stat
