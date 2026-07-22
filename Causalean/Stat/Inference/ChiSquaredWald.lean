/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# χ² identification of the Wald quadratic form

This file closes the open step flagged in `Causalean/Stat/Inference/WaldVec.lean`: pushing the
concrete multivariate-CLT Gaussian limit (`Causalean/Stat/CLT/GaussianLimit.lean`,
`gaussianLimit`) through the Wald quadratic form `S ↦ ⟪S, Σ⁻¹ S⟫` and recognising
the image as the χ²_d distribution (`Causalean/Stat/CLT/ChiSquared.lean`, `chiSqDist`).

The argument is **whitening**.  Writing the limit as `gaussianLimit = (stdGaussian E).map √Σ`
and assuming the asymptotic-variance operator `Σ` is non-degenerate (injective,
hence invertible in finite dimension), the inverse `Σ⁻¹ = (√Σ)⁻¹ ∘ (√Σ)⁻¹` exists
and, by self-adjointness of `√Σ`,

    ⟪√Σ w, Σ⁻¹ (√Σ w)⟫ = ⟪√Σ w, (√Σ)⁻¹ w⟫ = ⟪w, √Σ ((√Σ)⁻¹ w)⟫ = ⟪w, w⟫ = ‖w‖².

Hence the Wald form composed with `√Σ` is exactly the squared norm, so the
pushforward of `gaussianLimit` is the law of `‖·‖²` under `stdGaussian` — which is
`chiSqDist (finrank E)` by definition.

Key declarations:

* `secondMomentInv` — `Σ⁻¹` as a continuous linear map, with
  `secondMomentInv_secondMomentLM` / `secondMomentLM_secondMomentInv` certifying it
  is the genuine two-sided inverse of the second-moment operator `Σ`.
* `gaussianLimit_waldForm_map` — **the χ² identification**:
  `(gaussianLimit ψ).map (S ↦ ⟪S, Σ⁻¹ S⟫) = chiSqDist (finrank E)`.
* `Tendsto_dist.wald_coverage_chiSq` — the WaldVec ellipsoid-coverage theorem with
  the limit law pinned to `chiSqDist d` (atomless for `d ≥ 1`).
-/
import Causalean.Stat.CLT.GaussianLimit
import Causalean.Stat.CLT.ChiSquared
import Causalean.Stat.Inference.WaldVec

/-!
This file identifies the Gaussian Wald quadratic form with a chi-squared law and
then specializes multivariate Wald coverage to that limit.  It constructs the
inverse `secondMomentInv` of the second-moment operator from the positive square
root, proves the two-sided inverse identities
`secondMomentInv_secondMomentLM` and `secondMomentLM_secondMomentInv`, and uses
whitening in `gaussianLimit_waldForm_map` to show that
`gaussianLimit hψ hvar` pushed through `S ↦ ⟪S, Σ⁻¹ S⟫` is
`chiSqDist (Module.finrank ℝ E)`.

The final theorem `Tendsto_dist.wald_coverage_chiSq` plugs that chi-squared
limit into the generic ellipsoid-coverage theorem from
`Causalean.Stat.Inference.WaldVec`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace

namespace Causalean.Stat

variable {X : Type*} [MeasurableSpace X] {P : Measure X}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
  {ψ : X → E} (hψ : Measurable ψ) (hvar : Integrable (fun x => ‖ψ x‖ ^ 2) P)

/-! ## The inverse `Σ⁻¹` of the second-moment operator -/

/-- If the second-moment operator `Σ` is injective, so is its square root `√Σ`
(`Σ = √Σ ∘ √Σ`, so `√Σ x = 0 ⇒ Σ x = 0`). -/
private theorem posSqrt_injective
    (hinj : Function.Injective (secondMomentLM hψ hvar)) :
    Function.Injective (secondMomentLM_isPositive hψ hvar).posSqrt := by
  intro x y hxy
  refine hinj ?_
  have h := congrArg (secondMomentLM_isPositive hψ hvar).posSqrt hxy
  rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply,
    (secondMomentLM_isPositive hψ hvar).posSqrt_mul_self] at h

/-- `√Σ` as a linear equivalence (injective + finite-dimensional ⇒ bijective). -/
private noncomputable def posSqrtEquiv
    (hinj : Function.Injective (secondMomentLM hψ hvar)) : E ≃ₗ[ℝ] E :=
  LinearEquiv.ofBijective (secondMomentLM_isPositive hψ hvar).posSqrt
    ⟨posSqrt_injective hψ hvar hinj,
      LinearMap.injective_iff_surjective.mp (posSqrt_injective hψ hvar hinj)⟩

private theorem posSqrtEquiv_apply
    (hinj : Function.Injective (secondMomentLM hψ hvar)) (x : E) :
    posSqrtEquiv hψ hvar hinj x = (secondMomentLM_isPositive hψ hvar).posSqrt x := rfl

/-- The inverse `Σ⁻¹ = (√Σ)⁻¹ ∘ (√Σ)⁻¹` of the second-moment operator, as a
continuous linear map (continuity is automatic in finite dimension). -/
noncomputable def secondMomentInv
    (hinj : Function.Injective (secondMomentLM hψ hvar)) : E →L[ℝ] E :=
  (((posSqrtEquiv hψ hvar hinj).symm.trans (posSqrtEquiv hψ hvar hinj).symm) :
    E →ₗ[ℝ] E).toContinuousLinearMap

private theorem secondMomentInv_apply
    (hinj : Function.Injective (secondMomentLM hψ hvar)) (x : E) :
    secondMomentInv hψ hvar hinj x
      = (posSqrtEquiv hψ hvar hinj).symm ((posSqrtEquiv hψ hvar hinj).symm x) := rfl

/-- `Σ⁻¹` is a left inverse of `Σ`. -/
theorem secondMomentInv_secondMomentLM
    (hinj : Function.Injective (secondMomentLM hψ hvar)) (x : E) :
    secondMomentInv hψ hvar hinj (secondMomentLM hψ hvar x) = x := by
  have hsig : secondMomentLM hψ hvar x
      = posSqrtEquiv hψ hvar hinj (posSqrtEquiv hψ hvar hinj x) := by
    rw [posSqrtEquiv_apply, posSqrtEquiv_apply, ← LinearMap.comp_apply,
      (secondMomentLM_isPositive hψ hvar).posSqrt_mul_self]
  rw [secondMomentInv_apply, hsig, (posSqrtEquiv hψ hvar hinj).symm_apply_apply,
    (posSqrtEquiv hψ hvar hinj).symm_apply_apply]

/-- `Σ⁻¹` is a right inverse of `Σ`. -/
theorem secondMomentLM_secondMomentInv
    (hinj : Function.Injective (secondMomentLM hψ hvar)) (x : E) :
    secondMomentLM hψ hvar (secondMomentInv hψ hvar hinj x) = x := by
  have hsig : ∀ z, secondMomentLM hψ hvar z
      = posSqrtEquiv hψ hvar hinj (posSqrtEquiv hψ hvar hinj z) := fun z => by
    rw [posSqrtEquiv_apply, posSqrtEquiv_apply, ← LinearMap.comp_apply,
      (secondMomentLM_isPositive hψ hvar).posSqrt_mul_self]
  rw [secondMomentInv_apply, hsig, (posSqrtEquiv hψ hvar hinj).apply_symm_apply,
    (posSqrtEquiv hψ hvar hinj).apply_symm_apply]

/-! ## The whitening identity and the χ² recognition -/

/-- Whitening at a point: the Wald quadratic form pulled back through `√Σ` is the
squared norm. -/
private theorem waldForm_posSqrt
    (hinj : Function.Injective (secondMomentLM hψ hvar)) (w : E) :
    ⟪(secondMomentLM_isPositive hψ hvar).posSqrt w,
        secondMomentInv hψ hvar hinj ((secondMomentLM_isPositive hψ hvar).posSqrt w)⟫
      = ‖w‖ ^ 2 := by
  have h1 : secondMomentInv hψ hvar hinj ((secondMomentLM_isPositive hψ hvar).posSqrt w)
      = (posSqrtEquiv hψ hvar hinj).symm w := by
    rw [secondMomentInv_apply,
      show (secondMomentLM_isPositive hψ hvar).posSqrt w = posSqrtEquiv hψ hvar hinj w
        from (posSqrtEquiv_apply hψ hvar hinj w).symm,
      (posSqrtEquiv hψ hvar hinj).symm_apply_apply]
  rw [h1, (secondMomentLM_isPositive hψ hvar).posSqrt_isSymmetric w
        ((posSqrtEquiv hψ hvar hinj).symm w),
    show (secondMomentLM_isPositive hψ hvar).posSqrt ((posSqrtEquiv hψ hvar hinj).symm w)
        = posSqrtEquiv hψ hvar hinj ((posSqrtEquiv hψ hvar hinj).symm w)
        from posSqrtEquiv_apply hψ hvar hinj _,
    (posSqrtEquiv hψ hvar hinj).apply_symm_apply, real_inner_self_eq_norm_sq]

/-- **χ² identification of the Wald quadratic form.**  When the asymptotic-variance
operator `Σ` is non-degenerate, the multivariate-CLT Gaussian limit, pushed through
the Wald quadratic form `S ↦ ⟪S, Σ⁻¹ S⟫`, is the χ²_d distribution with
`d = finrank E` degrees of freedom. -/
theorem gaussianLimit_waldForm_map
    (hinj : Function.Injective (secondMomentLM hψ hvar)) :
    (gaussianLimit hψ hvar).map (fun S => ⟪S, secondMomentInv hψ hvar hinj S⟫)
      = chiSqDist (Module.finrank ℝ E) := by
  have hQmeas : Measurable (fun S : E => ⟪S, secondMomentInv hψ hvar hinj S⟫) :=
    (continuous_id.inner (secondMomentInv hψ hvar hinj).continuous).measurable
  rw [gaussianLimit,
    Measure.map_map hQmeas (secondMomentLM_isPositive hψ hvar).posSqrtCLM.continuous.measurable,
    ← stdGaussian_map_normSq (E := E)]
  refine Measure.map_congr (ae_of_all _ fun w => ?_)
  change ⟪(secondMomentLM_isPositive hψ hvar).posSqrtCLM w,
      secondMomentInv hψ hvar hinj ((secondMomentLM_isPositive hψ hvar).posSqrtCLM w)⟫
      = ‖w‖ ^ 2
  rw [(secondMomentLM_isPositive hψ hvar).posSqrtCLM_apply]
  exact waldForm_posSqrt hψ hvar hinj w

/-! ## Wiring into WaldVec coverage -/

/-- **χ²-coverage of the Wald confidence ellipsoid.**  Instantiates
`Tendsto_dist.wald_coverage_Iic_of_noAtoms` at the identified limit law
`chiSqDist d`, which is atomless for `d ≥ 1`.  If the scalar Wald statistic
`Wₙ ⇒ χ²_d` and `coverProb` is asymptotically the ellipsoid event probability, then
`coverProb n → χ²_d(Iic c)`. -/
theorem Tendsto_dist.wald_coverage_chiSq
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {Wn : ℕ → Ω → ℝ} (hWn : ∀ n, AEMeasurable (Wn n) ν)
    {d : ℕ} (hd : 1 ≤ d)
    (hW : Tendsto_dist Wn (chiSqDist d) ν hWn)
    (c : ℝ) (coverProb : ℕ → ℝ)
    (h_bridge : Tendsto
      (fun n => coverProb n - (ν {ω | Wn n ω ≤ c}).toReal) atTop (𝓝 0)) :
    Tendsto coverProb atTop (𝓝 ((chiSqDist d (Set.Iic c)).toReal)) := by
  haveI := noAtoms_chiSqDist hd
  exact Tendsto_dist.wald_coverage_Iic_of_noAtoms hWn hW c coverProb h_bridge

end Causalean.Stat
