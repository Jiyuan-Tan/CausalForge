/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The law of `‖P z‖²` for an orthogonal projection `P` is `χ²_{rank P}`

Let `E` be a finite-dimensional real inner-product space and let `P : E →L[ℝ] E`
be an *orthogonal projection*, i.e. self-adjoint (`IsSelfAdjoint P`) and idempotent
(`P ∘L P = P`).  If `z` is a standard Gaussian on `E`, then `‖P z‖²` is distributed
as `χ²_r` where `r = rank P = finrank ℝ (range P)`:

  `(stdGaussian E).map (fun z => ‖P z‖ ^ 2) = chiSqDist (finrank ℝ (range P))`.

## Proof outline

Let `S := LinearMap.range P`, a finite-dimensional inner-product subspace of `E`,
and fix a linear isometry `ι : S ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r)` with
`r = finrank ℝ S` (the standard orthonormal basis of `S`).  Corestrict `P` to a
continuous linear map `Pc : E →L[ℝ] S` and set `Q := ι ∘L Pc : E → EuclideanSpace`.

1. `Q` is a *coisometry*: `Q.adjoint` is an isometric embedding, equivalently
   `⟪Q.adjoint s, Q.adjoint t⟫_E = ⟪s, t⟫`.  The crux is that the adjoint of the
   corestriction `Pc` is the subspace inclusion (uses self-adjoint + idempotent +
   `P w = w` for `w ∈ range P`).
2. Hence `(stdGaussian E).map Q` is a centered Gaussian with covariance the inner
   product, so it equals `stdGaussian (EuclideanSpace ℝ (Fin r))`
   (`Measure.ext_of_charFun`, mirroring `stdGaussian_map_linearIsometryEquiv`).
3. `‖Q z‖ = ‖P z‖` (`ι` is an isometry and corestriction preserves the norm), and
   the law of `‖·‖²` under `stdGaussian (EuclideanSpace ℝ (Fin r))` is `chiSqDist r`
   by `stdGaussian_map_normSq`.

Main result: `stdGaussian_map_normSq_orthogonalProjection`.
-/
import Causalean.Stat.CLT.ChiSquared

/-! # Chi-Squared Law for Projected Gaussians

This file proves that the squared norm of an orthogonal projection of a standard
finite-dimensional Gaussian vector has a chi-squared distribution. The degrees of
freedom are the dimension of the projection range.

The public theorem is `stdGaussian_map_normSq_orthogonalProjection`: if a
continuous linear map `P` is self-adjoint and idempotent, then the law of
`‖P z‖²` under `stdGaussian` is `chiSqDist` with degrees of freedom
`finrank ℝ (range P)`. -/

open MeasureTheory ProbabilityTheory Complex Causalean.Mathlib
open scoped RealInnerProductSpace

namespace Causalean.Stat

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- An idempotent linear map fixes every vector in its range: `P w = w` for
`w ∈ range P`. -/
private lemma apply_eq_self_of_mem_range {P : E →L[ℝ] E} (hidem : P ∘L P = P)
    {w : E} (hw : w ∈ LinearMap.range (P : E →ₗ[ℝ] E)) : P w = w := by
  obtain ⟨y, rfl⟩ := hw
  have := congrArg (fun (f : E →L[ℝ] E) => f y) hidem
  simpa using this

/-- **The law of `‖P z‖²` under the standard Gaussian, for `P` an orthogonal
projection (self-adjoint idempotent).**  It is the chi-squared distribution with
`finrank ℝ (range P)` degrees of freedom. -/
theorem stdGaussian_map_normSq_orthogonalProjection
    (P : E →L[ℝ] E) (hsa : IsSelfAdjoint P) (hidem : P ∘L P = P) :
    (stdGaussian E).map (fun z => ‖P z‖ ^ 2)
      = chiSqDist (Module.finrank ℝ (LinearMap.range (P : E →ₗ[ℝ] E))) := by
  classical
  -- The image subspace and its dimension.
  set S : Submodule ℝ E := LinearMap.range (P : E →ₗ[ℝ] E) with hS
  set r : ℕ := Module.finrank ℝ S with hr
  -- An isometry from `S` to Euclidean space.
  set ι : S ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r) := (stdOrthonormalBasis ℝ S).repr with hι
  -- `P` lands in `S`.
  have hmem : ∀ x : E, P x ∈ S := fun x => LinearMap.mem_range_self _ x
  -- Corestriction of `P` to `S` as a continuous linear map.
  set Pc : E →L[ℝ] S := P.codRestrict S hmem with hPc
  -- The composite map to Euclidean space.
  set Q : E →L[ℝ] EuclideanSpace ℝ (Fin r) :=
    ι.toContinuousLinearEquiv.toContinuousLinearMap ∘L Pc with hQ
  -- `‖Q z‖ = ‖P z‖` for every `z`.
  -- `↑(Pc x) = P x` definitionally.
  have hPccoe : ∀ x, (↑(Pc x) : E) = P x := fun _ => rfl
  have hnorm : ∀ z, ‖Q z‖ = ‖P z‖ := by
    intro z
    rw [hQ]
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [ι.norm_map]
    -- norm in subtype = ambient norm
    rw [← hPccoe z]
    rfl
  -- The adjoint of `Q` sends `s` to `↑(ι.symm s)`, the inclusion of `ι.symm s`.
  have hadj : ∀ s : EuclideanSpace ℝ (Fin r),
      ContinuousLinearMap.adjoint Q s = (ι.symm s : E) := by
    intro s
    refine ext_inner_right ℝ (fun x => ?_)
    rw [ContinuousLinearMap.adjoint_inner_left]
    -- `⟪s, Q x⟫ = ⟪↑(ι.symm s), x⟫`
    rw [hQ]
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    -- `⟪s, ι (Pc x)⟫ = ⟪ι.symm s, Pc x⟫_S = ⟪↑(ι.symm s), ↑(Pc x)⟫_E`
    rw [show s = ι (ι.symm s) from (ι.apply_symm_apply s).symm, ι.inner_map_map,
      Submodule.coe_inner, ι.symm_apply_apply]
    -- `↑(Pc x) = P x`, and `⟪↑(ι.symm s), P x⟫ = ⟪P ↑(ι.symm s), x⟫ = ⟪↑(ι.symm s), x⟫`.
    change (inner ℝ (ι.symm s : E) (P x) : ℝ) = (inner ℝ (ι.symm s : E) x : ℝ)
    rw [show (inner ℝ (ι.symm s : E) (P x) : ℝ)
        = (inner ℝ (P (ι.symm s : E)) x : ℝ) from ?_]
    · rw [apply_eq_self_of_mem_range hidem (ι.symm s).2]
    · rw [← ContinuousLinearMap.adjoint_inner_left,
        (ContinuousLinearMap.isSelfAdjoint_iff'.mp hsa)]
  -- Key: the pushforward of `stdGaussian E` along `Q` is `stdGaussian Euclidean`.
  have hpush : (stdGaussian E).map Q = stdGaussian (EuclideanSpace ℝ (Fin r)) := by
    haveI : IsGaussian ((stdGaussian E).map Q) := isGaussian_map _
    -- mean of pushforward is `0`
    have hmean_map : ∫ x, x ∂((stdGaussian E).map Q) = 0 := by
      have hstep : ∫ x, x ∂((stdGaussian E).map Q) = Q (∫ x, x ∂(stdGaussian E)) := by
        rw [integral_map (by fun_prop) (by fun_prop)]
        exact ContinuousLinearMap.integral_comp_comm Q IsGaussian.integrable_id
      rw [hstep, stdGaussian_mean, map_zero]
    refine Measure.ext_of_charFun ?_
    funext t
    have hmemLp : MemLp id 2 (stdGaussian E) := IsGaussian.memLp_two_id
    have hcoveq : covarianceBilin ((stdGaussian E).map Q) t t
        = covarianceBilin (stdGaussian (EuclideanSpace ℝ (Fin r))) t t := by
      rw [covarianceBilin_map hmemLp, hadj, covarianceBilin_stdGaussian,
        covarianceBilin_stdGaussian, ← Submodule.coe_inner, ι.symm.inner_map_map]
    rw [charFun_isGaussian_centered _ hmean_map t,
      charFun_isGaussian_centered _ stdGaussian_mean t, hcoveq]
  -- Assemble.
  have hmap2 : (stdGaussian E).map (fun z => ‖Q z‖ ^ 2)
      = ((stdGaussian E).map Q).map (fun w => ‖w‖ ^ 2) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  calc (stdGaussian E).map (fun z => ‖P z‖ ^ 2)
      = (stdGaussian E).map (fun z => ‖Q z‖ ^ 2) := by
        refine Measure.map_congr (ae_of_all _ fun z => ?_)
        simp only [hnorm z]
    _ = ((stdGaussian E).map Q).map (fun w => ‖w‖ ^ 2) := hmap2
    _ = (stdGaussian (EuclideanSpace ℝ (Fin r))).map (fun w => ‖w‖ ^ 2) := by rw [hpush]
    _ = chiSqDist (Module.finrank ℝ (EuclideanSpace ℝ (Fin r))) := stdGaussian_map_normSq
    _ = chiSqDist r := by rw [finrank_euclideanSpace_fin]

end Causalean.Stat
