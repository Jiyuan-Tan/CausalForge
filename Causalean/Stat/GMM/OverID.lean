/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The whitened GMM over-identification (J / Hansen–Sargan) test

For an over-identified GMM problem with Jacobian `G : E →L[ℝ] F` (`E` the
parameter space, dimension `k`; `F` the moment space, dimension `m`, with
`k ≤ m`), the efficient `Σ̂⁻¹`-weighted **J-statistic** measures how far the
empirical moments are from zero after projecting out the `k` directions the
estimator can fit.  Working in *whitened* coordinates — where the moment
covariance has been normalised to the identity (`z ↦ Σ^{-1/2} z`), which is
exactly the change of variables the `Σ̂⁻¹`-weighting performs — the relevant
operator is the residual maker

    M = I − G (GᵀG)⁻¹ Gᵀ        (`gmmResidualMaker`)

with hat matrix

    H = G (GᵀG)⁻¹ Gᵀ            (`gmmHatMatrix`).

`M` is an orthogonal projection (self-adjoint, idempotent) onto the orthogonal
complement of `range G`, hence has rank `m − k`.  Therefore the J-statistic's
limit law `‖M w‖²` under a standard Gaussian `w` on the moment space `F` is
`χ²_{m−k}` (`jStatistic_chiSq`), the classical Hansen–Sargan degrees-of-freedom
count: number of moments minus number of parameters.

The general (non-identity-covariance) case reduces to this one by the change of
variables `z ↦ Σ^{-1/2} z`, which whitens the moments; `effInv = (GᵀΣ⁻¹G)⁻¹`
plays the role of `(GᵀG)⁻¹` in those coordinates.

Inverses are carried as *data with two-sided witnesses* (mirroring
`Causalean/Stat/GMM/VarianceAlgebra.lean`): the caller supplies `effInv` together
with `heL : effInv ∘L (GᵀG) = id` and `heR : (GᵀG) ∘L effInv = id`, so no
operator inverse needs to be constructed here.
-/
import Causalean.Stat.CLT.ChiSquaredProjection
import Causalean.Stat.GMM.VarianceAlgebra

/-! # GMM Over-Identification Test

This file develops the whitened linear-algebra form of the GMM
over-identification statistic.  It defines the hat matrix `gmmHatMatrix` and
residual maker `gmmResidualMaker`, proves the public projection facts
`gmmResidualMaker_isSelfAdjoint`, `gmmResidualMaker_idempotent`, and
`gmmResidualMaker_finrank_range`, and concludes with `jStatistic_chiSq`, the
whitened Hansen-Sargan chi-squared limit law with `finrank F - finrank E`
degrees of freedom. -/

open MeasureTheory ProbabilityTheory Causalean.Mathlib ContinuousLinearMap
open scoped RealInnerProductSpace

namespace Causalean.Stat

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- The **hat matrix** `H = G (GᵀG)⁻¹ Gᵀ : F →L F` of a whitened GMM problem
with Jacobian `G` and bread inverse `effInv` (a two-sided inverse of `GᵀG`).
It is the orthogonal projection onto `range G`. -/
noncomputable def gmmHatMatrix (G : E →L[ℝ] F) (effInv : E →L[ℝ] E) : F →L[ℝ] F :=
  G ∘L effInv ∘L adjoint G

/-- The **residual maker** `M = I − H : F →L F` of a whitened GMM problem.  It is
the orthogonal projection onto the orthogonal complement of `range G`; the
J-statistic's limit law is `‖M w‖²` for `w` a standard Gaussian on `F`. -/
noncomputable def gmmResidualMaker (G : E →L[ℝ] F) (effInv : E →L[ℝ] E) : F →L[ℝ] F :=
  ContinuousLinearMap.id ℝ F - gmmHatMatrix G effInv

variable {G : E →L[ℝ] F} {effInv : E →L[ℝ] E}
  (heL : effInv ∘L (adjoint G ∘L G) = ContinuousLinearMap.id ℝ E)
  (heR : (adjoint G ∘L G) ∘L effInv = ContinuousLinearMap.id ℝ E)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
include heR in
/-- `effInv` is self-adjoint: `GᵀG` is self-adjoint and the inverse of a
self-adjoint operator is self-adjoint. -/
private theorem effInv_isSelfAdjoint : adjoint effInv = effInv := by
  have hB : adjoint (adjoint G ∘L G) = adjoint G ∘L G := by
    simp only [adjoint_comp, adjoint_adjoint]
  exact adjoint_inv_self hB heR

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
include heR in
/-- The hat matrix `H = G effInv Gᵀ` is self-adjoint. -/
private theorem gmmHatMatrix_isSelfAdjoint :
    IsSelfAdjoint (gmmHatMatrix G effInv) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  unfold gmmHatMatrix
  simp only [adjoint_comp, adjoint_adjoint, effInv_isSelfAdjoint heR, comp_assoc]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
include heR in
/-- The hat matrix `H = G effInv Gᵀ` is idempotent: `H ∘L H = H`, using
`(GᵀG) ∘L effInv = id`. -/
private theorem gmmHatMatrix_idempotent :
    gmmHatMatrix G effInv ∘L gmmHatMatrix G effInv = gmmHatMatrix G effInv := by
  have peR : ∀ x, (adjoint G ∘L G) (effInv x) = x := fun x => by
    rw [← comp_apply, heR, id_apply]
  ext y
  unfold gmmHatMatrix
  simp only [comp_apply]
  have hpe : adjoint G (G (effInv (adjoint G y))) = adjoint G y := by
    have := peR (adjoint G y)
    simpa only [comp_apply] using this
  rw [hpe]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
include heR in
/-- **The residual maker `M = I − H` is self-adjoint.** -/
theorem gmmResidualMaker_isSelfAdjoint :
    IsSelfAdjoint (gmmResidualMaker G effInv) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  unfold gmmResidualMaker
  rw [map_sub, adjoint_id,
    (ContinuousLinearMap.isSelfAdjoint_iff'.mp (gmmHatMatrix_isSelfAdjoint heR))]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
include heR in
/-- **The residual maker `M = I − H` is idempotent:** `M ∘L M = M`. -/
theorem gmmResidualMaker_idempotent :
    gmmResidualMaker G effInv ∘L gmmResidualMaker G effInv
      = gmmResidualMaker G effInv := by
  unfold gmmResidualMaker
  rw [sub_comp, comp_sub, comp_sub, id_comp, comp_id, id_comp,
    gmmHatMatrix_idempotent heR]
  abel

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
include heL heR in
/-- **The rank of the residual maker's range is `m − k`** (`finrank F − finrank E`),
the Hansen–Sargan degrees of freedom. -/
theorem gmmResidualMaker_finrank_range :
    Module.finrank ℝ (LinearMap.range (gmmResidualMaker G effInv : F →ₗ[ℝ] F))
      = Module.finrank ℝ F - Module.finrank ℝ E := by
  -- Pointwise inverse witnesses.
  have peL : ∀ x, effInv ((adjoint G ∘L G) x) = x := fun x => by
    rw [← comp_apply, heL, id_apply]
  have peR : ∀ x, (adjoint G ∘L G) (effInv x) = x := fun x => by
    rw [← comp_apply, heR, id_apply]
  have hidem := gmmHatMatrix_idempotent heR
  -- Pointwise idempotence of `H`.
  have hHidem : ∀ v, gmmHatMatrix G effInv (gmmHatMatrix G effInv v)
      = gmmHatMatrix G effInv v := fun v => by
    have := congrArg (fun (f : F →L[ℝ] F) => f v) hidem
    simpa only [comp_apply] using this
  set H := gmmHatMatrix G effInv with hHdef
  set M := gmmResidualMaker G effInv with hMdef
  have hMv : ∀ v, M v = v - H v := fun v => by
    rw [hMdef, hHdef]; rfl
  -- `range M = ker H`.
  have hrange_ker :
      LinearMap.range (M : F →ₗ[ℝ] F) = LinearMap.ker (H : F →ₗ[ℝ] F) := by
    apply Submodule.ext
    intro w
    simp only [LinearMap.mem_range, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    constructor
    · rintro ⟨v, rfl⟩
      rw [hMv v, map_sub, hHidem v, sub_self]
    · intro hw
      exact ⟨w, by rw [hMv w, hw, sub_zero]⟩
  -- `range H = range G`.
  have hrange_HG :
      LinearMap.range (H : F →ₗ[ℝ] F) = LinearMap.range (G : E →ₗ[ℝ] F) := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact ⟨effInv (adjoint G v), rfl⟩
    · rintro _ ⟨x, rfl⟩
      refine ⟨G x, ?_⟩
      change H (G x) = G x
      rw [hHdef]
      unfold gmmHatMatrix
      simp only [comp_apply]
      have : adjoint G (G x) = (adjoint G ∘L G) x := by simp only [comp_apply]
      rw [this, peL x]
  -- `G` injective.
  have hGinj' : Function.Injective ((G : E →ₗ[ℝ] F)) := by
    intro x y hxy
    have hx : effInv (adjoint G (G x)) = effInv (adjoint G (G y)) := by
      rw [show G x = G y from hxy]
    have e1 : effInv (adjoint G (G x)) = x := by
      have : adjoint G (G x) = (adjoint G ∘L G) x := by simp only [comp_apply]
      rw [this, peL x]
    have e2 : effInv (adjoint G (G y)) = y := by
      have : adjoint G (G y) = (adjoint G ∘L G) y := by simp only [comp_apply]
      rw [this, peL y]
    rw [e1, e2] at hx
    exact hx
  -- `finrank (range G) = finrank E`.
  have hrankG : Module.finrank ℝ (LinearMap.range (G : E →ₗ[ℝ] F))
      = Module.finrank ℝ E := LinearMap.finrank_range_of_inj hGinj'
  -- `finrank (range H) + finrank (ker H) = finrank F`.
  have hrankH := LinearMap.finrank_range_add_finrank_ker (H : F →ₗ[ℝ] F)
  -- Assemble.
  rw [hrange_ker]
  rw [hrange_HG, hrankG] at hrankH
  omega

omit [MeasurableSpace E] [BorelSpace E] in
include heL heR in
/-- **Headline: the whitened GMM J-statistic limit law is `χ²_{m−k}`.**

Under a standard Gaussian `w` on the moment space `F`, the J-statistic
`‖M w‖²` (with `M` the residual maker) is distributed as the chi-squared law
with `finrank F − finrank E = m − k` degrees of freedom — the Hansen–Sargan
over-identification test statistic. -/
theorem jStatistic_chiSq :
    (stdGaussian F).map (fun w => ‖gmmResidualMaker G effInv w‖ ^ 2)
      = chiSqDist (Module.finrank ℝ F - Module.finrank ℝ E) := by
  rw [stdGaussian_map_normSq_orthogonalProjection (gmmResidualMaker G effInv)
      (gmmResidualMaker_isSelfAdjoint heR) (gmmResidualMaker_idempotent heR),
    gmmResidualMaker_finrank_range heL heR]

end Causalean.Stat
