/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Positive square roots of finite-dimensional positive operators

This file constructs the positive square root of a positive operator on a
finite-dimensional real inner-product space by diagonalizing the operator in an
orthonormal eigenbasis.  The main linear-map construction is `posSqrt`, with
`posSqrt_mul_self`, `posSqrt_isSymmetric`, and `posSqrt_isPositive` proving that it
is the positive square root.  The file also packages the same map as a continuous
linear map `posSqrtCLM`, proves it is self-adjoint, and proves the corresponding
continuous square law `posSqrtCLM_comp_self`. -/

open Module
open scoped RealInnerProductSpace

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

namespace IsPositive

variable {T : E →ₗ[ℝ] E} (hT : T.IsPositive)

/-- Abbreviation: `n = finrank ℝ E`. -/
private noncomputable abbrev rk : ℕ := finrank ℝ E

/-- An orthonormal eigenbasis of `T`, obtained from the symmetry of a positive operator. -/
noncomputable def eigBasis : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E :=
  hT.isSymmetric.eigenvectorBasis rfl

/-- The real eigenvalues of `T`, indexed compatibly with `eigBasis`. -/
noncomputable def eigVals : Fin (finrank ℝ E) → ℝ :=
  hT.isSymmetric.eigenvalues rfl

/-- Applying the operator to an eigenbasis vector scales that vector by its indexed
eigenvalue. -/
theorem apply_eigBasis (i : Fin (finrank ℝ E)) :
    T (hT.eigBasis i) = (hT.eigVals i) • hT.eigBasis i := by
  simp only [eigBasis, eigVals]
  exact hT.isSymmetric.apply_eigenvectorBasis rfl i

/-- Eigenvalues of a positive operator are nonnegative. -/
theorem eigVals_nonneg (i : Fin (finrank ℝ E)) : 0 ≤ hT.eigVals i := by
  have hb : ⟪hT.eigBasis i, hT.eigBasis i⟫ = 1 := by
    have := (hT.eigBasis).orthonormal.1 i
    rw [real_inner_self_eq_norm_sq, this]; norm_num
  have hpos := hT.2 (hT.eigBasis i)
  rw [hT.apply_eigBasis i, inner_smul_left] at hpos
  -- `hpos : 0 ≤ ⟪T (b i), b i⟫` becomes `0 ≤ μ i`
  simpa only [conj_trivial, hb, mul_one] using hpos

/-- The positive square root of `T`: the linear operator that acts as
`√(eigenvalue)` on each vector of the chosen orthonormal eigenbasis. -/
noncomputable def posSqrt : E →ₗ[ℝ] E :=
  (hT.eigBasis).toBasis.constr ℝ (fun i => Real.sqrt (hT.eigVals i) • hT.eigBasis i)

/-- The positive square root sends each eigenbasis vector to the same vector scaled by the
square root of its eigenvalue. -/
theorem posSqrt_apply_eigBasis (i : Fin (finrank ℝ E)) :
    hT.posSqrt (hT.eigBasis i) = Real.sqrt (hT.eigVals i) • hT.eigBasis i := by
  rw [posSqrt, ← OrthonormalBasis.coe_toBasis, Basis.constr_basis]

/-- The square law: `posSqrt ∘ₗ posSqrt = T`. -/
theorem posSqrt_mul_self : hT.posSqrt ∘ₗ hT.posSqrt = T := by
  refine (hT.eigBasis).toBasis.ext fun i => ?_
  simp only [OrthonormalBasis.coe_toBasis, coe_comp, Function.comp_apply,
    hT.posSqrt_apply_eigBasis i, map_smul, smul_smul,
    Real.mul_self_sqrt (hT.eigVals_nonneg i), hT.apply_eigBasis i]

/-- Inner-product form of `posSqrt`: a symmetric weighted sum over the eigenbasis. -/
theorem posSqrt_inner (x y : E) :
    ⟪hT.posSqrt x, y⟫
      = ∑ i, Real.sqrt (hT.eigVals i) * ⟪hT.eigBasis i, x⟫ * ⟪hT.eigBasis i, y⟫ := by
  have hx : hT.posSqrt x
      = ∑ i, (⟪hT.eigBasis i, x⟫ * Real.sqrt (hT.eigVals i)) • hT.eigBasis i := by
    conv_lhs => rw [← (hT.eigBasis).sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hT.posSqrt_apply_eigBasis i, smul_smul,
      OrthonormalBasis.repr_apply_apply]
  rw [hx, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, conj_trivial]
  ring

/-- `posSqrt` is symmetric. -/
theorem posSqrt_isSymmetric : hT.posSqrt.IsSymmetric := fun x y => by
  rw [hT.posSqrt_inner x y,
    show ⟪x, hT.posSqrt y⟫ = ⟪hT.posSqrt y, x⟫ from real_inner_comm _ _,
    hT.posSqrt_inner y x]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `posSqrt` is itself a positive operator. -/
theorem posSqrt_isPositive : hT.posSqrt.IsPositive := by
  refine (LinearMap.isPositive_iff _).mpr ⟨hT.posSqrt_isSymmetric, fun x => ?_⟩
  rw [hT.posSqrt_inner x x]
  refine Finset.sum_nonneg fun i _ => ?_
  nlinarith [Real.sqrt_nonneg (hT.eigVals i), mul_self_nonneg ⟪hT.eigBasis i, x⟫]

/-! ### Continuous-linear-map packaging -/

/-- `posSqrt` packaged as a continuous linear map (finite-dimensional domain). -/
noncomputable def posSqrtCLM : E →L[ℝ] E := hT.posSqrt.toContinuousLinearMap

/-- The continuous-linear-map packaging of the positive square root has the same pointwise
action as the linear-map square root. -/
theorem posSqrtCLM_apply (x : E) : hT.posSqrtCLM x = hT.posSqrt x := rfl

/-- The continuous square root is self-adjoint. -/
theorem posSqrtCLM_isSelfAdjoint : IsSelfAdjoint hT.posSqrtCLM :=
  (LinearMap.isSelfAdjoint_toContinuousLinearMap_iff _).mpr
    ((LinearMap.isSymmetric_iff_isSelfAdjoint _).mp hT.posSqrt_isSymmetric)

/-- Adjoint form of self-adjointness. -/
theorem posSqrtCLM_adjoint :
    ContinuousLinearMap.adjoint hT.posSqrtCLM = hT.posSqrtCLM := by
  rw [← ContinuousLinearMap.star_eq_adjoint]; exact hT.posSqrtCLM_isSelfAdjoint

/-- The continuous square law: `posSqrtCLM ∘L posSqrtCLM = T`. -/
theorem posSqrtCLM_comp_self :
    hT.posSqrtCLM ∘L hT.posSqrtCLM = T.toContinuousLinearMap := by
  ext x
  change hT.posSqrt (hT.posSqrt x) = T x
  rw [← LinearMap.comp_apply, hT.posSqrt_mul_self]

end IsPositive
end LinearMap
