/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Finite-dimensional normal-equation maps for semidefinite bilinear forms

This file isolates a Mathlib-style linear-algebra fact for degenerate normal
equations: a symmetric positive-semidefinite bilinear form on a
finite-dimensional real vector space admits a linear map into every linear
subspace whose residual satisfies the corresponding normal equations. The proof
works through the range of the induced map from the subspace to its dual and
uses a linear right inverse on that range.

Candidate for upstreaming to Mathlib.
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Module.Projective
import Mathlib.Data.Real.Basic

/-! # Semidefinite Normal-Equation Maps

This file proves `exists_orthogonalProjection_of_posSemidef`: every subspace of
a finite-dimensional real vector space admits a linear map into that subspace
whose residual is orthogonal, with respect to a symmetric positive-semidefinite
bilinear form, to every vector in the subspace. The result supplies the
linear-algebra substrate for weighted normal-equation arguments where the inner
product may be degenerate. -/

namespace Causalean.Mathlib

open LinearMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- In a finite-dimensional real vector space with a symmetric
positive-semidefinite bilinear form, every linear subspace admits a linear map
into the subspace whose residual is orthogonal to all vectors in the subspace.

The proof views `B` as a map from `H` to `H`'s dual, shows the functional
`h ↦ B X h` lies in its range by annihilating the kernel, chooses a linear right
inverse on that range, and composes with the subtype map of `H`. -/
lemma exists_orthogonalProjection_of_posSemidef
    (B : LinearMap.BilinForm ℝ V)
    (hsymm : ∀ x y, B x y = B y x)
    (hpos : ∀ x, 0 ≤ B x x)
    (H : Submodule ℝ V) :
    ∃ P : V →ₗ[ℝ] V,
      (∀ X, P X ∈ H) ∧ (∀ X, ∀ h ∈ H, B (X - P X) h = 0) := by
  classical
  let A : H →ₗ[ℝ] Module.Dual ℝ H :=
    LinearMap.mk₂ ℝ (fun x y : H => B x.1 y.1)
      (by
        intro x y z
        simp)
      (by
        intro a x z
        simp)
      (by
        intro x y z
        simp)
      (by
        intro a x z
        simp)
  let L : V →ₗ[ℝ] Module.Dual ℝ H :=
    LinearMap.mk₂ ℝ (fun (x : V) (y : H) => B x y.1)
      (by
        intro x y z
        simp)
      (by
        intro a x z
        simp)
      (by
        intro x y z
        simp)
      (by
        intro a x z
        simp)
  have hBsymm : B.IsSymm := ⟨fun x y => hsymm x y⟩
  have hAflip : A.flip = A := by
    ext x y
    simpa [A] using (hsymm x.1 y.1).symm
  have hL_mem_range : ∀ X, L X ∈ LinearMap.range A := by
    intro X
    have hL_ann : L X ∈ (LinearMap.ker A).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro x hx
      have hxself : B x.1 x.1 = 0 := by
        have hAx : A x = 0 := by
          simpa [LinearMap.mem_ker] using hx
        have := congrArg (fun f : Module.Dual ℝ H => f x) hAx
        simpa [A] using this
      have hxker : x.1 ∈ LinearMap.ker B := by
        exact (B.apply_apply_same_eq_zero_iff hpos hBsymm).mp hxself
      have hxX : B x.1 X = 0 := by
        have hBx : B x.1 = 0 := by
          simpa [LinearMap.mem_ker] using hxker
        have := congrArg (fun f : Module.Dual ℝ V => f X) hBx
        simpa using this
      simpa [L, hsymm X x.1] using hxX
    rwa [LinearMap.dualAnnihilator_ker_eq_range_flip, hAflip] at hL_ann
  let Lrange : V →ₗ[ℝ] LinearMap.range A :=
    L.codRestrict (LinearMap.range A) hL_mem_range
  obtain ⟨S, hS⟩ :=
    A.rangeRestrict.exists_rightInverse_of_surjective
      (LinearMap.range_rangeRestrict A)
  let PH : V →ₗ[ℝ] H := S.comp Lrange
  refine ⟨H.subtype.comp PH, ?_, ?_⟩
  · intro X
    exact (PH X).2
  · intro X h hH
    let hh : H := ⟨h, hH⟩
    have hEq : A (PH X) hh = L X hh := by
      have hRangeEq : A.rangeRestrict (S (Lrange X)) = Lrange X := by
        exact congrArg (fun f : LinearMap.range A →ₗ[ℝ] LinearMap.range A =>
          f (Lrange X)) hS
      have hValEq : (A.rangeRestrict (S (Lrange X)) : Module.Dual ℝ H) =
          (Lrange X : Module.Dual ℝ H) :=
        congrArg (fun y : LinearMap.range A => (y : Module.Dual ℝ H)) hRangeEq
      exact congrArg (fun f : Module.Dual ℝ H => f hh) hValEq
    have hB_eq : B (PH X).1 h = B X h := by
      simpa [A, L, PH, hh] using hEq
    simp [hB_eq]

end Causalean.Mathlib
