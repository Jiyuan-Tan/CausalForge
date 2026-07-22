/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension.PolynomialRetractDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Exact dimension of finite-dimensional affine subspaces

This file realizes affine subspaces as polynomial retracts of affine space and
computes their exact irreducible-chain dimension.
-/

namespace Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension

noncomputable section

/-- A linear map from a finite-coordinate source is polynomial. -/
lemma linearMap_isPolynomial {ι κ : Type*} [Fintype ι]
    (F : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) : IsPolynomialMap F := by
  classical
  intro k
  let P : MvPolynomial ι ℂ := ∑ i,
    MvPolynomial.C (F (Pi.single i 1) k) * MvPolynomial.X i
  refine ⟨P, ?_⟩
  intro x
  have hx : x = ∑ i, x i • (Pi.single i (1 : ℂ) : ι → ℂ) := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb.symm]
    · simp
  have hFx : F x k = ∑ i, x i * F (Pi.single i 1) k := by
    calc
      F x k = F (∑ i, x i • (Pi.single i (1 : ℂ) : ι → ℂ)) k :=
        congrArg (fun y => F y k) hx
      _ = ∑ i, x i * F (Pi.single i 1) k := by
        rw [map_sum]
        simp
  simpa [P, mul_comm] using hFx.symm

/-- An affine-linear map from a finite-coordinate source is polynomial. -/
lemma affineLinearMap_isPolynomial {ι κ : Type*} [Fintype ι]
    (F : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) (c : κ → ℂ) :
    IsPolynomialMap (fun x => c + F x) := by
  obtain hF := linearMap_isPolynomial F
  intro k
  obtain ⟨P, hP⟩ := hF k
  refine ⟨MvPolynomial.C (c k) + P, ?_⟩
  intro x
  simp [hP x]

/-- An affine translate of a `d`-dimensional linear subspace has exact
irreducible-chain dimension `d`. -/
theorem affineSubspace_hasAffineZariskiDimension {κ : Type*} [Fintype κ]
    (V : Submodule ℂ (κ → ℂ)) (x₀ : κ → ℂ) (d : ℕ)
    (hdim : Module.finrank ℂ V = d) :
    HasAffineZariskiDimension d {x | x - x₀ ∈ V} := by
  let b := Module.finBasisOfFinrankEq ℂ V hdim
  let E : (Fin d → ℂ) ≃ₗ[ℂ] V := b.equivFun.symm
  let inclusion : V →ₗ[ℂ] (κ → ℂ) := V.subtype
  let F : (Fin d → ℂ) →ₗ[ℂ] (κ → ℂ) := inclusion.comp E.toLinearMap
  have hFinj : Function.Injective F := by
    intro a c hac
    apply E.injective
    apply Subtype.ext
    exact hac
  have hFker : LinearMap.ker F = ⊥ := LinearMap.ker_eq_bot.mpr hFinj
  let G : (κ → ℂ) →ₗ[ℂ] (Fin d → ℂ) := F.leftInverse
  have hGF : ∀ z, G (F z) = z := by
    intro z
    exact LinearMap.leftInverse_apply_of_inj hFker z
  let f : (Fin d → ℂ) → (κ → ℂ) := fun z => x₀ + F z
  let g : (κ → ℂ) → (Fin d → ℂ) := fun x => G (x - x₀)
  have hf : IsPolynomialMap f := affineLinearMap_isPolynomial F x₀
  have hg : IsPolynomialMap g := by
    have hG := linearMap_isPolynomial G
    intro i
    obtain ⟨P, hP⟩ := hG i
    refine ⟨P - MvPolynomial.C (G x₀ i), ?_⟩
    intro x
    simp [g, map_sub, hP x]
  have hleft : Function.LeftInverse g f := by
    intro z
    simp [f, g, hGF z]
  have hrange : Set.range f = {x | x - x₀ ∈ V} := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      simp [f, F, inclusion]
    · intro hx
      let v : V := ⟨x - x₀, hx⟩
      let z : Fin d → ℂ := E.symm v
      refine ⟨z, ?_⟩
      have hEz : E z = v := E.apply_symm_apply v
      funext k
      have hk := congrArg (fun q : V => (q : κ → ℂ) k) hEz
      dsimp [f, F, inclusion] at hk ⊢
      rw [hk]
      simp [v]
  rw [← hrange]
  exact polynomialRetract_range_dimension hf hg hleft

end

end Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension
