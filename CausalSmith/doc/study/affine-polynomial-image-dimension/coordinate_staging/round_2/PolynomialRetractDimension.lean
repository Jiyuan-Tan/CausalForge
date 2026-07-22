/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension.AffineSpaceDimension
import Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension.PolynomialMap

/-!
# Dimension transfer along polynomial retractions

This file proves that polynomial retracts preserve irreducibility and transfer
the exact affine chain dimension of their source affine space to their range.
-/

namespace Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension

noncomputable section

private lemma image_strictMono_global {α β ι : Type*} [Preorder ι]
    (f : α → β) (hf : Function.Injective f)
    {chain : ι → Set α} (hc : StrictMono chain) :
    StrictMono (fun i => f '' chain i) := by
  intro i j hij
  have hs := hc hij
  refine Set.ssubset_iff_subset_ne.mpr ⟨Set.image_mono hs.le, ?_⟩
  intro heq
  change f '' chain i = f '' chain j at heq
  apply hs.ne
  ext x
  constructor
  · intro hx
    have : f x ∈ f '' chain j := by
      rw [← heq]
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := this
    exact hf hxy.symm ▸ hy
  · intro hx
    have him : f x ∈ f '' chain i := by
      rw [heq]
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hfy⟩ := him
    exact hf hfy.symm ▸ hy

private lemma image_strictMono_on {α β ι : Type*} [Preorder ι]
    (f : α → β) {S : Set α} (hf : Set.InjOn f S)
    {chain : ι → Set α} (hc : StrictMono chain)
    (hsub : ∀ i, chain i ⊆ S) :
    StrictMono (fun i => f '' chain i) := by
  intro i j hij
  have hs := hc hij
  refine Set.ssubset_iff_subset_ne.mpr ⟨Set.image_mono hs.le, ?_⟩
  intro heq
  change f '' chain i = f '' chain j at heq
  apply hs.ne
  ext x
  constructor
  · intro hx
    have him : f x ∈ f '' chain j := by
      rw [← heq]
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hfy⟩ := him
    exact hf (hsub i hx) (hsub j hy) hfy.symm ▸ hy
  · intro hx
    have him : f x ∈ f '' chain i := by
      rw [heq]
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hfy⟩ := him
    exact hf (hsub j hx) (hsub i hy) hfy.symm ▸ hy

/-- A polynomial embedding with a polynomial retraction sends irreducible
affine-closed subsets to irreducible affine-closed images. -/
lemma irreducible_image_polynomial_retract {ι κ : Type*} [Finite ι] [Finite κ]
    {f : (ι → ℂ) → (κ → ℂ)} {g : (κ → ℂ) → (ι → ℂ)}
    (hf : IsPolynomialMap f) (hg : IsPolynomialMap g)
    (hleft : Function.LeftInverse g f) {A : Set (ι → ℂ)} :
    IsIrreducibleAffineClosed A → IsIrreducibleAffineClosed (f '' A) := by
  intro hA
  refine ⟨polynomial_image_closed_of_retract hf hg hleft hA.1,
    hA.2.1.image f, ?_⟩
  intro B C hB hC hBC
  have hpreB := polynomial_preimage_closed hf hB
  have hpreC := polynomial_preimage_closed hf hC
  have hApre : A = f ⁻¹' B ∪ f ⁻¹' C := by
    ext x
    constructor
    · intro hx
      exact (Set.ext_iff.mp hBC (f x)).mp ⟨x, hx, rfl⟩
    · intro hx
      have him : f x ∈ f '' A := (Set.ext_iff.mp hBC (f x)).mpr hx
      obtain ⟨y, hy, hfy⟩ := him
      exact hleft.injective hfy ▸ hy
  rcases hA.2.2 _ _ hpreB hpreC hApre with h | h
  · left
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : x ∈ f ⁻¹' B := by rw [← h]; exact hx
      exact this
    · intro hy
      exact (Set.ext_iff.mp hBC y).mpr (Or.inl hy)
  · right
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : x ∈ f ⁻¹' C := by rw [← h]; exact hx
      exact this
    · intro hy
      exact (Set.ext_iff.mp hBC y).mpr (Or.inr hy)

/-- A polynomial embedding with a polynomial retraction has an image of the
same exact irreducible-chain dimension as its source affine space. -/
theorem polynomialRetract_range_dimension {d : ℕ} {κ : Type*} [Finite κ]
    {f : (Fin d → ℂ) → (κ → ℂ)} {g : (κ → ℂ) → (Fin d → ℂ)}
    (hf : IsPolynomialMap f) (hg : IsPolynomialMap g)
    (hleft : Function.LeftInverse g f) :
    HasAffineZariskiDimension d (Set.range f) := by
  have hbase := affineSpace_hasAffineZariskiDimension d
  constructor
  · obtain ⟨chain, hmono, hirr, _⟩ := hbase.1
    refine ⟨fun i => f '' chain i,
      image_strictMono_global f hleft.injective hmono, ?_, ?_⟩
    · intro i
      exact irreducible_image_polynomial_retract hf hg hleft (hirr i)
    · intro i _ hx
      rcases hx with ⟨x, _, rfl⟩
      exact ⟨x, rfl⟩
  · rintro ⟨chain, hmono, hirr, hsub⟩
    apply hbase.2
    refine ⟨fun i => g '' chain i, ?_, ?_, fun _ => Set.subset_univ _⟩
    · apply image_strictMono_on g (S := Set.range f)
        (hc := hmono) (hsub := hsub)
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hxy
      apply congrArg f
      simpa [hleft a, hleft b] using hxy
    · intro i
      have hi := hirr i
      have hclosed : affineZariskiClosure (g '' chain i) = g '' chain i := by
        have heq : g '' chain i = f ⁻¹' chain i := by
          ext x
          constructor
          · rintro ⟨y, hy, rfl⟩
            have hyrange := hsub i hy
            obtain ⟨z, rfl⟩ := hyrange
            simpa [hleft z] using hy
          · intro hx
            exact ⟨f x, hx, hleft x⟩
        rw [heq]
        exact polynomial_preimage_closed hf hi.1
      refine ⟨hclosed, hi.2.1.image g, ?_⟩
      intro A B hA hB hAB
      have hfA := polynomial_image_closed_of_retract hf hg hleft hA
      have hfB := polynomial_image_closed_of_retract hf hg hleft hB
      have himage : chain i = f '' A ∪ f '' B := by
        rw [← Set.image_union, ← hAB]
        ext y
        constructor
        · intro hy
          exact ⟨g y, ⟨y, hy, rfl⟩, by
            obtain ⟨x, rfl⟩ := hsub i hy
            simp [hleft x]⟩
        · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
          obtain ⟨z, rfl⟩ := hsub i hy
          simpa [hleft z] using hy
      rcases hi.2.2 _ _ hfA hfB himage with h | h
      · left
        change g '' chain i = A
        rw [h]
        ext x
        constructor
        · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
          simpa [hleft a] using ha
        · intro hx
          exact ⟨f x, ⟨x, hx, rfl⟩, hleft x⟩
      · right
        change g '' chain i = B
        rw [h]
        ext x
        constructor
        · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
          simpa [hleft a] using ha
        · intro hx
          exact ⟨f x, ⟨x, hx, rfl⟩, hleft x⟩

end

end Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension
