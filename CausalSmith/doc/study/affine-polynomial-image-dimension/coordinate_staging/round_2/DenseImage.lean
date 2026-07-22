/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension.Irreducibility
import Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension.PolynomialMap

/-!
# Dense polynomial images

This file proves that restricting a polynomial map to a Zariski-dense source
does not change its image closure and that this closure is irreducible.
-/

namespace Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension

noncomputable section

/-- The closure of the image of a dense set under a polynomial map equals the
closure of the full range. -/
lemma affineZariskiClosure_polynomial_image_of_dense
    {ι κ : Type*} {f : (ι → ℂ) → (κ → ℂ)} (hf : IsPolynomialMap f)
    {A : Set (ι → ℂ)} (hA : affineZariskiClosure A = Set.univ) :
    affineZariskiClosure (f '' A) = affineZariskiClosure (Set.range f) := by
  apply Set.Subset.antisymm
  · exact affineZariskiClosure_mono (Set.image_subset_range f A)
  · intro y hy P hP
    change MvPolynomial.eval y P = 0
    obtain ⟨Q, hQ⟩ := hf.eval_comp P
    have hQA : ∀ x ∈ A, MvPolynomial.eval x Q = 0 := by
      intro x hx
      rw [hQ x]
      exact hP (f x) ⟨x, hx, rfl⟩
    have hQall : ∀ x, MvPolynomial.eval x Q = 0 := by
      intro x
      have hx : x ∈ affineZariskiClosure A := by rw [hA]; trivial
      exact hx Q hQA
    exact hy P (by
      rintro _ ⟨x, rfl⟩
      have hx : MvPolynomial.eval (f x) P = 0 := (hQ x).symm.trans (hQall x)
      simpa [MvPolynomial.aeval_def, MvPolynomial.eval₂_id] using hx)

/-- The closure of a polynomial image of a nonempty dense subset of finite
complex affine space is irreducible. -/
theorem irreducible_affineClosure_polynomial_image_of_dense
    {ι κ : Type*} [Finite ι] [Finite κ]
    {f : (ι → ℂ) → (κ → ℂ)} (hf : IsPolynomialMap f)
    {A : Set (ι → ℂ)} (hA : affineZariskiClosure A = Set.univ)
    (hne : A.Nonempty) :
    IsIrreducibleAffineClosed (affineZariskiClosure (f '' A)) := by
  refine ⟨affineZariskiClosure_idem _, hne.image f |>.mono
      (affineZariskiClosure_extensive _), ?_⟩
  intro B C hB hC hBC
  have hpreB := polynomial_preimage_closed hf hB
  have hpreC := polynomial_preimage_closed hf hC
  have hpreUnion : affineZariskiClosure (f ⁻¹' (B ∪ C)) = f ⁻¹' (B ∪ C) := by
    rw [Set.preimage_union]
    exact affineZariskiClosure_union hpreB hpreC
  have hrange : Set.range f ⊆ B ∪ C := by
    intro y hy
    have hyc : y ∈ affineZariskiClosure (f '' A) := by
      rw [affineZariskiClosure_polynomial_image_of_dense hf hA]
      exact affineZariskiClosure_extensive _ hy
    rw [hBC] at hyc
    exact hyc
  have huniv : Set.univ = f ⁻¹' B ∪ f ⁻¹' C := by
    rw [← Set.preimage_union]
    symm
    apply Set.eq_univ_of_forall
    intro x
    exact hrange ⟨x, rfl⟩
  have hirrUniv : IsIrreducibleAffineClosed (Set.univ : Set (ι → ℂ)) := by
    have hzero : MvPolynomial.vanishingIdeal ℂ (Set.univ : Set (ι → ℂ)) = ⊥ := by
      apply le_antisymm
      · intro P hP
        apply MvPolynomial.funext
        intro x
        exact hP x trivial
      · exact bot_le
    have hclosed : affineZariskiClosure (Set.univ : Set (ι → ℂ)) = Set.univ := by
      exact Set.eq_univ_of_forall (fun _ => affineZariskiClosure_extensive _ trivial)
    apply (irreducibleAffineClosed_iff_isPrime hclosed Set.univ_nonempty).mpr
    rw [hzero]
    infer_instance
  rcases hirrUniv.2.2 _ _ hpreB hpreC huniv with hfull | hfull
  · left
    apply Set.Subset.antisymm
    · have him : f '' A ⊆ B := by
        rintro _ ⟨x, _, rfl⟩
        have : x ∈ f ⁻¹' B := by rw [← hfull]; trivial
        exact this
      simpa [hB] using affineZariskiClosure_mono him
    · intro y hy
      rw [hBC]
      exact Or.inl hy
  · right
    apply Set.Subset.antisymm
    · have him : f '' A ⊆ C := by
        rintro _ ⟨x, _, rfl⟩
        have : x ∈ f ⁻¹' C := by rw [← hfull]; trivial
        exact this
      simpa [hC] using affineZariskiClosure_mono him
    · intro y hy
      rw [hBC]
      exact Or.inr hy

/-- The closure of the full range of a polynomial map between finite complex
affine spaces is irreducible. -/
theorem polynomialImageClosure_isIrreducible
    {ι κ : Type*} [Finite ι] [Finite κ]
    {f : (ι → ℂ) → (κ → ℂ)} (hf : IsPolynomialMap f) :
    IsIrreducibleAffineClosed (affineZariskiClosure (Set.range f)) := by
  have hdense : affineZariskiClosure (Set.univ : Set (ι → ℂ)) = Set.univ :=
    Set.eq_univ_of_forall (fun _ => affineZariskiClosure_extensive _ trivial)
  have hirr := irreducible_affineClosure_polynomial_image_of_dense hf hdense
    (Set.univ_nonempty : (Set.univ : Set (ι → ℂ)).Nonempty)
  simpa [Set.image_univ] using hirr

end

end Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension
