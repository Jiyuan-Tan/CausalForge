/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension.ZariskiClosure

/-!
# Polynomial maps between complex affine spaces

This file defines coordinatewise polynomial maps and proves their composition,
substitution, and affine-closed preimage laws.
-/

namespace Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension

noncomputable section

/-- Every coordinate of `f` is a polynomial in the source coordinates. -/
def IsPolynomialMap {ι κ : Type*} (f : (ι → ℂ) → (κ → ℂ)) : Prop :=
  ∀ k, ∃ P : MvPolynomial ι ℂ, ∀ x, MvPolynomial.eval x P = f x k

/-- The identity map is polynomial. -/
lemma isPolynomialMap_id {ι : Type*} :
    IsPolynomialMap (id : (ι → ℂ) → (ι → ℂ)) := by
  intro i
  exact ⟨MvPolynomial.X i, by simp⟩

/-- A composite of polynomial maps is polynomial. -/
lemma IsPolynomialMap.comp {ι κ τ : Type*}
    {f : (ι → ℂ) → (κ → ℂ)} {g : (κ → ℂ) → (τ → ℂ)}
    (hg : IsPolynomialMap g) (hf : IsPolynomialMap f) :
    IsPolynomialMap (g ∘ f) := by
  classical
  choose Pf hPf using hf
  intro t
  obtain ⟨Q, hQ⟩ := hg t
  refine ⟨MvPolynomial.eval₂ MvPolynomial.C Pf Q, ?_⟩
  intro x
  rw [MvPolynomial.eval_eval₂]
  have hC : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℂ := by
    ext z
    simp
  rw [hC, MvPolynomial.eval₂_id]
  calc
    MvPolynomial.eval (fun k => MvPolynomial.eval x (Pf k)) Q =
        MvPolynomial.eval (f x) Q := by
          apply congrArg (fun v => MvPolynomial.eval v Q)
          funext k
          exact hPf k x
    _ = g (f x) t := hQ (f x)

/-- Substituting a polynomial map into a target polynomial yields a source polynomial. -/
lemma IsPolynomialMap.eval_comp {ι κ : Type*}
    {f : (ι → ℂ) → (κ → ℂ)} (hf : IsPolynomialMap f)
    (Q : MvPolynomial κ ℂ) :
    ∃ P : MvPolynomial ι ℂ, ∀ x,
      MvPolynomial.eval x P = MvPolynomial.eval (f x) Q := by
  classical
  choose Pf hPf using hf
  refine ⟨MvPolynomial.eval₂ MvPolynomial.C Pf Q, ?_⟩
  intro x
  rw [MvPolynomial.eval_eval₂]
  have hC : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℂ := by
    ext z
    simp
  rw [hC, MvPolynomial.eval₂_id]
  apply congrArg (fun v => MvPolynomial.eval v Q)
  funext k
  exact hPf k x

/-- The preimage of an affine-closed set under a polynomial map is affine-closed. -/
lemma polynomial_preimage_closed {ι κ : Type*}
    {f : (ι → ℂ) → (κ → ℂ)} (hf : IsPolynomialMap f)
    {A : Set (κ → ℂ)} (hA : affineZariskiClosure A = A) :
    affineZariskiClosure (f ⁻¹' A) = f ⁻¹' A := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [← hA]
    intro Q hQ
    change MvPolynomial.eval (f x) Q = 0
    obtain ⟨P, hP⟩ := hf.eval_comp Q
    rw [← hP x]
    exact hx P (by
      intro y hy
      change MvPolynomial.eval y P = 0
      rw [hP y]
      simpa [MvPolynomial.aeval_def, MvPolynomial.eval₂_id] using hQ (f y) hy)
  · exact affineZariskiClosure_extensive _

/-- The fixed-point set of a polynomial endomorphism is affine-closed. -/
lemma polynomial_fixedPoints_closed {ι : Type*}
    {f : (ι → ℂ) → (ι → ℂ)} (hf : IsPolynomialMap f) :
    affineZariskiClosure {x | f x = x} = {x | f x = x} := by
  apply Set.Subset.antisymm
  · intro x hx
    funext i
    obtain ⟨P, hP⟩ := hf i
    let Q := P - MvPolynomial.X i
    have hQ : ∀ y ∈ {y | f y = y}, MvPolynomial.eval y Q = 0 := by
      intro y hy
      simp [Q, hP y, congrFun hy i]
    have := hx Q hQ
    exact sub_eq_zero.mp (by simpa [Q, hP x] using this)
  · exact affineZariskiClosure_extensive _

/-- The range of a polynomial embedding with a polynomial left inverse is affine-closed. -/
lemma polynomial_range_closed_of_retract {ι κ : Type*}
    {f : (ι → ℂ) → (κ → ℂ)} {g : (κ → ℂ) → (ι → ℂ)}
    (hf : IsPolynomialMap f) (hg : IsPolynomialMap g)
    (hleft : Function.LeftInverse g f) :
    affineZariskiClosure (Set.range f) = Set.range f := by
  have hfix : Set.range f = {y | f (g y) = y} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact congrArg f (hleft x)
    · intro hy
      exact ⟨g y, hy⟩
  rw [hfix]
  exact polynomial_fixedPoints_closed (hf.comp hg)

/-- A polynomial retract sends affine-closed source subsets to affine-closed images. -/
lemma polynomial_image_closed_of_retract {ι κ : Type*}
    {f : (ι → ℂ) → (κ → ℂ)} {g : (κ → ℂ) → (ι → ℂ)}
    (hf : IsPolynomialMap f) (hg : IsPolynomialMap g)
    (hleft : Function.LeftInverse g f)
    {A : Set (ι → ℂ)} (hA : affineZariskiClosure A = A) :
    affineZariskiClosure (f '' A) = f '' A := by
  have hrange := polynomial_range_closed_of_retract hf hg hleft
  have hpre := polynomial_preimage_closed hg hA
  have heq : f '' A = Set.range f ∩ g ⁻¹' A := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, rfl⟩, by simpa [hleft x] using hx⟩
    · rintro ⟨⟨x, rfl⟩, hx⟩
      exact ⟨x, by simpa [hleft x] using hx, rfl⟩
  rw [heq]
  exact affineZariskiClosure_inter hrange hpre

end

end Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension
