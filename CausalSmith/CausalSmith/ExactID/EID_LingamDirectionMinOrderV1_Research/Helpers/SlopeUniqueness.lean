/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ApolarKernelAux
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ReverseApolarKernel

/-!
This file recovers, with multiplicity, the finite forward and reverse loading
slopes from the one-dimensional common apolar-contraction kernel.
-/

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

private noncomputable def dehomX :
    MvPolynomial (Fin 2) ℂ →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i : Fin 2 => if i = 0 then 1 else Polynomial.X)

private noncomputable def dehomY :
    MvPolynomial (Fin 2) ℂ →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i : Fin 2 => if i = 0 then Polynomial.X else 1)

private lemma map_fin_succ {α : Type*} (n : ℕ) (f : Fin (n + 1) → α) :
    Finset.univ.val.map f =
      f 0 ::ₘ Finset.univ.val.map (fun i : Fin n => f i.succ) := by
  have h := congrArg Finset.val (Fin.univ_succAbove n (0 : Fin (n + 1)))
  simpa [Finset.cons_val, Finset.map_val, Multiset.map_map] using
    congrArg (Multiset.map f) h

private lemma map_fin_castSucc {α : Type*} (n : ℕ) (f : Fin (n + 1) → α) :
    Finset.univ.val.map f =
      f (Fin.last n) ::ₘ Finset.univ.val.map (fun i : Fin n => f i.castSucc) := by
  have h := congrArg Finset.val (Fin.univ_castSuccEmb n)
  simpa [Finset.cons_val, Finset.map_val, Multiset.map_map] using
    congrArg (Multiset.map f) h

private lemma roots_prod_X_sub_C {n : ℕ} (f : Fin n → ℂ) :
    (∏ i, (Polynomial.X - Polynomial.C (f i))).roots =
      Finset.univ.val.map f := by
  rw [Polynomial.roots_prod]
  · simp
  · exact Finset.prod_ne_zero_iff.mpr
      (fun i _ => Polynomial.X_sub_C_ne_zero (f i))

private lemma roots_prod_C_sub_X {n : ℕ} (f : Fin n → ℂ) :
    (∏ i, (Polynomial.C (f i) - Polynomial.X)).roots =
      Finset.univ.val.map f := by
  rw [Polynomial.roots_prod]
  · simp only [show ∀ i, Polynomial.C (f i) - Polynomial.X =
        -(Polynomial.X - Polynomial.C (f i)) by intro i; ring,
      Polynomial.roots_neg, Polynomial.roots_X_sub_C]
    simp
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    rw [show Polynomial.C (f i) - Polynomial.X =
      -(Polynomial.X - Polynomial.C (f i)) by ring]
    exact neg_ne_zero.mpr (Polynomial.X_sub_C_ne_zero (f i))

private lemma dehomX_supportAnnihilator_forward (m : ℕ) (γ : ℂ)
    (ρ : Fin m → ℂ) :
    dehomX (supportAnnihilator (forwardLoading m γ ρ)) =
      ∏ j : Fin (m + 1),
        (Polynomial.C (forwardLoading m γ ρ (Fin.castSucc j)).2 - Polynomial.X) := by
  rw [supportAnnihilator, map_prod, Fin.prod_univ_castSucc]
  have hfirst : ∀ j : Fin (m + 1),
      (forwardLoading m γ ρ (Fin.castSucc j)).1 = 1 := by
    intro j
    by_cases hj : j = 0
    · simp [forwardLoading, hj]
    · have hlast : j.val ≠ m + 1 := by omega
      simp [forwardLoading, hj, hlast]
  rw [show dehomX
      (MvPolynomial.C (forwardLoading m γ ρ (Fin.last (m + 1))).2 *
        MvPolynomial.X 0 -
        MvPolynomial.C (forwardLoading m γ ρ (Fin.last (m + 1))).1 *
          MvPolynomial.X 1) = 1 by simp [dehomX, forwardLoading]]
  rw [mul_one]
  apply Finset.prod_congr rfl
  intro j _
  simp [dehomX, hfirst j]

private lemma roots_dehomX_supportAnnihilator_forward (m : ℕ) (γ : ℂ)
    (ρ : Fin m → ℂ) :
    (dehomX (supportAnnihilator (forwardLoading m γ ρ))).roots =
      γ ::ₘ Finset.univ.val.map (fun i => ρ i) := by
  rw [dehomX_supportAnnihilator_forward, roots_prod_C_sub_X, map_fin_succ]
  have htail : (fun i : Fin m =>
      (forwardLoading m γ ρ (Fin.castSucc i.succ)).2) = ρ := by
    funext i
    have hi : i.val ≠ m := by omega
    simp [forwardLoading, hi]
  rw [htail]
  simp [forwardLoading]

private lemma dehomY_supportAnnihilator_reverse (m : ℕ) (δ : ℂ)
    (σ : Fin m → ℂ) :
    dehomY (supportAnnihilator (reverseLoading m δ σ)) =
      -∏ j : Fin (m + 1),
        (Polynomial.X - Polynomial.C (reverseLoading m δ σ j.succ).1) := by
  rw [supportAnnihilator, map_prod, Fin.prod_univ_succ]
  simp [dehomY, reverseLoading]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hlast : j.val = m
  · simp [hlast]
  · simp [hlast]

private lemma roots_dehomY_supportAnnihilator_reverse (m : ℕ) (δ : ℂ)
    (σ : Fin m → ℂ) :
    (dehomY (supportAnnihilator (reverseLoading m δ σ))).roots =
      δ ::ₘ Finset.univ.val.map (fun i => σ i) := by
  rw [dehomY_supportAnnihilator_reverse, Polynomial.roots_neg,
    roots_prod_X_sub_C, map_fin_castSucc]
  have hmiddle : (fun i : Fin m =>
      (reverseLoading m δ σ i.castSucc.succ).1) = σ := by
    funext i
    have hi : i.val ≠ m := by omega
    simp [reverseLoading, hi]
  rw [hmiddle]
  simp [reverseLoading]

private lemma forward_support_ne_zero (m : ℕ) (γ : ℂ) (ρ : Fin m → ℂ) :
    supportAnnihilator (forwardLoading m γ ρ) ≠ 0 := by
  apply supportAnnihilator_ne_zero
  intro j
  by_cases hzero : j.val = 0
  · simp [forwardLoading, hzero]
  by_cases hlast : j.val = m + 1
  · simp [forwardLoading, hzero, hlast]
  · simp [forwardLoading, hzero, hlast]

private lemma reverse_support_ne_zero (m : ℕ) (δ : ℂ) (σ : Fin m → ℂ) :
    supportAnnihilator (reverseLoading m δ σ) ≠ 0 := by
  apply supportAnnihilator_ne_zero
  intro j
  by_cases hzero : j.val = 0
  · simp [reverseLoading, hzero]
  by_cases hlast : j.val = m + 1
  · simp [reverseLoading, hzero, hlast]
  · simp [reverseLoading, hzero, hlast]

/--
At a forward parameter where the common apolar-contraction kernel is the
support-annihilator line, cumulants through order `2m+2` determine the multiset
of the direct and latent finite loading slopes.
-/
theorem forward_slopes_determined_by_cumulants (m : ℕ) (θ : ParamSpace ℂ m)
    (hslopes : Function.Injective
      (fun j : Fin (m + 1) => (forwardLoading m θ.1 θ.2.1 (Fin.castSucc j)).2))
    (hnonzero : ∀ j : Fin (m + 1),
      (forwardLoading m θ.1 θ.2.1 (Fin.castSucc j)).2 ≠ 0)
    (hrank : Function.Injective (forwardWeightedContraction m θ))
    (θ'' : ParamSpace ℂ m)
    (heq : forwardCumulantMap m (2 * m + 2) θ'' = forwardCumulantMap m (2 * m + 2) θ) :
    θ''.1 ::ₘ (Finset.univ.val.map (fun i => θ''.2.1 i)) =
      θ.1 ::ₘ (Finset.univ.val.map (fun i => θ.2.1 i)) := by
  let Q'' := supportAnnihilator (forwardLoading m θ''.1 θ''.2.1)
  let Q := supportAnnihilator (forwardLoading m θ.1 θ.2.1)
  have hhom : Q''.IsHomogeneous (m + 2) :=
    supportAnnihilator_isHomogeneous _
  have hcon : ∀ k, k ≤ m → diffApply Q''
      (dividedPowerBlock (forwardCumulantMap m (2 * m + 2) θ) (m + 2 + k)) = 0 := by
    have hown := forward_supportAnnihilator_in_contraction_kernel m θ'' Q'' hhom
      ⟨1, by simp [Q'']⟩
    rw [heq] at hown
    exact hown
  obtain ⟨c, hcQ⟩ :=
    (forward_apolar_kernel_identity m θ hslopes hnonzero hrank Q'' hhom).mp hcon
  have hc : c ≠ 0 := by
    intro hc0
    have hQzero : Q'' = 0 := by simpa [hc0] using hcQ
    exact forward_support_ne_zero m θ''.1 θ''.2.1 (by simpa [Q''] using hQzero)
  have hdehom : dehomX Q'' = Polynomial.C c * dehomX Q := by
    have hcQ' : Q'' = c • Q := by simpa [Q] using hcQ
    rw [hcQ']
    simp [MvPolynomial.smul_eq_C_mul, dehomX]
  have hroots : (dehomX Q'').roots = (dehomX Q).roots := by
    rw [hdehom, Polynomial.roots_C_mul _ hc]
  simpa [Q'', Q, roots_dehomX_supportAnnihilator_forward] using hroots

/--
At a reverse parameter where the common apolar-contraction kernel is the
support-annihilator line, cumulants through order `2m+2` determine the multiset
of the direct and latent finite loading slopes.
-/
theorem reverse_slopes_determined_by_cumulants (m : ℕ) (η : ParamSpace ℂ m)
    (hslopes : Function.Injective
      (fun j : Fin (m + 1) => (reverseLoading m η.1 η.2.1 j.succ).1))
    (hnonzero : ∀ j : Fin (m + 1), (reverseLoading m η.1 η.2.1 j.succ).1 ≠ 0)
    (hrank : Function.Injective (reverseWeightedContraction m η))
    (η'' : ParamSpace ℂ m)
    (heq : reverseCumulantMap m (2 * m + 2) η'' = reverseCumulantMap m (2 * m + 2) η) :
    η''.1 ::ₘ (Finset.univ.val.map (fun i => η''.2.1 i)) =
      η.1 ::ₘ (Finset.univ.val.map (fun i => η.2.1 i)) := by
  let Q'' := supportAnnihilator (reverseLoading m η''.1 η''.2.1)
  let Q := supportAnnihilator (reverseLoading m η.1 η.2.1)
  have hhom : Q''.IsHomogeneous (m + 2) :=
    supportAnnihilator_isHomogeneous _
  have hcon : ∀ k, k ≤ m → diffApply Q''
      (dividedPowerBlock (reverseCumulantMap m (2 * m + 2) η) (m + 2 + k)) = 0 := by
    have hown := reverse_supportAnnihilator_in_contraction_kernel m η'' Q'' hhom
      ⟨1, by simp [Q'']⟩
    rw [heq] at hown
    exact hown
  obtain ⟨c, hcQ⟩ :=
    (reverse_apolar_kernel_identity m η hslopes hnonzero hrank Q'' hhom).mp hcon
  have hc : c ≠ 0 := by
    intro hc0
    have hQzero : Q'' = 0 := by simpa [hc0] using hcQ
    exact reverse_support_ne_zero m η''.1 η''.2.1 (by simpa [Q''] using hQzero)
  have hdehom : dehomY Q'' = Polynomial.C c * dehomY Q := by
    have hcQ' : Q'' = c • Q := by simpa [Q] using hcQ
    rw [hcQ']
    simp [MvPolynomial.smul_eq_C_mul, dehomY]
  have hroots : (dehomY Q'').roots = (dehomY Q).roots := by
    rw [hdehom, Polynomial.roots_C_mul _ hc]
  simpa [Q'', Q, roots_dehomY_supportAnnihilator_reverse] using hroots

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
