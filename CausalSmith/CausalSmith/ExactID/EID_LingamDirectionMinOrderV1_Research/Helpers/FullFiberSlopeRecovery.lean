/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Loading-slope recovery on the complete same-arrow fiber

The apolar flagship exposes the common contraction-kernel identity at its base
point.  The lemmas here apply that identity to an arbitrary retained-band
same-arrow representation; no genericity assumption is imposed on the competing
parameter.
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.DirectLatentSwaps
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.SlopeUniqueness

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

private noncomputable def fullFiberDehomX :
    MvPolynomial (Fin 2) ℂ →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i : Fin 2 => if i = 0 then 1 else Polynomial.X)

private noncomputable def fullFiberDehomY :
    MvPolynomial (Fin 2) ℂ →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i : Fin 2 => if i = 0 then Polynomial.X else 1)

private lemma map_fin_succ' {α : Type*} (n : ℕ) (f : Fin (n + 1) → α) :
    Finset.univ.val.map f =
      f 0 ::ₘ Finset.univ.val.map (fun i : Fin n => f i.succ) := by
  have h := congrArg Finset.val (Fin.univ_succAbove n (0 : Fin (n + 1)))
  simpa [Finset.cons_val, Finset.map_val, Multiset.map_map] using
    congrArg (Multiset.map f) h

private lemma map_fin_castSucc' {α : Type*} (n : ℕ) (f : Fin (n + 1) → α) :
    Finset.univ.val.map f =
      f (Fin.last n) ::ₘ Finset.univ.val.map (fun i : Fin n => f i.castSucc) := by
  have h := congrArg Finset.val (Fin.univ_castSuccEmb n)
  simpa [Finset.cons_val, Finset.map_val, Multiset.map_map] using
    congrArg (Multiset.map f) h

private lemma roots_prod_X_sub_C' {n : ℕ} (f : Fin n → ℂ) :
    (∏ i, (Polynomial.X - Polynomial.C (f i))).roots =
      Finset.univ.val.map f := by
  rw [Polynomial.roots_prod]
  · simp
  · exact Finset.prod_ne_zero_iff.mpr
      (fun i _ => Polynomial.X_sub_C_ne_zero (f i))

private lemma roots_prod_C_sub_X' {n : ℕ} (f : Fin n → ℂ) :
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

private lemma fullFiberDehomX_support_forward (m : ℕ) (γ : ℂ) (ρ : Fin m → ℂ) :
    fullFiberDehomX (supportAnnihilator (forwardLoading m γ ρ)) =
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
  rw [show fullFiberDehomX
      (MvPolynomial.C (forwardLoading m γ ρ (Fin.last (m + 1))).2 *
        MvPolynomial.X 0 -
        MvPolynomial.C (forwardLoading m γ ρ (Fin.last (m + 1))).1 *
          MvPolynomial.X 1) = 1 by simp [fullFiberDehomX, forwardLoading]]
  rw [mul_one]
  apply Finset.prod_congr rfl
  intro j _
  simp [fullFiberDehomX, hfirst j]

private lemma roots_fullFiberDehomX_forward (m : ℕ) (γ : ℂ) (ρ : Fin m → ℂ) :
    (fullFiberDehomX (supportAnnihilator (forwardLoading m γ ρ))).roots =
      γ ::ₘ Finset.univ.val.map (fun i => ρ i) := by
  rw [fullFiberDehomX_support_forward, roots_prod_C_sub_X', map_fin_succ']
  have htail : (fun i : Fin m =>
      (forwardLoading m γ ρ (Fin.castSucc i.succ)).2) = ρ := by
    funext i
    have hi : i.val ≠ m := by omega
    simp [forwardLoading, hi]
  rw [htail]
  simp [forwardLoading]

private lemma fullFiberDehomY_support_reverse (m : ℕ) (δ : ℂ) (σ : Fin m → ℂ) :
    fullFiberDehomY (supportAnnihilator (reverseLoading m δ σ)) =
      -∏ j : Fin (m + 1),
        (Polynomial.X - Polynomial.C (reverseLoading m δ σ j.succ).1) := by
  rw [supportAnnihilator, map_prod, Fin.prod_univ_succ]
  simp [fullFiberDehomY, reverseLoading]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hlast : j.val = m
  · simp [hlast]
  · simp [hlast]

private lemma roots_fullFiberDehomY_reverse (m : ℕ) (δ : ℂ) (σ : Fin m → ℂ) :
    (fullFiberDehomY (supportAnnihilator (reverseLoading m δ σ))).roots =
      δ ::ₘ Finset.univ.val.map (fun i => σ i) := by
  rw [fullFiberDehomY_support_reverse, Polynomial.roots_neg,
    roots_prod_X_sub_C', map_fin_castSucc']
  have hmiddle : (fun i : Fin m =>
      (reverseLoading m δ σ i.castSucc.succ).1) = σ := by
    funext i
    have hi : i.val ≠ m := by omega
    simp [reverseLoading, hi]
  rw [hmiddle]
  simp [reverseLoading]

private lemma forward_support_ne_zero' (m : ℕ) (γ : ℂ) (ρ : Fin m → ℂ) :
    supportAnnihilator (forwardLoading m γ ρ) ≠ 0 := by
  apply supportAnnihilator_ne_zero
  intro j
  by_cases hzero : j.val = 0
  · simp [forwardLoading, hzero]
  by_cases hlast : j.val = m + 1
  · simp [forwardLoading, hzero, hlast]
  · simp [forwardLoading, hzero, hlast]

private lemma reverse_support_ne_zero' (m : ℕ) (δ : ℂ) (σ : Fin m → ℂ) :
    supportAnnihilator (reverseLoading m δ σ) ≠ 0 := by
  apply supportAnnihilator_ne_zero
  intro j
  by_cases hzero : j.val = 0
  · simp [reverseLoading, hzero]
  by_cases hlast : j.val = m + 1
  · simp [reverseLoading, hzero, hlast]
  · simp [reverseLoading, hzero, hlast]

/-- The displayed forward common-kernel identity determines the finite-slope
multiset of every same-arrow representation, including nongeneric ones. -/
theorem forward_slopes_determined_by_kernel_identity (m : ℕ) (θ : ParamSpace ℂ m)
    (hkernel : ∀ q : MvPolynomial (Fin 2) ℂ, q.IsHomogeneous (m + 2) →
      ((∀ k, k ≤ m → diffApply q
          (dividedPowerBlock (forwardCumulantMap m (2 * m + 2) θ) (m + 2 + k)) = 0) ↔
        ∃ c : ℂ, q = c • supportAnnihilator (forwardLoading m θ.1 θ.2.1)))
    (θ' : ParamSpace ℂ m)
    (heq : forwardCumulantMap m (2 * m + 2) θ' =
      forwardCumulantMap m (2 * m + 2) θ) :
    loadingSlopeMultiset θ' = loadingSlopeMultiset θ := by
  let Q' := supportAnnihilator (forwardLoading m θ'.1 θ'.2.1)
  let Q := supportAnnihilator (forwardLoading m θ.1 θ.2.1)
  have hhom : Q'.IsHomogeneous (m + 2) := supportAnnihilator_isHomogeneous _
  have hcon : ∀ k, k ≤ m → diffApply Q'
      (dividedPowerBlock (forwardCumulantMap m (2 * m + 2) θ) (m + 2 + k)) = 0 := by
    have hown := forward_supportAnnihilator_in_contraction_kernel m θ' Q' hhom
      ⟨1, by simp [Q']⟩
    rw [heq] at hown
    exact hown
  obtain ⟨c, hcQ⟩ := (hkernel Q' hhom).mp hcon
  have hc : c ≠ 0 := by
    intro hc0
    have hQzero : Q' = 0 := by simpa [hc0] using hcQ
    exact forward_support_ne_zero' m θ'.1 θ'.2.1 (by simpa [Q'] using hQzero)
  have hdehom : fullFiberDehomX Q' = Polynomial.C c * fullFiberDehomX Q := by
    have hcQ' : Q' = c • Q := by simpa [Q] using hcQ
    rw [hcQ']
    simp [MvPolynomial.smul_eq_C_mul, fullFiberDehomX]
  have hroots : (fullFiberDehomX Q').roots = (fullFiberDehomX Q).roots := by
    rw [hdehom, Polynomial.roots_C_mul _ hc]
  simpa [loadingSlopeMultiset, Q', Q, roots_fullFiberDehomX_forward] using hroots

/-- Reverse-arrow mirror of `forward_slopes_determined_by_kernel_identity`. -/
theorem reverse_slopes_determined_by_kernel_identity (m : ℕ) (η : ParamSpace ℂ m)
    (hkernel : ∀ q : MvPolynomial (Fin 2) ℂ, q.IsHomogeneous (m + 2) →
      ((∀ k, k ≤ m → diffApply q
          (dividedPowerBlock (reverseCumulantMap m (2 * m + 2) η) (m + 2 + k)) = 0) ↔
        ∃ c : ℂ, q = c • supportAnnihilator (reverseLoading m η.1 η.2.1)))
    (η' : ParamSpace ℂ m)
    (heq : reverseCumulantMap m (2 * m + 2) η' =
      reverseCumulantMap m (2 * m + 2) η) :
    loadingSlopeMultiset η' = loadingSlopeMultiset η := by
  let Q' := supportAnnihilator (reverseLoading m η'.1 η'.2.1)
  let Q := supportAnnihilator (reverseLoading m η.1 η.2.1)
  have hhom : Q'.IsHomogeneous (m + 2) := supportAnnihilator_isHomogeneous _
  have hcon : ∀ k, k ≤ m → diffApply Q'
      (dividedPowerBlock (reverseCumulantMap m (2 * m + 2) η) (m + 2 + k)) = 0 := by
    have hown := reverse_supportAnnihilator_in_contraction_kernel m η' Q' hhom
      ⟨1, by simp [Q']⟩
    rw [heq] at hown
    exact hown
  obtain ⟨c, hcQ⟩ := (hkernel Q' hhom).mp hcon
  have hc : c ≠ 0 := by
    intro hc0
    have hQzero : Q' = 0 := by simpa [hc0] using hcQ
    exact reverse_support_ne_zero' m η'.1 η'.2.1 (by simpa [Q'] using hQzero)
  have hdehom : fullFiberDehomY Q' = Polynomial.C c * fullFiberDehomY Q := by
    have hcQ' : Q' = c • Q := by simpa [Q] using hcQ
    rw [hcQ']
    simp [MvPolynomial.smul_eq_C_mul, fullFiberDehomY]
  have hroots : (fullFiberDehomY Q').roots = (fullFiberDehomY Q).roots := by
    rw [hdehom, Polynomial.roots_C_mul _ hc]
  simpa [loadingSlopeMultiset, Q', Q, roots_fullFiberDehomY_reverse] using hroots

/-- A root polynomial nonzero at zero certifies that every displayed latent
slope is nonzero. -/
lemma latent_slopes_ne_zero_of_root_polynomial {m : ℕ} {θ : ParamSpace ℂ m}
    {Q : Polynomial ℂ} (hQ : Q ≠ 0)
    (hroots : Q.roots = loadingSlopeMultiset θ) (hzero : Q.eval 0 ≠ 0) :
    ∀ i, θ.2.1 i ≠ 0 := by
  intro i hi
  apply hzero
  have hm : (0 : ℂ) ∈ Q.roots := by
    rw [hroots]
    rw [loadingSlopeMultiset, Multiset.mem_cons, Multiset.mem_map]
    exact Or.inr ⟨i, Finset.mem_univ i, hi⟩
  exact (Polynomial.mem_roots hQ).mp hm

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
