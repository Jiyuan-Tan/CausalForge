/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The finite retained cumulant band

The project represents cumulant vectors by an `ℕ × ℕ`-indexed function, but all
exceptional-locus sets are supported on a finite retained band.  This file makes
the finite affine space explicit and proves that the two closure conventions
agree there.  It is the bridge needed before applying Noetherian dimension
theorems.
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.AlgebraicSetChains
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ExceptionalGeometryBasic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

noncomputable section

/-- Finite coordinates `(r,a)` with `2 ≤ r ≤ L` and `a ≤ r`. -/
abbrev RetainedCumCoord (L : ℕ) :=
  {p : Fin (L + 1) × Fin (L + 1) // 2 ≤ p.1.1 ∧ p.2.1 ≤ p.1.1}

/-- Retained coordinates are a triangular family: at order `k + 2` there
are exactly `k + 3` coordinate positions. -/
def retainedCumCoordEquivSigma (L : ℕ) :
    RetainedCumCoord L ≃ Σ k : Fin (L - 1), Fin (k.1 + 3) where
  toFun p := ⟨⟨p.val.1.val - 2, by
    have hrL := p.val.1.isLt
    have hr2 := p.property.1
    omega⟩, ⟨p.val.2.val, by
      have ha := p.property.2
      have hr2 := p.property.1
      change p.val.2.val < (p.val.1.val - 2) + 3
      omega⟩⟩
  invFun p := ⟨(⟨p.1.val + 2, by
      have hk : p.1.val < L - 1 := p.1.isLt
      change p.1.val + 2 < L + 1
      omega⟩, ⟨p.2.val, by
        have hk : p.1.val < L - 1 := p.1.isLt
        have ha : p.2.val < p.1.val + 3 := p.2.isLt
        change p.2.val < L + 1
        omega⟩), by
          show 2 ≤ p.1.val + 2
          omega, by
          have ha : p.2.val < p.1.val + 3 := p.2.isLt
          change p.2.val ≤ p.1.val + 2
          omega⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> simp <;> omega
  right_inv p := by
    rcases p with ⟨⟨k, hk⟩, ⟨a, ha⟩⟩
    simp
    rw [Fin.heq_ext_iff]
    omega

/-- The finite retained band has the observable dimension `q_L`. -/
theorem card_retainedCumCoord (L : ℕ) :
    Fintype.card (RetainedCumCoord L) = qDim L := by
  rw [Fintype.card_congr (retainedCumCoordEquivSigma L), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Finset.sum_fin_eq_sum_range]
  have hsum :
      (∑ x ∈ Finset.range (L - 1), if h : x < L - 1 then x + 3 else 0) =
        ∑ x ∈ Finset.range (L - 1), (x + 3) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [dif_pos (Finset.mem_range.mp hx)]
  rw [hsum]
  change (Finset.range (L - 1)).sum (fun x => x + 3) = qDim L
  rw [Finset.sum_add_distrib, Finset.sum_range_id]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold qDim
  change (L - 1) * (L - 1 - 1) / 2 + (L - 1) * 3 =
    L * (L + 3) / 2 - 2
  by_cases hL : L < 2
  · interval_cases L <;> decide
  · obtain ⟨k, rfl⟩ : ∃ k, L = k + 2 := by
      exact ⟨L - 2, by omega⟩
    have hpoly : (k + 2) * (k + 2 + 3) =
        k * (k + 1) + (6 * (k + 1) + 4) := by ring
    have h1 : k + 2 - 1 = k + 1 := by omega
    have h2 : k + 1 - 1 = k := by omega
    rw [h1, h2, Nat.mul_comm (k + 1) k, hpoly,
      Nat.add_div_of_dvd_right (Nat.two_dvd_mul_add_one k)]
    omega

/-- Restriction of an infinite cumulant vector to its retained coordinates. -/
def restrictCumBand (L : ℕ) (t : CumVec ℂ) : RetainedCumCoord L → ℂ :=
  fun p => t p.1.1 p.1.2.1

/-- Extend finite retained coordinates by zero. -/
def extendCumBand (L : ℕ) (x : RetainedCumCoord L → ℂ) : CumVec ℂ :=
  fun r a => if h : 2 ≤ r ∧ r ≤ L ∧ a ≤ r then
    x ⟨(⟨r, by omega⟩, ⟨a, by omega⟩), h.1, h.2.2⟩ else 0

lemma extendCumBand_mem_band (L : ℕ) (x : RetainedCumCoord L → ℂ) :
    extendCumBand L x ∈ bandSupportedCumulants L := by
  intro r a h
  simp [extendCumBand, h]

@[simp] lemma restrict_extendCumBand (L : ℕ) (x : RetainedCumCoord L → ℂ) :
    restrictCumBand L (extendCumBand L x) = x := by
  funext p
  have hrL : p.1.1 ≤ L := by omega
  simp [restrictCumBand, extendCumBand, p.2.1, hrL, p.2.2]

lemma extend_restrictCumBand {L : ℕ} {t : CumVec ℂ}
    (ht : t ∈ bandSupportedCumulants L) :
    extendCumBand L (restrictCumBand L t) = t := by
  funext r a
  by_cases h : 2 ≤ r ∧ r ≤ L ∧ a ≤ r
  · simp [extendCumBand, restrictCumBand, h]
  · rw [extendCumBand, dif_neg h, ht r a h]

private def retainedIndex? (L : ℕ) (p : ℕ × ℕ) : Option (RetainedCumCoord L) :=
  if h : 2 ≤ p.1 ∧ p.1 ≤ L ∧ p.2 ≤ p.1 then
    some ⟨(⟨p.1, by omega⟩, ⟨p.2, by omega⟩), h.1, h.2.2⟩
  else none

/-- Substitute zero for every off-band observable variable. -/
def restrictCumPolynomial (L : ℕ) :
    MvPolynomial (ℕ × ℕ) ℂ →ₐ[ℂ] MvPolynomial (RetainedCumCoord L) ℂ :=
  MvPolynomial.bind₁ fun p =>
    match retainedIndex? L p with
    | some q => MvPolynomial.X q
    | none => 0

/-- Regard a finite-band polynomial as a polynomial in all cumulant variables. -/
def extendCumPolynomial (L : ℕ) :
    MvPolynomial (RetainedCumCoord L) ℂ →ₐ[ℂ] MvPolynomial (ℕ × ℕ) ℂ :=
  MvPolynomial.rename fun p => (p.1.1, p.1.2.1)

private lemma retainedIndex_some (L : ℕ) (p : RetainedCumCoord L) :
    retainedIndex? L (p.1.1, p.1.2.1) = some p := by
  have hrL : p.1.1 ≤ L := by omega
  rw [retainedIndex?, dif_pos ⟨p.2.1, hrL, p.2.2⟩]

lemma eval_restrictCumPolynomial_of_band {L : ℕ} {t : CumVec ℂ}
    (ht : t ∈ bandSupportedCumulants L) (P : MvPolynomial (ℕ × ℕ) ℂ) :
    MvPolynomial.eval (restrictCumBand L t) (restrictCumPolynomial L P) =
      MvPolynomial.eval (fun p => t p.1 p.2) P := by
  change (MvPolynomial.eval₂Hom (RingHom.id ℂ) (restrictCumBand L t))
      (restrictCumPolynomial L P) =
    (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun p => t p.1 p.2)) P
  rw [restrictCumPolynomial, MvPolynomial.eval₂Hom_bind₁]
  apply DFunLike.congr_fun _ P
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro p
    by_cases h : 2 ≤ p.1 ∧ p.1 ≤ L ∧ p.2 ≤ p.1
    · simp [retainedIndex?, h, restrictCumBand]
    · simp [retainedIndex?, h, ht p.1 p.2 h]

/-- Gives the stated evaluation formula for eval extend Cum Polynomial. -/
@[simp] lemma eval_extendCumPolynomial (L : ℕ) (x : RetainedCumCoord L → ℂ)
    (P : MvPolynomial (RetainedCumCoord L) ℂ) :
    MvPolynomial.eval (fun p => extendCumBand L x p.1 p.2)
        (extendCumPolynomial L P) = MvPolynomial.eval x P := by
  rw [extendCumPolynomial, MvPolynomial.eval_rename]
  apply DFunLike.congr_fun _ P
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro p
    have hrL : p.1.1 ≤ L := by omega
    simp [extendCumBand, p.2.1, hrL, p.2.2]

/-- Proves the stated mathematical property of restrict extend Cum Polynomial. -/
lemma restrict_extendCumPolynomial (L : ℕ)
    (P : MvPolynomial (RetainedCumCoord L) ℂ) :
    restrictCumPolynomial L (extendCumPolynomial L P) = P := by
  apply MvPolynomial.funext
  intro x
  calc
    MvPolynomial.eval x
        (restrictCumPolynomial L (extendCumPolynomial L P)) =
        MvPolynomial.eval (restrictCumBand L (extendCumBand L x))
          (restrictCumPolynomial L (extendCumPolynomial L P)) := by
            rw [restrict_extendCumBand]
    _ = MvPolynomial.eval (fun p => extendCumBand L x p.1 p.2)
          (extendCumPolynomial L P) :=
      eval_restrictCumPolynomial_of_band (extendCumBand_mem_band L x) _
    _ = MvPolynomial.eval x P := eval_extendCumPolynomial L x P

/-- On band-supported sets, ambient closure is exactly finite affine closure. -/
theorem mem_zariskiClosure_iff_mem_affineZariskiClosure {L : ℕ}
    {A : Set (CumVec ℂ)} (hA : A ⊆ bandSupportedCumulants L)
    {t : CumVec ℂ} (ht : t ∈ bandSupportedCumulants L) :
    t ∈ zariskiClosure A ↔
      restrictCumBand L t ∈
        affineZariskiClosure (restrictCumBand L '' A) := by
  constructor
  · intro hclose P hP
    change MvPolynomial.eval (restrictCumBand L t) P = 0
    rw [← eval_extendCumPolynomial L (restrictCumBand L t) P]
    rw [extend_restrictCumBand ht]
    apply hclose (extendCumPolynomial L P)
    intro s hs
    calc
      MvPolynomial.eval (fun p => s p.1 p.2) (extendCumPolynomial L P) =
          MvPolynomial.eval
            (fun p => extendCumBand L (restrictCumBand L s) p.1 p.2)
            (extendCumPolynomial L P) := by rw [extend_restrictCumBand (hA hs)]
      _ = MvPolynomial.eval (restrictCumBand L s) P :=
        eval_extendCumPolynomial L (restrictCumBand L s) P
      _ = 0 := by
        simpa [MvPolynomial.aeval_def] using
          hP (restrictCumBand L s) ⟨s, hs, rfl⟩
  · intro hclose P hP
    rw [← eval_restrictCumPolynomial_of_band ht P]
    apply hclose (restrictCumPolynomial L P)
    rintro _ ⟨s, hs, rfl⟩
    simpa [MvPolynomial.aeval_def, eval_restrictCumPolynomial_of_band (hA hs)] using hP s hs

/-- Proves the stated set-containment or membership property for zariski Closure subset band. -/
lemma zariskiClosure_subset_band {L : ℕ} {A : Set (CumVec ℂ)}
    (hA : A ⊆ bandSupportedCumulants L) :
    zariskiClosure A ⊆ bandSupportedCumulants L := by
  intro t ht r a hout
  let P : MvPolynomial (ℕ × ℕ) ℂ := MvPolynomial.X (r, a)
  have hvan : ∀ s ∈ A, MvPolynomial.eval (fun p => s p.1 p.2) P = 0 := by
    intro s hs
    simpa [P] using hA hs r a hout
  simpa [P] using ht P hvan

/-- Proves that the map or coordinate assignment called the restrict Cum Band on band is injective. -/
lemma restrictCumBand_injective_on_band (L : ℕ) :
    Set.InjOn (restrictCumBand L) (bandSupportedCumulants L) := by
  intro s hs t ht heq
  rw [← extend_restrictCumBand hs, ← extend_restrictCumBand ht, heq]

/-- Proves the stated set-containment or membership property for image restrict Cum Band subset iff. -/
lemma image_restrictCumBand_subset_iff {L : ℕ}
    {A B : Set (CumVec ℂ)} (hA : A ⊆ bandSupportedCumulants L)
    (hB : B ⊆ bandSupportedCumulants L) :
    restrictCumBand L '' A ⊆ restrictCumBand L '' B ↔ A ⊆ B := by
  constructor
  · intro h s hs
    obtain ⟨t, ht, heq⟩ := h ⟨s, hs, rfl⟩
    have := restrictCumBand_injective_on_band L (hA hs) (hB ht) heq.symm
    simpa [this] using ht
  · exact Set.image_mono

/-- Proves the stated mathematical property of image restrict Cum Band inj. -/
lemma image_restrictCumBand_inj {L : ℕ}
    {A B : Set (CumVec ℂ)} (hA : A ⊆ bandSupportedCumulants L)
    (hB : B ⊆ bandSupportedCumulants L)
    (h : restrictCumBand L '' A = restrictCumBand L '' B) : A = B := by
  apply Set.Subset.antisymm
  · exact (image_restrictCumBand_subset_iff hA hB).mp h.le
  · exact (image_restrictCumBand_subset_iff hB hA).mp h.ge

/-- Proves the stated mathematical property of image restrict Cum Band union. -/
lemma image_restrictCumBand_union (L : ℕ) (A B : Set (CumVec ℂ)) :
    restrictCumBand L '' (A ∪ B) =
      restrictCumBand L '' A ∪ restrictCumBand L '' B := by
  exact Set.image_union _ _ _

/-- Closed band-supported sets correspond exactly to closed finite affine sets. -/
lemma closed_iff_affineClosed {L : ℕ} {A : Set (CumVec ℂ)}
    (hA : A ⊆ bandSupportedCumulants L) :
    zariskiClosure A = A ↔
      affineZariskiClosure (restrictCumBand L '' A) =
        restrictCumBand L '' A := by
  constructor
  · intro hclosed
    apply Set.Subset.antisymm
    · intro x hx
      have ht : extendCumBand L x ∈ zariskiClosure A :=
        (mem_zariskiClosure_iff_mem_affineZariskiClosure hA
          (extendCumBand_mem_band L x)).mpr (by simpa using hx)
      exact ⟨extendCumBand L x, hclosed ▸ ht, restrict_extendCumBand L x⟩
    · exact affineZariskiClosure_extensive _
  · intro hclosed
    apply Set.Subset.antisymm
    · intro t ht
      have htband := zariskiClosure_subset_band hA ht
      have hfin : restrictCumBand L t ∈
          affineZariskiClosure (restrictCumBand L '' A) :=
        (mem_zariskiClosure_iff_mem_affineZariskiClosure hA htband).mp ht
      rw [hclosed] at hfin
      obtain ⟨s, hs, heq⟩ := hfin
      have hts := restrictCumBand_injective_on_band L htband (hA hs) heq.symm
      simpa [hts] using hs
    · exact subset_zariskiClosure _

/-- Irreducible closed band-supported sets correspond to irreducible closed
sets in the finite retained affine space. -/
theorem irreducibleZariskiClosed_iff_affine {L : ℕ} {A : Set (CumVec ℂ)}
    (hA : A ⊆ bandSupportedCumulants L) :
    IsIrreducibleZariskiClosed A ↔
      IsIrreducibleAffineClosed (restrictCumBand L '' A) := by
  constructor
  · intro h
    refine ⟨(closed_iff_affineClosed hA).mp h.1, h.2.1.image _, ?_⟩
    intro U V hU hV huv
    let U' := extendCumBand L '' U
    let V' := extendCumBand L '' V
    have hUband : U' ⊆ bandSupportedCumulants L := fun _ hx => by
      obtain ⟨x, _, rfl⟩ := hx; exact extendCumBand_mem_band L x
    have hVband : V' ⊆ bandSupportedCumulants L := fun _ hx => by
      obtain ⟨x, _, rfl⟩ := hx; exact extendCumBand_mem_band L x
    have hUclosed : zariskiClosure U' = U' := by
      apply (closed_iff_affineClosed hUband).mpr
      simpa [U', Set.image_image] using hU
    have hVclosed : zariskiClosure V' = V' := by
      apply (closed_iff_affineClosed hVband).mpr
      simpa [V', Set.image_image] using hV
    have hAeq : A = U' ∪ V' := by
      apply image_restrictCumBand_inj hA (Set.union_subset hUband hVband)
      simpa [U', V', image_restrictCumBand_union, Set.image_image] using huv
    rcases h.2.2 U' V' hUclosed hVclosed hAeq with hAU | hAV
    · left
      simpa [U', Set.image_image] using congrArg (fun S => restrictCumBand L '' S) hAU
    · right
      simpa [V', Set.image_image] using congrArg (fun S => restrictCumBand L '' S) hAV
  · intro h
    refine ⟨(closed_iff_affineClosed hA).mpr h.1, ?_, ?_⟩
    · obtain ⟨x, hx⟩ := h.2.1
      obtain ⟨t, ht, _⟩ := hx
      exact ⟨t, ht⟩
    · intro U V hU hV huv
      have hUsub : U ⊆ bandSupportedCumulants L := by
        intro u hu
        exact hA (huv.symm ▸ Or.inl hu)
      have hVsub : V ⊆ bandSupportedCumulants L := by
        intro v hv
        exact hA (huv.symm ▸ Or.inr hv)
      have hi := h.2.2 (restrictCumBand L '' U) (restrictCumBand L '' V)
        ((closed_iff_affineClosed hUsub).mp hU)
        ((closed_iff_affineClosed hVsub).mp hV)
        (by simpa [image_restrictCumBand_union] using
          congrArg (fun S => restrictCumBand L '' S) huv)
      rcases hi with hi | hi
      · exact Or.inl (image_restrictCumBand_inj hA hUsub hi)
      · exact Or.inr (image_restrictCumBand_inj hA hVsub hi)

end

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
