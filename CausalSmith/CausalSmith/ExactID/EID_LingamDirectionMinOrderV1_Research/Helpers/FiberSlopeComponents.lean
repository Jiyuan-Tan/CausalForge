/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Irreducible subsets of recovered-slope fibers
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.FixedLoadingFiberDimension
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.IrreducibleFiniteRange
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.DirectLatentSwaps
import Mathlib.Logic.Equiv.Fin.Rotate

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

noncomputable section

private lemma loadingSlopeMultiset_eq_map_cons {m : ℕ} (θ : ParamSpace ℂ m) :
    loadingSlopeMultiset θ =
      Finset.univ.val.map (Fin.cons θ.1 θ.2.1 : Fin (m + 1) → ℂ) := by
  have h := congrArg Finset.val (Fin.univ_succAbove m (0 : Fin (m + 1)))
  have hmapped := congrArg
    (Multiset.map (Fin.cons θ.1 θ.2.1 : Fin (m + 1) → ℂ)) h
  simpa [loadingSlopeMultiset, Finset.cons_val, Finset.map_val,
    Multiset.map_map] using hmapped.symm

private lemma slopeTuple_injective_of_recovery {m L : ℕ}
    {θ θ' : ParamSpace ℂ m} (hgen : θ ∈ genericParameterLocus m L)
    (heq : loadingSlopeMultiset θ' = loadingSlopeMultiset θ) :
    Function.Injective (Fin.cons θ'.1 θ'.2.1 : Fin (m + 1) → ℂ) := by
  have htup : Function.Injective
      (Fin.cons θ.1 θ.2.1 : Fin (m + 1) → ℂ) := by
    have hs := forward_slopes_injective_of_generic hgen
    have hfun : (fun j : Fin (m + 1) =>
        (forwardLoading m θ.1 θ.2.1 j.castSucc).2) =
        Fin.cons θ.1 θ.2.1 := by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [forwardLoading]
      · have hi : i.val ≠ m := Nat.ne_of_lt i.isLt
        simp [forwardLoading, hi]
    rwa [hfun] at hs
  have hnodup : (loadingSlopeMultiset θ).Nodup := by
    rw [loadingSlopeMultiset_eq_map_cons]
    exact Fintype.nodup_map_univ_iff_injective.mpr htup
  rw [← heq, loadingSlopeMultiset_eq_map_cons] at hnodup
  exact Fintype.nodup_map_univ_iff_injective.mp hnodup

private lemma forward_actual_slopes_injective_of_recovery {m L : ℕ}
    {θ θ' : ParamSpace ℂ m} (hgen : θ ∈ genericParameterLocus m L)
    (heq : loadingSlopeMultiset θ' = loadingSlopeMultiset θ) :
    Function.Injective (fun j : Fin (m + 1) =>
      (forwardLoading m θ'.1 θ'.2.1 j.castSucc).2) := by
  have htup := slopeTuple_injective_of_recovery hgen heq
  have hfun : (fun j : Fin (m + 1) =>
      (forwardLoading m θ'.1 θ'.2.1 j.castSucc).2) =
      Fin.cons θ'.1 θ'.2.1 := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [forwardLoading]
    · have hi : i.val ≠ m := Nat.ne_of_lt i.isLt
      simp [forwardLoading, hi]
  rw [hfun]
  exact htup

private lemma reverse_actual_slopes_injective_of_recovery {m L : ℕ}
    {η η' : ParamSpace ℂ m} (hgen : η ∈ genericParameterLocus m L)
    (heq : loadingSlopeMultiset η' = loadingSlopeMultiset η) :
    Function.Injective (fun j : Fin (m + 1) =>
      (reverseLoading m η'.1 η'.2.1 j.succ).1) := by
  have htup := slopeTuple_injective_of_recovery hgen heq
  have hfun : (fun j : Fin (m + 1) =>
      (reverseLoading m η'.1 η'.2.1 j.succ).1) =
      Fin.snoc η'.2.1 η'.1 := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [reverseLoading]
    · have hi : i.val ≠ m := Nat.ne_of_lt i.isLt
      simp [reverseLoading, hi]
  rw [hfun, Fin.snoc_eq_cons_rotate]
  exact htup.comp (finRotate (m + 1)).injective

private lemma slopeCoordinate_mem_target {m : ℕ} {θ θ' : ParamSpace ℂ m}
    (heq : loadingSlopeMultiset θ' = loadingSlopeMultiset θ) :
    θ'.1 ∈ (loadingSlopeMultiset θ).toFinset ∧
      ∀ i, θ'.2.1 i ∈ (loadingSlopeMultiset θ).toFinset := by
  rw [← heq]
  constructor
  · simp [loadingSlopeMultiset]
  · intro i
    simp [loadingSlopeMultiset]

/-- Proves the stated set-containment or membership property for forward irreducible subset fixed Loading. -/
theorem forward_irreducible_subset_fixedLoading {m L : ℕ}
    (θ : ParamSpace ℂ m) (hgen : θ ∈ genericParameterLocus m L)
    (hrecover : ∀ θ' ∈ fiberCorrespondence L (forwardCumulantMap m L)
      (forwardCumulantMap m L θ), loadingSlopeMultiset θ' = loadingSlopeMultiset θ)
    {T : Set (BandParamCoord m L → ℂ)} (hT : IsIrreducibleAffineClosed T)
    (hsub : T ⊆ encodeBandParam (L := L) '' fiberCorrespondence L
      (forwardCumulantMap m L) (forwardCumulantMap m L θ)) :
    ∃ θ₀ ∈ fiberCorrespondence L (forwardCumulantMap m L)
        (forwardCumulantMap m L θ),
      Function.Injective (fun j : Fin (m + 1) =>
        (forwardLoading m θ₀.1 θ₀.2.1 j.castSucc).2) ∧
      T ⊆ encodeBandParam (L := L) '' forwardFixedLoadingFiber m L θ₀ := by
  obtain ⟨x₀, hx₀⟩ := hT.2.1
  obtain ⟨θ₀, hθ₀, rfl⟩ := hsub hx₀
  let S := (loadingSlopeMultiset θ).toFinset
  have hrangeDirect : ∀ x ∈ T, x (Sum.inl ()) ∈ S := by
    intro x hx
    obtain ⟨θ', hθ', rfl⟩ := hsub hx
    exact (slopeCoordinate_mem_target (hrecover θ' hθ')).1
  obtain ⟨_, _, hdirect⟩ :=
    irreducible_coordinate_constant_of_finite_range hT (Sum.inl ()) S hrangeDirect
  have hrangeLatent : ∀ i : Fin m, ∀ x ∈ T,
      x (Sum.inr (Sum.inl i)) ∈ S := by
    intro i x hx
    obtain ⟨θ', hθ', rfl⟩ := hsub hx
    exact (slopeCoordinate_mem_target (hrecover θ' hθ')).2 i
  choose zi hziS hlatent using fun i =>
    irreducible_coordinate_constant_of_finite_range hT
      (Sum.inr (Sum.inl i)) S (hrangeLatent i)
  refine ⟨θ₀, hθ₀,
    forward_actual_slopes_injective_of_recovery hgen (hrecover θ₀ hθ₀), ?_⟩
  intro x hx
  obtain ⟨θ', hθ', rfl⟩ := hsub hx
  have hγ : θ'.1 = θ₀.1 := by
    have h1 := hdirect (encodeBandParam θ') hx
    have h0 := hdirect (encodeBandParam θ₀) hx₀
    simpa [encodeBandParam] using h1.trans h0.symm
  have hρ : θ'.2.1 = θ₀.2.1 := by
    funext i
    have h1 := hlatent i (encodeBandParam θ') hx
    have h0 := hlatent i (encodeBandParam θ₀) hx₀
    simpa [encodeBandParam] using h1.trans h0.symm
  have hfib₀ : θ' ∈ fiberCorrespondence L (forwardCumulantMap m L)
      (forwardCumulantMap m L θ₀) := by
    refine ⟨hθ'.1, ?_⟩
    intro r a hr hrL ha
    exact (hθ'.2 r a hr hrL ha).trans (hθ₀.2 r a hr hrL ha).symm
  exact ⟨θ', ⟨hfib₀, hγ, hρ⟩, rfl⟩

/-- Proves the stated set-containment or membership property for reverse irreducible subset fixed Loading. -/
theorem reverse_irreducible_subset_fixedLoading {m L : ℕ}
    (η : ParamSpace ℂ m) (hgen : η ∈ genericParameterLocus m L)
    (hrecover : ∀ η' ∈ fiberCorrespondence L (reverseCumulantMap m L)
      (reverseCumulantMap m L η), loadingSlopeMultiset η' = loadingSlopeMultiset η)
    {T : Set (BandParamCoord m L → ℂ)} (hT : IsIrreducibleAffineClosed T)
    (hsub : T ⊆ encodeBandParam (L := L) '' fiberCorrespondence L
      (reverseCumulantMap m L) (reverseCumulantMap m L η)) :
    ∃ η₀ ∈ fiberCorrespondence L (reverseCumulantMap m L)
        (reverseCumulantMap m L η),
      Function.Injective (fun j : Fin (m + 1) =>
        (reverseLoading m η₀.1 η₀.2.1 j.succ).1) ∧
      T ⊆ encodeBandParam (L := L) '' reverseFixedLoadingFiber m L η₀ := by
  obtain ⟨x₀, hx₀⟩ := hT.2.1
  obtain ⟨η₀, hη₀, rfl⟩ := hsub hx₀
  let S := (loadingSlopeMultiset η).toFinset
  have hrangeDirect : ∀ x ∈ T, x (Sum.inl ()) ∈ S := by
    intro x hx
    obtain ⟨η', hη', rfl⟩ := hsub hx
    exact (slopeCoordinate_mem_target (hrecover η' hη')).1
  obtain ⟨_, _, hdirect⟩ :=
    irreducible_coordinate_constant_of_finite_range hT (Sum.inl ()) S hrangeDirect
  have hrangeLatent : ∀ i : Fin m, ∀ x ∈ T,
      x (Sum.inr (Sum.inl i)) ∈ S := by
    intro i x hx
    obtain ⟨η', hη', rfl⟩ := hsub hx
    exact (slopeCoordinate_mem_target (hrecover η' hη')).2 i
  choose zi hziS hlatent using fun i =>
    irreducible_coordinate_constant_of_finite_range hT
      (Sum.inr (Sum.inl i)) S (hrangeLatent i)
  refine ⟨η₀, hη₀,
    reverse_actual_slopes_injective_of_recovery hgen (hrecover η₀ hη₀), ?_⟩
  intro x hx
  obtain ⟨η', hη', rfl⟩ := hsub hx
  have hδ : η'.1 = η₀.1 := by
    have h1 := hdirect (encodeBandParam η') hx
    have h0 := hdirect (encodeBandParam η₀) hx₀
    simpa [encodeBandParam] using h1.trans h0.symm
  have hσ : η'.2.1 = η₀.2.1 := by
    funext i
    have h1 := hlatent i (encodeBandParam η') hx
    have h0 := hlatent i (encodeBandParam η₀) hx₀
    simpa [encodeBandParam] using h1.trans h0.symm
  have hfib₀ : η' ∈ fiberCorrespondence L (reverseCumulantMap m L)
      (reverseCumulantMap m L η₀) := by
    refine ⟨hη'.1, ?_⟩
    intro r a hr hrL ha
    exact (hη'.2 r a hr hrL ha).trans (hη₀.2 r a hr hrL ha).symm
  exact ⟨η', ⟨hfib₀, hδ, hσ⟩, rfl⟩

end

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
