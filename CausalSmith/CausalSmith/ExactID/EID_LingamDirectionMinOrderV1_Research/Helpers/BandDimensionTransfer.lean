/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Transfer of irreducible chains to retained-band coordinates
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.BandParameterCoordinates

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

noncomputable section

private lemma encodeBandParam_injectiveOn {m L : ℕ} (hL : 2 ≤ L) :
    Set.InjOn (encodeBandParam (L := L)) (bandSupportedParams m L) := by
  intro a ha b hb heq
  rw [← decode_encodeBandParam hL ha, ← decode_encodeBandParam hL hb, heq]

private lemma eq_of_image_eq_of_injOn {α β : Type*} {f : α → β} {S A B : Set α}
    (hf : Set.InjOn f S) (hA : A ⊆ S) (hB : B ⊆ S)
    (h : f '' A = f '' B) : A = B := by
  ext x
  constructor
  · intro hx
    have : f x ∈ f '' B := h ▸ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hfy⟩ := this
    exact hf (hA hx) (hB hy) hfy.symm ▸ hy
  · intro hx
    have : f x ∈ f '' A := h.symm ▸ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hfy⟩ := this
    exact hf (hB hx) (hA hy) hfy.symm ▸ hy

private lemma image_decodeBandParam {m L : ℕ} (hL : 2 ≤ L)
    (W : Set (BandParamCoord m L → ℂ)) :
    (encodeBandParam (L := L)) '' ((decodeBandParam (L := L)) '' W) = W := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simpa [encode_decodeBandParam hL] using hy
  · intro hx
    exact ⟨decodeBandParam x, ⟨x, hx, rfl⟩, encode_decodeBandParam hL x⟩

private lemma decodeBandParam_image {m L : ℕ} (hL : 2 ≤ L)
    {Z : Set (ParamSpace ℂ m)} (hZ : Z ⊆ bandSupportedParams m L) :
    (decodeBandParam (L := L)) '' ((encodeBandParam (L := L)) '' Z) = Z := by
  ext θ
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    simpa [decode_encodeBandParam hL (hZ hs)] using hs
  · intro hθ
    exact ⟨encodeBandParam θ, ⟨θ, hθ, rfl⟩,
      decode_encodeBandParam hL (hZ hθ)⟩

/-- Proves the stated closedness property for encode Band Param closed iff. -/
lemma encodeBandParam_closed_iff {m L : ℕ} (hL : 2 ≤ L)
    {Z : Set (ParamSpace ℂ m)} (hZ : Z ⊆ bandSupportedParams m L) :
    zariskiClosureParamIn L Z = Z ↔
      affineZariskiClosure ((encodeBandParam (L := L)) '' Z) =
        (encodeBandParam (L := L)) '' Z := by
  constructor
  · intro hc
    rw [← encodeBandParam_zariskiClosureParamIn hL hZ, hc]
  · intro hc
    apply eq_of_image_eq_of_injOn (encodeBandParam_injectiveOn hL)
    · intro θ hθ
      exact hθ.1
    · exact hZ
    rw [encodeBandParam_zariskiClosureParamIn hL hZ, hc]

/-- Proves the stated closedness property for decode Band Param closed. -/
lemma decodeBandParam_closed {m L : ℕ} (hL : 2 ≤ L)
    {W : Set (BandParamCoord m L → ℂ)}
    (hW : affineZariskiClosure W = W) :
    zariskiClosureParamIn L ((decodeBandParam (L := L)) '' W) =
      (decodeBandParam (L := L)) '' W := by
  have hs : (decodeBandParam (L := L)) '' W ⊆ bandSupportedParams m L := by
    rintro _ ⟨x, _, rfl⟩
    exact decodeBandParam_supported x
  apply (encodeBandParam_closed_iff hL hs).mpr
  rw [image_decodeBandParam hL, hW]

/-- Irreducibility is unchanged by passage to finite retained-band
coordinates. -/
theorem irreducibleParamIn_iff_irreducibleBand {m L : ℕ} (hL : 2 ≤ L)
    {Z : Set (ParamSpace ℂ m)} (hZ : Z ⊆ bandSupportedParams m L) :
    IsIrreducibleZariskiClosedParamIn L Z ↔
      IsIrreducibleAffineClosed ((encodeBandParam (L := L)) '' Z) := by
  constructor
  · rintro ⟨hclosed, hne, hirr⟩
    refine ⟨(encodeBandParam_closed_iff hL hZ).mp hclosed,
      hne.image _, ?_⟩
    intro A B hA hB hAB
    let A' := (decodeBandParam (L := L)) '' A
    let B' := (decodeBandParam (L := L)) '' B
    have hA' := decodeBandParam_closed hL hA
    have hB' := decodeBandParam_closed hL hB
    have hZAB : Z = A' ∪ B' := by
      rw [← decodeBandParam_image hL hZ, hAB, Set.image_union]
    rcases hirr A' B' hA' hB' hZAB with h | h
    · left
      simpa [h, A', image_decodeBandParam hL]
    · right
      simpa [h, B', image_decodeBandParam hL]
  · rintro ⟨hclosed, hne, hirr⟩
    refine ⟨(encodeBandParam_closed_iff hL hZ).mpr hclosed, ?_, ?_⟩
    · obtain ⟨_, ⟨z, hz, rfl⟩⟩ := hne
      exact ⟨z, hz⟩
    · intro A B hA hB hZAB
      have hAs : A ⊆ bandSupportedParams m L := by
        rw [← hA]
        intro x hx
        exact hx.1
      have hBs : B ⊆ bandSupportedParams m L := by
        rw [← hB]
        intro x hx
        exact hx.1
      have hiA := (encodeBandParam_closed_iff hL hAs).mp hA
      have hiB := (encodeBandParam_closed_iff hL hBs).mp hB
      have hiUnion : (encodeBandParam (L := L)) '' Z =
          (encodeBandParam (L := L)) '' A ∪
            (encodeBandParam (L := L)) '' B := by
        rw [hZAB, Set.image_union]
      rcases hirr _ _ hiA hiB hiUnion with hi | hi
      · left
        exact eq_of_image_eq_of_injOn (encodeBandParam_injectiveOn hL) hZ hAs hi
      · right
        exact eq_of_image_eq_of_injOn (encodeBandParam_injectiveOn hL) hZ hBs hi

private lemma image_strictMono {α β ι : Type*} [Preorder ι]
    (f : α → β) {S : Set α} (hf : Set.InjOn f S)
    {chain : ι → Set α} (hchain : StrictMono chain)
    (hsub : ∀ i, chain i ⊆ S) : StrictMono (fun i => f '' chain i) := by
  intro i j hij
  have hs := hchain hij
  refine Set.ssubset_iff_subset_ne.mpr ⟨Set.image_mono hs.le, ?_⟩
  intro heq
  exact hs.ne (eq_of_image_eq_of_injOn hf (hsub i) (hsub j) heq)

/-- The paper's relative chain dimension is literally the affine chain
dimension of the encoded finite-band set. -/
theorem relativeDimension_iff_bandDimension {m L d : ℕ} (hL : 2 ≤ L)
    {Z : Set (ParamSpace ℂ m)} (hZ : Z ⊆ bandSupportedParams m L) :
    HasRelativeZariskiDimension L d Z ↔
      HasAffineZariskiDimension d ((encodeBandParam (L := L)) '' Z) := by
  let f := encodeBandParam (m := m) (L := L)
  have hf : Set.InjOn f (bandSupportedParams m L) := encodeBandParam_injectiveOn hL
  constructor
  · rintro ⟨⟨chain, hmono, hirr, hsub⟩, hmax⟩
    constructor
    · refine ⟨fun i => f '' chain i,
        image_strictMono f hf hmono (fun i => (hsub i).trans hZ), ?_, ?_⟩
      · intro i
        apply (irreducibleParamIn_iff_irreducibleBand hL
          ((hsub i).trans hZ)).mp
        exact hirr i
      · intro i
        exact Set.image_mono (hsub i)
    · rintro ⟨c, hcmono, hcirr, hcsub⟩
      let c' := fun i => (decodeBandParam (m := m) (L := L)) '' c i
      apply hmax
      refine ⟨c', ?_, ?_, ?_⟩
      · intro i j hij
        have hs := hcmono hij
        exact image_strictMono (decodeBandParam (m := m) (L := L))
          (fun _ _ _ _ h => congrArg (encodeBandParam (L := L)) h |>
            (by simpa [encode_decodeBandParam hL] using ·)) hcmono
          (fun _ => Set.subset_univ _) hij
      · intro i
        have hs : c' i ⊆ bandSupportedParams m L := by
          rintro _ ⟨x, _, rfl⟩
          exact decodeBandParam_supported x
        apply (irreducibleParamIn_iff_irreducibleBand hL hs).mpr
        simpa [c', image_decodeBandParam hL] using hcirr i
      · intro i _ hx
        rcases hx with ⟨x, hxc, rfl⟩
        have := hcsub i hxc
        rcases this with ⟨z, hz, heq⟩
        rw [← heq, decode_encodeBandParam hL (hZ hz)]
        exact hz
  · rintro ⟨⟨chain, hmono, hirr, hsub⟩, hmax⟩
    constructor
    · let c := fun i => (decodeBandParam (m := m) (L := L)) '' chain i
      refine ⟨c, ?_, ?_, ?_⟩
      · exact image_strictMono _ (fun _ _ _ _ heq => by
          simpa [encode_decodeBandParam hL] using
            congrArg (encodeBandParam (L := L)) heq) hmono
          (fun _ => Set.subset_univ _)
      · intro i
        have hs : c i ⊆ bandSupportedParams m L := by
          rintro _ ⟨x, _, rfl⟩
          exact decodeBandParam_supported x
        apply (irreducibleParamIn_iff_irreducibleBand hL hs).mpr
        simpa [c, image_decodeBandParam hL] using hirr i
      · intro i _ hx
        rcases hx with ⟨x, hxc, rfl⟩
        rcases hsub i hxc with ⟨z, hz, heq⟩
        rw [← heq, decode_encodeBandParam hL (hZ hz)]
        exact hz
    · rintro ⟨c, hcmono, hcirr, hcsub⟩
      apply hmax
      refine ⟨fun i => f '' c i,
        image_strictMono f hf hcmono (fun i => (hcsub i).trans hZ), ?_, ?_⟩
      · intro i
        exact (irreducibleParamIn_iff_irreducibleBand hL
          ((hcsub i).trans hZ)).mp (hcirr i)
      · intro i
        exact Set.image_mono (hcsub i)

end

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
