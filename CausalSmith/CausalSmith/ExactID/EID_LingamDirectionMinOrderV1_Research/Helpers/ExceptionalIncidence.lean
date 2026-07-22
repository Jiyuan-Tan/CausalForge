/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Set-theoretic identities for the exceptional locus

The generic-preimage and worked-incidence parts of the exceptional-locus
theorem follow directly from the retained-band definitions.  Keeping them here
separates those exact identities from the algebraic-geometric codimension
argument.
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Handles

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

/-- Proves the stated set-containment or membership property for forward Cumulant Map mem band Supported Cumulants. -/
lemma forwardCumulantMap_mem_bandSupportedCumulants {R : Type*} [CommRing R]
    (m L : ℕ) (θ : ParamSpace R m) :
    forwardCumulantMap m L θ ∈ bandSupportedCumulants L := by
  intro r a hra
  simp only [forwardCumulantMap]
  rw [if_neg hra]

/-- Proves the stated set-containment or membership property for reverse Cumulant Map mem band Supported Cumulants. -/
lemma reverseCumulantMap_mem_bandSupportedCumulants {R : Type*} [CommRing R]
    (m L : ℕ) (η : ParamSpace R m) :
    reverseCumulantMap m L η ∈ bandSupportedCumulants L := by
  intro r a hra
  simp only [reverseCumulantMap]
  rw [if_neg hra]

/-- Proves the stated set-containment or membership property for mem fiber Correspondence self. -/
lemma mem_fiberCorrespondence_self {R : Type*} [Zero R] {m L : ℕ}
    {Φ : ParamSpace R m → CumVec R} {θ : ParamSpace R m}
    (hθ : θ ∈ bandSupportedParams m L) :
    θ ∈ fiberCorrespondence L Φ (Φ θ) := by
  exact ⟨hθ, fun _ _ _ _ _ => rfl⟩

/-- Proves the stated set-containment or membership property for maps equality of mem fiber Correspondence. -/
lemma maps_eq_of_mem_fiberCorrespondence {R : Type*} [CommRing R]
    {m L : ℕ} {Φ Ψ : ParamSpace R m → CumVec R}
    (hΦ : ∀ θ, Φ θ ∈ bandSupportedCumulants L)
    (hΨ : ∀ η, Ψ η ∈ bandSupportedCumulants L)
    {t : CumVec R} {θ η : ParamSpace R m}
    (hθ : θ ∈ fiberCorrespondence L Φ t)
    (hη : η ∈ fiberCorrespondence L Ψ t) :
    Φ θ = Ψ η := by
  funext r a
  by_cases hra : 2 ≤ r ∧ r ≤ L ∧ a ≤ r
  · exact (hθ.2 r a hra.1 hra.2.1 hra.2.2).trans
      (hη.2 r a hra.1 hra.2.1 hra.2.2).symm
  · rw [hΦ θ r a hra, hΨ η r a hra]

/-- Proves the stated set-containment or membership property for map equality target of mem fiber Correspondence. -/
lemma map_eq_target_of_mem_fiberCorrespondence {R : Type*} [CommRing R]
    {m L : ℕ} {Φ : ParamSpace R m → CumVec R}
    (hΦ : ∀ θ, Φ θ ∈ bandSupportedCumulants L)
    {t : CumVec R} {θ : ParamSpace R m}
    (ht : t ∈ bandSupportedCumulants L)
    (hθ : θ ∈ fiberCorrespondence L Φ t) :
    Φ θ = t := by
  funext r a
  by_cases hra : 2 ≤ r ∧ r ≤ L ∧ a ≤ r
  · exact hθ.2 r a hra.1 hra.2.1 hra.2.2
  · rw [hΦ θ r a hra, ht r a hra]

/-- Proves the stated set-containment or membership property for forward image mem generic Full Fiber Compatibility iff. -/
lemma forward_image_mem_genericFullFiberCompatibility_iff {m : ℕ}
    {θ : ParamSpace ℂ m} (hθ : θ ∈ genericParameterLocus m (2 * m + 2)) :
    forwardCumulantMap m (2 * m + 2) θ ∈ genericFullFiberCompatibility m ↔
      (fiberCorrespondence (2 * m + 2) (reverseCumulantMap m (2 * m + 2))
        (forwardCumulantMap m (2 * m + 2) θ)).Nonempty := by
  let L := 2 * m + 2
  have hself : θ ∈ fiberCorrespondence L (forwardCumulantMap m L)
      (forwardCumulantMap m L θ) :=
    mem_fiberCorrespondence_self (genericParameterLocus_bandSupported hθ)
  constructor
  · rintro ⟨_, hcompat⟩
    rcases hcompat with hcompat | hcompat
    · exact hcompat.2
    · rcases hcompat.1 with ⟨η, hηfib, _⟩
      exact ⟨η, hηfib⟩
  · intro hopp
    refine ⟨forwardCumulantMap_mem_bandSupportedCumulants m L θ, ?_⟩
    exact Or.inl ⟨⟨θ, hself, hθ⟩, hopp⟩

/-- Proves the stated set-containment or membership property for reverse image mem generic Full Fiber Compatibility iff. -/
lemma reverse_image_mem_genericFullFiberCompatibility_iff {m : ℕ}
    {η : ParamSpace ℂ m} (hη : η ∈ genericParameterLocus m (2 * m + 2)) :
    reverseCumulantMap m (2 * m + 2) η ∈ genericFullFiberCompatibility m ↔
      (fiberCorrespondence (2 * m + 2) (forwardCumulantMap m (2 * m + 2))
        (reverseCumulantMap m (2 * m + 2) η)).Nonempty := by
  let L := 2 * m + 2
  have hself : η ∈ fiberCorrespondence L (reverseCumulantMap m L)
      (reverseCumulantMap m L η) :=
    mem_fiberCorrespondence_self (genericParameterLocus_bandSupported hη)
  constructor
  · rintro ⟨_, hcompat⟩
    rcases hcompat with hcompat | hcompat
    · rcases hcompat.1 with ⟨θ, hθfib, _⟩
      exact ⟨θ, hθfib⟩
    · exact hcompat.2
  · intro hopp
    refine ⟨reverseCumulantMap_mem_bandSupportedCumulants m L η, ?_⟩
    exact Or.inr ⟨⟨η, hself, hη⟩, hopp⟩

/-- Proves the stated equality or equivalence for generic Compatibility Preimage Right iff. -/
lemma genericCompatibilityPreimageRight_iff (m : ℕ) (θ : ParamSpace ℂ m) :
    θ ∈ genericCompatibilityPreimageRight m ↔
      θ ∈ bandSupportedParams m (2 * m + 2) ∧
      θ ∈ genericParameterLocus m (2 * m + 2) ∧
      (fiberCorrespondence (2 * m + 2) (reverseCumulantMap m (2 * m + 2))
        (forwardCumulantMap m (2 * m + 2) θ)).Nonempty := by
  rw [genericCompatibilityPreimageRight, genericCompatibilityPreimage]
  constructor
  · rintro ⟨⟨hband, hgen⟩, hmem⟩
    exact ⟨hband, hgen,
      (forward_image_mem_genericFullFiberCompatibility_iff hgen).mp hmem⟩
  · rintro ⟨hband, hgen, hopp⟩
    exact ⟨⟨hband, hgen⟩,
      (forward_image_mem_genericFullFiberCompatibility_iff hgen).mpr hopp⟩

/-- Proves the stated equality or equivalence for generic Compatibility Preimage Left iff. -/
lemma genericCompatibilityPreimageLeft_iff (m : ℕ) (η : ParamSpace ℂ m) :
    η ∈ genericCompatibilityPreimageLeft m ↔
      η ∈ bandSupportedParams m (2 * m + 2) ∧
      η ∈ genericParameterLocus m (2 * m + 2) ∧
      (fiberCorrespondence (2 * m + 2) (forwardCumulantMap m (2 * m + 2))
        (reverseCumulantMap m (2 * m + 2) η)).Nonempty := by
  rw [genericCompatibilityPreimageLeft, genericCompatibilityPreimage]
  constructor
  · rintro ⟨⟨hband, hgen⟩, hmem⟩
    exact ⟨hband, hgen,
      (reverse_image_mem_genericFullFiberCompatibility_iff hgen).mp hmem⟩
  · rintro ⟨hband, hgen, hopp⟩
    exact ⟨⟨hband, hgen⟩,
      (reverse_image_mem_genericFullFiberCompatibility_iff hgen).mpr hopp⟩

/-- Proves the stated equality or equivalence for generic Full Fiber Compatibility equality worked projection. -/
lemma genericFullFiberCompatibility_eq_worked_projection (m : ℕ)
    (hm : m = 1 ∨ m = 2) :
    genericFullFiberCompatibility m =
      {t : CumVec ℂ | ∃ p ∈ (workedCompatibilitySystems m).1,
        forwardCumulantMap m (2 * m + 2) p.1 = t} := by
  let L := 2 * m + 2
  ext t
  constructor
  · rintro ⟨htband, hcompat⟩
    rcases hcompat with ⟨⟨θ, hθfib, hθgen⟩, ⟨η, hηfib⟩⟩ |
        ⟨⟨η, hηfib, hηgen⟩, ⟨θ, hθfib⟩⟩
    · refine ⟨(θ, η), ?_, ?_⟩
      · exact ⟨hm, hθfib.1, hηfib.1,
          maps_eq_of_mem_fiberCorrespondence
            (forwardCumulantMap_mem_bandSupportedCumulants m L)
            (reverseCumulantMap_mem_bandSupportedCumulants m L) hθfib hηfib,
          Or.inl hθgen⟩
      · funext r a
        by_cases hra : 2 ≤ r ∧ r ≤ L ∧ a ≤ r
        · exact hθfib.2 r a hra.1 hra.2.1 hra.2.2
        · exact (forwardCumulantMap_mem_bandSupportedCumulants m L θ r a hra).trans
            (htband r a hra).symm
    · refine ⟨(θ, η), ?_, ?_⟩
      · exact ⟨hm, hθfib.1, hηfib.1,
          maps_eq_of_mem_fiberCorrespondence
            (forwardCumulantMap_mem_bandSupportedCumulants m L)
            (reverseCumulantMap_mem_bandSupportedCumulants m L) hθfib hηfib,
          Or.inr hηgen⟩
      · funext r a
        by_cases hra : 2 ≤ r ∧ r ≤ L ∧ a ≤ r
        · exact hθfib.2 r a hra.1 hra.2.1 hra.2.2
        · exact (forwardCumulantMap_mem_bandSupportedCumulants m L θ r a hra).trans
            (htband r a hra).symm
  · rintro ⟨⟨θ, η⟩, hp, rfl⟩
    rcases hp with ⟨_, hθband, hηband, heq, hgen | hgen⟩
    · refine ⟨forwardCumulantMap_mem_bandSupportedCumulants m L θ, Or.inl ?_⟩
      exact ⟨⟨θ, mem_fiberCorrespondence_self hθband, hgen⟩,
        ⟨η, hηband, fun r a hr hrL ha => by rw [← heq]⟩⟩
    · refine ⟨forwardCumulantMap_mem_bandSupportedCumulants m L θ, Or.inr ?_⟩
      exact ⟨⟨η, ⟨hηband, fun r a hr hrL ha => by rw [← heq]⟩, hgen⟩,
        ⟨θ, mem_fiberCorrespondence_self hθband⟩⟩

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
