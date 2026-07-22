/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Exact dimension of generic same-arrow fibers

For recovered distinct loading directions, the fiber is a finite union of affine
weight-kernel components.  The order-`r` synthesis kernel has dimension
`m+1-r` for `2 ≤ r ≤ m`; their product therefore has dimension
`m(m-1)/2`.
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.FiberSlopeComponents

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

/-- Establishes the stated dimension formula for forward full fiber. -/
theorem forward_full_fiber_dimension (m : ℕ) (θ : ParamSpace ℂ m)
    (hgen : θ ∈ genericParameterLocus m (2 * m + 2))
    (hrecover : ∀ θ' ∈ fiberCorrespondence (2 * m + 2)
      (forwardCumulantMap m (2 * m + 2))
      (forwardCumulantMap m (2 * m + 2) θ),
      loadingSlopeMultiset θ' = loadingSlopeMultiset θ)
    (hm : 2 ≤ m) :
    HasRelativeZariskiDimension (2 * m + 2) (m * (m - 1) / 2)
      (fiberCorrespondence (2 * m + 2) (forwardCumulantMap m (2 * m + 2))
        (forwardCumulantMap m (2 * m + 2) θ)) := by
  let L := 2 * m + 2
  let d := m * (m - 1) / 2
  let Z := fiberCorrespondence L (forwardCumulantMap m L)
    (forwardCumulantMap m L θ)
  have hZband : Z ⊆ bandSupportedParams m L := fun _ h => h.1
  apply (relativeDimension_iff_bandDimension (m := m) (L := L) (d := d)
    (by omega) hZband).2
  have hfixedRel := forward_fixedLoadingFiber_dimension m θ hgen hm
  have hfixedAff := (relativeDimension_iff_bandDimension (m := m) (L := L)
    (d := d) (by omega) forwardFixedLoadingFiber_subset_band).1 hfixedRel
  constructor
  · obtain ⟨chain, hmono, hirr, hsub⟩ := hfixedAff.1
    refine ⟨chain, hmono, hirr, ?_⟩
    intro i
    exact (hsub i).trans (Set.image_mono fun _ h => h.1)
  · rintro ⟨chain, hmono, hirr, hsub⟩
    let top : Fin (d + 2) := Fin.last (d + 1)
    obtain ⟨θ₀, hθ₀, hsθ₀, htop⟩ :=
      forward_irreducible_subset_fixedLoading θ hgen hrecover
        (hirr top) (hsub top)
    have hcomponentRel := forward_fixedLoadingFiber_dimension_of_injective
      m θ₀ hθ₀.1 hsθ₀ hm
    have hcomponentAff := (relativeDimension_iff_bandDimension (m := m) (L := L)
      (d := d) (by omega) forwardFixedLoadingFiber_subset_band).1 hcomponentRel
    apply hcomponentAff.2
    refine ⟨chain, hmono, hirr, ?_⟩
    intro i
    exact (hmono.monotone (Fin.le_last i)).trans htop

/-- Establishes the stated dimension formula for reverse full fiber. -/
theorem reverse_full_fiber_dimension (m : ℕ) (η : ParamSpace ℂ m)
    (hgen : η ∈ genericParameterLocus m (2 * m + 2))
    (hrecover : ∀ η' ∈ fiberCorrespondence (2 * m + 2)
      (reverseCumulantMap m (2 * m + 2))
      (reverseCumulantMap m (2 * m + 2) η),
      loadingSlopeMultiset η' = loadingSlopeMultiset η)
    (hm : 2 ≤ m) :
    HasRelativeZariskiDimension (2 * m + 2) (m * (m - 1) / 2)
      (fiberCorrespondence (2 * m + 2) (reverseCumulantMap m (2 * m + 2))
        (reverseCumulantMap m (2 * m + 2) η)) := by
  let L := 2 * m + 2
  let d := m * (m - 1) / 2
  let Z := fiberCorrespondence L (reverseCumulantMap m L)
    (reverseCumulantMap m L η)
  have hZband : Z ⊆ bandSupportedParams m L := fun _ h => h.1
  apply (relativeDimension_iff_bandDimension (m := m) (L := L) (d := d)
    (by omega) hZband).2
  have hfixedRel := reverse_fixedLoadingFiber_dimension m η hgen hm
  have hfixedAff := (relativeDimension_iff_bandDimension (m := m) (L := L)
    (d := d) (by omega) reverseFixedLoadingFiber_subset_band).1 hfixedRel
  constructor
  · obtain ⟨chain, hmono, hirr, hsub⟩ := hfixedAff.1
    refine ⟨chain, hmono, hirr, ?_⟩
    intro i
    exact (hsub i).trans (Set.image_mono fun _ h => h.1)
  · rintro ⟨chain, hmono, hirr, hsub⟩
    let top : Fin (d + 2) := Fin.last (d + 1)
    obtain ⟨η₀, hη₀, hsη₀, htop⟩ :=
      reverse_irreducible_subset_fixedLoading η hgen hrecover
        (hirr top) (hsub top)
    have hcomponentRel := reverse_fixedLoadingFiber_dimension_of_injective
      m η₀ hη₀.1 hsη₀ hm
    have hcomponentAff := (relativeDimension_iff_bandDimension (m := m) (L := L)
      (d := d) (by omega) reverseFixedLoadingFiber_subset_band).1 hcomponentRel
    apply hcomponentAff.2
    refine ⟨chain, hmono, hirr, ?_⟩
    intro i
    exact (hmono.monotone (Fin.le_last i)).trans htop

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
