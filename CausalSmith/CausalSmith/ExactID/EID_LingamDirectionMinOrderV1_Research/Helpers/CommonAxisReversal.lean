/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Coordinate reversal of the common-axis height-one problem
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.CommonAxisImageGeometry
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.CoordinateReversalGeometry

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

noncomputable section

/-- Observable coordinate reversal on the finite retained affine space. -/
def reverseRetainedCoordinates {L : ℕ}
    (x : RetainedCumCoord L → ℂ) : RetainedCumCoord L → ℂ :=
  fun p => x (reverseRetainedCumCoord p)

@[simp] lemma reverseRetainedCoordinates_involutive {L : ℕ}
    (x : RetainedCumCoord L → ℂ) :
    reverseRetainedCoordinates (reverseRetainedCoordinates x) = x := by
  funext p
  simp [reverseRetainedCoordinates]

lemma reverseRetainedCoordinates_isPolynomial (L : ℕ) :
    IsPolynomialMap (@reverseRetainedCoordinates L) := by
  intro p
  exact ⟨MvPolynomial.X (reverseRetainedCumCoord p), by
    intro x
    simp [reverseRetainedCoordinates]⟩

/-- Proves the stated mathematical property of restrict Cum Band reverse Cum Coordinates. -/
lemma restrictCumBand_reverseCumCoordinates {L : ℕ} (t : CumVec ℂ) :
    restrictCumBand L (reverseCumCoordinates t) =
      reverseRetainedCoordinates (restrictCumBand L t) := by
  funext p
  simp [restrictCumBand, reverseRetainedCoordinates,
    reverseRetainedCumCoord, reverseCumCoordinates, p.2.2]

/-- Proves the stated mathematical property of reverse Retained Coordinates image image. -/
lemma reverseRetainedCoordinates_image_image {L : ℕ}
    (A : Set (RetainedCumCoord L → ℂ)) :
    reverseRetainedCoordinates '' (reverseRetainedCoordinates '' A) = A := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨reverseRetainedCoordinates x,
      ⟨x, hx, rfl⟩,
      reverseRetainedCoordinates_involutive x⟩

/-- A polynomial involution commutes with affine Zariski closure. -/
lemma polynomialInvolution_image_affineZariskiClosure
    {ι : Type*} {f : (ι → ℂ) → (ι → ℂ)}
    (hf : IsPolynomialMap f) (hinv : Function.LeftInverse f f)
    (A : Set (ι → ℂ)) :
    f '' affineZariskiClosure A = affineZariskiClosure (f '' A) := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    intro P hP
    change MvPolynomial.eval (f x) P = 0
    obtain ⟨Q, hQ⟩ := hf.eval_comp P
    rw [← hQ x]
    apply hx Q
    intro z hz
    have hz' := hP (f z) ⟨z, hz, rfl⟩
    simpa [MvPolynomial.aeval_def, MvPolynomial.eval₂_id, hQ z] using hz'
  · have hclosed : affineZariskiClosure (f '' affineZariskiClosure A) =
        f '' affineZariskiClosure A :=
      polynomial_image_closed_of_retract hf hf hinv
        (affineZariskiClosure_idem A)
    rw [← hclosed]
    exact affineZariskiClosure_mono
      (Set.image_mono (affineZariskiClosure_extensive A))

private lemma axisReverseParameter_map_surjective (m : ℕ) :
    Function.Surjective (axisReverseParameter m) := by
  intro η
  exact ⟨axisReverseParameter m η, axisReverseParameter_involutive m η⟩

/-- Proves the stated mathematical property of reverse Cum Coordinates forward range. -/
lemma reverseCumCoordinates_forward_range (m L : ℕ) :
    reverseCumCoordinates '' Set.range (forwardCumulantMap m L) =
      Set.range (reverseCumulantMap m L) := by
  ext t
  constructor
  · rintro ⟨_, ⟨θ, rfl⟩, rfl⟩
    exact ⟨axisReverseParameter m θ,
      reverseCumulantMap_axisReverseParameter m L θ⟩
  · rintro ⟨η, rfl⟩
    obtain ⟨θ, rfl⟩ := axisReverseParameter_map_surjective m η
    exact ⟨forwardCumulantMap m L θ, ⟨θ, rfl⟩,
      (reverseCumulantMap_axisReverseParameter m L θ).symm⟩

/-- Proves the stated mathematical property of reverse Cum Coordinates common Axis raw. -/
lemma reverseCumCoordinates_commonAxis_raw (m : ℕ) (hm : 1 ≤ m) :
    reverseCumCoordinates ''
        (forwardCumulantMap m (2 * m + 2) '' forwardCommonAxisDivisor m hm) =
      forwardCumulantMap m (2 * m + 2) '' forwardCommonAxisDivisor m hm := by
  let L := 2 * m + 2
  let A := forwardCumulantMap m L '' forwardCommonAxisDivisor m hm
  have hsubset : reverseCumCoordinates '' A ⊆ A := by
    rintro _ ⟨_, ⟨θ, hθ, rfl⟩, rfl⟩
    let η := commonAxisReverseTwin m hm θ
    let θ' := axisReverseParameter m η
    have hηgen : η ∈ genericParameterLocus m L :=
      commonAxisReverseTwin_generic hm hθ
    have hθ'gen : θ' ∈ genericParameterLocus m L :=
      axisReverseParameter_generic hηgen
    have hθ'axis : θ'.2.1 ⟨0, hm⟩ = 0 := by
      simp [θ', axisReverseParameter, η, commonAxisReverseTwin]
    refine ⟨θ', ⟨hθ'gen, hθ'axis⟩, ?_⟩
    have htwin : reverseCumulantMap m L η = forwardCumulantMap m L θ :=
      commonAxisReverseTwin_map_eq hm hθ.2
        (gamma_ne_zero_of_generic hθ.1) (by
          intro i hi
          have hinj := rho_injective_of_generic hθ.1
          intro hz
          have heq : i = ⟨0, hm⟩ := hinj (hz.trans hθ.2.symm)
          exact hi (congrArg Fin.val heq))
    have hrev := reverseCumulantMap_axisReverseParameter m L θ'
    have hparam : axisReverseParameter m θ' = η := by
      simp [θ', axisReverseParameter_involutive]
    rw [hparam] at hrev
    have := congrArg reverseCumCoordinates hrev
    simpa [reverseCumCoordinates_involutive, htwin] using this.symm
  apply Set.Subset.antisymm hsubset
  intro t ht
  have hrt : reverseCumCoordinates t ∈ A :=
    hsubset ⟨t, ht, rfl⟩
  exact ⟨reverseCumCoordinates t, hrt,
    reverseCumCoordinates_involutive t⟩

private lemma restrict_image_reverse {L : ℕ} (A : Set (CumVec ℂ)) :
    reverseRetainedCoordinates '' (restrictCumBand L '' A) =
      restrictCumBand L '' (reverseCumCoordinates '' A) := by
  ext x
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨reverseCumCoordinates t, ⟨t, ht, rfl⟩,
      restrictCumBand_reverseCumCoordinates t⟩
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨restrictCumBand L t, ⟨t, ht, rfl⟩,
      (restrictCumBand_reverseCumCoordinates t).symm⟩

/-- Proves the stated mathematical property of reverse Retained Coordinates forward Variety. -/
lemma reverseRetainedCoordinates_forwardVariety (m : ℕ) :
    reverseRetainedCoordinates ''
        (restrictCumBand (2 * m + 2) ''
          cumulantImageVariety (forwardCumulantMap m (2 * m + 2))) =
      restrictCumBand (2 * m + 2) ''
        cumulantImageVariety (reverseCumulantMap m (2 * m + 2)) := by
  let L := 2 * m + 2
  let Af : Set (CumVec ℂ) := Set.range (forwardCumulantMap m L)
  let Ar : Set (CumVec ℂ) := Set.range (reverseCumulantMap m L)
  have hAf : Af ⊆ bandSupportedCumulants L := by
    rintro _ ⟨θ, rfl⟩
    exact forwardCumulantMap_mem_bandSupportedCumulants m L θ
  have hAr : Ar ⊆ bandSupportedCumulants L := by
    rintro _ ⟨η, rfl⟩
    exact reverseCumulantMap_mem_bandSupportedCumulants m L η
  change reverseRetainedCoordinates ''
      (restrictCumBand L '' zariskiClosure Af) =
    restrictCumBand L '' zariskiClosure Ar
  rw [restrictCumBand_image_zariskiClosure hAf,
    restrictCumBand_image_zariskiClosure hAr,
    polynomialInvolution_image_affineZariskiClosure
      (reverseRetainedCoordinates_isPolynomial L)
      reverseRetainedCoordinates_involutive]
  congr 1
  rw [restrict_image_reverse, reverseCumCoordinates_forward_range]

/-- Proves the stated mathematical property of reverse Retained Coordinates common Axis Closure. -/
lemma reverseRetainedCoordinates_commonAxisClosure (m : ℕ) (hm : 1 ≤ m) :
    reverseRetainedCoordinates ''
        (restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm) =
      restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm := by
  let L := 2 * m + 2
  let A : Set (CumVec ℂ) :=
    forwardCumulantMap m L '' forwardCommonAxisDivisor m hm
  have hA : A ⊆ bandSupportedCumulants L := by
    rintro _ ⟨θ, _, rfl⟩
    exact forwardCumulantMap_mem_bandSupportedCumulants m L θ
  change reverseRetainedCoordinates ''
      (restrictCumBand L '' zariskiClosure A) =
    restrictCumBand L '' zariskiClosure A
  rw [restrictCumBand_image_zariskiClosure hA,
    polynomialInvolution_image_affineZariskiClosure
      (reverseRetainedCoordinates_isPolynomial L)
      reverseRetainedCoordinates_involutive]
  congr 1
  rw [restrict_image_reverse, reverseCumCoordinates_commonAxis_raw]

private lemma image_ssubset_image_of_injective {α β : Type*}
    {f : α → β} (hf : Function.Injective f) {A B : Set α} (hAB : A ⊂ B) :
    f '' A ⊂ f '' B := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨Set.image_mono hAB.le, ?_⟩
  intro heq
  apply hAB.ne
  ext x
  constructor
  · intro hx
    have : f x ∈ f '' B := heq ▸ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hfy⟩ := this
    exact hf hfy.symm ▸ hy
  · intro hx
    have : f x ∈ f '' A := heq.symm ▸ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hfy⟩ := this
    exact hf hfy.symm ▸ hy

/-- Coordinate reversal transfers the reverse no-intermediate statement from
the forward one. -/
theorem reverse_no_intermediate_of_forward (m : ℕ) (hm : 1 ≤ m)
    (hforward : ¬ ∃ Y, IsIrreducibleAffineClosed Y ∧
      restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm ⊂ Y ∧
      Y ⊂ restrictCumBand (2 * m + 2) ''
        cumulantImageVariety (forwardCumulantMap m (2 * m + 2))) :
    ¬ ∃ Y, IsIrreducibleAffineClosed Y ∧
      restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm ⊂ Y ∧
      Y ⊂ restrictCumBand (2 * m + 2) ''
        cumulantImageVariety (reverseCumulantMap m (2 * m + 2)) := by
  rintro ⟨Y, hY, hCY, hYX⟩
  let R := @reverseRetainedCoordinates (2 * m + 2)
  have hRinj : Function.Injective R := by
    intro x y h
    have := congrArg R h
    simpa [R] using this
  apply hforward
  refine ⟨R '' Y, ?_, ?_, ?_⟩
  · exact irreducible_image_polynomial_retract
      (reverseRetainedCoordinates_isPolynomial _) (reverseRetainedCoordinates_isPolynomial _)
      reverseRetainedCoordinates_involutive hY
  · rw [← reverseRetainedCoordinates_commonAxisClosure m hm]
    exact image_ssubset_image_of_injective hRinj hCY
  · have h := image_ssubset_image_of_injective hRinj hYX
    have hvar :
        restrictCumBand (2 * m + 2) ''
            cumulantImageVariety (forwardCumulantMap m (2 * m + 2)) =
          R '' (restrictCumBand (2 * m + 2) ''
            cumulantImageVariety (reverseCumulantMap m (2 * m + 2))) := by
      calc
        _ = R '' (R '' (restrictCumBand (2 * m + 2) ''
              cumulantImageVariety (forwardCumulantMap m (2 * m + 2)))) := by
            symm
            exact reverseRetainedCoordinates_image_image _
        _ = _ := congrArg (fun S => R '' S)
          (reverseRetainedCoordinates_forwardVariety m)
    rw [← hvar] at h
    exact h

end

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
