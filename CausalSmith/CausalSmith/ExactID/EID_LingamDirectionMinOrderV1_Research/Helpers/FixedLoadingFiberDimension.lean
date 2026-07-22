/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Exact dimension of a fixed-loading fiber
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.AffineSubspaceDimension
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.BandDimensionTransfer
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.LoadingWeightKernelDimension

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

noncomputable section

/-- The part of a forward fiber with the ordered loading coordinates fixed. -/
def forwardFixedLoadingFiber (m L : ℕ) (θ : ParamSpace ℂ m) :
    Set (ParamSpace ℂ m) :=
  { θ' | θ' ∈ fiberCorrespondence L (forwardCumulantMap m L)
      (forwardCumulantMap m L θ) ∧ θ'.1 = θ.1 ∧ θ'.2.1 = θ.2.1 }

/-- The part of a reverse fiber with the ordered loading coordinates fixed. -/
def reverseFixedLoadingFiber (m L : ℕ) (η : ParamSpace ℂ m) :
    Set (ParamSpace ℂ m) :=
  { η' | η' ∈ fiberCorrespondence L (reverseCumulantMap m L)
      (reverseCumulantMap m L η) ∧ η'.1 = η.1 ∧ η'.2.1 = η.2.1 }

lemma forwardFixedLoadingFiber_subset_band {m L : ℕ} {θ : ParamSpace ℂ m} :
    forwardFixedLoadingFiber m L θ ⊆ bandSupportedParams m L :=
  fun _ h => h.1.1

lemma reverseFixedLoadingFiber_subset_band {m L : ℕ} {η : ParamSpace ℂ m} :
    reverseFixedLoadingFiber m L η ⊆ bandSupportedParams m L :=
  fun _ h => h.1.1

private lemma forward_weight_difference (m L : ℕ) (hL : 2 ≤ L)
    (θ θ' : ParamSpace ℂ m) (hγ : θ'.1 = θ.1) (hρ : θ'.2.1 = θ.2.1) :
    encodeBandParam (L := L) θ' - encodeBandParam (L := L) θ ∈
        loadingBandWeightKernel m L (forwardLoading m θ.1 θ.2.1) ↔
      ∀ r a, 2 ≤ r → r ≤ L → a ≤ r →
        forwardCumulantMap m L θ' r a = forwardCumulantMap m L θ r a := by
  have hload : forwardLoading m θ'.1 θ'.2.1 =
      forwardLoading m θ.1 θ.2.1 := by rw [hγ, hρ]
  constructor
  · intro hmem r a hr hrL ha
    have hklt : r - 2 < L - 1 := by omega
    let k : Fin (L - 1) := ⟨r - 2, hklt⟩
    have hak : a < k.val + 2 + 1 := by
      dsimp [k]
      omega
    have hk := congrFun (hmem.2.2 k) ⟨a, hak⟩
    simp only [loadingOrderSynthesis, Pi.sub_apply, encodeBandParam] at hk
    have hrback : r - 2 + 2 = r := Nat.sub_add_cancel hr
    simp only [forwardCumulantMap, hr, hrL, ha, and_self, hload]
    rw [← sub_eq_zero]
    simpa [k, hrback, sub_mul, Finset.sum_sub_distrib] using hk
  · intro heq
    refine ⟨by simpa [encodeBandParam, hγ],
      fun i => by simpa [encodeBandParam, hρ], ?_⟩
    intro k
    funext a
    have he := heq (k.val + 2) a.val (by omega) (by omega) (by omega)
    rw [← sub_eq_zero] at he
    simp only [forwardCumulantMap, show 2 ≤ k.val + 2 by omega,
      show k.val + 2 ≤ L by omega, show a.val ≤ k.val + 2 by omega,
      and_self, hload] at he
    simpa [loadingOrderSynthesis, encodeBandParam, sub_mul,
      Finset.sum_sub_distrib] using he

private lemma reverse_weight_difference (m L : ℕ) (hL : 2 ≤ L)
    (η η' : ParamSpace ℂ m) (hδ : η'.1 = η.1) (hσ : η'.2.1 = η.2.1) :
    encodeBandParam (L := L) η' - encodeBandParam (L := L) η ∈
        loadingBandWeightKernel m L (reverseLoading m η.1 η.2.1) ↔
      ∀ r a, 2 ≤ r → r ≤ L → a ≤ r →
        reverseCumulantMap m L η' r a = reverseCumulantMap m L η r a := by
  have hload : reverseLoading m η'.1 η'.2.1 =
      reverseLoading m η.1 η.2.1 := by rw [hδ, hσ]
  constructor
  · intro hmem r a hr hrL ha
    have hklt : r - 2 < L - 1 := by omega
    let k : Fin (L - 1) := ⟨r - 2, hklt⟩
    have hak : a < k.val + 2 + 1 := by
      dsimp [k]
      omega
    have hk := congrFun (hmem.2.2 k) ⟨a, hak⟩
    simp only [loadingOrderSynthesis, Pi.sub_apply, encodeBandParam] at hk
    have hrback : r - 2 + 2 = r := Nat.sub_add_cancel hr
    simp only [reverseCumulantMap, hr, hrL, ha, and_self, hload]
    rw [← sub_eq_zero]
    simpa [k, hrback, sub_mul, Finset.sum_sub_distrib] using hk
  · intro heq
    refine ⟨by simpa [encodeBandParam, hδ],
      fun i => by simpa [encodeBandParam, hσ], ?_⟩
    intro k
    funext a
    have he := heq (k.val + 2) a.val (by omega) (by omega) (by omega)
    rw [← sub_eq_zero] at he
    simp only [reverseCumulantMap, show 2 ≤ k.val + 2 by omega,
      show k.val + 2 ≤ L by omega, show a.val ≤ k.val + 2 by omega,
      and_self, hload] at he
    simpa [loadingOrderSynthesis, encodeBandParam, sub_mul,
      Finset.sum_sub_distrib] using he

private theorem encode_forwardFixedLoadingFiber (m L : ℕ) (hL : 2 ≤ L)
    (θ : ParamSpace ℂ m) (hθ : θ ∈ bandSupportedParams m L) :
    encodeBandParam (L := L) '' forwardFixedLoadingFiber m L θ =
      {x | x - encodeBandParam (L := L) θ ∈
        loadingBandWeightKernel m L (forwardLoading m θ.1 θ.2.1)} := by
  ext x
  constructor
  · rintro ⟨θ', ⟨hfib, hγ, hρ⟩, rfl⟩
    exact (forward_weight_difference m L hL θ θ' hγ hρ).2 hfib.2
  · intro hx
    let θ' := decodeBandParam (m := m) (L := L) x
    have henc : encodeBandParam (L := L) θ' = x := encode_decodeBandParam hL x
    have hmem : encodeBandParam (L := L) θ' - encodeBandParam (L := L) θ ∈
        loadingBandWeightKernel m L (forwardLoading m θ.1 θ.2.1) := by
      rwa [henc]
    have hγ : θ'.1 = θ.1 := by
      have := hmem.1
      simpa [θ', decodeBandParam, encodeBandParam] using sub_eq_zero.mp this
    have hρ : θ'.2.1 = θ.2.1 := by
      funext i
      have := hmem.2.1 i
      simpa [θ', decodeBandParam, encodeBandParam] using sub_eq_zero.mp this
    refine ⟨θ', ⟨⟨decodeBandParam_supported x,
      (forward_weight_difference m L hL θ θ' hγ hρ).1 hmem⟩, hγ, hρ⟩, henc⟩

private theorem encode_reverseFixedLoadingFiber (m L : ℕ) (hL : 2 ≤ L)
    (η : ParamSpace ℂ m) (hη : η ∈ bandSupportedParams m L) :
    encodeBandParam (L := L) '' reverseFixedLoadingFiber m L η =
      {x | x - encodeBandParam (L := L) η ∈
        loadingBandWeightKernel m L (reverseLoading m η.1 η.2.1)} := by
  ext x
  constructor
  · rintro ⟨η', ⟨hfib, hδ, hσ⟩, rfl⟩
    exact (reverse_weight_difference m L hL η η' hδ hσ).2 hfib.2
  · intro hx
    let η' := decodeBandParam (m := m) (L := L) x
    have henc : encodeBandParam (L := L) η' = x := encode_decodeBandParam hL x
    have hmem : encodeBandParam (L := L) η' - encodeBandParam (L := L) η ∈
        loadingBandWeightKernel m L (reverseLoading m η.1 η.2.1) := by
      rwa [henc]
    have hδ : η'.1 = η.1 := by
      have := hmem.1
      simpa [η', decodeBandParam, encodeBandParam] using sub_eq_zero.mp this
    have hσ : η'.2.1 = η.2.1 := by
      funext i
      have := hmem.2.1 i
      simpa [η', decodeBandParam, encodeBandParam] using sub_eq_zero.mp this
    refine ⟨η', ⟨⟨decodeBandParam_supported x,
      (reverse_weight_difference m L hL η η' hδ hσ).1 hmem⟩, hδ, hσ⟩, henc⟩

/-- Proves that the map or coordinate assignment called the forward fixed Loading Fiber dimension of is injective. -/
theorem forward_fixedLoadingFiber_dimension_of_injective (m : ℕ)
    (θ : ParamSpace ℂ m) (hband : θ ∈ bandSupportedParams m (2 * m + 2))
    (hs : Function.Injective (fun j : Fin (m + 1) =>
      (forwardLoading m θ.1 θ.2.1 j.castSucc).2)) (hm : 2 ≤ m) :
    HasRelativeZariskiDimension (2 * m + 2) (m * (m - 1) / 2)
      (forwardFixedLoadingFiber m (2 * m + 2) θ) := by
  apply (relativeDimension_iff_bandDimension (by omega)
    forwardFixedLoadingFiber_subset_band).2
  rw [encode_forwardFixedLoadingFiber m (2 * m + 2) (by omega) θ hband]
  exact affineSubspace_hasAffineZariskiDimension _ _ _
    (forward_loadingBandWeightKernel_finrank_of_injective m θ hs hm)

/-- Proves that the map or coordinate assignment called the reverse fixed Loading Fiber dimension of is injective. -/
theorem reverse_fixedLoadingFiber_dimension_of_injective (m : ℕ)
    (η : ParamSpace ℂ m) (hband : η ∈ bandSupportedParams m (2 * m + 2))
    (hs : Function.Injective (fun j : Fin (m + 1) =>
      (reverseLoading m η.1 η.2.1 j.succ).1)) (hm : 2 ≤ m) :
    HasRelativeZariskiDimension (2 * m + 2) (m * (m - 1) / 2)
      (reverseFixedLoadingFiber m (2 * m + 2) η) := by
  apply (relativeDimension_iff_bandDimension (by omega)
    reverseFixedLoadingFiber_subset_band).2
  rw [encode_reverseFixedLoadingFiber m (2 * m + 2) (by omega) η hband]
  exact affineSubspace_hasAffineZariskiDimension _ _ _
    (reverse_loadingBandWeightKernel_finrank_of_injective m η hs hm)

/-- Establishes the stated dimension formula for forward fixed Loading Fiber. -/
theorem forward_fixedLoadingFiber_dimension (m : ℕ) (θ : ParamSpace ℂ m)
    (hgen : θ ∈ genericParameterLocus m (2 * m + 2)) (hm : 2 ≤ m) :
    HasRelativeZariskiDimension (2 * m + 2) (m * (m - 1) / 2)
      (forwardFixedLoadingFiber m (2 * m + 2) θ) :=
  forward_fixedLoadingFiber_dimension_of_injective m θ hgen.1
    (forward_slopes_injective_of_generic hgen) hm

/-- Establishes the stated dimension formula for reverse fixed Loading Fiber. -/
theorem reverse_fixedLoadingFiber_dimension (m : ℕ) (η : ParamSpace ℂ m)
    (hgen : η ∈ genericParameterLocus m (2 * m + 2)) (hm : 2 ≤ m) :
    HasRelativeZariskiDimension (2 * m + 2) (m * (m - 1) / 2)
      (reverseFixedLoadingFiber m (2 * m + 2) η) :=
  reverse_fixedLoadingFiber_dimension_of_injective m η hgen.1
    (reverse_slopes_injective_of_generic hgen) hm

end

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
