/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Generic arrow recovery and the same-arrow fiber obstruction

The corrected resolution of the former generic-separation question.  Generic
opposite-arrow separation holds, but the same-arrow fiber is not a single
`G_m`-orbit: direct/latent source-pair swaps give additional components and the
low-order weight kernels give dimension `m(m-1)/2` when `m ≥ 2`.
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.TApolar
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.FiberDimensionDefs
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.FullFiberSlopeRecovery
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.GenericFiberDimension
import Mathlib.Topology.Constructions

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

-- @node: thm:generic-arrow-recovery-and-fiber-obstruction
/-- **Generic arrow recovery and fiber obstruction.**  At `K = 2m+2`, relative
Zariski-open dense loci meet the real feasible regions in nonempty relatively
Euclidean-open sets.  On them the unordered loading directions are recovered and
the full opposite-arrow fiber is empty.  Nevertheless a direct/latent source-pair
swap lies in the same-arrow fiber but outside the admissible `G_m`-orbit; for
`m ≥ 2` the complete same-arrow fiber has exact relative Zariski dimension
`m(m-1)/2` from the independent low-order weight kernels. -/
theorem genericArrowRecoveryAndFiberObstruction (m : ℕ) (hm : ValidComplexity m) :
    ∃ Ur Ul : Set (ParamSpace ℂ m),
      Ur ⊆ genericParameterLocus m (2 * m + 2) ∧
      Ul ⊆ genericParameterLocus m (2 * m + 2) ∧
      IsZariskiOpenParamIn (2 * m + 2) Ur ∧
      IsZariskiDenseParamIn (2 * m + 2) Ur ∧
      IsZariskiOpenParamIn (2 * m + 2) Ul ∧
      IsZariskiDenseParamIn (2 * m + 2) Ul ∧
      (∃ O : Set (ParamSpace ℝ m), IsOpen O ∧
        (O ∩ realFeasibleRegion m (2 * m + 2)).Nonempty ∧
        ∀ θ ∈ O ∩ realFeasibleRegion m (2 * m + 2), complexifyParam θ ∈ Ur) ∧
      (∃ O : Set (ParamSpace ℝ m), IsOpen O ∧
        (O ∩ realFeasibleRegion m (2 * m + 2)).Nonempty ∧
        ∀ eta ∈ O ∩ realFeasibleRegion m (2 * m + 2), complexifyParam eta ∈ Ul) ∧
      (∀ θ ∈ Ur,
        (∀ θ' ∈ fiberCorrespondence (2 * m + 2)
            (forwardCumulantMap m (2 * m + 2))
            (forwardCumulantMap m (2 * m + 2) θ),
          loadingSlopeMultiset θ' = loadingSlopeMultiset θ) ∧
        fiberCorrespondence (2 * m + 2) (reverseCumulantMap m (2 * m + 2))
            (forwardCumulantMap m (2 * m + 2) θ) = ∅ ∧
        (∀ i : Fin m, ∃ θ' ∈ genericParameterLocus m (2 * m + 2),
          IsForwardDirectLatentSwap i θ θ' ∧
          forwardCumulantMap m (2 * m + 2) θ' =
            forwardCumulantMap m (2 * m + 2) θ ∧
          θ' ∉ admissibleOrbit θ) ∧
        (2 ≤ m → HasRelativeZariskiDimension (2 * m + 2) (m * (m - 1) / 2)
          (fiberCorrespondence (2 * m + 2) (forwardCumulantMap m (2 * m + 2))
            (forwardCumulantMap m (2 * m + 2) θ)))) ∧
      (∀ eta ∈ Ul,
        (∀ eta' ∈ fiberCorrespondence (2 * m + 2)
            (reverseCumulantMap m (2 * m + 2))
            (reverseCumulantMap m (2 * m + 2) eta),
          loadingSlopeMultiset eta' = loadingSlopeMultiset eta) ∧
        fiberCorrespondence (2 * m + 2) (forwardCumulantMap m (2 * m + 2))
            (reverseCumulantMap m (2 * m + 2) eta) = ∅ ∧
        (∀ i : Fin m, ∃ eta' ∈ genericParameterLocus m (2 * m + 2),
          IsReverseDirectLatentSwap i eta eta' ∧
          reverseCumulantMap m (2 * m + 2) eta' =
            reverseCumulantMap m (2 * m + 2) eta ∧
          eta' ∉ admissibleOrbit eta) ∧
        (2 ≤ m → HasRelativeZariskiDimension (2 * m + 2) (m * (m - 1) / 2)
          (fiberCorrespondence (2 * m + 2) (reverseCumulantMap m (2 * m + 2))
            (reverseCumulantMap m (2 * m + 2) eta)))) := by
  obtain ⟨Ur, Ul, hUr, hUl, hUro, hUrd, hUlo, hUld, hrealr, hreall,
      hforward, hreverse⟩ := generic_apolar_arrow_recovery m hm
  refine ⟨Ur, Ul, hUr, hUl, hUro, hUrd, hUlo, hUld, hrealr, hreall, ?_, ?_⟩
  · intro θ hθ
    rcases hforward θ hθ with
      ⟨hempty, ⟨Q, hQne, _hQsq, hQroots, hQzero, _hgenericRecovery⟩, hkernelData⟩
    dsimp only at hkernelData
    rcases hkernelData with ⟨_hQ2ne, _hvertical, _hhorizontal, hkernel⟩
    have hrecover : ∀ θ' ∈ fiberCorrespondence (2 * m + 2)
        (forwardCumulantMap m (2 * m + 2))
        (forwardCumulantMap m (2 * m + 2) θ),
        loadingSlopeMultiset θ' = loadingSlopeMultiset θ := by
      intro θ' hθ'
      have heq : forwardCumulantMap m (2 * m + 2) θ' =
          forwardCumulantMap m (2 * m + 2) θ := by
        funext r a
        by_cases hb : 2 ≤ r ∧ r ≤ 2 * m + 2 ∧ a ≤ r
        · exact hθ'.2 r a hb.1 hb.2.1 hb.2.2
        · simp [forwardCumulantMap, hb]
      exact forward_slopes_determined_by_kernel_identity m θ hkernel θ' heq
    have hρ : ∀ i, θ.2.1 i ≠ 0 :=
      latent_slopes_ne_zero_of_root_polynomial hQne hQroots hQzero
    refine ⟨hrecover, hempty, ?_, ?_⟩
    · intro i
      let θ' := forwardDirectLatentSwap i θ
      refine ⟨θ', forwardDirectLatentSwap_generic i θ (hUr hθ) (hρ i),
        forwardDirectLatentSwap_spec i θ, forwardCumulantMap_directLatentSwap i θ, ?_⟩
      exact forwardDirectLatentSwap_not_mem_admissibleOrbit i θ
        (gamma_ne_rho_of_generic (hUr hθ) i)
    · intro hm2
      exact forward_full_fiber_dimension m θ (hUr hθ) hrecover hm2
  · intro η hη
    rcases hreverse η hη with
      ⟨hempty, ⟨Q, hQne, _hQsq, hQroots, hQzero, _hgenericRecovery⟩, hkernelData⟩
    dsimp only at hkernelData
    rcases hkernelData with ⟨_hQ2ne, _hhorizontal, _hvertical, hkernel⟩
    have hrecover : ∀ η' ∈ fiberCorrespondence (2 * m + 2)
        (reverseCumulantMap m (2 * m + 2))
        (reverseCumulantMap m (2 * m + 2) η),
        loadingSlopeMultiset η' = loadingSlopeMultiset η := by
      intro η' hη'
      have heq : reverseCumulantMap m (2 * m + 2) η' =
          reverseCumulantMap m (2 * m + 2) η := by
        funext r a
        by_cases hb : 2 ≤ r ∧ r ≤ 2 * m + 2 ∧ a ≤ r
        · exact hη'.2 r a hb.1 hb.2.1 hb.2.2
        · simp [reverseCumulantMap, hb]
      exact reverse_slopes_determined_by_kernel_identity m η hkernel η' heq
    have hσ : ∀ i, η.2.1 i ≠ 0 :=
      latent_slopes_ne_zero_of_root_polynomial hQne hQroots hQzero
    refine ⟨hrecover, hempty, ?_, ?_⟩
    · intro i
      let η' := reverseDirectLatentSwap i η
      refine ⟨η', reverseDirectLatentSwap_generic i η (hUl hη) (hσ i),
        reverseDirectLatentSwap_spec i η, reverseCumulantMap_directLatentSwap i η, ?_⟩
      exact reverseDirectLatentSwap_not_mem_admissibleOrbit i η
        (gamma_ne_rho_of_generic (hUl hη) i)
    · intro hm2
      exact reverse_full_fiber_dimension m η (hUl hη) hrecover hm2

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
