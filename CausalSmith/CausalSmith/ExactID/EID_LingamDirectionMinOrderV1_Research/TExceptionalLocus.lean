/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The exceptional locus has codimension one

The resolved exceptional-locus theorem.  Its codimension is one in both arrow
image varieties, not `m` for `m ≥ 2`; the parameter preimages and the two worked
incidence projections retain their exact full-fiber meanings.
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ExceptionalJacobianMinor

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

/-- **Exceptional-locus codimension one.**  For every `m ≥ 1`, the complex
exceptional closure has codimension exactly one in both arrow-image varieties;
for `m ≥ 2` it therefore does not have the formerly conjectured codimension
`m`.  The two generic parameter preimages are exactly the band-supported generic
points retaining a complete opposite-arrow fiber, and the `m=1` and `m=2`
incidence systems project exactly to `E_m`. -/
-- @node: thm:exceptional-locus-codimension-one
theorem exceptionalLocusCodimensionOne (m : ℕ) (hm : ValidComplexity m) :
    HasCodimensionIn 1 (genericCompatibilityClosure m)
      (cumulantImageVariety (forwardCumulantMap m (2 * m + 2))) ∧
    HasCodimensionIn 1 (genericCompatibilityClosure m)
      (cumulantImageVariety (reverseCumulantMap m (2 * m + 2))) ∧
    (2 ≤ m →
      ¬ HasCodimensionIn m (genericCompatibilityClosure m)
        (cumulantImageVariety (forwardCumulantMap m (2 * m + 2))) ∧
      ¬ HasCodimensionIn m (genericCompatibilityClosure m)
        (cumulantImageVariety (reverseCumulantMap m (2 * m + 2)))) ∧
    (∀ θ : ParamSpace ℂ m,
      θ ∈ genericCompatibilityPreimageRight m ↔
        θ ∈ bandSupportedParams m (2 * m + 2) ∧
        θ ∈ genericParameterLocus m (2 * m + 2) ∧
        (fiberCorrespondence (2 * m + 2) (reverseCumulantMap m (2 * m + 2))
          (forwardCumulantMap m (2 * m + 2) θ)).Nonempty) ∧
    (∀ eta : ParamSpace ℂ m,
      eta ∈ genericCompatibilityPreimageLeft m ↔
        eta ∈ bandSupportedParams m (2 * m + 2) ∧
        eta ∈ genericParameterLocus m (2 * m + 2) ∧
        (fiberCorrespondence (2 * m + 2) (forwardCumulantMap m (2 * m + 2))
          (reverseCumulantMap m (2 * m + 2) eta)).Nonempty) ∧
    (m = 1 → genericFullFiberCompatibility m =
      { t : CumVec ℂ | ∃ p ∈ (workedCompatibilitySystems m).1,
        forwardCumulantMap m (2 * m + 2) p.1 = t }) ∧
    (m = 2 → genericFullFiberCompatibility m =
      { t : CumVec ℂ | ∃ p ∈ (workedCompatibilitySystems m).1,
        forwardCumulantMap m (2 * m + 2) p.1 = t }) := by
  apply exceptionalLocusCodimensionOne_of_commonAxis_certificates m hm
  apply commonAxisFiniteHeightOneCertificates_of_exact_forward_dimensions m hm
  exact ⟨restrict_forwardCommonAxisImageClosure_dimension_expected m hm,
    restrict_forwardCumulantImageVariety_dimension_expected m hm⟩

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
