/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Principal equations through the common-axis image
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.CommonAxisTwin
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.CoordinateReversalGeometry

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

noncomputable section

private abbrev finiteCommonAxisImage (m : ℕ) (hm : 1 ≤ m) :=
  restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm

private abbrev finiteForwardVariety (m : ℕ) :=
  restrictCumBand (2 * m + 2) ''
    cumulantImageVariety (forwardCumulantMap m (2 * m + 2))

private abbrev finiteReverseVariety (m : ℕ) :=
  restrictCumBand (2 * m + 2) ''
    cumulantImageVariety (reverseCumulantMap m (2 * m + 2))

/-- The horizontal contraction minor is an actual equation of the finite
common-axis image closure. -/
lemma horizontalContractionMinor_mem_commonAxis_vanishingIdeal
    (m : ℕ) (hm : 1 ≤ m) :
    horizontalContractionMinorPolynomial m ∈
      MvPolynomial.vanishingIdeal ℂ (finiteCommonAxisImage m hm) := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := hx
  exact forwardCommonAxisImageClosure_horizontalMinor_vanishes hm ht

/-- The same equation is nontrivial modulo the forward arrow-image ideal. -/
lemma horizontalContractionMinor_not_mem_forward_vanishingIdeal
    (m : ℕ) (hm : 1 ≤ m) :
    horizontalContractionMinorPolynomial m ∉
      MvPolynomial.vanishingIdeal ℂ (finiteForwardVariety m) := by
  intro hmem
  let theta := forwardContractionMinorWitnessParameter m
  let t := forwardCumulantMap m (2 * m + 2) theta
  have ht : restrictCumBand (2 * m + 2) t ∈ finiteForwardVariety m :=
    ⟨t, subset_zariskiClosure _ ⟨theta, rfl⟩, rfl⟩
  exact (horizontalContractionMinorPolynomial_forwardWitness_ne_zero m hm)
    (hmem _ ht)

/-- Since the common-axis family lies in the exceptional locus and hence in
the forward variety, the coordinate-reversed vertical minor is its second
explicit principal equation. -/
lemma verticalContractionMinor_mem_commonAxis_vanishingIdeal
    (m : ℕ) (hm : 1 ≤ m) :
    verticalContractionMinorPolynomial m ∈
      MvPolynomial.vanishingIdeal ℂ (finiteCommonAxisImage m hm) := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := hx
  apply verticalContractionMinorPolynomial_forwardVariety_vanishes m
  exact genericCompatibilityClosure_subset_forwardVariety m
    (forwardCommonAxisImageClosure_subset_exceptional hm ht)

/-- The vertical equation is nontrivial modulo the reverse arrow-image ideal,
witnessed by the coordinate reversal of the forward block-Vandermonde point. -/
lemma verticalContractionMinor_not_mem_reverse_vanishingIdeal
    (m : ℕ) (hm : 1 ≤ m) :
    verticalContractionMinorPolynomial m ∉
      MvPolynomial.vanishingIdeal ℂ (finiteReverseVariety m) := by
  intro hmem
  let eta := axisReverseParameter m (forwardContractionMinorWitnessParameter m)
  let t := reverseCumulantMap m (2 * m + 2) eta
  have ht : restrictCumBand (2 * m + 2) t ∈ finiteReverseVariety m :=
    ⟨t, subset_zariskiClosure _ ⟨eta, rfl⟩, rfl⟩
  exact (verticalContractionMinorPolynomial_reverseWitness_ne_zero m hm)
    (hmem _ ht)

end

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
