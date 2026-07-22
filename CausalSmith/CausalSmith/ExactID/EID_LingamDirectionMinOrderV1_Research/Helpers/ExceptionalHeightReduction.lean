/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Finite height-one reduction for the exceptional locus
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ArrowPolynomialGeometry
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.CommonAxisPrincipalEquations
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.CommonAxisImageGeometry
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.CommonAxisReversal
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.PrincipalHeightOne

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

noncomputable section

/-- Proves the stated set-containment or membership property for generic Compatibility Closure subset band. -/
lemma genericCompatibilityClosure_subset_band (m : ℕ) :
    genericCompatibilityClosure m ⊆ bandSupportedCumulants (2 * m + 2) := by
  apply zariskiClosure_subset_band
  intro t ht
  exact ht.1

/-- Proves the stated set-containment or membership property for forward Cumulant Image Variety subset band. -/
lemma forwardCumulantImageVariety_subset_band (m L : ℕ) :
    cumulantImageVariety (forwardCumulantMap m L) ⊆
      bandSupportedCumulants L := by
  apply zariskiClosure_subset_band
  rintro _ ⟨θ, rfl⟩
  exact forwardCumulantMap_mem_bandSupportedCumulants m L θ

/-- Proves the stated set-containment or membership property for reverse Cumulant Image Variety subset band. -/
lemma reverseCumulantImageVariety_subset_band (m L : ℕ) :
    cumulantImageVariety (reverseCumulantMap m L) ⊆
      bandSupportedCumulants L := by
  apply zariskiClosure_subset_band
  rintro _ ⟨η, rfl⟩
  exact reverseCumulantMap_mem_bandSupportedCumulants m L η

/-- The exceptional closure is proper in the forward arrow variety.  The
separating equation is the explicit observable horizontal contraction minor:
it vanishes on the reverse variety, while the block-Vandermonde forward witness
has nonzero value. -/
lemma genericCompatibilityClosure_ne_forwardVariety (m : ℕ) (hm : 1 ≤ m) :
    genericCompatibilityClosure m ≠
      cumulantImageVariety (forwardCumulantMap m (2 * m + 2)) := by
  intro heq
  let theta := forwardContractionMinorWitnessParameter m
  let t := forwardCumulantMap m (2 * m + 2) theta
  have htForward : t ∈
      cumulantImageVariety (forwardCumulantMap m (2 * m + 2)) :=
    subset_zariskiClosure _ ⟨theta, rfl⟩
  have htExceptional : t ∈ genericCompatibilityClosure m := by
    rw [heq]
    exact htForward
  have htReverse : t ∈
      cumulantImageVariety (reverseCumulantMap m (2 * m + 2)) :=
    genericCompatibilityClosure_subset_reverseVariety m htExceptional
  exact (horizontalContractionMinorPolynomial_forwardWitness_ne_zero m hm)
    (horizontalContractionMinorPolynomial_reverseVariety_vanishes m htReverse)

/-- Proves the stated mathematical property of restrict generic Compatibility Closure ne forward Variety. -/
lemma restrict_genericCompatibilityClosure_ne_forwardVariety
    (m : ℕ) (hm : 1 ≤ m) :
    restrictCumBand (2 * m + 2) '' genericCompatibilityClosure m ≠
      restrictCumBand (2 * m + 2) ''
        cumulantImageVariety (forwardCumulantMap m (2 * m + 2)) := by
  intro heq
  apply genericCompatibilityClosure_ne_forwardVariety m hm
  exact image_restrictCumBand_inj
    (genericCompatibilityClosure_subset_band m)
    (forwardCumulantImageVariety_subset_band m (2 * m + 2)) heq

/-- The coordinate-reversed observable minor gives the symmetric properness
statement in the reverse ambient arrow variety. -/
lemma genericCompatibilityClosure_ne_reverseVariety (m : ℕ) (hm : 1 ≤ m) :
    genericCompatibilityClosure m ≠
      cumulantImageVariety (reverseCumulantMap m (2 * m + 2)) := by
  intro heq
  let eta := axisReverseParameter m (forwardContractionMinorWitnessParameter m)
  let t := reverseCumulantMap m (2 * m + 2) eta
  have htReverse : t ∈
      cumulantImageVariety (reverseCumulantMap m (2 * m + 2)) :=
    subset_zariskiClosure _ ⟨eta, rfl⟩
  have htExceptional : t ∈ genericCompatibilityClosure m := by
    rw [heq]
    exact htReverse
  have htForward : t ∈
      cumulantImageVariety (forwardCumulantMap m (2 * m + 2)) :=
    genericCompatibilityClosure_subset_forwardVariety m htExceptional
  exact (verticalContractionMinorPolynomial_reverseWitness_ne_zero m hm)
    (verticalContractionMinorPolynomial_forwardVariety_vanishes m htForward)

/-- Proves the stated mathematical property of restrict generic Compatibility Closure ne reverse Variety. -/
lemma restrict_genericCompatibilityClosure_ne_reverseVariety
    (m : ℕ) (hm : 1 ≤ m) :
    restrictCumBand (2 * m + 2) '' genericCompatibilityClosure m ≠
      restrictCumBand (2 * m + 2) ''
        cumulantImageVariety (reverseCumulantMap m (2 * m + 2)) := by
  intro heq
  apply genericCompatibilityClosure_ne_reverseVariety m hm
  exact image_restrictCumBand_inj
    (genericCompatibilityClosure_subset_band m)
    (reverseCumulantImageVariety_subset_band m (2 * m + 2)) heq

/-- The exact finite certificate still required for one arrow: properness of
the exceptional closure and one of its affine irreducible components being a
minimal prime over a single observable equation in the arrow coordinate ring.
-/
def ExceptionalFiniteHeightOneCertificate (m : ℕ)
    (D X : Set (CumVec ℂ)) : Prop :=
  let L := 2 * m + 2
  let Zf := restrictCumBand L '' genericCompatibilityClosure m
  let Df := restrictCumBand L '' D
  let Xf := restrictCumBand L '' X
  Zf ≠ Xf ∧
    ∃ P : MvPolynomial (RetainedCumCoord L) ℂ,
        IsIrreducibleAffineComponent Df Zf ∧
        MvPolynomial.vanishingIdeal ℂ Df ∈
          (MvPolynomial.vanishingIdeal ℂ Xf ⊔ Ideal.span {P}).minimalPrimes

/-- The model-specific specialization demanded by the D0 proof: the component
is the closure of the explicit common-axis opposite-arrow twin family. -/
def CommonAxisFiniteHeightOneCertificates (m : ℕ) (hm : 1 ≤ m) : Prop :=
  ExceptionalFiniteHeightOneCertificate m (forwardCommonAxisImageClosure m hm)
      (cumulantImageVariety (forwardCumulantMap m (2 * m + 2))) ∧
    ExceptionalFiniteHeightOneCertificate m (forwardCommonAxisImageClosure m hm)
      (cumulantImageVariety (reverseCumulantMap m (2 * m + 2)))

/-- For the forward ambient, observable-minor properness is compiled; only the
common-axis component and its principal minimal-prime certificate remain. -/
theorem forwardExceptionalFiniteHeightOneCertificate_of_commonAxis_principal
    (m : ℕ) (hm : 1 ≤ m)
    (P : MvPolynomial (RetainedCumCoord (2 * m + 2)) ℂ)
    (hcomponent : IsIrreducibleAffineComponent
      (restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm)
      (restrictCumBand (2 * m + 2) '' genericCompatibilityClosure m))
    (hmin : MvPolynomial.vanishingIdeal ℂ
        (restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm) ∈
      (MvPolynomial.vanishingIdeal ℂ
          (restrictCumBand (2 * m + 2) ''
            cumulantImageVariety (forwardCumulantMap m (2 * m + 2))) ⊔
        Ideal.span {P}).minimalPrimes) :
    ExceptionalFiniteHeightOneCertificate m
      (forwardCommonAxisImageClosure m hm)
      (cumulantImageVariety (forwardCumulantMap m (2 * m + 2))) := by
  exact ⟨restrict_genericCompatibilityClosure_ne_forwardVariety m hm,
    P, hcomponent, hmin⟩

/-- Reverse-ambient assembly using the coordinate-reversed principal equation. -/
theorem reverseExceptionalFiniteHeightOneCertificate_of_commonAxis_principal
    (m : ℕ) (hm : 1 ≤ m)
    (P : MvPolynomial (RetainedCumCoord (2 * m + 2)) ℂ)
    (hcomponent : IsIrreducibleAffineComponent
      (restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm)
      (restrictCumBand (2 * m + 2) '' genericCompatibilityClosure m))
    (hmin : MvPolynomial.vanishingIdeal ℂ
        (restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm) ∈
      (MvPolynomial.vanishingIdeal ℂ
          (restrictCumBand (2 * m + 2) ''
            cumulantImageVariety (reverseCumulantMap m (2 * m + 2))) ⊔
        Ideal.span {P}).minimalPrimes) :
    ExceptionalFiniteHeightOneCertificate m
      (forwardCommonAxisImageClosure m hm)
      (cumulantImageVariety (reverseCumulantMap m (2 * m + 2))) := by
  exact ⟨restrict_genericCompatibilityClosure_ne_reverseVariety m hm,
    P, hcomponent, hmin⟩

/-- The exact residual after both observable properness arguments: one common
irreducible-component proof and the two explicit principal minimal-prime
certificates. -/
theorem commonAxisFiniteHeightOneCertificates_of_principal
    (m : ℕ) (hm : 1 ≤ m)
    (hcomponent : IsIrreducibleAffineComponent
      (restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm)
      (restrictCumBand (2 * m + 2) '' genericCompatibilityClosure m))
    (hforward : MvPolynomial.vanishingIdeal ℂ
        (restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm) ∈
      (MvPolynomial.vanishingIdeal ℂ
          (restrictCumBand (2 * m + 2) ''
            cumulantImageVariety (forwardCumulantMap m (2 * m + 2))) ⊔
        Ideal.span {horizontalContractionMinorPolynomial m}).minimalPrimes)
    (hreverse : MvPolynomial.vanishingIdeal ℂ
        (restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm) ∈
      (MvPolynomial.vanishingIdeal ℂ
          (restrictCumBand (2 * m + 2) ''
            cumulantImageVariety (reverseCumulantMap m (2 * m + 2))) ⊔
        Ideal.span {verticalContractionMinorPolynomial m}).minimalPrimes) :
    CommonAxisFiniteHeightOneCertificates m hm := by
  exact ⟨
    forwardExceptionalFiniteHeightOneCertificate_of_commonAxis_principal m hm
      (horizontalContractionMinorPolynomial m) hcomponent hforward,
    reverseExceptionalFiniteHeightOneCertificate_of_commonAxis_principal m hm
      (verticalContractionMinorPolynomial m) hcomponent hreverse⟩

/-- The principal certificates follow formally from the honest geometric
height-one statement for the common-axis closure.  This isolates the remaining
model-specific work to irreducibility and the absence of an intermediate
irreducible closed set in each arrow variety. -/
theorem commonAxisFiniteHeightOneCertificates_of_no_intermediate
    (m : ℕ) (hm : 1 ≤ m)
    (hC : IsIrreducibleAffineClosed
      (restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm))
    (hforward : ¬ ∃ Y, IsIrreducibleAffineClosed Y ∧
      restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm ⊂ Y ∧
      Y ⊂ restrictCumBand (2 * m + 2) ''
        cumulantImageVariety (forwardCumulantMap m (2 * m + 2)))
    (hreverse : ¬ ∃ Y, IsIrreducibleAffineClosed Y ∧
      restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm ⊂ Y ∧
      Y ⊂ restrictCumBand (2 * m + 2) ''
        cumulantImageVariety (reverseCumulantMap m (2 * m + 2))) :
    CommonAxisFiniteHeightOneCertificates m hm := by
  let C := restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm
  let Z := restrictCumBand (2 * m + 2) '' genericCompatibilityClosure m
  let Xf := restrictCumBand (2 * m + 2) ''
    cumulantImageVariety (forwardCumulantMap m (2 * m + 2))
  let Xr := restrictCumBand (2 * m + 2) ''
    cumulantImageVariety (reverseCumulantMap m (2 * m + 2))
  have hCZ : C ⊆ Z :=
    Set.image_mono (forwardCommonAxisImageClosure_subset_exceptional hm)
  have hZXf : Z ⊆ Xf :=
    Set.image_mono (genericCompatibilityClosure_subset_forwardVariety m)
  have hZXr : Z ⊆ Xr :=
    Set.image_mono (genericCompatibilityClosure_subset_reverseVariety m)
  have hXf : IsIrreducibleAffineClosed Xf :=
    (irreducibleZariskiClosed_iff_affine
      (forwardCumulantImageVariety_subset_band m (2 * m + 2))).mp
        (forwardCumulantImageVariety_isIrreducible m (2 * m + 2))
  have hXr : IsIrreducibleAffineClosed Xr :=
    (irreducibleZariskiClosed_iff_affine
      (reverseCumulantImageVariety_subset_band m (2 * m + 2))).mp
        (reverseCumulantImageVariety_isIrreducible m (2 * m + 2))
  have hcomponent : IsIrreducibleAffineComponent C Z :=
    irreducibleAffineComponent_of_no_intermediate hC hCZ hZXf
      (restrict_genericCompatibilityClosure_ne_forwardVariety m hm) hforward
  apply commonAxisFiniteHeightOneCertificates_of_principal m hm hcomponent
  · exact vanishingIdeal_mem_minimalPrimes_span_of_no_intermediate
      hC hXf (hCZ.trans hZXf) (horizontalContractionMinorPolynomial m)
      (horizontalContractionMinor_mem_commonAxis_vanishingIdeal m hm)
      (horizontalContractionMinor_not_mem_forward_vanishingIdeal m hm) hforward
  · exact vanishingIdeal_mem_minimalPrimes_span_of_no_intermediate
      hC hXr (hCZ.trans hZXr) (verticalContractionMinorPolynomial m)
      (verticalContractionMinor_mem_commonAxis_vanishingIdeal m hm)
      (verticalContractionMinor_not_mem_reverse_vanishingIdeal m hm) hreverse

/-- After proving polynomial-image irreducibility of the common-axis closure,
the complete residual consists only of the two height-one (no-intermediate)
statements. -/
theorem commonAxisFiniteHeightOneCertificates_of_no_intermediate_only
    (m : ℕ) (hm : 1 ≤ m)
    (hforward : ¬ ∃ Y, IsIrreducibleAffineClosed Y ∧
      restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm ⊂ Y ∧
      Y ⊂ restrictCumBand (2 * m + 2) ''
        cumulantImageVariety (forwardCumulantMap m (2 * m + 2)))
    (hreverse : ¬ ∃ Y, IsIrreducibleAffineClosed Y ∧
      restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm ⊂ Y ∧
      Y ⊂ restrictCumBand (2 * m + 2) ''
        cumulantImageVariety (reverseCumulantMap m (2 * m + 2))) :
    CommonAxisFiniteHeightOneCertificates m hm := by
  exact commonAxisFiniteHeightOneCertificates_of_no_intermediate m hm
    (restrict_forwardCommonAxisImageClosure_isIrreducible m hm)
    hforward hreverse

/-- Coordinate reversal supplies the reverse height-one statement, so the
single remaining model-specific premise is the forward `D - 1` versus `D`
dimension gap. -/
theorem commonAxisFiniteHeightOneCertificates_of_forward_no_intermediate
    (m : ℕ) (hm : 1 ≤ m)
    (hforward : ¬ ∃ Y, IsIrreducibleAffineClosed Y ∧
      restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm ⊂ Y ∧
      Y ⊂ restrictCumBand (2 * m + 2) ''
        cumulantImageVariety (forwardCumulantMap m (2 * m + 2))) :
    CommonAxisFiniteHeightOneCertificates m hm := by
  exact commonAxisFiniteHeightOneCertificates_of_no_intermediate_only m hm
    hforward (reverse_no_intermediate_of_forward m hm hforward)

/-- The expected dimension of the common-axis image, namely `D - 1` in the
notation of the D0 Jacobian calculation.  The forward arrow variety has the
successor dimension. -/
def commonAxisExpectedDimension (m : ℕ) : ℕ :=
  (3 * (m + 2) ^ 2 + (m + 2)) / 2 - 5

/-- Exact `D - 1` and `D` image dimensions discharge the sole remaining
height-one premise. -/
theorem commonAxisFiniteHeightOneCertificates_of_exact_forward_dimensions
    (m : ℕ) (hm : 1 ≤ m)
    (hdims :
      HasAffineZariskiDimension (commonAxisExpectedDimension m)
        (restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm) ∧
      HasAffineZariskiDimension (commonAxisExpectedDimension m + 1)
        (restrictCumBand (2 * m + 2) ''
          cumulantImageVariety (forwardCumulantMap m (2 * m + 2)))) :
    CommonAxisFiniteHeightOneCertificates m hm := by
  let C := restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm
  let X := restrictCumBand (2 * m + 2) ''
    cumulantImageVariety (forwardCumulantMap m (2 * m + 2))
  have hCXle : C ⊆ X := Set.image_mono
    ((forwardCommonAxisImageClosure_subset_exceptional hm).trans
      (genericCompatibilityClosure_subset_forwardVariety m))
  have hCXne : C ≠ X := by
    intro hCX
    apply restrict_genericCompatibilityClosure_ne_forwardVariety m hm
    apply Set.Subset.antisymm
    · exact Set.image_mono (genericCompatibilityClosure_subset_forwardVariety m)
    · change X ⊆ restrictCumBand (2 * m + 2) '' genericCompatibilityClosure m
      rw [← hCX]
      exact Set.image_mono (forwardCommonAxisImageClosure_subset_exceptional hm)
  have hX : IsIrreducibleAffineClosed X :=
    (irreducibleZariskiClosed_iff_affine
      (forwardCumulantImageVariety_subset_band m (2 * m + 2))).mp
        (forwardCumulantImageVariety_isIrreducible m (2 * m + 2))
  apply commonAxisFiniteHeightOneCertificates_of_forward_no_intermediate m hm
  exact no_intermediate_of_exact_affine_dimensions hX
    (Set.ssubset_iff_subset_ne.mpr ⟨hCXle, hCXne⟩) hdims.1 hdims.2

/-- Once the explicit principal minimal-prime certificates are supplied, the
frozen custom codimension-one claims follow exactly. -/
theorem exceptionalCodimensionOne_of_finite_certificates (m : ℕ)
    {Df Dl : Set (CumVec ℂ)}
    (hf : ExceptionalFiniteHeightOneCertificate m Df
      (cumulantImageVariety (forwardCumulantMap m (2 * m + 2))))
    (hr : ExceptionalFiniteHeightOneCertificate m Dl
      (cumulantImageVariety (reverseCumulantMap m (2 * m + 2)))) :
    HasCodimensionIn 1 (genericCompatibilityClosure m)
        (cumulantImageVariety (forwardCumulantMap m (2 * m + 2))) ∧
      HasCodimensionIn 1 (genericCompatibilityClosure m)
        (cumulantImageVariety (reverseCumulantMap m (2 * m + 2))) := by
  let L := 2 * m + 2
  let Z := genericCompatibilityClosure m
  let Xr := cumulantImageVariety (forwardCumulantMap m L)
  let Xl := cumulantImageVariety (reverseCumulantMap m L)
  have hZband : Z ⊆ bandSupportedCumulants L :=
    genericCompatibilityClosure_subset_band m
  have hXrband : Xr ⊆ bandSupportedCumulants L :=
    forwardCumulantImageVariety_subset_band m L
  have hXlband : Xl ⊆ bandSupportedCumulants L :=
    reverseCumulantImageVariety_subset_band m L
  have hZXr : restrictCumBand L '' Z ⊆ restrictCumBand L '' Xr :=
    Set.image_mono (genericCompatibilityClosure_subset_forwardVariety m)
  have hZXl : restrictCumBand L '' Z ⊆ restrictCumBand L '' Xl :=
    Set.image_mono (genericCompatibilityClosure_subset_reverseVariety m)
  have hXrirr : IsIrreducibleAffineClosed (restrictCumBand L '' Xr) :=
    (irreducibleZariskiClosed_iff_affine hXrband).mp
      (forwardCumulantImageVariety_isIrreducible m L)
  have hXlirr : IsIrreducibleAffineClosed (restrictCumBand L '' Xl) :=
    (irreducibleZariskiClosed_iff_affine hXlband).mp
      (reverseCumulantImageVariety_isIrreducible m L)
  constructor
  · apply (hasCodimensionIn_iff_affineCodimensionIn hZband hXrband).mpr
    rcases hf with ⟨hne, P, hC, hmin⟩
    exact hasAffineCodimensionIn_one_of_minimalPrime_span
      hXrirr hZXr hne hC P hmin
  · apply (hasCodimensionIn_iff_affineCodimensionIn hZband hXlband).mpr
    rcases hr with ⟨hne, P, hC, hmin⟩
    exact hasAffineCodimensionIn_one_of_minimalPrime_span
      hXlirr hZXl hne hC P hmin

/-- All non-geometric conjuncts of the flagship assemble from the compiled
incidence helpers.  Consequently the two explicit finite height certificates
are the complete residual for `exceptionalLocusCodimensionOne`. -/
theorem exceptionalLocusCodimensionOne_of_finite_certificates
    (m : ℕ) (hm : ValidComplexity m)
    {Df Dl : Set (CumVec ℂ)}
    (hf : ExceptionalFiniteHeightOneCertificate m Df
      (cumulantImageVariety (forwardCumulantMap m (2 * m + 2))))
    (hr : ExceptionalFiniteHeightOneCertificate m Dl
      (cumulantImageVariety (reverseCumulantMap m (2 * m + 2)))) :
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
        (fiberCorrespondence (2 * m + 2)
          (reverseCumulantMap m (2 * m + 2))
          (forwardCumulantMap m (2 * m + 2) θ)).Nonempty) ∧
    (∀ eta : ParamSpace ℂ m,
      eta ∈ genericCompatibilityPreimageLeft m ↔
        eta ∈ bandSupportedParams m (2 * m + 2) ∧
        eta ∈ genericParameterLocus m (2 * m + 2) ∧
        (fiberCorrespondence (2 * m + 2)
          (forwardCumulantMap m (2 * m + 2))
          (reverseCumulantMap m (2 * m + 2) eta)).Nonempty) ∧
    (m = 1 → genericFullFiberCompatibility m =
      {t : CumVec ℂ | ∃ p ∈ (workedCompatibilitySystems m).1,
        forwardCumulantMap m (2 * m + 2) p.1 = t}) ∧
    (m = 2 → genericFullFiberCompatibility m =
      {t : CumVec ℂ | ∃ p ∈ (workedCompatibilitySystems m).1,
        forwardCumulantMap m (2 * m + 2) p.1 = t}) := by
  have hcodim := exceptionalCodimensionOne_of_finite_certificates m hf hr
  refine ⟨hcodim.1, hcodim.2, ?_,
    genericCompatibilityPreimageRight_iff m,
    genericCompatibilityPreimageLeft_iff m, ?_, ?_⟩
  · intro hm2
    exact ⟨hcodim.1.not_of_one hm2, hcodim.2.not_of_one hm2⟩
  · intro hm1
    exact genericFullFiberCompatibility_eq_worked_projection m (Or.inl hm1)
  · intro hm2
    exact genericFullFiberCompatibility_eq_worked_projection m (Or.inr hm2)

/-- The explicit common-axis certificates alone imply the entire flagship
conclusion. -/
def exceptionalLocusCodimensionOne_of_commonAxis_certificates
    (m : ℕ) (hm : ValidComplexity m)
    (hcert : CommonAxisFiniteHeightOneCertificates m hm) :=
  exceptionalLocusCodimensionOne_of_finite_certificates m hm hcert.1 hcert.2

end

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
