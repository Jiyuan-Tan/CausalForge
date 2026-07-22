/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Finite polynomial-image models for the exceptional-locus dimension proof
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.CommonAxisImageGeometry
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ExceptionalHeightReduction
import Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension.Jacobian
import Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension.Transcendence

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension

-- `coordinateSubalgebra_trdeg_le_of_polynomial_factorization` is neutral substrate;
-- promoted to `Causalean.…PolynomialImageDimension.Transcendence` and re-exported here
-- to preserve the paper-facing name.
export Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension
  (coordinateSubalgebra_trdeg_le_of_polynomial_factorization)

noncomputable section

/-- The forward cumulant map on the finite retained-band parameter space. -/
def forwardBandFiniteMap (m L : ℕ) (x : BandParamCoord m L → ℂ) :
    RetainedCumCoord L → ℂ :=
  restrictCumBand L (forwardCumulantMap m L (decodeBandParam x))

lemma forwardBandFiniteMap_isPolynomial (m L : ℕ) (hL : 2 ≤ L) :
    IsPolynomialMap (forwardBandFiniteMap m L) := by
  obtain ⟨coord, hcoord⟩ := forwardCumulantMap_isPolynomial m L
  intro q
  refine ⟨restrictParamPolynomial (coord (q.1.1, q.1.2.1)), ?_⟩
  intro x
  rw [eval_restrictParamPolynomial hL, hcoord]
  rfl

/-- A canonical coordinate-polynomial family for the finite forward map. -/
noncomputable def forwardBandCoordinatePolynomial (m L : ℕ) (hL : 2 ≤ L)
    (q : RetainedCumCoord L) : MvPolynomial (BandParamCoord m L) ℂ :=
  Classical.choose (forwardBandFiniteMap_isPolynomial m L hL q)

lemma eval_forwardBandCoordinatePolynomial (m L : ℕ) (hL : 2 ≤ L)
    (x : BandParamCoord m L → ℂ) (q : RetainedCumCoord L) :
    MvPolynomial.eval x (forwardBandCoordinatePolynomial m L hL q) =
      forwardBandFiniteMap m L x q :=
  Classical.choose_spec (forwardBandFiniteMap_isPolynomial m L hL q) x

lemma polynomialCoordinateMap_forwardBand (m L : ℕ) (hL : 2 ≤ L) :
    polynomialCoordinateMap (forwardBandCoordinatePolynomial m L hL) =
      forwardBandFiniteMap m L := by
  funext x q
  exact eval_forwardBandCoordinatePolynomial m L hL x q

/-- Pinning the unused parameter coordinates does not change a truncated
forward cumulant vector. -/
lemma forwardCumulantMap_decode_encodeBandParam (m L : ℕ) (hL : 2 ≤ L)
    (θ : ParamSpace ℂ m) :
    forwardCumulantMap m L
        (decodeBandParam (L := L) (encodeBandParam (L := L) θ)) =
      forwardCumulantMap m L θ := by
  funext r a
  simp only [forwardCumulantMap]
  split
  · rename_i h
    apply Finset.sum_congr rfl
    intro j _
    simp [decodeBandParam, encodeBandParam, h]
  · rfl

lemma range_forwardBandFiniteMap (m L : ℕ) (hL : 2 ≤ L) :
    Set.range (forwardBandFiniteMap m L) =
      restrictCumBand L '' Set.range (forwardCumulantMap m L) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨forwardCumulantMap m L (decodeBandParam x),
      ⟨decodeBandParam x, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨θ, rfl⟩, rfl⟩
    refine ⟨encodeBandParam (L := L) θ, ?_⟩
    simp only [forwardBandFiniteMap]
    rw [forwardCumulantMap_decode_encodeBandParam m L hL θ]

/-- The finite restriction of the forward arrow variety is exactly the
polynomial-image closure to which the promoted dimension bridge applies. -/
theorem restrict_forwardCumulantImageVariety_eq_polynomialImageClosure
    (m L : ℕ) (hL : 2 ≤ L) :
    restrictCumBand L ''
        cumulantImageVariety (forwardCumulantMap m L) =
      polynomialImageClosure (forwardBandCoordinatePolynomial m L hL) := by
  change restrictCumBand L '' zariskiClosure (Set.range (forwardCumulantMap m L)) = _
  rw [restrictCumBand_image_zariskiClosure (by
    rintro _ ⟨θ, rfl⟩
    exact forwardCumulantMap_mem_bandSupportedCumulants m L θ)]
  change affineZariskiClosure
      (restrictCumBand L '' Set.range (forwardCumulantMap m L)) =
    affineZariskiClosure
      (Set.range (polynomialCoordinateMap
        (forwardBandCoordinatePolynomial m L hL)))
  rw [← range_forwardBandFiniteMap m L hL,
    polynomialCoordinateMap_forwardBand m L hL]

/-- A canonical coordinate-polynomial family for the common-axis map. -/
noncomputable def forwardCommonAxisCoordinatePolynomial (m L : ℕ)
    (hm : 1 ≤ m) (hL : 2 ≤ L) (q : RetainedCumCoord L) :
    MvPolynomial (CommonAxisBandCoord m L hm) ℂ :=
  Classical.choose (forwardCommonAxisFiniteMap_isPolynomial m L hm hL q)

lemma polynomialCoordinateMap_forwardCommonAxis (m L : ℕ)
    (hm : 1 ≤ m) (hL : 2 ≤ L) :
    polynomialCoordinateMap
        (forwardCommonAxisCoordinatePolynomial m L hm hL) =
      forwardCommonAxisFiniteMap m L hm := by
  funext x q
  exact Classical.choose_spec
    (forwardCommonAxisFiniteMap_isPolynomial m L hm hL q) x

/-- The finite common-axis closure is the corresponding polynomial-image
closure; density removes the generic nonvanishing condition on the source. -/
theorem restrict_forwardCommonAxisImageClosure_eq_polynomialImageClosure
    (m : ℕ) (hm : 1 ≤ m) :
    restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm =
      polynomialImageClosure
        (forwardCommonAxisCoordinatePolynomial m (2 * m + 2) hm (by omega)) := by
  let L := 2 * m + 2
  let A : Set (CumVec ℂ) :=
    forwardCumulantMap m L '' forwardCommonAxisDivisor m hm
  have hA : A ⊆ bandSupportedCumulants L := by
    rintro _ ⟨θ, _, rfl⟩
    exact forwardCumulantMap_mem_bandSupportedCumulants m L θ
  change restrictCumBand L '' zariskiClosure A = _
  rw [restrictCumBand_image_zariskiClosure hA]
  have himage : restrictCumBand L '' A =
      forwardCommonAxisFiniteMap m L hm '' commonAxisSource m L hm := by
    symm
    simpa [A, forwardCommonAxisDivisor] using
      commonAxisFiniteImage_eq m L hm (by omega)
  rw [himage]
  rw [affineZariskiClosure_polynomial_image_of_dense
    (forwardCommonAxisFiniteMap_isPolynomial m L hm (by omega))
    (commonAxisSource_dense hm (by omega))]
  change affineZariskiClosure (Set.range (forwardCommonAxisFiniteMap m L hm)) =
    affineZariskiClosure
      (Set.range (polynomialCoordinateMap
        (forwardCommonAxisCoordinatePolynomial m L hm (by omega))))
  rw [polynomialCoordinateMap_forwardCommonAxis m L hm (by omega)]

/-- The promoted Jacobian/transcendence bridge specialized to the full forward
arrow image.  The two hypotheses are precisely the model-specific lower and
upper certificates still owed by the confluent-Vandermonde calculation and the
low-order weight kernels. -/
theorem restrict_forwardCumulantImageVariety_dimension_of_jacobian
    (m d : ℕ)
    (rows : Fin d → RetainedCumCoord (2 * m + 2))
    (cols : Fin d → BandParamCoord m (2 * m + 2))
    (hminor : polynomialJacobianMinor
      (forwardBandCoordinatePolynomial m (2 * m + 2) (by omega)) rows cols ≠ 0)
    (hupper : @Algebra.trdeg ℂ
      (polynomialCoordinateSubalgebra
        (forwardBandCoordinatePolynomial m (2 * m + 2) (by omega))) _ _
      (jacobianCoordinateSubalgebraAlgebra
        (forwardBandCoordinatePolynomial m (2 * m + 2) (by omega))) ≤ d) :
    HasAffineZariskiDimension d
      (restrictCumBand (2 * m + 2) ''
        cumulantImageVariety (forwardCumulantMap m (2 * m + 2))) := by
  rw [restrict_forwardCumulantImageVariety_eq_polynomialImageClosure m
    (2 * m + 2) (by omega)]
  exact polynomialImageClosure_dimension_of_jacobian _ rows cols hminor hupper

/-- The same promoted bridge specialized to the common-axis divisor image. -/
theorem restrict_forwardCommonAxisImageClosure_dimension_of_jacobian
    (m : ℕ) (hm : 1 ≤ m)
    (rows : Fin (commonAxisExpectedDimension m) →
      RetainedCumCoord (2 * m + 2))
    (cols : Fin (commonAxisExpectedDimension m) →
      CommonAxisBandCoord m (2 * m + 2) hm)
    (hminor : polynomialJacobianMinor
      (forwardCommonAxisCoordinatePolynomial m (2 * m + 2) hm (by omega))
      rows cols ≠ 0)
    (hupper : @Algebra.trdeg ℂ
      (polynomialCoordinateSubalgebra
        (forwardCommonAxisCoordinatePolynomial m (2 * m + 2) hm (by omega))) _ _
      (jacobianCoordinateSubalgebraAlgebra
        (forwardCommonAxisCoordinatePolynomial m (2 * m + 2) hm (by omega))) ≤
      commonAxisExpectedDimension m) :
    HasAffineZariskiDimension (commonAxisExpectedDimension m)
      (restrictCumBand (2 * m + 2) '' forwardCommonAxisImageClosure m hm) := by
  rw [restrict_forwardCommonAxisImageClosure_eq_polynomialImageClosure m hm]
  exact polynomialImageClosure_dimension_of_jacobian _ rows cols hminor hupper

end

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
