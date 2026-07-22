/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Coordinate reversal for the arrow-image geometry
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ArrowPolynomialGeometry
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.CommonAxisTwin

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

noncomputable section

/-- Exchange the two observable coordinates in every cumulant block. -/
def reverseCumCoordinates (t : CumVec ℂ) : CumVec ℂ :=
  fun r a => if a ≤ r then t r (r - a) else t r a

@[simp] lemma reverseCumCoordinates_apply_of_le (t : CumVec ℂ)
    {r a : ℕ} (ha : a ≤ r) :
    reverseCumCoordinates t r a = t r (r - a) := by
  simp [reverseCumCoordinates, ha]

@[simp] lemma reverseCumCoordinates_involutive (t : CumVec ℂ) :
    reverseCumCoordinates (reverseCumCoordinates t) = t := by
  funext r a
  by_cases ha : a ≤ r
  · simp [reverseCumCoordinates, ha, Nat.sub_sub_self ha]
  · simp [reverseCumCoordinates, ha]

/-- Reverse the source order at the two fixed axes. -/
def axisSourceReversal (m : ℕ) : Equiv.Perm (Fin (m + 2)) :=
  Equiv.swap 0 (Fin.last (m + 1))

/-- The same slope coordinates and weights, with the two fixed-axis sources
exchanged.  Observable coordinate reversal turns this forward parameter into a
reverse parameter. -/
def axisReverseParameter (m : ℕ) (theta : ParamSpace ℂ m) : ParamSpace ℂ m :=
  (theta.1, theta.2.1, fun j r => theta.2.2 (axisSourceReversal m j) r)

@[simp] lemma axisSourceReversal_involutive (m : ℕ) (j : Fin (m + 2)) :
    axisSourceReversal m (axisSourceReversal m j) = j := by
  exact Equiv.apply_symm_apply (axisSourceReversal m) j

@[simp] lemma axisReverseParameter_involutive (m : ℕ)
    (theta : ParamSpace ℂ m) :
    axisReverseParameter m (axisReverseParameter m theta) = theta := by
  rcases theta with ⟨γ, ρ, w⟩
  simp [axisReverseParameter]

private lemma reverseLoading_axisReverseParameter (m : ℕ)
    (theta : ParamSpace ℂ m) (j : Fin (m + 2)) :
    reverseLoading m (axisReverseParameter m theta).1
        (axisReverseParameter m theta).2.1 j =
      ((forwardLoading m theta.1 theta.2.1 (axisSourceReversal m j)).2,
        (forwardLoading m theta.1 theta.2.1 (axisSourceReversal m j)).1) := by
  by_cases h0 : j = 0
  · subst j
    simp [axisReverseParameter, axisSourceReversal, reverseLoading, forwardLoading,
      Fin.last]
  · by_cases hlast : j = Fin.last (m + 1)
    · subst j
      simp [axisReverseParameter, axisSourceReversal, reverseLoading, forwardLoading,
        Fin.last]
    · have hj0 : j.val ≠ 0 := fun h => h0 (Fin.ext h)
      have hjlast : j.val ≠ m + 1 := fun h => hlast (Fin.ext (by simpa [Fin.last] using h))
      have hswap : axisSourceReversal m j = j := by
        exact Equiv.swap_apply_of_ne_of_ne h0 hlast
      simp [axisReverseParameter, reverseLoading, forwardLoading, hswap, hj0, hjlast]

/-- Honest coordinate reversal identifies the two polynomial arrow maps. -/
lemma reverseCumulantMap_axisReverseParameter (m L : ℕ)
    (theta : ParamSpace ℂ m) :
    reverseCumulantMap m L (axisReverseParameter m theta) =
      reverseCumCoordinates (forwardCumulantMap m L theta) := by
  funext r a
  by_cases ha : a ≤ r
  · simp only [reverseCumulantMap, reverseCumCoordinates_apply_of_le _ ha,
      forwardCumulantMap]
    by_cases hr : 2 ≤ r ∧ r ≤ L
    · rw [if_pos ⟨hr.1, hr.2, ha⟩]
      have hra : r - a ≤ r := Nat.sub_le r a
      rw [if_pos ⟨hr.1, hr.2, hra⟩]
      calc
        _ = ∑ j : Fin (m + 2),
            theta.2.2 (axisSourceReversal m j) r *
              (forwardLoading m theta.1 theta.2.1
                (axisSourceReversal m j)).1 ^ a *
              (forwardLoading m theta.1 theta.2.1
                (axisSourceReversal m j)).2 ^ (r - a) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [reverseLoading_axisReverseParameter]
              simp only [axisReverseParameter]
              ring
        _ = ∑ j : Fin (m + 2),
            theta.2.2 j r *
              (forwardLoading m theta.1 theta.2.1 j).1 ^ a *
              (forwardLoading m theta.1 theta.2.1 j).2 ^ (r - a) :=
          by
            simpa using Equiv.sum_comp (axisSourceReversal m)
              (fun j : Fin (m + 2) =>
                theta.2.2 j r *
                  (forwardLoading m theta.1 theta.2.1 j).1 ^ a *
                  (forwardLoading m theta.1 theta.2.1 j).2 ^ (r - a))
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Nat.sub_sub_self ha]
    · have hleft : ¬ (2 ≤ r ∧ r ≤ L ∧ a ≤ r) := by aesop
      have hright : ¬ (2 ≤ r ∧ r ≤ L ∧ r - a ≤ r) := by aesop
      rw [if_neg hleft, if_neg hright]
  · have hleft : ¬ (2 ≤ r ∧ r ≤ L ∧ a ≤ r) := by aesop
    simp [reverseCumCoordinates, ha, reverseCumulantMap, forwardCumulantMap, hleft]

/-- Proves the stated mathematical property of axis Reverse Parameter band Supported. -/
lemma axisReverseParameter_bandSupported {m L : ℕ}
    {theta : ParamSpace ℂ m} (htheta : theta ∈ bandSupportedParams m L) :
    axisReverseParameter m theta ∈ bandSupportedParams m L := by
  intro j r hr
  exact htheta (axisSourceReversal m j) r hr

/-- Proves the stated mathematical property of axis Reverse Parameter generic. -/
lemma axisReverseParameter_generic {m L : ℕ}
    {theta : ParamSpace ℂ m} (htheta : theta ∈ genericParameterLocus m L) :
    axisReverseParameter m theta ∈ genericParameterLocus m L := by
  refine ⟨axisReverseParameter_bandSupported
    (genericParameterLocus_bandSupported htheta), ?_⟩
  let base := theta.1 * (∏ i : Fin m, (theta.1 - theta.2.1 i)) *
    (∏ i : Fin m, ∏ i' : Fin m,
      if i < i' then theta.2.1 i - theta.2.1 i' else 1)
  have hw : (∏ j : Fin (m + 2), ∏ r ∈ Finset.Icc 2 L,
      theta.2.2 (axisSourceReversal m j) r) =
      ∏ j : Fin (m + 2), ∏ r ∈ Finset.Icc 2 L, theta.2.2 j r := by
    simpa using Equiv.prod_comp (axisSourceReversal m)
      (fun j : Fin (m + 2) => ∏ r ∈ Finset.Icc 2 L, theta.2.2 j r)
  change base * (∏ j : Fin (m + 2), ∏ r ∈ Finset.Icc 2 L,
    theta.2.2 (axisSourceReversal m j) r) ≠ 0
  rw [hw]
  exact genericParameterLocus_prod_ne_zero htheta

/-- Proves the stated set-containment or membership property for reverse Cum Coordinates mem band. -/
lemma reverseCumCoordinates_mem_band {L : ℕ} {t : CumVec ℂ}
    (ht : t ∈ bandSupportedCumulants L) :
    reverseCumCoordinates t ∈ bandSupportedCumulants L := by
  intro r a hout
  by_cases ha : a ≤ r
  · rw [reverseCumCoordinates_apply_of_le _ ha]
    apply ht
    omega
  · simp [reverseCumCoordinates, ha, ht r a hout]

/-- Coordinate reversal on finite retained cumulant coordinates. -/
def reverseRetainedCumCoord {L : ℕ} (p : RetainedCumCoord L) :
    RetainedCumCoord L :=
  ⟨(p.1.1, ⟨p.1.1 - p.1.2.1, by omega⟩), p.2.1, Nat.sub_le _ _⟩

@[simp] lemma reverseRetainedCumCoord_involutive {L : ℕ}
    (p : RetainedCumCoord L) :
    reverseRetainedCumCoord (reverseRetainedCumCoord p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Fin.ext
    simp [reverseRetainedCumCoord, Nat.sub_sub_self p.2.2]

/-- The coordinate-reversed observable contraction minor. -/
def verticalContractionMinorPolynomial (m : ℕ) :
    MvPolynomial (RetainedCumCoord (2 * m + 2)) ℂ :=
  MvPolynomial.rename reverseRetainedCumCoord
    (horizontalContractionMinorPolynomial m)

lemma eval_verticalContractionMinorPolynomial (m : ℕ) (t : CumVec ℂ) :
    MvPolynomial.eval (restrictCumBand (2 * m + 2) t)
        (verticalContractionMinorPolynomial m) =
      MvPolynomial.eval
        (restrictCumBand (2 * m + 2) (reverseCumCoordinates t))
        (horizontalContractionMinorPolynomial m) := by
  rw [verticalContractionMinorPolynomial, MvPolynomial.eval_rename]
  apply congrArg (fun f => MvPolynomial.eval f (horizontalContractionMinorPolynomial m))
  funext p
  simp [Function.comp_apply, restrictCumBand, reverseRetainedCumCoord,
    reverseCumCoordinates, p.2.2]

/-- Proves the stated mathematical property of vertical Contraction Minor Polynomial forward vanishes. -/
lemma verticalContractionMinorPolynomial_forward_vanishes (m : ℕ)
    (theta : ParamSpace ℂ m) :
    MvPolynomial.eval
        (restrictCumBand (2 * m + 2)
          (forwardCumulantMap m (2 * m + 2) theta))
        (verticalContractionMinorPolynomial m) = 0 := by
  rw [eval_verticalContractionMinorPolynomial]
  rw [← reverseCumulantMap_axisReverseParameter]
  exact horizontalContractionMinorPolynomial_reverse_vanishes m
    (axisReverseParameter m theta)

/-- The vertical minor vanishes on the entire forward arrow-image variety. -/
lemma verticalContractionMinorPolynomial_forwardVariety_vanishes (m : ℕ)
    {t : CumVec ℂ}
    (ht : t ∈ cumulantImageVariety (forwardCumulantMap m (2 * m + 2))) :
    MvPolynomial.eval (restrictCumBand (2 * m + 2) t)
      (verticalContractionMinorPolynomial m) = 0 := by
  have htband : t ∈ bandSupportedCumulants (2 * m + 2) := by
    apply zariskiClosure_subset_band
      (A := Set.range (forwardCumulantMap m (2 * m + 2)))
    · rintro _ ⟨theta, rfl⟩
      exact forwardCumulantMap_mem_bandSupportedCumulants m (2 * m + 2) theta
    · exact ht
  rw [← eval_extendCumPolynomial (2 * m + 2)
    (restrictCumBand (2 * m + 2) t) (verticalContractionMinorPolynomial m)]
  rw [extend_restrictCumBand htband]
  apply ht (extendCumPolynomial (2 * m + 2)
    (verticalContractionMinorPolynomial m))
  rintro _ ⟨theta, rfl⟩
  rw [← extend_restrictCumBand
    (forwardCumulantMap_mem_bandSupportedCumulants m (2 * m + 2) theta)]
  rw [eval_extendCumPolynomial]
  exact verticalContractionMinorPolynomial_forward_vanishes m theta

/-- The mirrored block-Vandermonde witness makes the vertical minor nonzero on
the reverse arrow image. -/
lemma verticalContractionMinorPolynomial_reverseWitness_ne_zero
    (m : ℕ) (hm : 1 ≤ m) :
    MvPolynomial.eval
      (restrictCumBand (2 * m + 2)
        (reverseCumulantMap m (2 * m + 2)
          (axisReverseParameter m (forwardContractionMinorWitnessParameter m))))
      (verticalContractionMinorPolynomial m) ≠ 0 := by
  rw [eval_verticalContractionMinorPolynomial,
    reverseCumulantMap_axisReverseParameter, reverseCumCoordinates_involutive]
  exact horizontalContractionMinorPolynomial_forwardWitness_ne_zero m hm

lemma verticalContractionMinorPolynomial_ne_zero (m : ℕ) (hm : 1 ≤ m) :
    verticalContractionMinorPolynomial m ≠ 0 := by
  intro hzero
  exact (verticalContractionMinorPolynomial_reverseWitness_ne_zero m hm)
    (by rw [hzero, map_zero])

end

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
