/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Explicit coordinate polynomials for the exceptional-locus Jacobian
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ConfluentVandermonde
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ExceptionalImageDimension
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

noncomputable section

private def bandDirectPolynomial (m L : ℕ) :
    MvPolynomial (BandParamCoord m L) ℂ :=
  MvPolynomial.X (Sum.inl ())

private def bandLatentPolynomial (m L : ℕ) (i : Fin m) :
    MvPolynomial (BandParamCoord m L) ℂ :=
  MvPolynomial.X (Sum.inr (Sum.inl i))

private def bandWeightPolynomial (m L : ℕ) (j : Fin (m + 2))
    (k : Fin (L - 1)) : MvPolynomial (BandParamCoord m L) ℂ :=
  MvPolynomial.X (Sum.inr (Sum.inr (j, k)))

private def forwardBandLoadingPolynomial (m L : ℕ) (j : Fin (m + 2)) :
    MvPolynomial (BandParamCoord m L) ℂ ×
      MvPolynomial (BandParamCoord m L) ℂ :=
  if h0 : j.val = 0 then (1, bandDirectPolynomial m L)
  else if hlast : j.val = m + 1 then (0, 1)
  else (1, bandLatentPolynomial m L
    ⟨j.val - 1, by have := j.isLt; omega⟩)

/-- Gives the stated evaluation formula for eval forward Band Loading Polynomial. -/
lemma eval_forwardBandLoadingPolynomial (m L : ℕ)
    (x : BandParamCoord m L → ℂ) (j : Fin (m + 2)) :
    (MvPolynomial.eval x (forwardBandLoadingPolynomial m L j).1,
      MvPolynomial.eval x (forwardBandLoadingPolynomial m L j).2) =
      forwardLoading m (decodeBandParam x).1 (decodeBandParam x).2.1 j := by
  by_cases h0 : j.val = 0
  · simp [forwardBandLoadingPolynomial, forwardLoading, h0,
      bandDirectPolynomial, decodeBandParam]
  · by_cases hlast : j.val = m + 1
    · simp [forwardBandLoadingPolynomial, forwardLoading, h0, hlast]
    · simp [forwardBandLoadingPolynomial, forwardLoading, h0, hlast,
        bandLatentPolynomial, decodeBandParam]

/-- A definitionally explicit representative of the forward retained
coordinate polynomial.  Unlike the `Classical.choose` representative, its
partial derivatives simplify directly. -/
def explicitForwardBandCoordinatePolynomial (m L : ℕ) (hL : 2 ≤ L)
    (q : RetainedCumCoord L) : MvPolynomial (BandParamCoord m L) ℂ :=
  ∑ j : Fin (m + 2),
    bandWeightPolynomial m L j ⟨q.1.1 - 2, by omega⟩ *
      (forwardBandLoadingPolynomial m L j).1 ^ (q.1.1 - q.1.2.1) *
      (forwardBandLoadingPolynomial m L j).2 ^ q.1.2.1

lemma eval_explicitForwardBandCoordinatePolynomial (m L : ℕ) (hL : 2 ≤ L)
    (q : RetainedCumCoord L) (x : BandParamCoord m L → ℂ) :
    MvPolynomial.eval x (explicitForwardBandCoordinatePolynomial m L hL q) =
      forwardBandFiniteMap m L x q := by
  simp only [explicitForwardBandCoordinatePolynomial, map_sum, map_mul, map_pow,
    bandWeightPolynomial, MvPolynomial.eval_X]
  simp only [forwardBandFiniteMap, restrictCumBand, forwardCumulantMap]
  have hqL : q.1.1 ≤ L := by omega
  rw [if_pos ⟨q.2.1, hqL, q.2.2⟩]
  apply Finset.sum_congr rfl
  intro j _
  rw [show MvPolynomial.eval x (forwardBandLoadingPolynomial m L j).1 =
      (forwardLoading m (decodeBandParam x).1 (decodeBandParam x).2.1 j).1 by
        simpa using congrArg Prod.fst
          (eval_forwardBandLoadingPolynomial m L x j),
    show MvPolynomial.eval x (forwardBandLoadingPolynomial m L j).2 =
      (forwardLoading m (decodeBandParam x).1 (decodeBandParam x).2.1 j).2 by
        simpa using congrArg Prod.snd
          (eval_forwardBandLoadingPolynomial m L x j)]
  simp only [decodeBandParam]
  rw [dif_pos ⟨q.2.1, hqL⟩]

/-- The chosen coordinate family used by the promoted substrate is equal to
the explicit coordinate polynomial above. -/
theorem forwardBandCoordinatePolynomial_eq_explicit (m L : ℕ) (hL : 2 ≤ L)
    (q : RetainedCumCoord L) :
    forwardBandCoordinatePolynomial m L hL q =
      explicitForwardBandCoordinatePolynomial m L hL q := by
  apply MvPolynomial.funext
  intro x
  rw [eval_forwardBandCoordinatePolynomial,
    eval_explicitForwardBandCoordinatePolynomial]

/-- Partial derivatives of the canonical chosen coordinates may henceforth be
computed from the explicit representative. -/
theorem pderiv_forwardBandCoordinatePolynomial_eq_explicit
    (m L : ℕ) (hL : 2 ≤ L) (q : RetainedCumCoord L)
    (c : BandParamCoord m L) :
    MvPolynomial.pderiv c (forwardBandCoordinatePolynomial m L hL q) =
      MvPolynomial.pderiv c
        (explicitForwardBandCoordinatePolynomial m L hL q) := by
  rw [forwardBandCoordinatePolynomial_eq_explicit]

private lemma pderiv_weight_forwardBandLoadingPolynomial
    (m L : ℕ) (j k : Fin (m + 2)) (a b : Fin (L - 1)) :
    MvPolynomial.pderiv (Sum.inr (Sum.inr (j, a)))
        (forwardBandLoadingPolynomial m L k).1 = 0 ∧
      MvPolynomial.pderiv (Sum.inr (Sum.inr (j, b)))
        (forwardBandLoadingPolynomial m L k).2 = 0 := by
  by_cases h0 : k.val = 0
  · simp [forwardBandLoadingPolynomial, h0, bandDirectPolynomial]
  · by_cases hlast : k.val = m + 1
    · simp [forwardBandLoadingPolynomial, h0, hlast]
    · simp [forwardBandLoadingPolynomial, h0, hlast, bandLatentPolynomial]

/-- A weight derivative is the corresponding binary-form monomial.  This is
the ordinary Vandermonde block used at every retained order. -/
lemma pderiv_explicitForwardBandCoordinatePolynomial_weight
    (m L : ℕ) (hL : 2 ≤ L) (q : RetainedCumCoord L)
    (j : Fin (m + 2)) :
    MvPolynomial.pderiv
        (Sum.inr (Sum.inr (j, ⟨q.1.1 - 2, by omega⟩)))
        (explicitForwardBandCoordinatePolynomial m L hL q) =
      (forwardBandLoadingPolynomial m L j).1 ^ (q.1.1 - q.1.2.1) *
        (forwardBandLoadingPolynomial m L j).2 ^ q.1.2.1 := by
  classical
  simp only [explicitForwardBandCoordinatePolynomial, map_sum,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow]
  rw [Finset.sum_eq_single j]
  · have hload := pderiv_weight_forwardBandLoadingPolynomial m L j j
        ⟨q.1.1 - 2, by omega⟩ ⟨q.1.1 - 2, by omega⟩
    rw [hload.1, hload.2]
    simp [bandWeightPolynomial]
  · intro k _ hkj
    let a : Fin (L - 1) := ⟨q.1.1 - 2, by omega⟩
    have hpair : (k, a) ≠ (j, a) := by
      intro h
      exact hkj (congrArg Prod.fst h)
    have hload := pderiv_weight_forwardBandLoadingPolynomial m L j k a a
    rw [hload.1, hload.2]
    simp [bandWeightPolynomial, a, hpair]
  · intro h
    exact (h (Finset.mem_univ j)).elim

/-- A weight coordinate belonging to a different retained order has zero
derivative.  This is the off-diagonal vanishing used by the block Jacobian. -/
lemma pderiv_explicitForwardBandCoordinatePolynomial_weight_otherOrder
    (m L : ℕ) (hL : 2 ≤ L) (q : RetainedCumCoord L)
    (j : Fin (m + 2)) (k : Fin (L - 1))
    (hk : k.val ≠ q.1.1 - 2) :
    MvPolynomial.pderiv
        (Sum.inr (Sum.inr (j, k)) : BandParamCoord m L)
        (explicitForwardBandCoordinatePolynomial m L hL q) = 0 := by
  classical
  simp only [explicitForwardBandCoordinatePolynomial, map_sum,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow]
  apply Finset.sum_eq_zero
  intro i _
  have hload := pderiv_weight_forwardBandLoadingPolynomial m L j i k k
  rw [hload.1, hload.2]
  have hpair :
      ((i, ⟨q.1.1 - 2, by omega⟩) : Fin (m + 2) × Fin (L - 1)) ≠ (j, k) := by
    intro h
    apply hk
    have := congrArg (fun z : Fin (m + 2) × Fin (L - 1) => z.2.val) h
    simpa using this.symm
  simp [bandWeightPolynomial, hpair]

/-- Gives the stated evaluation formula for eval pderiv explicit Forward Band Coordinate Polynomial weight. -/
lemma eval_pderiv_explicitForwardBandCoordinatePolynomial_weight
    (m L : ℕ) (hL : 2 ≤ L) (q : RetainedCumCoord L)
    (j : Fin (m + 2)) (x : BandParamCoord m L → ℂ) :
    MvPolynomial.eval x
        (MvPolynomial.pderiv
          (Sum.inr (Sum.inr (j, ⟨q.1.1 - 2, by omega⟩)))
          (explicitForwardBandCoordinatePolynomial m L hL q)) =
      (forwardLoading m (decodeBandParam x).1 (decodeBandParam x).2.1 j).1 ^
          (q.1.1 - q.1.2.1) *
        (forwardLoading m (decodeBandParam x).1 (decodeBandParam x).2.1 j).2 ^
          q.1.2.1 := by
  rw [pderiv_explicitForwardBandCoordinatePolynomial_weight]
  simp only [map_mul, map_pow]
  rw [show MvPolynomial.eval x (forwardBandLoadingPolynomial m L j).1 =
      (forwardLoading m (decodeBandParam x).1 (decodeBandParam x).2.1 j).1 by
        simpa using congrArg Prod.fst
          (eval_forwardBandLoadingPolynomial m L x j),
    show MvPolynomial.eval x (forwardBandLoadingPolynomial m L j).2 =
      (forwardLoading m (decodeBandParam x).1 (decodeBandParam x).2.1 j).2 by
        simpa using congrArg Prod.snd
          (eval_forwardBandLoadingPolynomial m L x j)]

/-- Weight derivatives at an arbitrary retained order.  Distinct weight-order
blocks do not interact; the matching block is the binary-form monomial. -/
lemma pderiv_explicitForwardBandCoordinatePolynomial_weight_general
    (m L : ℕ) (hL : 2 ≤ L) (q : RetainedCumCoord L)
    (j : Fin (m + 2)) (k : Fin (L - 1)) :
    MvPolynomial.pderiv
        (Sum.inr (Sum.inr (j, k)) : BandParamCoord m L)
        (explicitForwardBandCoordinatePolynomial m L hL q) =
      if k.val = q.1.1 - 2 then
        (forwardBandLoadingPolynomial m L j).1 ^ (q.1.1 - q.1.2.1) *
          (forwardBandLoadingPolynomial m L j).2 ^ q.1.2.1
      else 0 := by
  classical
  by_cases hk : k.val = q.1.1 - 2
  · rw [if_pos hk]
    have hcoord :
        (Sum.inr (Sum.inr (j, k)) : BandParamCoord m L) =
          Sum.inr (Sum.inr (j, ⟨q.1.1 - 2, by omega⟩)) := by
      apply congrArg (fun a : Fin (L - 1) =>
        (Sum.inr (Sum.inr (j, a)) : BandParamCoord m L))
      apply Fin.ext
      exact hk
    rw [hcoord]
    exact pderiv_explicitForwardBandCoordinatePolynomial_weight m L hL q j
  · rw [if_neg hk]
    simp only [explicitForwardBandCoordinatePolynomial, map_sum,
      MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow]
    apply Finset.sum_eq_zero
    intro i _
    have hload := pderiv_weight_forwardBandLoadingPolynomial m L j i k k
    rw [hload.1, hload.2]
    have hpair : ((i, ⟨q.1.1 - 2, by omega⟩) :
        Fin (m + 2) × Fin (L - 1)) ≠ (j, k) := by
      intro h
      apply hk
      have := congrArg (fun p : Fin (m + 2) × Fin (L - 1) => p.2.val) h
      simpa using this.symm
    simp [bandWeightPolynomial, hpair]

/-- Gives the stated evaluation formula for eval pderiv explicit Forward Band Coordinate Polynomial weight general. -/
lemma eval_pderiv_explicitForwardBandCoordinatePolynomial_weight_general
    (m L : ℕ) (hL : 2 ≤ L) (q : RetainedCumCoord L)
    (j : Fin (m + 2)) (k : Fin (L - 1))
    (x : BandParamCoord m L → ℂ) :
    MvPolynomial.eval x
        (MvPolynomial.pderiv
          (Sum.inr (Sum.inr (j, k)) : BandParamCoord m L)
          (explicitForwardBandCoordinatePolynomial m L hL q)) =
      if k.val = q.1.1 - 2 then
        (forwardLoading m (decodeBandParam x).1 (decodeBandParam x).2.1 j).1 ^
            (q.1.1 - q.1.2.1) *
          (forwardLoading m (decodeBandParam x).1 (decodeBandParam x).2.1 j).2 ^
            q.1.2.1
      else 0 := by
  rw [pderiv_explicitForwardBandCoordinatePolynomial_weight_general]
  split
  · simp only [map_mul, map_pow]
    rw [show MvPolynomial.eval x (forwardBandLoadingPolynomial m L j).1 =
        (forwardLoading m (decodeBandParam x).1 (decodeBandParam x).2.1 j).1 by
      simpa using congrArg Prod.fst (eval_forwardBandLoadingPolynomial m L x j),
      show MvPolynomial.eval x (forwardBandLoadingPolynomial m L j).2 =
        (forwardLoading m (decodeBandParam x).1 (decodeBandParam x).2.1 j).2 by
      simpa using congrArg Prod.snd (eval_forwardBandLoadingPolynomial m L x j)]
  · simp

/-! ### Loading-slope derivatives -/

/-- Proves the stated mathematical property of Forward Slope Index. -/
abbrev ForwardSlopeIndex (m : ℕ) := Unit ⊕ Fin m

/-- Defines the mathematical object called the forward Slope Band Coord. -/
def forwardSlopeBandCoord (m L : ℕ) :
    ForwardSlopeIndex m → BandParamCoord m L
  | Sum.inl u => Sum.inl u
  | Sum.inr i => Sum.inr (Sum.inl i)

/-- Defines the index set used to select the forward Slope Source Index coordinates. -/
def forwardSlopeSourceIndex (m : ℕ) : ForwardSlopeIndex m → Fin (m + 2)
  | Sum.inl _ => ⟨0, by omega⟩
  | Sum.inr i => ⟨i.val + 1, by omega⟩

/-- Proves that the map or coordinate assignment called the forward Slope Source Index is injective. -/
lemma forwardSlopeSourceIndex_injective (m : ℕ) :
    Function.Injective (forwardSlopeSourceIndex m) := by
  intro i j hij
  rcases i with _ | i <;> rcases j with _ | j
  · rfl
  · have h := congrArg Fin.val hij
    simp [forwardSlopeSourceIndex] at h
  · have h := congrArg Fin.val hij
    simp [forwardSlopeSourceIndex] at h
  · congr 1
    apply Fin.ext
    have h := congrArg Fin.val hij
    simp [forwardSlopeSourceIndex] at h
    omega

private lemma pderiv_forwardSlope_forwardBandLoadingPolynomial
    (m L : ℕ) (s : ForwardSlopeIndex m) (j : Fin (m + 2)) :
    MvPolynomial.pderiv (forwardSlopeBandCoord m L s)
        (forwardBandLoadingPolynomial m L j).1 = 0 ∧
      MvPolynomial.pderiv (forwardSlopeBandCoord m L s)
        (forwardBandLoadingPolynomial m L j).2 =
          if j = forwardSlopeSourceIndex m s then 1 else 0 := by
  by_cases hjs : j = forwardSlopeSourceIndex m s
  · rw [if_pos hjs, hjs]
    rcases s with u | i
    · obtain rfl : u = () := Subsingleton.elim _ _
      simp [forwardSlopeBandCoord, forwardSlopeSourceIndex,
        forwardBandLoadingPolynomial, bandDirectPolynomial]
    · have hi : i.val ≠ m := Nat.ne_of_lt i.isLt
      simp [forwardSlopeBandCoord, forwardSlopeSourceIndex,
        forwardBandLoadingPolynomial, bandLatentPolynomial, hi]
  · rw [if_neg hjs]
    rcases s with u | i
    · obtain rfl : u = () := Subsingleton.elim _ _
      have h0 : j.val ≠ 0 := by
        intro h
        apply hjs
        apply Fin.ext
        simpa [forwardSlopeSourceIndex] using h
      by_cases hlast : j.val = m + 1
      · simp [forwardSlopeBandCoord, forwardBandLoadingPolynomial, h0, hlast]
      · simp [forwardSlopeBandCoord, forwardBandLoadingPolynomial, h0, hlast,
          bandLatentPolynomial]
    · by_cases h0 : j.val = 0
      · simp [forwardSlopeBandCoord, forwardBandLoadingPolynomial, h0,
          bandDirectPolynomial]
      · by_cases hlast : j.val = m + 1
        · simp [forwardSlopeBandCoord, forwardBandLoadingPolynomial, h0, hlast]
        · let k : Fin m := ⟨j.val - 1, by omega⟩
          have hik : i ≠ k := by
            intro hik
            apply hjs
            apply Fin.ext
            have hv := congrArg Fin.val hik
            simp [k] at hv
            simp [forwardSlopeSourceIndex]
            omega
          simp [forwardSlopeBandCoord, forwardBandLoadingPolynomial, h0, hlast,
            bandLatentPolynomial, k, hik, Fin.ext_iff]

private lemma pderiv_forwardSlope_bandWeightPolynomial
    (m L : ℕ) (s : ForwardSlopeIndex m) (j : Fin (m + 2))
    (k : Fin (L - 1)) :
    MvPolynomial.pderiv (forwardSlopeBandCoord m L s)
        (bandWeightPolynomial m L j k) = 0 := by
  rcases s with u | i
  · obtain rfl : u = () := Subsingleton.elim _ _
    simp [forwardSlopeBandCoord, bandWeightPolynomial]
  · simp [forwardSlopeBandCoord, bandWeightPolynomial]

/-- A loading-slope derivative is the derivative column of the corresponding
finite node, multiplied by that source's weight. -/
lemma pderiv_explicitForwardBandCoordinatePolynomial_slope
    (m L : ℕ) (hL : 2 ≤ L) (q : RetainedCumCoord L)
    (s : ForwardSlopeIndex m) :
    MvPolynomial.pderiv (forwardSlopeBandCoord m L s)
        (explicitForwardBandCoordinatePolynomial m L hL q) =
      bandWeightPolynomial m L (forwardSlopeSourceIndex m s)
          ⟨q.1.1 - 2, by omega⟩ *
        (forwardBandLoadingPolynomial m L
          (forwardSlopeSourceIndex m s)).1 ^ (q.1.1 - q.1.2.1) *
        (MvPolynomial.C (q.1.2.1 : ℂ) *
          (forwardBandLoadingPolynomial m L
            (forwardSlopeSourceIndex m s)).2 ^ (q.1.2.1 - 1)) := by
  classical
  simp only [explicitForwardBandCoordinatePolynomial, map_sum]
  rw [Finset.sum_eq_single (forwardSlopeSourceIndex m s)]
  · have hload := pderiv_forwardSlope_forwardBandLoadingPolynomial
        m L s (forwardSlopeSourceIndex m s)
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_pow, MvPolynomial.pderiv_pow,
      pderiv_forwardSlope_bandWeightPolynomial, hload.1, hload.2]
    simp [bandWeightPolynomial]
  · intro j _ hj
    have hload := pderiv_forwardSlope_forwardBandLoadingPolynomial m L s j
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_pow, MvPolynomial.pderiv_pow,
      pderiv_forwardSlope_bandWeightPolynomial, hload.1, hload.2, if_neg hj]
    simp [bandWeightPolynomial]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- Evaluation form of the slope derivative.  This is the entry formula used
to identify the selected top-order Jacobian block with a confluent
Vandermonde matrix. -/
lemma eval_pderiv_explicitForwardBandCoordinatePolynomial_slope
    (m L : ℕ) (hL : 2 ≤ L) (q : RetainedCumCoord L)
    (s : ForwardSlopeIndex m) (x : BandParamCoord m L → ℂ) :
    MvPolynomial.eval x
        (MvPolynomial.pderiv (forwardSlopeBandCoord m L s)
          (explicitForwardBandCoordinatePolynomial m L hL q)) =
      (decodeBandParam x).2.2 (forwardSlopeSourceIndex m s) q.1.1 *
        (forwardLoading m (decodeBandParam x).1 (decodeBandParam x).2.1
          (forwardSlopeSourceIndex m s)).1 ^ (q.1.1 - q.1.2.1) *
        ((q.1.2.1 : ℂ) *
          (forwardLoading m (decodeBandParam x).1 (decodeBandParam x).2.1
            (forwardSlopeSourceIndex m s)).2 ^ (q.1.2.1 - 1)) := by
  rw [pderiv_explicitForwardBandCoordinatePolynomial_slope]
  simp only [map_mul, map_pow, map_natCast, bandWeightPolynomial,
    MvPolynomial.eval_X, MvPolynomial.eval_C]
  rw [show MvPolynomial.eval x
        (forwardBandLoadingPolynomial m L (forwardSlopeSourceIndex m s)).1 =
      (forwardLoading m (decodeBandParam x).1 (decodeBandParam x).2.1
        (forwardSlopeSourceIndex m s)).1 by
      simpa using congrArg Prod.fst
        (eval_forwardBandLoadingPolynomial m L x
          (forwardSlopeSourceIndex m s)),
    show MvPolynomial.eval x
        (forwardBandLoadingPolynomial m L (forwardSlopeSourceIndex m s)).2 =
      (forwardLoading m (decodeBandParam x).1 (decodeBandParam x).2.1
        (forwardSlopeSourceIndex m s)).2 by
      simpa using congrArg Prod.snd
        (eval_forwardBandLoadingPolynomial m L x
          (forwardSlopeSourceIndex m s))]
  rw [show x (Sum.inr (Sum.inr
        (forwardSlopeSourceIndex m s, ⟨q.1.1 - 2, by omega⟩))) =
      (decodeBandParam x).2.2 (forwardSlopeSourceIndex m s) q.1.1 by
    simp only [decodeBandParam]
    rw [dif_pos ⟨q.2.1, Nat.le_of_lt_succ q.1.1.isLt⟩]]

/-! ### The selected top-order block -/

/-- The loading-slope coordinate corresponding to a finite (non-infinity)
source. -/
def finiteSourceSlope (m : ℕ) : Fin (m + 1) → ForwardSlopeIndex m :=
  Fin.cases (Sum.inl ()) (fun i => Sum.inr i)

lemma forwardSlopeSourceIndex_finiteSourceSlope (m : ℕ)
    (j : Fin (m + 1)) :
    forwardSlopeSourceIndex m (finiteSourceSlope m j) = j.castSucc := by
  refine Fin.cases ?_ (fun i => ?_) j
  · rfl
  · apply Fin.ext
    simp [finiteSourceSlope, forwardSlopeSourceIndex]

/-- Monomial rows of the top-order finite-source block. -/
def forwardTopRow (m : ℕ) (a : Fin (m + 1) ⊕ Fin (m + 1)) :
    RetainedCumCoord (2 * m + 2) :=
  ⟨(⟨2 * m + 2, by omega⟩,
      ⟨doubledExponent a, by
        have h := doubledExponent_lt (n := m + 1) (by omega) a
        omega⟩),
    by
      change 2 ≤ 2 * m + 2
      omega, by
      change doubledExponent a ≤ 2 * m + 2
      have := doubledExponent_lt (n := m + 1) (by omega) a
      omega⟩

/-- Value columns are top-order weights; derivative columns are the finite
source loading slopes. -/
def forwardTopColumn (m : ℕ) :
    Fin (m + 1) ⊕ Fin (m + 1) → BandParamCoord m (2 * m + 2)
  | Sum.inl j =>
      Sum.inr (Sum.inr (j.castSucc, ⟨2 * m, by omega⟩))
  | Sum.inr j =>
      forwardSlopeBandCoord m (2 * m + 2) (finiteSourceSlope m j)

/-- A finite-coordinate witness tailored to the Jacobian calculation: the
finite loading slopes are `1, ..., m+1` and every retained weight is one. -/
def forwardJacobianWitnessCoord (m : ℕ) :
    BandParamCoord m (2 * m + 2) → ℂ
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl i) => ((i.val + 2 : ℕ) : ℂ)
  | Sum.inr (Sum.inr _) => 1

lemma forwardJacobianWitness_loading_castSucc (m : ℕ)
    (j : Fin (m + 1)) :
    forwardLoading m (decodeBandParam (forwardJacobianWitnessCoord m)).1
        (decodeBandParam (forwardJacobianWitnessCoord m)).2.1 j.castSucc =
      ((1 : ℂ), ((j.val + 1 : ℕ) : ℂ)) := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [forwardLoading, decodeBandParam, forwardJacobianWitnessCoord]
  · have hi : i.val ≠ m := Nat.ne_of_lt i.isLt
    simp [forwardLoading, decodeBandParam, forwardJacobianWitnessCoord, hi]
    push_cast
    ring

/-- Proves the stated mathematical property of forward Jacobian Witness top Weight cast Succ. -/
lemma forwardJacobianWitness_topWeight_castSucc (m : ℕ)
    (j : Fin (m + 1)) :
    (decodeBandParam (forwardJacobianWitnessCoord m)).2.2 j.castSucc
      (2 * m + 2) = 1 := by
  simp [decodeBandParam, forwardJacobianWitnessCoord]

/-- The selected finite-source part of the top-order Jacobian, evaluated at
the explicit witness used elsewhere in the LiNGAM development. -/
def forwardTopJacobianAtWitness (m : ℕ) :
    Matrix (Fin (m + 1) ⊕ Fin (m + 1))
      (Fin (m + 1) ⊕ Fin (m + 1)) ℂ :=
  fun a b =>
    MvPolynomial.eval
      (forwardJacobianWitnessCoord m)
      (MvPolynomial.pderiv (forwardTopColumn m b)
        (explicitForwardBandCoordinatePolynomial m (2 * m + 2) (by omega)
          (forwardTopRow m a)))

/-- The top-order finite-source block is exactly the standard doubled-node
confluent Vandermonde matrix. -/
theorem forwardTopJacobianAtWitness_eq_confluentVandermonde (m : ℕ) :
    forwardTopJacobianAtWitness m =
      confluentVandermonde
        (fun j : Fin (m + 1) => ((j.val + 1 : ℕ) : ℂ)) := by
  ext a b
  rcases b with j | j
  · rw [show forwardTopJacobianAtWitness m a (Sum.inl j) =
        MvPolynomial.eval
          (forwardJacobianWitnessCoord m)
          (MvPolynomial.pderiv
            (Sum.inr (Sum.inr (j.castSucc, ⟨2 * m, by omega⟩)))
            (explicitForwardBandCoordinatePolynomial m (2 * m + 2)
              (by omega) (forwardTopRow m a))) by rfl]
    rw [show (Sum.inr (Sum.inr (j.castSucc, ⟨2 * m, by omega⟩)) :
          BandParamCoord m (2 * m + 2)) =
        Sum.inr (Sum.inr (j.castSucc,
          ⟨(forwardTopRow m a).1.1 - 2, by omega⟩)) by
      apply congrArg (fun k : Fin (2 * m + 2 - 1) =>
        (Sum.inr (Sum.inr (j.castSucc, k)) :
          BandParamCoord m (2 * m + 2)))
      apply Fin.ext
      rfl]
    rw [eval_pderiv_explicitForwardBandCoordinatePolynomial_weight]
    change
      (forwardLoading m (decodeBandParam (forwardJacobianWitnessCoord m)).1
        (decodeBandParam (forwardJacobianWitnessCoord m)).2.1 j.castSucc).1 ^
          (2 * m + 2 - doubledExponent a) *
        (forwardLoading m (decodeBandParam (forwardJacobianWitnessCoord m)).1
          (decodeBandParam (forwardJacobianWitnessCoord m)).2.1 j.castSucc).2 ^
          doubledExponent a = _
    rw [forwardJacobianWitness_loading_castSucc]
    simp [confluentVandermonde]
  · rw [show forwardTopJacobianAtWitness m a (Sum.inr j) =
        MvPolynomial.eval
          (forwardJacobianWitnessCoord m)
          (MvPolynomial.pderiv
            (forwardSlopeBandCoord m (2 * m + 2) (finiteSourceSlope m j))
            (explicitForwardBandCoordinatePolynomial m (2 * m + 2)
              (by omega) (forwardTopRow m a))) by rfl]
    rw [eval_pderiv_explicitForwardBandCoordinatePolynomial_slope]
    rw [forwardSlopeSourceIndex_finiteSourceSlope]
    simp only [forwardTopRow]
    change
      (decodeBandParam (forwardJacobianWitnessCoord m)).2.2 j.castSucc
          (2 * m + 2) *
        (forwardLoading m (decodeBandParam (forwardJacobianWitnessCoord m)).1
          (decodeBandParam (forwardJacobianWitnessCoord m)).2.1 j.castSucc).1 ^
          (2 * m + 2 - doubledExponent a) *
        ((doubledExponent a : ℂ) *
          (forwardLoading m (decodeBandParam (forwardJacobianWitnessCoord m)).1
            (decodeBandParam (forwardJacobianWitnessCoord m)).2.1 j.castSucc).2 ^
              (doubledExponent a - 1)) = _
    rw [forwardJacobianWitness_topWeight_castSucc,
      forwardJacobianWitness_loading_castSucc]
    simp [confluentVandermonde]

/-- Proves that the quantity called the det forward Top Jacobian At Witness is nonzero. -/
theorem det_forwardTopJacobianAtWitness_ne_zero (m : ℕ) :
    (forwardTopJacobianAtWitness m).det ≠ 0 := by
  rw [forwardTopJacobianAtWitness_eq_confluentVandermonde]
  exact det_confluentVandermonde_ne_zero (by omega)
    (fun j : Fin (m + 1) => ((j.val + 1 : ℕ) : ℂ))
    (forwardContractionMinorWitness_slope_injective m)

/-- The same selected block formed from the canonical coordinate family used
by the polynomial-image dimension interface. -/
def canonicalForwardTopJacobianAtWitness (m : ℕ) :
    Matrix (Fin (m + 1) ⊕ Fin (m + 1))
      (Fin (m + 1) ⊕ Fin (m + 1)) ℂ :=
  fun a b =>
    MvPolynomial.eval
      (forwardJacobianWitnessCoord m)
      (MvPolynomial.pderiv (forwardTopColumn m b)
        (forwardBandCoordinatePolynomial m (2 * m + 2) (by omega)
          (forwardTopRow m a)))

theorem canonicalForwardTopJacobianAtWitness_eq (m : ℕ) :
    canonicalForwardTopJacobianAtWitness m = forwardTopJacobianAtWitness m := by
  ext a b
  simp only [canonicalForwardTopJacobianAtWitness, forwardTopJacobianAtWitness]
  rw [pderiv_forwardBandCoordinatePolynomial_eq_explicit]

/-- Proves that the quantity called the det canonical Forward Top Jacobian At Witness is nonzero. -/
theorem det_canonicalForwardTopJacobianAtWitness_ne_zero (m : ℕ) :
    (canonicalForwardTopJacobianAtWitness m).det ≠ 0 := by
  rw [canonicalForwardTopJacobianAtWitness_eq]
  exact det_forwardTopJacobianAtWitness_ne_zero m

/-! ### Adding the point at infinity to the top-order block -/

/-- Proves the stated mathematical property of Forward Top Augmented Index. -/
abbrev ForwardTopAugmentedIndex (m : ℕ) :=
  (Fin (m + 1) ⊕ Fin (m + 1)) ⊕ Unit

/-- Defines the mathematical object called the forward Top Augmented Row. -/
def forwardTopAugmentedRow (m : ℕ) :
    ForwardTopAugmentedIndex m → RetainedCumCoord (2 * m + 2)
  | Sum.inl a => forwardTopRow m a
  | Sum.inr _ =>
      ⟨(⟨2 * m + 2, by omega⟩, ⟨2 * m + 2, by omega⟩),
        by change 2 ≤ 2 * m + 2; omega,
        by change 2 * m + 2 ≤ 2 * m + 2; omega⟩

/-- Defines the mathematical object called the forward Top Augmented Column. -/
def forwardTopAugmentedColumn (m : ℕ) :
    ForwardTopAugmentedIndex m → BandParamCoord m (2 * m + 2)
  | Sum.inl b => forwardTopColumn m b
  | Sum.inr _ =>
      Sum.inr (Sum.inr (Fin.last (m + 1), ⟨2 * m, by omega⟩))

/-- Defines the Jacobian matrix, row, column, or indexing object called the canonical Forward Top Augmented Jacobian At Witness. -/
def canonicalForwardTopAugmentedJacobianAtWitness (m : ℕ) :
    Matrix (ForwardTopAugmentedIndex m) (ForwardTopAugmentedIndex m) ℂ :=
  fun a b =>
    MvPolynomial.eval (forwardJacobianWitnessCoord m)
      (MvPolynomial.pderiv (forwardTopAugmentedColumn m b)
        (forwardBandCoordinatePolynomial m (2 * m + 2) (by omega)
          (forwardTopAugmentedRow m a)))

private def forwardTopAugmentedLowerLeft (m : ℕ) :
    Matrix Unit (Fin (m + 1) ⊕ Fin (m + 1)) ℂ :=
  fun u b => canonicalForwardTopAugmentedJacobianAtWitness m (Sum.inr u) (Sum.inl b)

/-- Proves the stated mathematical property of forward Jacobian Witness loading last. -/
lemma forwardJacobianWitness_loading_last (m : ℕ) :
    forwardLoading m (decodeBandParam (forwardJacobianWitnessCoord m)).1
        (decodeBandParam (forwardJacobianWitnessCoord m)).2.1
        (Fin.last (m + 1)) = (0, 1) := by
  simp [forwardLoading, decodeBandParam, forwardJacobianWitnessCoord, Fin.last]

/-- Proves the stated equality or equivalence for canonical Forward Top Augmented Jacobian At Witness eq. -/
theorem canonicalForwardTopAugmentedJacobianAtWitness_eq (m : ℕ) :
    canonicalForwardTopAugmentedJacobianAtWitness m =
      Matrix.fromBlocks (canonicalForwardTopJacobianAtWitness m) 0
        (forwardTopAugmentedLowerLeft m) 1 := by
  ext a b
  rcases a with a | u <;> rcases b with b | v
  · rfl
  · obtain rfl : v = () := Subsingleton.elim _ _
    simp only [canonicalForwardTopAugmentedJacobianAtWitness,
      forwardTopAugmentedColumn, forwardTopAugmentedRow,
      Matrix.fromBlocks_apply₁₂, Pi.zero_apply]
    rw [pderiv_forwardBandCoordinatePolynomial_eq_explicit,
      eval_pderiv_explicitForwardBandCoordinatePolynomial_weight_general,
      if_pos (by rfl)]
    change
      (forwardLoading m (decodeBandParam (forwardJacobianWitnessCoord m)).1
          (decodeBandParam (forwardJacobianWitnessCoord m)).2.1
          (Fin.last (m + 1))).1 ^
            (2 * m + 2 - doubledExponent a) *
        (forwardLoading m (decodeBandParam (forwardJacobianWitnessCoord m)).1
          (decodeBandParam (forwardJacobianWitnessCoord m)).2.1
          (Fin.last (m + 1))).2 ^ doubledExponent a = 0
    rw [forwardJacobianWitness_loading_last]
    simp [show 2 * m + 2 - doubledExponent a ≠ 0 by
      have := doubledExponent_lt (n := m + 1) (by omega) a
      omega]
  · rfl
  · obtain rfl : u = () := Subsingleton.elim _ _
    obtain rfl : v = () := Subsingleton.elim _ _
    simp only [canonicalForwardTopAugmentedJacobianAtWitness,
      forwardTopAugmentedColumn, forwardTopAugmentedRow,
      Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
    rw [pderiv_forwardBandCoordinatePolynomial_eq_explicit,
      eval_pderiv_explicitForwardBandCoordinatePolynomial_weight_general,
      if_pos (by rfl)]
    rw [forwardJacobianWitness_loading_last]
    simp

/-- Proves that the quantity called the det canonical Forward Top Augmented Jacobian At Witness is nonzero. -/
theorem det_canonicalForwardTopAugmentedJacobianAtWitness_ne_zero (m : ℕ) :
    (canonicalForwardTopAugmentedJacobianAtWitness m).det ≠ 0 := by
  rw [canonicalForwardTopAugmentedJacobianAtWitness_eq,
    Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]
  exact det_canonicalForwardTopJacobianAtWitness_ne_zero m

/- The ordinary blocks are assembled once, in `ExceptionalJacobianMinor`.
The low- and high-order homogeneous pieces below are exported so that the
global assembly can avoid a costly dependent `Sigma` elaboration. -/
/-! ### Ordinary weight blocks below the top order -/

/-- Proves the stated mathematical property of Forward Low Weight Index. -/
abbrev ForwardLowWeightIndex (m : ℕ) :=
  Σ k : Fin (m - 1), Fin (k.val + 3)

/-- Defines the mathematical object called the forward Low Weight Row. -/
def forwardLowWeightRow (m : ℕ) :
    ForwardLowWeightIndex m → RetainedCumCoord (2 * m + 2)
  | ⟨k, a⟩ =>
      ⟨(⟨k.val + 2, by omega⟩, ⟨a.val, by omega⟩),
        by change 2 ≤ k.val + 2; omega,
        by change a.val ≤ k.val + 2; have := a.isLt; omega⟩

/-- Defines the mathematical object called the forward Low Weight Column. -/
def forwardLowWeightColumn (m : ℕ) :
    ForwardLowWeightIndex m → BandParamCoord m (2 * m + 2)
  | ⟨k, a⟩ =>
      Sum.inr (Sum.inr
        (⟨a.val, by have := a.isLt; have := k.isLt; omega⟩, ⟨k.val, by omega⟩))

/-- Defines the Jacobian matrix, row, column, or indexing object called the canonical Forward Low Weight Jacobian At Witness. -/
def canonicalForwardLowWeightJacobianAtWitness (m : ℕ) :
    Matrix (ForwardLowWeightIndex m) (ForwardLowWeightIndex m) ℂ :=
  fun a b =>
    MvPolynomial.eval (forwardJacobianWitnessCoord m)
      (MvPolynomial.pderiv (forwardLowWeightColumn m b)
        (forwardBandCoordinatePolynomial m (2 * m + 2) (by omega)
          (forwardLowWeightRow m a)))

private def forwardLowVandermondeBlock (m : ℕ) (k : Fin (m - 1)) :
    Matrix (Fin (k.val + 3)) (Fin (k.val + 3)) ℂ :=
  (Matrix.vandermonde (fun j => ((j.val + 1 : ℕ) : ℂ))).transpose

/-- Proves the stated equality or equivalence for canonical Forward Low Weight Jacobian At Witness eq. -/
theorem canonicalForwardLowWeightJacobianAtWitness_eq (m : ℕ) :
    canonicalForwardLowWeightJacobianAtWitness m =
      Matrix.blockDiagonal' (forwardLowVandermondeBlock m) := by
  ext a b
  rcases a with ⟨ka, a⟩
  rcases b with ⟨kb, b⟩
  by_cases h : ka = kb
  · subst kb
    rw [Matrix.blockDiagonal'_apply_eq]
    simp only [canonicalForwardLowWeightJacobianAtWitness,
      forwardLowWeightColumn, forwardLowWeightRow]
    rw [pderiv_forwardBandCoordinatePolynomial_eq_explicit,
      eval_pderiv_explicitForwardBandCoordinatePolynomial_weight_general,
      if_pos (by rfl)]
    let j : Fin (m + 1) := ⟨b.val, by
      have := b.isLt
      have := ka.isLt
      omega⟩
    change
      (forwardLoading m (decodeBandParam (forwardJacobianWitnessCoord m)).1
          (decodeBandParam (forwardJacobianWitnessCoord m)).2.1 j.castSucc).1 ^
            (ka.val + 2 - a.val) *
        (forwardLoading m (decodeBandParam (forwardJacobianWitnessCoord m)).1
          (decodeBandParam (forwardJacobianWitnessCoord m)).2.1 j.castSucc).2 ^
            a.val = _
    rw [forwardJacobianWitness_loading_castSucc]
    simp [forwardLowVandermondeBlock, Matrix.vandermonde, j]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
    simp only [canonicalForwardLowWeightJacobianAtWitness,
      forwardLowWeightColumn, forwardLowWeightRow]
    rw [pderiv_forwardBandCoordinatePolynomial_eq_explicit,
      pderiv_explicitForwardBandCoordinatePolynomial_weight_otherOrder]
    · simp
    · intro heq
      apply h
      apply Fin.ext
      simpa using heq.symm

/-- Proves that the quantity called the det canonical Forward Low Weight Jacobian At Witness is nonzero. -/
theorem det_canonicalForwardLowWeightJacobianAtWitness_ne_zero (m : ℕ) :
    (canonicalForwardLowWeightJacobianAtWitness m).det ≠ 0 := by
  rw [canonicalForwardLowWeightJacobianAtWitness_eq]
  have hblocks : IsUnit (forwardLowVandermondeBlock m) := by
    rw [Pi.isUnit_iff]
    intro k
    rw [Matrix.isUnit_iff_isUnit_det]
    rw [forwardLowVandermondeBlock, Matrix.det_transpose]
    exact (Matrix.det_vandermonde_ne_zero_iff.mpr (by
      intro i j hij
      apply Fin.ext
      have hc : (i.val : ℂ) + 1 = (j.val : ℂ) + 1 := by
        simpa using hij
      exact_mod_cast add_right_cancel hc)).isUnit
  have hmatrix : IsUnit (Matrix.blockDiagonal'
      (forwardLowVandermondeBlock m)) :=
    hblocks.map (Matrix.blockDiagonal'RingHom
      (fun k : Fin (m - 1) => Fin (k.val + 3)) ℂ)
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hmatrix).ne_zero

/-- Proves the stated mathematical property of Forward High Weight Node. -/
abbrev ForwardHighWeightNode (m : ℕ) := Fin (m + 1) ⊕ Unit
/-- Proves the stated mathematical property of Forward High Weight Index. -/
abbrev ForwardHighWeightIndex (m : ℕ) :=
  ForwardHighWeightNode m × Fin (m + 1)

private def forwardHighOrder (m : ℕ) (k : Fin (m + 1)) : ℕ :=
  m + 1 + k.val

/-- Defines the mathematical object called the forward High Weight Row. -/
def forwardHighWeightRow (m : ℕ) (hm : 1 ≤ m) :
    ForwardHighWeightIndex m → RetainedCumCoord (2 * m + 2)
  | (Sum.inl a, k) =>
      ⟨(⟨forwardHighOrder m k, by
          have := k.isLt
          simp only [forwardHighOrder]
          omega⟩,
        ⟨a.val, by
          have := a.isLt
          have := k.isLt
          omega⟩), by
            simp only [forwardHighOrder]
            omega, by
            have := a.isLt
            simp only [forwardHighOrder]
            omega⟩
  | (Sum.inr _, k) =>
      ⟨(⟨forwardHighOrder m k, by
          have := k.isLt
          simp only [forwardHighOrder]
          omega⟩,
        ⟨forwardHighOrder m k, by
          have := k.isLt
          simp only [forwardHighOrder]
          omega⟩), by
            simp only [forwardHighOrder]
            omega, le_rfl⟩

/-- Proves the stated mathematical property of forward High Weight Row order. -/
lemma forwardHighWeightRow_order (m : ℕ) (hm : 1 ≤ m)
    (a : ForwardHighWeightNode m) (k : Fin (m + 1)) :
    (forwardHighWeightRow m hm (a, k)).1.1 = m + 1 + k.val := by
  rcases a with a | u <;> rfl

/-- Defines the mathematical object called the forward High Weight Column. -/
def forwardHighWeightColumn (m : ℕ) :
    ForwardHighWeightIndex m → BandParamCoord m (2 * m + 2)
  | (Sum.inl j, k) =>
      Sum.inr (Sum.inr (j.castSucc, ⟨m - 1 + k.val, by
        have := k.isLt
        omega⟩))
  | (Sum.inr _, k) =>
      Sum.inr (Sum.inr (Fin.last (m + 1), ⟨m - 1 + k.val, by
        have := k.isLt
        omega⟩))

/-- Defines the Jacobian matrix, row, column, or indexing object called the canonical Forward High Weight Jacobian At Witness. -/
def canonicalForwardHighWeightJacobianAtWitness (m : ℕ) (hm : 1 ≤ m) :
    Matrix (ForwardHighWeightIndex m) (ForwardHighWeightIndex m) ℂ :=
  fun a b =>
    MvPolynomial.eval (forwardJacobianWitnessCoord m)
      (MvPolynomial.pderiv (forwardHighWeightColumn m b)
        (forwardBandCoordinatePolynomial m (2 * m + 2) (by omega)
          (forwardHighWeightRow m hm a)))

private def forwardHighWeightBlock (m : ℕ) (k : Fin (m + 1)) :
    Matrix (ForwardHighWeightNode m) (ForwardHighWeightNode m) ℂ :=
  Matrix.fromBlocks
    (Matrix.vandermonde
      (fun j : Fin (m + 1) => ((j.val + 1 : ℕ) : ℂ))).transpose
    0
    (fun _ j => ((j.val + 1 : ℕ) : ℂ) ^ forwardHighOrder m k)
    1

private theorem det_forwardHighWeightBlock_ne_zero (m : ℕ)
    (k : Fin (m + 1)) : (forwardHighWeightBlock m k).det ≠ 0 := by
  rw [forwardHighWeightBlock, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_transpose, Matrix.det_one, mul_one]
  exact Matrix.det_vandermonde_ne_zero_iff.mpr
    (forwardContractionMinorWitness_slope_injective m)

/-- Proves the stated equality or equivalence for canonical Forward High Weight Jacobian At Witness eq. -/
theorem canonicalForwardHighWeightJacobianAtWitness_eq (m : ℕ) (hm : 1 ≤ m) :
    canonicalForwardHighWeightJacobianAtWitness m hm =
      Matrix.blockDiagonal (forwardHighWeightBlock m) := by
  ext a b
  rcases a with ⟨a, ka⟩
  rcases b with ⟨b, kb⟩
  by_cases h : ka = kb
  · subst kb
    rw [Matrix.blockDiagonal_apply_eq]
    rcases a with a | u <;> rcases b with b | v
    · simp only [canonicalForwardHighWeightJacobianAtWitness,
        forwardHighWeightColumn, forwardHighWeightRow,
        forwardHighWeightBlock, Matrix.fromBlocks_apply₁₁]
      rw [pderiv_forwardBandCoordinatePolynomial_eq_explicit,
        eval_pderiv_explicitForwardBandCoordinatePolynomial_weight_general,
        if_pos (by simp only [forwardHighOrder]; omega)]
      change
        (forwardLoading m (decodeBandParam (forwardJacobianWitnessCoord m)).1
            (decodeBandParam (forwardJacobianWitnessCoord m)).2.1 b.castSucc).1 ^
              (forwardHighOrder m ka - a.val) *
          (forwardLoading m (decodeBandParam (forwardJacobianWitnessCoord m)).1
            (decodeBandParam (forwardJacobianWitnessCoord m)).2.1 b.castSucc).2 ^
              a.val = _
      rw [forwardJacobianWitness_loading_castSucc]
      simp [Matrix.vandermonde]
    · obtain rfl : v = () := Subsingleton.elim _ _
      simp only [canonicalForwardHighWeightJacobianAtWitness,
        forwardHighWeightColumn, forwardHighWeightRow,
        forwardHighWeightBlock, Matrix.fromBlocks_apply₁₂, Pi.zero_apply]
      rw [pderiv_forwardBandCoordinatePolynomial_eq_explicit,
        eval_pderiv_explicitForwardBandCoordinatePolynomial_weight_general,
        if_pos (by simp only [forwardHighOrder]; omega),
        forwardJacobianWitness_loading_last]
      simp [show forwardHighOrder m ka - a.val ≠ 0 by
        have := a.isLt
        simp only [forwardHighOrder]
        omega]
    · obtain rfl : u = () := Subsingleton.elim _ _
      simp only [canonicalForwardHighWeightJacobianAtWitness,
        forwardHighWeightColumn, forwardHighWeightRow,
        forwardHighWeightBlock, Matrix.fromBlocks_apply₂₁]
      rw [pderiv_forwardBandCoordinatePolynomial_eq_explicit,
        eval_pderiv_explicitForwardBandCoordinatePolynomial_weight_general,
        if_pos (by simp only [forwardHighOrder]; omega),
        forwardJacobianWitness_loading_castSucc]
      simp
    · obtain rfl : u = () := Subsingleton.elim _ _
      obtain rfl : v = () := Subsingleton.elim _ _
      simp only [canonicalForwardHighWeightJacobianAtWitness,
        forwardHighWeightColumn, forwardHighWeightRow,
        forwardHighWeightBlock, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
      rw [pderiv_forwardBandCoordinatePolynomial_eq_explicit,
        eval_pderiv_explicitForwardBandCoordinatePolynomial_weight_general,
        if_pos (by simp only [forwardHighOrder]; omega),
        forwardJacobianWitness_loading_last]
      simp
  · rw [Matrix.blockDiagonal_apply_ne _ _ _ h]
    rcases a with a | u <;> rcases b with b | v
    all_goals try { obtain rfl : u = () := Subsingleton.elim _ _ }
    all_goals try { obtain rfl : v = () := Subsingleton.elim _ _ }
    all_goals
      simp only [canonicalForwardHighWeightJacobianAtWitness,
        forwardHighWeightColumn, forwardHighWeightRow]
      rw [pderiv_forwardBandCoordinatePolynomial_eq_explicit,
        pderiv_explicitForwardBandCoordinatePolynomial_weight_general,
        if_neg]
      · simp
      · intro heq
        apply h
        apply Fin.ext
        simp only [forwardHighOrder] at heq
        omega

/-- Proves that the quantity called the det canonical Forward High Weight Jacobian At Witness is nonzero. -/
theorem det_canonicalForwardHighWeightJacobianAtWitness_ne_zero (m : ℕ)
    (hm : 1 ≤ m) :
    (canonicalForwardHighWeightJacobianAtWitness m hm).det ≠ 0 := by
  rw [canonicalForwardHighWeightJacobianAtWitness_eq,
    Matrix.det_blockDiagonal]
  exact Finset.prod_ne_zero_iff.mpr fun k _ =>
    det_forwardHighWeightBlock_ne_zero m k

end

/-- The explicit polynomial for a forward-band cumulant coordinate is unchanged when equal
dimensions, admissibility conditions, and retained coordinates are substituted. -/
add_decl_doc explicitForwardBandCoordinatePolynomial.congr_simp

/-- The row selector for the high-weight forward Jacobian is unchanged when equal model orders,
admissibility conditions, and row indices are substituted. -/
add_decl_doc forwardHighWeightRow.congr_simp

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
