/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Rank witnesses for the shorter apolar stack
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ReverseApolarKernel
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.MomentGate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

noncomputable section

/-- Defines the polynomial called the lower First Polynomial. -/
def lowerFirstPolynomial {R : Type*} [CommRing R] (m : ℕ) (j : Fin (m + 2)) :
    MvPolynomial (ParamCoord m) R :=
  if j.1 = m + 1 then 0 else 1

/-- Defines the polynomial called the lower Slope Polynomial. -/
def lowerSlopePolynomial {R : Type*} [CommRing R] (m : ℕ) (j : Fin (m + 2)) :
    MvPolynomial (ParamCoord m) R :=
  if h0 : j.1 = 0 then MvPolynomial.X (Sum.inl ())
  else if ha : j.1 = m + 1 then 1
  else MvPolynomial.X (Sum.inr (Sum.inl ⟨j.1 - 1, by omega⟩))

/-- Defines the polynomial called the lower Reverse First Polynomial. -/
def lowerReverseFirstPolynomial {R : Type*} [CommRing R]
    (m : ℕ) (j : Fin (m + 2)) : MvPolynomial (ParamCoord m) R :=
  if h0 : j.1 = 0 then 1
  else if ha : j.1 = m + 1 then MvPolynomial.X (Sum.inl ())
  else MvPolynomial.X (Sum.inr (Sum.inl ⟨j.1 - 1, by omega⟩))

/-- Defines the polynomial called the lower Reverse Second Polynomial. -/
def lowerReverseSecondPolynomial {R : Type*} [CommRing R]
    (m : ℕ) (j : Fin (m + 2)) : MvPolynomial (ParamCoord m) R :=
  if j.1 = 0 then 0 else 1

/-- Defines the polynomial called the lower Weight Polynomial. -/
def lowerWeightPolynomial {R : Type*} [CommRing R]
    (m : ℕ) (j : Fin (m + 2)) (r : ℕ) : MvPolynomial (ParamCoord m) R :=
  MvPolynomial.X (Sum.inr (Sum.inr (j, r)))

-- @node: lowerForwardContractionMinorPolynomial
/-- Selected rows for the block partition `J₀={axis}`, `J₁={direct}` and
`J_{m-1}={latent sources}`. -/
def lowerForwardContractionMinorPolynomial (R : Type*) [CommRing R] (m : ℕ) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) (MvPolynomial (ParamCoord m) R) :=
  fun i j =>
    if i.1 = 0 then lowerWeightPolynomial m j (m + 2)
    else if i.1 = 1 then
      lowerWeightPolynomial m j (m + 3) * lowerFirstPolynomial m j
    else lowerWeightPolynomial m j (2 * m + 1) *
      MvPolynomial.C ((m - 1).choose (i.1 - 2) : R) *
      lowerFirstPolynomial m j ^ (m - 1 - (i.1 - 2)) *
      lowerSlopePolynomial m j ^ (i.1 - 2)

-- @node: lowerReverseContractionMinorPolynomial
/-- The coordinate-reversed selected minor.  Its top block uses coefficients in
reverse order so that the latent columns are an ordinary Vandermonde matrix. -/
def lowerReverseContractionMinorPolynomial (R : Type*) [CommRing R] (m : ℕ) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) (MvPolynomial (ParamCoord m) R) :=
  fun i j =>
    if i.1 = 0 then lowerWeightPolynomial m j (m + 2)
    else if i.1 = 1 then
      lowerWeightPolynomial m j (m + 3) * lowerReverseSecondPolynomial m j
    else lowerWeightPolynomial m j (2 * m + 1) *
      MvPolynomial.C ((m - 1).choose (i.1 - 2) : R) *
      lowerReverseFirstPolynomial m j ^ (i.1 - 2) *
      lowerReverseSecondPolynomial m j ^ (m - 1 - (i.1 - 2))

-- @node: lowerForwardRealRankPolynomial
def lowerForwardRealRankPolynomial (m : ℕ) : MvPolynomial (RealParamCoord m) ℝ :=
  (lowerForwardContractionMinorPolynomial ℝ m).det

-- @node: lowerReverseRealRankPolynomial
/-- Defines the polynomial called the lower Reverse Real Rank Polynomial. -/
def lowerReverseRealRankPolynomial (m : ℕ) : MvPolynomial (RealParamCoord m) ℝ :=
  (lowerReverseContractionMinorPolynomial ℝ m).det

-- @node: lowerForwardComplexRankPolynomial
/-- Defines the polynomial called the lower Forward Complex Rank Polynomial. -/
def lowerForwardComplexRankPolynomial (m : ℕ) : MvPolynomial (ParamCoord m) ℂ :=
  (lowerForwardContractionMinorPolynomial ℂ m).det

-- @node: lowerReverseComplexRankPolynomial
/-- Defines the polynomial called the lower Reverse Complex Rank Polynomial. -/
def lowerReverseComplexRankPolynomial (m : ℕ) : MvPolynomial (ParamCoord m) ℂ :=
  (lowerReverseContractionMinorPolynomial ℂ m).det

private lemma map_lowerFirstPolynomial (m : ℕ) (j : Fin (m + 2)) :
    MvPolynomial.map Complex.ofRealHom (lowerFirstPolynomial (R := ℝ) m j) =
      lowerFirstPolynomial (R := ℂ) m j := by
  unfold lowerFirstPolynomial
  split_ifs <;> simp

private lemma map_lowerSlopePolynomial (m : ℕ) (j : Fin (m + 2)) :
    MvPolynomial.map Complex.ofRealHom (lowerSlopePolynomial (R := ℝ) m j) =
      lowerSlopePolynomial (R := ℂ) m j := by
  unfold lowerSlopePolynomial
  split_ifs <;> simp

private lemma map_lowerReverseFirstPolynomial (m : ℕ) (j : Fin (m + 2)) :
    MvPolynomial.map Complex.ofRealHom (lowerReverseFirstPolynomial (R := ℝ) m j) =
      lowerReverseFirstPolynomial (R := ℂ) m j := by
  unfold lowerReverseFirstPolynomial
  split_ifs <;> simp

private lemma map_lowerReverseSecondPolynomial (m : ℕ) (j : Fin (m + 2)) :
    MvPolynomial.map Complex.ofRealHom (lowerReverseSecondPolynomial (R := ℝ) m j) =
      lowerReverseSecondPolynomial (R := ℂ) m j := by
  unfold lowerReverseSecondPolynomial
  split_ifs <;> simp

private lemma map_lowerWeightPolynomial (m : ℕ) (j : Fin (m + 2)) (r : ℕ) :
    MvPolynomial.map Complex.ofRealHom (lowerWeightPolynomial (R := ℝ) m j r) =
      lowerWeightPolynomial (R := ℂ) m j r := by
  simp [lowerWeightPolynomial]

-- @node: lowerForwardRankPolynomial_map_ofReal
/-- Proves the stated mathematical property of lower Forward Rank Polynomial map of Real. -/
lemma lowerForwardRankPolynomial_map_ofReal (m : ℕ) :
    MvPolynomial.map Complex.ofRealHom (lowerForwardRealRankPolynomial m) =
      lowerForwardComplexRankPolynomial m := by
  rw [lowerForwardRealRankPolynomial, lowerForwardComplexRankPolynomial,
    RingHom.map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  change MvPolynomial.map Complex.ofRealHom
      (lowerForwardContractionMinorPolynomial ℝ m i j) =
    lowerForwardContractionMinorPolynomial ℂ m i j
  by_cases hi0 : i.val = 0
  · have hi : i = 0 := Fin.ext hi0
    subst i
    simp [lowerForwardContractionMinorPolynomial, map_lowerWeightPolynomial]
  by_cases hi1 : i.val = 1
  · have hi : i = 1 := Fin.ext hi1
    subst i
    simp [lowerForwardContractionMinorPolynomial, map_lowerWeightPolynomial,
      map_lowerFirstPolynomial]
  · simp only [lowerForwardContractionMinorPolynomial, hi0, hi1, if_false,
      map_mul, map_pow, MvPolynomial.map_C]
    rw [map_lowerWeightPolynomial, map_lowerFirstPolynomial,
      map_lowerSlopePolynomial]
    simp

-- @node: lowerReverseRankPolynomial_map_ofReal
/-- Proves the stated mathematical property of lower Reverse Rank Polynomial map of Real. -/
lemma lowerReverseRankPolynomial_map_ofReal (m : ℕ) :
    MvPolynomial.map Complex.ofRealHom (lowerReverseRealRankPolynomial m) =
      lowerReverseComplexRankPolynomial m := by
  rw [lowerReverseRealRankPolynomial, lowerReverseComplexRankPolynomial,
    RingHom.map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  change MvPolynomial.map Complex.ofRealHom
      (lowerReverseContractionMinorPolynomial ℝ m i j) =
    lowerReverseContractionMinorPolynomial ℂ m i j
  by_cases hi0 : i.val = 0
  · have hi : i = 0 := Fin.ext hi0
    subst i
    simp [lowerReverseContractionMinorPolynomial, map_lowerWeightPolynomial]
  by_cases hi1 : i.val = 1
  · have hi : i = 1 := Fin.ext hi1
    subst i
    simp [lowerReverseContractionMinorPolynomial, map_lowerWeightPolynomial,
      map_lowerReverseSecondPolynomial]
  · simp only [lowerReverseContractionMinorPolynomial, hi0, hi1, if_false,
      map_mul, map_pow, MvPolynomial.map_C]
    rw [map_lowerWeightPolynomial, map_lowerReverseFirstPolynomial,
      map_lowerReverseSecondPolynomial]
    simp

-- @node: lowerForwardRankPolynomial_eval_complexify
/-- Gives the stated evaluation formula for lower Forward Rank Polynomial complexify. -/
lemma lowerForwardRankPolynomial_eval_complexify (m : ℕ) (θ : ParamSpace ℝ m) :
    MvPolynomial.eval (paramEval (complexifyParam θ))
        (lowerForwardComplexRankPolynomial m) =
      (MvPolynomial.eval (realParamEval θ) (lowerForwardRealRankPolynomial m) : ℂ) := by
  have h := MvPolynomial.map_eval Complex.ofRealHom (realParamEval θ)
    (lowerForwardRealRankPolynomial m)
  rw [lowerForwardRankPolynomial_map_ofReal] at h
  have hcoord : Complex.ofRealHom ∘ realParamEval θ =
      paramEval (complexifyParam θ) := by
    funext i
    rcases i with _ | i
    · rfl
    rcases i with i | jr <;> rfl
  rw [← hcoord]
  exact h.symm

-- @node: lowerReverseRankPolynomial_eval_complexify
/-- Gives the stated evaluation formula for lower Reverse Rank Polynomial complexify. -/
lemma lowerReverseRankPolynomial_eval_complexify (m : ℕ) (η : ParamSpace ℝ m) :
    MvPolynomial.eval (paramEval (complexifyParam η))
        (lowerReverseComplexRankPolynomial m) =
      (MvPolynomial.eval (realParamEval η) (lowerReverseRealRankPolynomial m) : ℂ) := by
  have h := MvPolynomial.map_eval Complex.ofRealHom (realParamEval η)
    (lowerReverseRealRankPolynomial m)
  rw [lowerReverseRankPolynomial_map_ofReal] at h
  have hcoord : Complex.ofRealHom ∘ realParamEval η =
      paramEval (complexifyParam η) := by
    funext i
    rcases i with _ | i
    · rfl
    rcases i with i | jr <;> rfl
  rw [← hcoord]
  exact h.symm

/-- Defines the mathematical object called the lower Forward Minor. -/
def lowerForwardMinor (m : ℕ) (θ : ParamSpace ℂ m) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ :=
  (lowerForwardContractionMinorPolynomial ℂ m).map (MvPolynomial.eval (paramEval θ))

/-- Defines the mathematical object called the lower Reverse Minor. -/
def lowerReverseMinor (m : ℕ) (η : ParamSpace ℂ m) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ :=
  (lowerReverseContractionMinorPolynomial ℂ m).map (MvPolynomial.eval (paramEval η))

-- @node: lowerForwardWeightedContraction
/-- The selected scalar rows of the contractions visible at order `2m+1`.
They are the `k=0` constant coefficient, the `k=1` first coefficient, and all
coefficients of the `k=m-1` block. -/
def lowerForwardWeightedContraction (m : ℕ) (θ : ParamSpace ℂ m) :=
  (lowerForwardMinor m θ).mulVec

-- @node: lowerReverseWeightedContraction
/-- The coordinate-reversed selected contraction rows. -/
def lowerReverseWeightedContraction (m : ℕ) (η : ParamSpace ℂ m) :=
  (lowerReverseMinor m η).mulVec

private lemma eval_lowerFirstPolynomial (m : ℕ) (θ : ParamSpace ℂ m)
    (j : Fin (m + 2)) :
    MvPolynomial.eval (paramEval θ) (lowerFirstPolynomial m j) =
      (forwardLoading m θ.1 θ.2.1 j).1 := by
  simp [lowerFirstPolynomial, forwardLoading]
  split_ifs <;> simp_all

private lemma eval_lowerSlopePolynomial (m : ℕ) (θ : ParamSpace ℂ m)
    (j : Fin (m + 2)) :
    MvPolynomial.eval (paramEval θ) (lowerSlopePolynomial m j) =
      (forwardLoading m θ.1 θ.2.1 j).2 := by
  simp [lowerSlopePolynomial, forwardLoading]
  split_ifs <;> simp [paramEval]

private lemma eval_lowerReverseFirstPolynomial (m : ℕ) (η : ParamSpace ℂ m)
    (j : Fin (m + 2)) :
    MvPolynomial.eval (paramEval η) (lowerReverseFirstPolynomial m j) =
      (reverseLoading m η.1 η.2.1 j).1 := by
  simp [lowerReverseFirstPolynomial, reverseLoading]
  split_ifs <;> simp [paramEval]

private lemma eval_lowerReverseSecondPolynomial (m : ℕ) (η : ParamSpace ℂ m)
    (j : Fin (m + 2)) :
    MvPolynomial.eval (paramEval η) (lowerReverseSecondPolynomial m j) =
      (reverseLoading m η.1 η.2.1 j).2 := by
  simp [lowerReverseSecondPolynomial, reverseLoading]
  split_ifs <;> simp_all

/-- Gives the stated evaluation formula for lower Forward Minor. -/
lemma lowerForwardMinor_apply (m : ℕ) (θ : ParamSpace ℂ m)
    (i j : Fin (m + 2)) :
    lowerForwardMinor m θ i j =
      if i.1 = 0 then θ.2.2 j (m + 2)
      else if i.1 = 1 then
        θ.2.2 j (m + 3) * (forwardLoading m θ.1 θ.2.1 j).1
      else θ.2.2 j (2 * m + 1) * ((m - 1).choose (i.1 - 2) : ℂ) *
        (forwardLoading m θ.1 θ.2.1 j).1 ^ (m - 1 - (i.1 - 2)) *
        (forwardLoading m θ.1 θ.2.1 j).2 ^ (i.1 - 2) := by
  unfold lowerForwardMinor
  rw [Matrix.map_apply]
  unfold lowerForwardContractionMinorPolynomial
  split_ifs <;> simp [lowerWeightPolynomial, paramEval,
    eval_lowerFirstPolynomial, eval_lowerSlopePolynomial]

/-- Gives the stated evaluation formula for lower Reverse Minor. -/
lemma lowerReverseMinor_apply (m : ℕ) (η : ParamSpace ℂ m)
    (i j : Fin (m + 2)) :
    lowerReverseMinor m η i j =
      if i.1 = 0 then η.2.2 j (m + 2)
      else if i.1 = 1 then
        η.2.2 j (m + 3) * (reverseLoading m η.1 η.2.1 j).2
      else η.2.2 j (2 * m + 1) * ((m - 1).choose (i.1 - 2) : ℂ) *
        (reverseLoading m η.1 η.2.1 j).1 ^ (i.1 - 2) *
        (reverseLoading m η.1 η.2.1 j).2 ^ (m - 1 - (i.1 - 2)) := by
  unfold lowerReverseMinor
  rw [Matrix.map_apply]
  unfold lowerReverseContractionMinorPolynomial
  split_ifs <;> simp [lowerWeightPolynomial, paramEval,
    eval_lowerReverseFirstPolynomial, eval_lowerReverseSecondPolynomial]

private lemma lowerForward_injective_of_det (m : ℕ) (hm : 3 ≤ m)
    (θ : ParamSpace ℂ m) (hdet : (lowerForwardMinor m θ).det ≠ 0) :
    Function.Injective (lowerForwardWeightedContraction m θ) := by
  intro e e' he
  change (lowerForwardMinor m θ).mulVec e = (lowerForwardMinor m θ).mulVec e' at he
  apply sub_eq_zero.mp
  apply Matrix.eq_zero_of_mulVec_eq_zero hdet
  change (lowerForwardMinor m θ).mulVec (e - e') = 0
  rw [Matrix.mulVec_sub, he, sub_self]

private lemma lowerReverse_injective_of_det (m : ℕ) (hm : 3 ≤ m)
    (η : ParamSpace ℂ m) (hdet : (lowerReverseMinor m η).det ≠ 0) :
    Function.Injective (lowerReverseWeightedContraction m η) := by
  intro e e' he
  change (lowerReverseMinor m η).mulVec e = (lowerReverseMinor m η).mulVec e' at he
  apply sub_eq_zero.mp
  apply Matrix.eq_zero_of_mulVec_eq_zero hdet
  change (lowerReverseMinor m η).mulVec (e - e') = 0
  rw [Matrix.mulVec_sub, he, sub_self]

private def lowerForwardWitness (m : ℕ) : ParamSpace ℂ m :=
  (1, (fun i => ((i.1 + 2 : ℕ) : ℂ)), fun j r =>
    if r = m + 2 then if j.1 = m + 1 then 1 else 0
    else if r = m + 3 then if j.1 = 0 then 1 else 0
    else if r = 2 * m + 1 then if 0 < j.1 ∧ j.1 < m + 1 then 1 else 0
    else 0)

private def lowerReverseWitness (m : ℕ) : ParamSpace ℂ m :=
  (((m + 1 : ℕ) : ℂ), (fun i => ((i.1 + 1 : ℕ) : ℂ)), fun j r =>
    if r = m + 2 then if j.1 = 0 then 1 else 0
    else if r = m + 3 then if j.1 = m + 1 then 1 else 0
    else if r = 2 * m + 1 then if 0 < j.1 ∧ j.1 < m + 1 then 1 else 0
    else 0)

private lemma lowerForwardWitness_loading_succ (m : ℕ) (i : Fin m) :
    forwardLoading m (lowerForwardWitness m).1 (lowerForwardWitness m).2.1
        i.succ.castSucc =
      (1, ((i.1 + 2 : ℕ) : ℂ)) := by
  simp [lowerForwardWitness, forwardLoading]
  omega

private lemma lowerReverseWitness_loading_succ (m : ℕ) (i : Fin m) :
    reverseLoading m (lowerReverseWitness m).1 (lowerReverseWitness m).2.1
        i.succ.castSucc =
      (((i.1 + 1 : ℕ) : ℂ), 1) := by
  simp [lowerReverseWitness, reverseLoading]
  omega

private lemma natSlope_injective (c : ℕ) {m : ℕ} :
    Function.Injective (fun i : Fin m => (((i.1 + c : ℕ) : ℂ))) := by
  intro i j h
  apply Fin.ext
  have : i.1 + c = j.1 + c := by
    apply Nat.cast_injective (R := ℂ)
    simpa only [Nat.cast_add] using h
  omega

private lemma lowerForwardWitness_row_zero_castSucc (m : ℕ) (j : Fin (m + 1)) :
    lowerForwardMinor m (lowerForwardWitness m) 0 j.castSucc = 0 := by
  simp [lowerForwardMinor_apply, lowerForwardWitness]
  omega

private lemma lowerForwardWitness_row_zero_last (m : ℕ) :
    lowerForwardMinor m (lowerForwardWitness m) 0 (Fin.last (m + 1)) = 1 := by
  simp [lowerForwardMinor_apply, lowerForwardWitness]

private lemma lowerForwardWitness_row_one_zero (m : ℕ) (hm : 3 ≤ m) :
    lowerForwardMinor m (lowerForwardWitness m) 1 0 = 1 := by
  simp [lowerForwardMinor_apply, lowerForwardWitness, forwardLoading]

private lemma lowerForwardWitness_row_one_succ (m : ℕ) (hm : 3 ≤ m)
    (j : Fin (m + 1)) :
    lowerForwardMinor m (lowerForwardWitness m) 1 j.succ = 0 := by
  simp [lowerForwardMinor_apply, lowerForwardWitness]

private lemma lowerForwardWitness_top_zero (m : ℕ) (hm : 3 ≤ m) (r : Fin m) :
    lowerForwardMinor m (lowerForwardWitness m) r.succ.succ 0 = 0 := by
  simp [lowerForwardMinor_apply, lowerForwardWitness]
  omega

private lemma lowerForwardWitness_top_succ (m : ℕ) (hm : 3 ≤ m)
    (r i : Fin m) :
    lowerForwardMinor m (lowerForwardWitness m) r.succ.succ i.succ.castSucc =
      ((m - 1).choose r.1 : ℂ) * (((i.1 + 2 : ℕ) : ℂ) ^ r.1) := by
  rw [lowerForwardMinor_apply]
  have hv : (r.succ.succ : Fin (m + 2)).val - 2 = r.val := by
    simp only [Fin.val_succ]
    omega
  have hind : i.succ.castSucc = i.castSucc.succ := by ext; simp
  rw [hind]
  simp [lowerForwardWitness, hv, show 2 * m ≠ m + 1 by omega,
    show 2 * m ≠ m + 2 by omega, show i.1 ≠ m by omega,
    forwardLoading]

private lemma lowerForwardWitness_top_last (m : ℕ) (hm : 3 ≤ m) (r : Fin m) :
    lowerForwardMinor m (lowerForwardWitness m) r.succ.succ (Fin.last (m + 1)) = 0 := by
  simp [lowerForwardMinor_apply, lowerForwardWitness]
  omega

private lemma lowerReverseWitness_row_zero_zero (m : ℕ) :
    lowerReverseMinor m (lowerReverseWitness m) 0 0 = 1 := by
  simp [lowerReverseMinor_apply, lowerReverseWitness]

private lemma lowerReverseWitness_row_zero_succ (m : ℕ) (j : Fin (m + 1)) :
    lowerReverseMinor m (lowerReverseWitness m) 0 j.succ = 0 := by
  simp [lowerReverseMinor_apply, lowerReverseWitness]

private lemma lowerReverseWitness_row_one_castSucc (m : ℕ) (hm : 3 ≤ m)
    (j : Fin (m + 1)) :
    lowerReverseMinor m (lowerReverseWitness m) 1 j.castSucc = 0 := by
  simp [lowerReverseMinor_apply, lowerReverseWitness, reverseLoading]
  omega

private lemma lowerReverseWitness_row_one_last (m : ℕ) (hm : 3 ≤ m) :
    lowerReverseMinor m (lowerReverseWitness m) 1 (Fin.last (m + 1)) = 1 := by
  simp [lowerReverseMinor_apply, lowerReverseWitness, reverseLoading]

private lemma lowerReverseWitness_top_zero (m : ℕ) (hm : 3 ≤ m) (r : Fin m) :
    lowerReverseMinor m (lowerReverseWitness m) r.succ.succ 0 = 0 := by
  simp [lowerReverseMinor_apply, lowerReverseWitness]
  omega

private lemma lowerReverseWitness_top_succ (m : ℕ) (hm : 3 ≤ m)
    (r i : Fin m) :
    lowerReverseMinor m (lowerReverseWitness m) r.succ.succ i.succ.castSucc =
      ((m - 1).choose r.1 : ℂ) * (((i.1 + 1 : ℕ) : ℂ) ^ r.1) := by
  rw [lowerReverseMinor_apply]
  have hv : (r.succ.succ : Fin (m + 2)).val - 2 = r.val := by
    simp only [Fin.val_succ]
    omega
  have hind : i.succ.castSucc = i.castSucc.succ := by ext; simp
  rw [hind]
  simp [lowerReverseWitness, hv, show 2 * m ≠ m + 1 by omega,
    show 2 * m ≠ m + 2 by omega, show i.1 ≠ m by omega,
    reverseLoading]

private lemma lowerReverseWitness_top_last (m : ℕ) (hm : 3 ≤ m) (r : Fin m) :
    lowerReverseMinor m (lowerReverseWitness m) r.succ.succ (Fin.last (m + 1)) = 0 := by
  simp [lowerReverseMinor_apply, lowerReverseWitness]
  omega

private lemma lowerForwardWitness_det_ne_zero (m : ℕ) (hm : 3 ≤ m) :
    (lowerForwardMinor m (lowerForwardWitness m)).det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  have hu : IsUnit (lowerForwardMinor m (lowerForwardWitness m)) :=
    (Matrix.mulVec_injective_iff_isUnit).mp (by
      intro e e' he
      have hlast : e (Fin.last (m + 1)) = e' (Fin.last (m + 1)) := by
        have h := congrFun he 0
        change (∑ j, lowerForwardMinor m (lowerForwardWitness m) 0 j * e j) =
          ∑ j, lowerForwardMinor m (lowerForwardWitness m) 0 j * e' j at h
        conv_lhs at h => rw [Fin.sum_univ_castSucc]
        conv_rhs at h => rw [Fin.sum_univ_castSucc]
        simpa only [lowerForwardWitness_row_zero_castSucc,
          lowerForwardWitness_row_zero_last, zero_mul, Finset.sum_const_zero,
          zero_add, one_mul] using h
      have hzero : e 0 = e' 0 := by
        have h := congrFun he 1
        change (∑ j, lowerForwardMinor m (lowerForwardWitness m) 1 j * e j) =
          ∑ j, lowerForwardMinor m (lowerForwardWitness m) 1 j * e' j at h
        conv_lhs at h => rw [Fin.sum_univ_succ]
        conv_rhs at h => rw [Fin.sum_univ_succ]
        simpa only [lowerForwardWitness_row_one_zero m hm,
          lowerForwardWitness_row_one_succ m hm, one_mul, zero_mul,
          Finset.sum_const_zero, add_zero] using h
      have hlatent : (fun i : Fin m => e i.succ.castSucc) =
          fun i => e' i.succ.castSucc := by
        have hsum : ∀ r : Fin m,
            ∑ i : Fin m, (e i.succ.castSucc - e' i.succ.castSucc) *
              (((i.1 + 2 : ℕ) : ℂ) ^ r.1) = 0 := by
          intro r
          have h := congrFun he r.succ.succ
          change (∑ j, lowerForwardMinor m (lowerForwardWitness m)
              r.succ.succ j * e j) =
            ∑ j, lowerForwardMinor m (lowerForwardWitness m)
              r.succ.succ j * e' j at h
          conv_lhs at h => rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
          conv_rhs at h => rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
          simp only [lowerForwardWitness_top_zero m hm,
            lowerForwardWitness_top_succ m hm,
            lowerForwardWitness_top_last m hm, zero_mul, zero_add, add_zero] at h
          rw [show (Fin.castSucc (0 : Fin (m + 1)) : Fin (m + 2)) = 0 by rfl,
            lowerForwardWitness_top_zero m hm r, zero_mul, zero_add] at h
          simp only [zero_mul, zero_add] at h
          have hc : ((m - 1).choose r.1 : ℂ) ≠ 0 := by
            exact_mod_cast (Nat.choose_pos (by omega : r.1 ≤ m - 1)).ne'
          have hfac : ((m - 1).choose r.1 : ℂ) *
                (∑ i : Fin m, e i.succ.castSucc * (((i.1 + 2 : ℕ) : ℂ) ^ r.1)) =
              ((m - 1).choose r.1 : ℂ) *
                ∑ i : Fin m, e' i.succ.castSucc * (((i.1 + 2 : ℕ) : ℂ) ^ r.1) := by
            simpa only [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using h
          have heq := mul_left_cancel₀ hc hfac
          calc
            ∑ i : Fin m, (e i.succ.castSucc - e' i.succ.castSucc) *
                (((i.1 + 2 : ℕ) : ℂ) ^ r.1) =
                (∑ i : Fin m, e i.succ.castSucc * (((i.1 + 2 : ℕ) : ℂ) ^ r.1)) -
                  ∑ i : Fin m, e' i.succ.castSucc * (((i.1 + 2 : ℕ) : ℂ) ^ r.1) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro i _
              ring
            _ = 0 := sub_eq_zero.mpr heq
        have hv : (fun i : Fin m => e i.succ.castSucc - e' i.succ.castSucc) = 0 := by
          apply Matrix.eq_zero_of_vecMul_eq_zero
            (Matrix.det_vandermonde_ne_zero_iff.mpr (natSlope_injective 2))
          funext r
          exact hsum r
        funext i
        exact sub_eq_zero.mp (congrFun hv i)
      funext j
      refine Fin.lastCases hlast (fun j' => Fin.cases hzero (fun i => ?_) j') j
      exact congrFun hlatent i)
  have hd := hu.map (Matrix.detMonoidHom (n := Fin (m + 2)) (R := ℂ))
  simpa only [Matrix.coe_detMonoidHom] using hd

private lemma lowerReverseWitness_det_ne_zero (m : ℕ) (hm : 3 ≤ m) :
    (lowerReverseMinor m (lowerReverseWitness m)).det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  have hu : IsUnit (lowerReverseMinor m (lowerReverseWitness m)) :=
    (Matrix.mulVec_injective_iff_isUnit).mp (by
      intro e e' he
      have hzero : e 0 = e' 0 := by
        have h := congrFun he 0
        change (∑ j, lowerReverseMinor m (lowerReverseWitness m) 0 j * e j) =
          ∑ j, lowerReverseMinor m (lowerReverseWitness m) 0 j * e' j at h
        conv_lhs at h => rw [Fin.sum_univ_succ]
        conv_rhs at h => rw [Fin.sum_univ_succ]
        simpa only [lowerReverseWitness_row_zero_zero,
          lowerReverseWitness_row_zero_succ, one_mul, zero_mul,
          Finset.sum_const_zero, add_zero] using h
      have hlast : e (Fin.last (m + 1)) = e' (Fin.last (m + 1)) := by
        have h := congrFun he 1
        change (∑ j, lowerReverseMinor m (lowerReverseWitness m) 1 j * e j) =
          ∑ j, lowerReverseMinor m (lowerReverseWitness m) 1 j * e' j at h
        conv_lhs at h => rw [Fin.sum_univ_castSucc]
        conv_rhs at h => rw [Fin.sum_univ_castSucc]
        simpa only [lowerReverseWitness_row_one_castSucc m hm,
          lowerReverseWitness_row_one_last m hm, zero_mul,
          Finset.sum_const_zero, zero_add, one_mul] using h
      have hlatent : (fun i : Fin m => e i.succ.castSucc) =
          fun i => e' i.succ.castSucc := by
        have hsum : ∀ r : Fin m,
            ∑ i : Fin m, (e i.succ.castSucc - e' i.succ.castSucc) *
              (((i.1 + 1 : ℕ) : ℂ) ^ r.1) = 0 := by
          intro r
          have h := congrFun he r.succ.succ
          change (∑ j, lowerReverseMinor m (lowerReverseWitness m)
              r.succ.succ j * e j) =
            ∑ j, lowerReverseMinor m (lowerReverseWitness m)
              r.succ.succ j * e' j at h
          conv_lhs at h => rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
          conv_rhs at h => rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
          simp only [lowerReverseWitness_top_zero m hm,
            lowerReverseWitness_top_succ m hm,
            lowerReverseWitness_top_last m hm, zero_mul, zero_add, add_zero] at h
          rw [show (Fin.castSucc (0 : Fin (m + 1)) : Fin (m + 2)) = 0 by rfl,
            lowerReverseWitness_top_zero m hm r, zero_mul, zero_add] at h
          simp only [zero_mul, zero_add] at h
          have hc : ((m - 1).choose r.1 : ℂ) ≠ 0 := by
            exact_mod_cast (Nat.choose_pos (by omega : r.1 ≤ m - 1)).ne'
          have hfac : ((m - 1).choose r.1 : ℂ) *
                (∑ i : Fin m, e i.succ.castSucc * (((i.1 + 1 : ℕ) : ℂ) ^ r.1)) =
              ((m - 1).choose r.1 : ℂ) *
                ∑ i : Fin m, e' i.succ.castSucc * (((i.1 + 1 : ℕ) : ℂ) ^ r.1) := by
            simpa only [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using h
          have heq := mul_left_cancel₀ hc hfac
          calc
            ∑ i : Fin m, (e i.succ.castSucc - e' i.succ.castSucc) *
                (((i.1 + 1 : ℕ) : ℂ) ^ r.1) =
                (∑ i : Fin m, e i.succ.castSucc * (((i.1 + 1 : ℕ) : ℂ) ^ r.1)) -
                  ∑ i : Fin m, e' i.succ.castSucc * (((i.1 + 1 : ℕ) : ℂ) ^ r.1) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro i _
              ring
            _ = 0 := sub_eq_zero.mpr heq
        have hv : (fun i : Fin m => e i.succ.castSucc - e' i.succ.castSucc) = 0 := by
          apply Matrix.eq_zero_of_vecMul_eq_zero
            (Matrix.det_vandermonde_ne_zero_iff.mpr (natSlope_injective 1))
          funext r
          exact hsum r
        funext i
        exact sub_eq_zero.mp (congrFun hv i)
      funext j
      refine Fin.lastCases hlast (fun j' => Fin.cases hzero (fun i => ?_) j') j
      exact congrFun hlatent i)
  have hd := hu.map (Matrix.detMonoidHom (n := Fin (m + 2)) (R := ℂ))
  simpa only [Matrix.coe_detMonoidHom] using hd

-- @node: lowerForwardExplicitRankData
/-- Proves the stated mathematical property of lower Forward Explicit Rank Data. -/
theorem lowerForwardExplicitRankData (m : ℕ) (hm : 3 ≤ m) :
    lowerForwardComplexRankPolynomial m ≠ 0 ∧
      (∃ θ₀ : ParamSpace ℂ m,
        (∀ j r, (r < 2 ∨ 2 * m + 1 < r) → θ₀.2.2 j r = 0) ∧
        MvPolynomial.eval (paramEval θ₀) (lowerForwardComplexRankPolynomial m) ≠ 0) ∧
      ∀ θ, MvPolynomial.eval (paramEval θ) (lowerForwardComplexRankPolynomial m) ≠ 0 →
        Function.Injective (lowerForwardWeightedContraction m θ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    apply lowerForwardWitness_det_ne_zero m hm
    change Matrix.det ((MvPolynomial.eval (paramEval (lowerForwardWitness m))).mapMatrix
      (lowerForwardContractionMinorPolynomial ℂ m)) = 0
    rw [← RingHom.map_det, show (lowerForwardContractionMinorPolynomial ℂ m).det = 0 by
      simpa [lowerForwardComplexRankPolynomial] using hz, map_zero]
  · refine ⟨lowerForwardWitness m, ?_, ?_⟩
    · intro j r hr
      simp only [lowerForwardWitness]
      rcases hr with hr | hr <;> simp [show r ≠ m + 2 by omega,
        show r ≠ m + 3 by omega, show r ≠ 2 * m + 1 by omega]
    · rw [lowerForwardComplexRankPolynomial, RingHom.map_det]
      change (lowerForwardMinor m (lowerForwardWitness m)).det ≠ 0
      exact lowerForwardWitness_det_ne_zero m hm
  · intro θ hθ
    apply lowerForward_injective_of_det m hm θ
    change Matrix.det ((MvPolynomial.eval (paramEval θ)).mapMatrix
      (lowerForwardContractionMinorPolynomial ℂ m)) ≠ 0
    rw [← RingHom.map_det]
    simpa [lowerForwardComplexRankPolynomial] using hθ

-- @node: lowerReverseExplicitRankData
/-- Proves the stated mathematical property of lower Reverse Explicit Rank Data. -/
theorem lowerReverseExplicitRankData (m : ℕ) (hm : 3 ≤ m) :
    lowerReverseComplexRankPolynomial m ≠ 0 ∧
      (∃ η₀ : ParamSpace ℂ m,
        (∀ j r, (r < 2 ∨ 2 * m + 1 < r) → η₀.2.2 j r = 0) ∧
        MvPolynomial.eval (paramEval η₀) (lowerReverseComplexRankPolynomial m) ≠ 0) ∧
      ∀ η, MvPolynomial.eval (paramEval η) (lowerReverseComplexRankPolynomial m) ≠ 0 →
        Function.Injective (lowerReverseWeightedContraction m η) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    apply lowerReverseWitness_det_ne_zero m hm
    change Matrix.det ((MvPolynomial.eval (paramEval (lowerReverseWitness m))).mapMatrix
      (lowerReverseContractionMinorPolynomial ℂ m)) = 0
    rw [← RingHom.map_det, show (lowerReverseContractionMinorPolynomial ℂ m).det = 0 by
      simpa [lowerReverseComplexRankPolynomial] using hz, map_zero]
  · refine ⟨lowerReverseWitness m, ?_, ?_⟩
    · intro j r hr
      simp only [lowerReverseWitness]
      rcases hr with hr | hr <;> simp [show r ≠ m + 2 by omega,
        show r ≠ m + 3 by omega, show r ≠ 2 * m + 1 by omega]
    · rw [lowerReverseComplexRankPolynomial, RingHom.map_det]
      change (lowerReverseMinor m (lowerReverseWitness m)).det ≠ 0
      exact lowerReverseWitness_det_ne_zero m hm
  · intro η hη
    apply lowerReverse_injective_of_det m hm η
    change Matrix.det ((MvPolynomial.eval (paramEval η)).mapMatrix
      (lowerReverseContractionMinorPolynomial ℂ m)) ≠ 0
    rw [← RingHom.map_det]
    simpa [lowerReverseComplexRankPolynomial] using hη

-- @node: lowerForwardRealRankPolynomial_ne_zero
/-- Proves that the quantity called the lower Forward Real Rank Polynomial is nonzero. -/
theorem lowerForwardRealRankPolynomial_ne_zero (m : ℕ) (hm : 3 ≤ m) :
    lowerForwardRealRankPolynomial m ≠ 0 := by
  intro h
  exact (lowerForwardExplicitRankData m hm).1
    (by rw [← lowerForwardRankPolynomial_map_ofReal, h, map_zero])

-- @node: lowerReverseRealRankPolynomial_ne_zero
/-- Proves that the quantity called the lower Reverse Real Rank Polynomial is nonzero. -/
theorem lowerReverseRealRankPolynomial_ne_zero (m : ℕ) (hm : 3 ≤ m) :
    lowerReverseRealRankPolynomial m ≠ 0 := by
  intro h
  exact (lowerReverseExplicitRankData m hm).1
    (by rw [← lowerReverseRankPolynomial_map_ofReal, h, map_zero])

-- @node: lowerForwardContractionRankWitness
/-- Proves the stated mathematical property of lower Forward Contraction Rank Witness. -/
theorem lowerForwardContractionRankWitness (m : ℕ) (hm : 3 ≤ m) :
    ∃ P : MvPolynomial (ParamCoord m) ℂ, P ≠ 0 ∧
      (∃ θ₀ : ParamSpace ℂ m,
        (∀ j r, (r < 2 ∨ 2 * m + 1 < r) → θ₀.2.2 j r = 0) ∧
        MvPolynomial.eval (paramEval θ₀) P ≠ 0) ∧
      ∀ θ, MvPolynomial.eval (paramEval θ) P ≠ 0 →
        Function.Injective (lowerForwardWeightedContraction m θ) := by
  let P := lowerForwardComplexRankPolynomial m
  refine ⟨P, ?_, ?_, ?_⟩
  · intro hz
    dsimp [P, lowerForwardComplexRankPolynomial] at hz
    apply lowerForwardWitness_det_ne_zero m hm
    change Matrix.det ((MvPolynomial.eval (paramEval (lowerForwardWitness m))).mapMatrix
      (lowerForwardContractionMinorPolynomial ℂ m)) = 0
    rw [← RingHom.map_det, hz, map_zero]
  · refine ⟨lowerForwardWitness m, ?_, ?_⟩
    · intro j r hr
      simp only [lowerForwardWitness]
      rcases hr with hr | hr <;> simp [show r ≠ m + 2 by omega,
        show r ≠ m + 3 by omega, show r ≠ 2 * m + 1 by omega]
    · dsimp [P, lowerForwardComplexRankPolynomial]
      rw [RingHom.map_det]
      change (lowerForwardMinor m (lowerForwardWitness m)).det ≠ 0
      exact lowerForwardWitness_det_ne_zero m hm
  · intro θ hθ
    apply lowerForward_injective_of_det m hm θ
    change Matrix.det ((MvPolynomial.eval (paramEval θ)).mapMatrix
      (lowerForwardContractionMinorPolynomial ℂ m)) ≠ 0
    rw [← RingHom.map_det]
    exact hθ

-- @node: lowerReverseContractionRankWitness
/-- Proves the stated mathematical property of lower Reverse Contraction Rank Witness. -/
theorem lowerReverseContractionRankWitness (m : ℕ) (hm : 3 ≤ m) :
    ∃ P : MvPolynomial (ParamCoord m) ℂ, P ≠ 0 ∧
      (∃ η₀ : ParamSpace ℂ m,
        (∀ j r, (r < 2 ∨ 2 * m + 1 < r) → η₀.2.2 j r = 0) ∧
        MvPolynomial.eval (paramEval η₀) P ≠ 0) ∧
      ∀ η, MvPolynomial.eval (paramEval η) P ≠ 0 →
        Function.Injective (lowerReverseWeightedContraction m η) := by
  let P := lowerReverseComplexRankPolynomial m
  refine ⟨P, ?_, ?_, ?_⟩
  · intro hz
    dsimp [P, lowerReverseComplexRankPolynomial] at hz
    apply lowerReverseWitness_det_ne_zero m hm
    change Matrix.det ((MvPolynomial.eval (paramEval (lowerReverseWitness m))).mapMatrix
      (lowerReverseContractionMinorPolynomial ℂ m)) = 0
    rw [← RingHom.map_det, hz, map_zero]
  · refine ⟨lowerReverseWitness m, ?_, ?_⟩
    · intro j r hr
      simp only [lowerReverseWitness]
      rcases hr with hr | hr <;> simp [show r ≠ m + 2 by omega,
        show r ≠ m + 3 by omega, show r ≠ 2 * m + 1 by omega]
    · dsimp [P, lowerReverseComplexRankPolynomial]
      rw [RingHom.map_det]
      change (lowerReverseMinor m (lowerReverseWitness m)).det ≠ 0
      exact lowerReverseWitness_det_ne_zero m hm
  · intro η hη
    apply lowerReverse_injective_of_det m hm η
    change Matrix.det ((MvPolynomial.eval (paramEval η)).mapMatrix
      (lowerReverseContractionMinorPolynomial ℂ m)) ≠ 0
    rw [← RingHom.map_det]
    exact hη

end

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
