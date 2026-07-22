/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Lower-order apolar separation

The reusable proof step isolated from the resolved information-order theorem.
For `m ≥ 3`, the stacked contractions available through order `2m+1` already
recover the degree-`m+2` support annihilator generically, so the fixed vertical
and horizontal axes exclude every full opposite-arrow fiber.
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Selector
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.LowerOrderEmptyFiber
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.MomentGate

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

noncomputable section

-- @node: lowerSlopeProductPolynomial
/-- Defines the polynomial called the lower Slope Product Polynomial. -/
def lowerSlopeProductPolynomial (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial (ParamCoord m) R :=
  ∏ i : Fin m, MvPolynomial.X (Sum.inr (Sum.inl i))

-- @node: lowerForwardRealExceptionalPolynomial
/-- Defines the polynomial called the lower Forward Real Exceptional Polynomial. -/
def lowerForwardRealExceptionalPolynomial (m : ℕ) :
    MvPolynomial (RealParamCoord m) ℝ :=
  lowerSlopeProductPolynomial ℝ m * lowerForwardRealRankPolynomial m

-- @node: lowerReverseRealExceptionalPolynomial
/-- Defines the polynomial called the lower Reverse Real Exceptional Polynomial. -/
def lowerReverseRealExceptionalPolynomial (m : ℕ) :
    MvPolynomial (RealParamCoord m) ℝ :=
  lowerSlopeProductPolynomial ℝ m * lowerReverseRealRankPolynomial m

-- @node: lowerForwardComplexExceptionalPolynomial
/-- Defines the polynomial called the lower Forward Complex Exceptional Polynomial. -/
def lowerForwardComplexExceptionalPolynomial (m : ℕ) :
    MvPolynomial (ParamCoord m) ℂ :=
  lowerSlopeProductPolynomial ℂ m * lowerForwardComplexRankPolynomial m

-- @node: lowerReverseComplexExceptionalPolynomial
/-- Defines the polynomial called the lower Reverse Complex Exceptional Polynomial. -/
def lowerReverseComplexExceptionalPolynomial (m : ℕ) :
    MvPolynomial (ParamCoord m) ℂ :=
  lowerSlopeProductPolynomial ℂ m * lowerReverseComplexRankPolynomial m

-- @node: lowerSlopeProductPolynomial_ne_zero
/-- Proves that the quantity called the lower Slope Product Polynomial is nonzero. -/
lemma lowerSlopeProductPolynomial_ne_zero (R : Type*) [CommRing R] [IsDomain R] (m : ℕ) :
    lowerSlopeProductPolynomial R m ≠ 0 := by
  rw [lowerSlopeProductPolynomial]
  exact Finset.prod_ne_zero_iff.mpr
    (fun i _ => MvPolynomial.X_ne_zero (Sum.inr (Sum.inl i)))

-- @node: lowerForwardRealExceptionalPolynomial_ne_zero
/-- Proves that the quantity called the lower Forward Real Exceptional Polynomial is nonzero. -/
lemma lowerForwardRealExceptionalPolynomial_ne_zero (m : ℕ) (hm : 3 ≤ m) :
    lowerForwardRealExceptionalPolynomial m ≠ 0 := by
  exact mul_ne_zero (lowerSlopeProductPolynomial_ne_zero ℝ m)
    (lowerForwardRealRankPolynomial_ne_zero m hm)

-- @node: lowerReverseRealExceptionalPolynomial_ne_zero
/-- Proves that the quantity called the lower Reverse Real Exceptional Polynomial is nonzero. -/
lemma lowerReverseRealExceptionalPolynomial_ne_zero (m : ℕ) (hm : 3 ≤ m) :
    lowerReverseRealExceptionalPolynomial m ≠ 0 := by
  exact mul_ne_zero (lowerSlopeProductPolynomial_ne_zero ℝ m)
    (lowerReverseRealRankPolynomial_ne_zero m hm)

-- @node: lowerForwardExceptional_eval_complexify
/-- Gives the stated evaluation formula for lower Forward Exceptional complexify. -/
lemma lowerForwardExceptional_eval_complexify (m : ℕ) (θ : ParamSpace ℝ m) :
    MvPolynomial.eval (paramEval (complexifyParam θ))
        (lowerForwardComplexExceptionalPolynomial m) =
      (MvPolynomial.eval (realParamEval θ)
        (lowerForwardRealExceptionalPolynomial m) : ℂ) := by
  rw [lowerForwardComplexExceptionalPolynomial, lowerForwardRealExceptionalPolynomial,
    MvPolynomial.eval_mul, MvPolynomial.eval_mul,
    lowerForwardRankPolynomial_eval_complexify]
  simp [lowerSlopeProductPolynomial, paramEval, realParamEval, complexifyParam]

-- @node: lowerReverseExceptional_eval_complexify
/-- Gives the stated evaluation formula for lower Reverse Exceptional complexify. -/
lemma lowerReverseExceptional_eval_complexify (m : ℕ) (η : ParamSpace ℝ m) :
    MvPolynomial.eval (paramEval (complexifyParam η))
        (lowerReverseComplexExceptionalPolynomial m) =
      (MvPolynomial.eval (realParamEval η)
        (lowerReverseRealExceptionalPolynomial m) : ℂ) := by
  rw [lowerReverseComplexExceptionalPolynomial, lowerReverseRealExceptionalPolynomial,
    MvPolynomial.eval_mul, MvPolynomial.eval_mul,
    lowerReverseRankPolynomial_eval_complexify]
  simp [lowerSlopeProductPolynomial, paramEval, realParamEval, complexifyParam]

-- @node: forwardSlopesInjective_of_realFeasible
/-- Proves the stated mathematical property of forward Slopes Injective of real Feasible. -/
lemma forwardSlopesInjective_of_realFeasible {m L : ℕ} (θ : ParamSpace ℝ m)
    (hθ : θ ∈ realFeasibleRegion m L) :
    Function.Injective (fun j : Fin (m + 1) =>
      (forwardLoading m (complexifyParam θ).1 (complexifyParam θ).2.1 j.castSucc).2) := by
  have hγρ : ∀ k : Fin m, θ.1 ≠ θ.2.1 k := by
    intro k heq
    have hv : (Fin.cons θ.1 θ.2.1 : Fin (m + 1) → ℝ) 0 =
        (Fin.cons θ.1 θ.2.1 : Fin (m + 1) → ℝ) k.succ := by
      simpa only [Fin.cons_zero, Fin.cons_succ] using heq
    have he : (0 : Fin (m + 1)) = k.succ := hθ.2.1 hv
    have := congrArg Fin.val he
    simp at this
  have hρ : Function.Injective θ.2.1 := by
    intro k l heq
    have hv : (Fin.cons θ.1 θ.2.1 : Fin (m + 1) → ℝ) k.succ =
        (Fin.cons θ.1 θ.2.1 : Fin (m + 1) → ℝ) l.succ := by
      simpa only [Fin.cons_succ] using heq
    have he := hθ.2.1 hv
    exact Fin.ext (by simpa using congrArg Fin.val he)
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · intro j h
    refine Fin.cases (fun _ => rfl) (fun l h' => ?_) j h
    have hl : l.val ≠ m := Nat.ne_of_lt l.isLt
    exact ((hγρ l)
      (by simpa [forwardLoading, complexifyParam, hl] using h')).elim
  · intro j h
    have hk : k.val ≠ m := Nat.ne_of_lt k.isLt
    refine Fin.cases (fun h' => ?_) (fun l h' => ?_) j h
    · exact ((hγρ k)
        (by simpa [forwardLoading, complexifyParam, hk] using h'.symm)).elim
    · have hl : l.val ≠ m := Nat.ne_of_lt l.isLt
      exact congrArg Fin.succ (hρ
        (by simpa [forwardLoading, complexifyParam, hk, hl] using h'))

-- @node: reverseSlopesInjective_of_realFeasible
/-- Proves the stated mathematical property of reverse Slopes Injective of real Feasible. -/
lemma reverseSlopesInjective_of_realFeasible {m L : ℕ} (η : ParamSpace ℝ m)
    (hη : η ∈ realFeasibleRegion m L) :
    Function.Injective (fun j : Fin (m + 1) =>
      (reverseLoading m (complexifyParam η).1 (complexifyParam η).2.1 j.succ).1) := by
  have hδσ : ∀ k : Fin m, η.1 ≠ η.2.1 k := by
    intro k heq
    have hv : (Fin.cons η.1 η.2.1 : Fin (m + 1) → ℝ) 0 =
        (Fin.cons η.1 η.2.1 : Fin (m + 1) → ℝ) k.succ := by
      simpa only [Fin.cons_zero, Fin.cons_succ] using heq
    have he : (0 : Fin (m + 1)) = k.succ := hη.2.1 hv
    have := congrArg Fin.val he
    simp at this
  have hσ : Function.Injective η.2.1 := by
    intro k l heq
    have hv : (Fin.cons η.1 η.2.1 : Fin (m + 1) → ℝ) k.succ =
        (Fin.cons η.1 η.2.1 : Fin (m + 1) → ℝ) l.succ := by
      simpa only [Fin.cons_succ] using heq
    have he := hη.2.1 hv
    exact Fin.ext (by simpa using congrArg Fin.val he)
  intro i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · intro j h
    refine Fin.lastCases (fun _ => rfl) (fun l h' => ?_) j h
    have hl : l.val ≠ m := Nat.ne_of_lt l.isLt
    exact ((hδσ l) (by simpa [reverseLoading, complexifyParam, hl] using h')).elim
  · intro j h
    have hk : k.val ≠ m := Nat.ne_of_lt k.isLt
    refine Fin.lastCases (fun h' => ?_) (fun l h' => ?_) j h
    · exact ((hδσ k)
        (by simpa [reverseLoading, complexifyParam, hk] using h'.symm)).elim
    · have hl : l.val ≠ m := Nat.ne_of_lt l.isLt
      exact congrArg Fin.castSucc (hσ
        (by simpa [reverseLoading, complexifyParam, hk, hl] using h'))

-- @node: forwardCumulantMap_complexify
/-- Proves the stated compatibility of forward Cumulant Map with complexification. -/
lemma forwardCumulantMap_complexify {m L : ℕ} (θ : ParamSpace ℝ m) :
    forwardCumulantMap m L (complexifyParam θ) =
      fun r a => ((forwardCumulantMap m L θ r a : ℝ) : ℂ) := by
  funext r a
  unfold forwardCumulantMap
  split_ifs with h
  · change (∑ j : Fin (m + 2),
        (complexifyParam θ).2.2 j r *
          (forwardLoading m (complexifyParam θ).1
            (complexifyParam θ).2.1 j).1 ^ (r - a) *
          (forwardLoading m (complexifyParam θ).1
            (complexifyParam θ).2.1 j).2 ^ a) =
      Complex.ofRealHom (∑ j : Fin (m + 2),
        θ.2.2 j r * (forwardLoading m θ.1 θ.2.1 j).1 ^ (r - a) *
          (forwardLoading m θ.1 θ.2.1 j).2 ^ a)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj0 : j = 0
    · subst j
      simp [complexifyParam, forwardLoading]
    by_cases hjlast : j.val = m + 1
    · simp [complexifyParam, forwardLoading, hjlast]
    · simp [complexifyParam, forwardLoading, hj0, hjlast]
  · simp

-- @node: reverseCumulantMap_complexify
/-- Proves the stated compatibility of reverse Cumulant Map with complexification. -/
lemma reverseCumulantMap_complexify {m L : ℕ} (η : ParamSpace ℝ m) :
    reverseCumulantMap m L (complexifyParam η) =
      fun r a => ((reverseCumulantMap m L η r a : ℝ) : ℂ) := by
  funext r a
  unfold reverseCumulantMap
  split_ifs with h
  · change (∑ j : Fin (m + 2),
        (complexifyParam η).2.2 j r *
          (reverseLoading m (complexifyParam η).1
            (complexifyParam η).2.1 j).1 ^ (r - a) *
          (reverseLoading m (complexifyParam η).1
            (complexifyParam η).2.1 j).2 ^ a) =
      Complex.ofRealHom (∑ j : Fin (m + 2),
        η.2.2 j r * (reverseLoading m η.1 η.2.1 j).1 ^ (r - a) *
          (reverseLoading m η.1 η.2.1 j).2 ^ a)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj0 : j = 0
    · subst j
      simp [complexifyParam, reverseLoading]
    by_cases hjlast : j.val = m + 1
    · simp [complexifyParam, reverseLoading, hjlast]
    · simp [complexifyParam, reverseLoading, hj0, hjlast]
  · simp

-- @node: lowerOrderApolarSeparation
/-- At `m ≥ 3`, the complete cumulant truncation through order `2m+1`
generically separates the two real arrows. -/
theorem lowerOrderApolarSeparation (m : ℕ) (hm : 3 ≤ m) :
    separatesAtOrder m (2 * m + 1) := by
  have hgate : TruncatedMomentInterior (2 * m + 1) :=
    truncatedMomentInterior (2 * m + 1)
  obtain ⟨hPf_ne, ⟨θf0, hθf0_pin, hθf0_ne⟩, hPf_inj⟩ :=
    lowerForwardExplicitRankData m hm
  obtain ⟨hPr_ne, ⟨θr0, hθr0_pin, hθr0_ne⟩, hPr_inj⟩ :=
    lowerReverseExplicitRankData m hm
  let ρprod : MvPolynomial (ParamCoord m) ℂ := lowerSlopeProductPolynomial ℂ m
  let Rf := lowerForwardComplexExceptionalPolynomial m
  let Rr := lowerReverseComplexExceptionalPolynomial m
  have hpinρ : pinSubst m (2 * m + 1) ρprod ≠ 0 := by
    dsimp [ρprod, lowerSlopeProductPolynomial]
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => by
      rw [pinSubst_X_slope]
      exact MvPolynomial.X_ne_zero _)
  have hpinRf : pinSubst m (2 * m + 1) Rf ≠ 0 := by
    dsimp [Rf, lowerForwardComplexExceptionalPolynomial]
    rw [map_mul]
    exact mul_ne_zero hpinρ
      (pinSubst_ne_zero_of_pinned_witness
        (lowerForwardComplexRankPolynomial m) θf0 hθf0_pin hθf0_ne)
  have hpinRr : pinSubst m (2 * m + 1) Rr ≠ 0 := by
    dsimp [Rr, lowerReverseComplexExceptionalPolynomial]
    rw [map_mul]
    exact mul_ne_zero hpinρ
      (pinSubst_ne_zero_of_pinned_witness
        (lowerReverseComplexRankPolynomial m) θr0 hθr0_pin hθr0_ne)
  constructor
  · let excl : Set (ParamSpace ℝ m) :=
      {θ | MvPolynomial.eval (realParamEval θ)
        (lowerForwardRealExceptionalPolynomial m) = 0}
    refine ⟨excl, ?_, ?_, ?_⟩
    · exact ⟨lowerForwardRealExceptionalPolynomial m,
        lowerForwardRealExceptionalPolynomial_ne_zero m hm, rfl⟩
    · obtain ⟨θ, hθfeas, hθR⟩ := exists_feasible_nonvanishing hgate Rf hpinRf
      refine ⟨θ, hθfeas, ?_⟩
      change MvPolynomial.eval (realParamEval θ)
        (lowerForwardRealExceptionalPolynomial m) ≠ 0
      intro hz
      apply hθR
      dsimp [Rf]
      rw [lowerForwardExceptional_eval_complexify, hz]
      simp
    · intro θ hθfeas hθout
      change MvPolynomial.eval (realParamEval θ)
        (lowerForwardRealExceptionalPolynomial m) ≠ 0 at hθout
      have hθR : MvPolynomial.eval (paramEval (complexifyParam θ)) Rf ≠ 0 := by
        dsimp [Rf]
        rw [lowerForwardExceptional_eval_complexify]
        exact Complex.ofReal_ne_zero.mpr hθout
      have hparts :
          MvPolynomial.eval (paramEval (complexifyParam θ)) ρprod ≠ 0 ∧
          MvPolynomial.eval (paramEval (complexifyParam θ))
            (lowerForwardComplexRankPolynomial m) ≠ 0 := by
        dsimp [Rf, lowerForwardComplexExceptionalPolynomial] at hθR
        rw [MvPolynomial.eval_mul] at hθR
        exact mul_ne_zero_iff.mp hθR
      have hρ : ∀ i, (complexifyParam θ).2.1 i ≠ 0 := by
        have hp : (∏ i : Fin m, (complexifyParam θ).2.1 i) ≠ 0 := by
          simpa [ρprod, lowerSlopeProductPolynomial, paramEval] using hparts.1
        exact fun i => (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
      have hγ : (complexifyParam θ).1 ≠ 0 := by
        simpa [complexifyParam] using Complex.ofReal_ne_zero.mpr hθfeas.1
      have hslopes := forwardSlopesInjective_of_realFeasible θ hθfeas
      have hnonzero : ∀ j : Fin (m + 1),
          (forwardLoading m (complexifyParam θ).1
            (complexifyParam θ).2.1 j.castSucc).2 ≠ 0 := by
        intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · simpa [forwardLoading] using hγ
        · have hi : i.val ≠ m := Nat.ne_of_lt i.isLt
          simpa [forwardLoading, hi] using hρ i
      have hrank := hPf_inj (complexifyParam θ) hparts.2
      intro hex
      obtain ⟨η, _hηfeas, heq⟩ := hex
      apply lowerForwardReverseImpossible m hm (complexifyParam θ)
        hslopes hγ hρ hnonzero hrank (complexifyParam η)
      rw [forwardCumulantMap_complexify, reverseCumulantMap_complexify]
      exact congrArg (fun t : CumVec ℝ => fun r a => (t r a : ℂ)) heq
  · let excl : Set (ParamSpace ℝ m) :=
      {η | MvPolynomial.eval (realParamEval η)
        (lowerReverseRealExceptionalPolynomial m) = 0}
    refine ⟨excl, ?_, ?_, ?_⟩
    · exact ⟨lowerReverseRealExceptionalPolynomial m,
        lowerReverseRealExceptionalPolynomial_ne_zero m hm, rfl⟩
    · obtain ⟨η, hηfeas, hηR⟩ := exists_feasible_nonvanishing hgate Rr hpinRr
      refine ⟨η, hηfeas, ?_⟩
      change MvPolynomial.eval (realParamEval η)
        (lowerReverseRealExceptionalPolynomial m) ≠ 0
      intro hz
      apply hηR
      dsimp [Rr]
      rw [lowerReverseExceptional_eval_complexify, hz]
      simp
    · intro η hηfeas hηout
      change MvPolynomial.eval (realParamEval η)
        (lowerReverseRealExceptionalPolynomial m) ≠ 0 at hηout
      have hηR : MvPolynomial.eval (paramEval (complexifyParam η)) Rr ≠ 0 := by
        dsimp [Rr]
        rw [lowerReverseExceptional_eval_complexify]
        exact Complex.ofReal_ne_zero.mpr hηout
      have hparts :
          MvPolynomial.eval (paramEval (complexifyParam η)) ρprod ≠ 0 ∧
          MvPolynomial.eval (paramEval (complexifyParam η))
            (lowerReverseComplexRankPolynomial m) ≠ 0 := by
        dsimp [Rr, lowerReverseComplexExceptionalPolynomial] at hηR
        rw [MvPolynomial.eval_mul] at hηR
        exact mul_ne_zero_iff.mp hηR
      have hσ : ∀ i, (complexifyParam η).2.1 i ≠ 0 := by
        have hp : (∏ i : Fin m, (complexifyParam η).2.1 i) ≠ 0 := by
          simpa [ρprod, lowerSlopeProductPolynomial, paramEval] using hparts.1
        exact fun i => (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
      have hδ : (complexifyParam η).1 ≠ 0 := by
        simpa [complexifyParam] using Complex.ofReal_ne_zero.mpr hηfeas.1
      have hslopes := reverseSlopesInjective_of_realFeasible η hηfeas
      have hnonzero : ∀ j : Fin (m + 1),
          (reverseLoading m (complexifyParam η).1
            (complexifyParam η).2.1 j.succ).1 ≠ 0 := by
        intro j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simpa [reverseLoading] using hδ
        · have hi : i.val ≠ m := Nat.ne_of_lt i.isLt
          simpa [reverseLoading, hi] using hσ i
      have hrank := hPr_inj (complexifyParam η) hparts.2
      intro hex
      obtain ⟨θ, _hθfeas, heq⟩ := hex
      apply lowerReverseForwardImpossible m hm (complexifyParam η)
        hslopes hδ hσ hnonzero hrank (complexifyParam θ)
      rw [reverseCumulantMap_complexify, forwardCumulantMap_complexify]
      exact congrArg (fun t : CumVec ℝ => fun r a => (t r a : ℂ)) heq

end

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
