/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The one-dimensional kernel for the shorter apolar stack
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.LowerOrderApolarRank
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.EmptyFiber

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

noncomputable section

@[simp] private lemma lowerKernel_binaryDehom_C (c : ℂ) :
    binaryDehom (MvPolynomial.C c) = Polynomial.C c := by
  simp [binaryDehom]

private lemma lowerKernel_coeff_zero (u : ℂ × ℂ) :
    (binaryDehom (linForm u)).coeff 0 = u.1 := by
  simpa using coeff_binaryDehom_linForm_pow' u 1 0

private lemma lowerKernel_coeff_one (u : ℂ × ℂ) :
    (binaryDehom (linForm u)).coeff 1 = u.2 := by
  simpa using coeff_binaryDehom_linForm_pow' u 1 1

-- @node: lowerForwardStackEquation
private lemma lowerForwardStackEquation (m : ℕ) (hm : 3 ≤ m)
    (θ : ParamSpace ℂ m) (q : MvPolynomial (Fin 2) ℂ)
    (hq : q.IsHomogeneous (m + 2))
    (hcon : ∀ k, k ≤ m - 1 → diffApply q
      (dividedPowerBlock (forwardCumulantMap m (2 * m + 1) θ) (m + 2 + k)) = 0) :
    ∀ k, k ≤ m - 1 →
      ∑ j : Fin (m + 2),
        MvPolynomial.C (θ.2.2 j (m + 2 + k)) *
          MvPolynomial.C (evalAtDir q (forwardLoading m θ.1 θ.2.1 j)) *
          linForm (forwardLoading m θ.1 θ.2.1 j) ^ k = 0 := by
  intro k hk
  have h := hcon k hk
  rw [dividedPowerBlock_forward_eq_sum_linForm_pow m (2 * m + 1) (m + 2 + k) θ
    (by omega) (by omega), diffApply_sum] at h
  simp_rw [diffApply_C_mul, diffApply_linForm_pow q hq] at h
  have hfac : (Nat.descFactorial (m + 2 + k) (m + 2) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      (Nat.descFactorial_pos.mpr (by omega : m + 2 ≤ m + 2 + k))
  apply (mul_eq_zero.mp ?_).resolve_left (MvPolynomial.C_ne_zero.mpr hfac)
  rw [Finset.mul_sum]
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  ring

-- @node: lowerReverseStackEquation
private lemma lowerReverseStackEquation (m : ℕ) (hm : 3 ≤ m)
    (η : ParamSpace ℂ m) (q : MvPolynomial (Fin 2) ℂ)
    (hq : q.IsHomogeneous (m + 2))
    (hcon : ∀ k, k ≤ m - 1 → diffApply q
      (dividedPowerBlock (reverseCumulantMap m (2 * m + 1) η) (m + 2 + k)) = 0) :
    ∀ k, k ≤ m - 1 →
      ∑ j : Fin (m + 2),
        MvPolynomial.C (η.2.2 j (m + 2 + k)) *
          MvPolynomial.C (evalAtDir q (reverseLoading m η.1 η.2.1 j)) *
          linForm (reverseLoading m η.1 η.2.1 j) ^ k = 0 := by
  intro k hk
  have h := hcon k hk
  rw [dividedPowerBlock_reverse_eq_sum_linForm_pow m (2 * m + 1) (m + 2 + k) η
    (by omega) (by omega), diffApply_sum] at h
  simp_rw [diffApply_C_mul, diffApply_linForm_pow q hq] at h
  have hfac : (Nat.descFactorial (m + 2 + k) (m + 2) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      (Nat.descFactorial_pos.mpr (by omega : m + 2 ≤ m + 2 + k))
  apply (mul_eq_zero.mp ?_).resolve_left (MvPolynomial.C_ne_zero.mpr hfac)
  rw [Finset.mul_sum]
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  ring

-- @node: lowerForwardEvaluationsVanish
/-- Proves the stated mathematical property of lower Forward Evaluations Vanish. -/
lemma lowerForwardEvaluationsVanish (m : ℕ) (hm : 3 ≤ m) (θ : ParamSpace ℂ m)
    (q : MvPolynomial (Fin 2) ℂ) (hq : q.IsHomogeneous (m + 2))
    (hrank : Function.Injective (lowerForwardWeightedContraction m θ))
    (hcon : ∀ k, k ≤ m - 1 → diffApply q
      (dividedPowerBlock (forwardCumulantMap m (2 * m + 1) θ) (m + 2 + k)) = 0) :
    ∀ j, evalAtDir q (forwardLoading m θ.1 θ.2.1 j) = 0 := by
  let e : Fin (m + 2) → ℂ := fun j => evalAtDir q (forwardLoading m θ.1 θ.2.1 j)
  have hstack := lowerForwardStackEquation m hm θ q hq hcon
  have hminor : lowerForwardWeightedContraction m θ e =
      lowerForwardWeightedContraction m θ 0 := by
    funext i
    refine Fin.cases ?_ (fun i' => Fin.cases ?_ (fun r => ?_) i') i
    · have h := congrArg (fun p => (binaryDehom p).coeff 0) (hstack 0 (by omega))
      simp [lowerForwardWeightedContraction, lowerForwardMinor_apply, Matrix.mulVec,
        dotProduct, e, binaryDehom] at h ⊢
      simpa [mul_assoc] using h
    · have h := congrArg (fun p => (binaryDehom p).coeff 0) (hstack 1 (by omega))
      simp only [map_sum, map_mul, map_pow, map_zero, Polynomial.finset_sum_coeff,
        Polynomial.coeff_zero] at h
      simp only [lowerForwardWeightedContraction, lowerForwardMinor_apply, Matrix.mulVec,
        dotProduct, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
      simp only [Fin.val_succ]
      norm_num at h ⊢
      have hindex : m + 2 + 1 = m + 3 := by omega
      rw [hindex] at h
      dsimp [e]
      convert h using 1
      apply Finset.sum_congr rfl
      intro j _
      rw [lowerKernel_coeff_zero]
      ring
    · have h := congrArg (fun p => (binaryDehom p).coeff r.1)
        (hstack (m - 1) (by omega))
      simp only [map_sum, map_mul, map_pow, map_zero, Polynomial.finset_sum_coeff,
        Polynomial.coeff_zero] at h
      simp only [lowerForwardWeightedContraction, lowerForwardMinor_apply, Matrix.mulVec,
        dotProduct, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
      have hv0 : (r.succ.succ : Fin (m + 2)).val ≠ 0 := by simp
      have hv1 : (r.succ.succ : Fin (m + 2)).val ≠ 1 := by simp
      have hv2 : (r.succ.succ : Fin (m + 2)).val - 2 = r.val := by simp
      simp only [hv0, hv1, if_false, hv2]
      have hindex : m + 2 + (m - 1) = 2 * m + 1 := by omega
      rw [hindex] at h
      dsimp [e]
      convert h using 1
      apply Finset.sum_congr rfl
      intro j _
      simp only [lowerKernel_binaryDehom_C]
      rw [← Polynomial.C_mul, Polynomial.coeff_C_mul,
        coeff_binaryDehom_linForm_pow']
      ring
  have he : e = 0 := hrank hminor
  intro j
  exact congrFun he j

-- @node: lowerReverseEvaluationsVanish
/-- Proves the stated mathematical property of lower Reverse Evaluations Vanish. -/
lemma lowerReverseEvaluationsVanish (m : ℕ) (hm : 3 ≤ m) (η : ParamSpace ℂ m)
    (q : MvPolynomial (Fin 2) ℂ) (hq : q.IsHomogeneous (m + 2))
    (hrank : Function.Injective (lowerReverseWeightedContraction m η))
    (hcon : ∀ k, k ≤ m - 1 → diffApply q
      (dividedPowerBlock (reverseCumulantMap m (2 * m + 1) η) (m + 2 + k)) = 0) :
    ∀ j, evalAtDir q (reverseLoading m η.1 η.2.1 j) = 0 := by
  let e : Fin (m + 2) → ℂ := fun j => evalAtDir q (reverseLoading m η.1 η.2.1 j)
  have hstack := lowerReverseStackEquation m hm η q hq hcon
  have hminor : lowerReverseWeightedContraction m η e =
      lowerReverseWeightedContraction m η 0 := by
    funext i
    refine Fin.cases ?_ (fun i' => Fin.cases ?_ (fun r => ?_) i') i
    · have h := congrArg (fun p => (binaryDehom p).coeff 0) (hstack 0 (by omega))
      simp [lowerReverseWeightedContraction, lowerReverseMinor_apply, Matrix.mulVec,
        dotProduct, e, binaryDehom] at h ⊢
      simpa [mul_assoc] using h
    · have h := congrArg (fun p => (binaryDehom p).coeff 1) (hstack 1 (by omega))
      simp only [map_sum, map_mul, map_pow, map_zero, Polynomial.finset_sum_coeff,
        Polynomial.coeff_zero] at h
      simp only [lowerReverseWeightedContraction, lowerReverseMinor_apply, Matrix.mulVec,
        dotProduct, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
      simp only [Fin.val_succ]
      norm_num at h ⊢
      have hindex : m + 2 + 1 = m + 3 := by omega
      rw [hindex] at h
      dsimp [e]
      convert h using 1
      apply Finset.sum_congr rfl
      intro j _
      rw [← Polynomial.C_mul, Polynomial.coeff_C_mul, lowerKernel_coeff_one]
      ring
    · have h := congrArg (fun p => (binaryDehom p).coeff (m - 1 - r.1))
        (hstack (m - 1) (by omega))
      simp only [map_sum, map_mul, map_pow, map_zero, Polynomial.finset_sum_coeff,
        Polynomial.coeff_zero] at h
      simp only [lowerReverseWeightedContraction, lowerReverseMinor_apply, Matrix.mulVec,
        dotProduct, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
      have hv0 : (r.succ.succ : Fin (m + 2)).val ≠ 0 := by simp
      have hv1 : (r.succ.succ : Fin (m + 2)).val ≠ 1 := by simp
      have hv2 : (r.succ.succ : Fin (m + 2)).val - 2 = r.val := by simp
      simp only [hv0, hv1, if_false, hv2]
      have hindex : m + 2 + (m - 1) = 2 * m + 1 := by omega
      rw [hindex] at h
      dsimp [e]
      convert h using 1
      apply Finset.sum_congr rfl
      intro j _
      simp only [lowerKernel_binaryDehom_C]
      rw [← Polynomial.C_mul, Polynomial.coeff_C_mul,
        coeff_binaryDehom_linForm_pow']
      have hsub : m - 1 - (m - 1 - r.1) = r.1 := by omega
      have hchoose : (m - 1).choose (m - 1 - r.1) = (m - 1).choose r.1 := by
        rw [Nat.choose_symm (by omega)]
      rw [hsub, hchoose]
      ring
  have he : e = 0 := hrank hminor
  intro j
  exact congrFun he j

-- @node: lowerForwardSupportAnnihilatorInKernel
/-- Proves the stated mathematical property of lower Forward Support Annihilator In Kernel. -/
lemma lowerForwardSupportAnnihilatorInKernel (m : ℕ) (hm : 3 ≤ m) (θ : ParamSpace ℂ m)
    (q : MvPolynomial (Fin 2) ℂ) (hq : q.IsHomogeneous (m + 2))
    (hqD : ∃ c : ℂ, q = c • supportAnnihilator (forwardLoading m θ.1 θ.2.1)) :
    ∀ k, k ≤ m - 1 → diffApply q
      (dividedPowerBlock (forwardCumulantMap m (2 * m + 1) θ) (m + 2 + k)) = 0 := by
  intro k hk
  rw [dividedPowerBlock_forward_eq_sum_linForm_pow m (2 * m + 1) (m + 2 + k) θ
    (by omega) (by omega), diffApply_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [diffApply_C_mul, diffApply_linForm_pow q hq]
  rcases hqD with ⟨c, rfl⟩
  simp only [MvPolynomial.smul_eq_C_mul, evalAtDir, MvPolynomial.eval_mul,
    MvPolynomial.eval_C]
  have hzero := evalAtDir_supportAnnihilator_eq_zero
    (forwardLoading m θ.1 θ.2.1) j
  simp only [evalAtDir] at hzero
  rw [hzero, mul_zero]
  simp

-- @node: lowerReverseSupportAnnihilatorInKernel
/-- Proves the stated mathematical property of lower Reverse Support Annihilator In Kernel. -/
lemma lowerReverseSupportAnnihilatorInKernel (m : ℕ) (hm : 3 ≤ m) (η : ParamSpace ℂ m)
    (q : MvPolynomial (Fin 2) ℂ) (hq : q.IsHomogeneous (m + 2))
    (hqD : ∃ c : ℂ, q = c • supportAnnihilator (reverseLoading m η.1 η.2.1)) :
    ∀ k, k ≤ m - 1 → diffApply q
      (dividedPowerBlock (reverseCumulantMap m (2 * m + 1) η) (m + 2 + k)) = 0 := by
  intro k hk
  rw [dividedPowerBlock_reverse_eq_sum_linForm_pow m (2 * m + 1) (m + 2 + k) η
    (by omega) (by omega), diffApply_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [diffApply_C_mul, diffApply_linForm_pow q hq]
  rcases hqD with ⟨c, rfl⟩
  simp only [MvPolynomial.smul_eq_C_mul, evalAtDir, MvPolynomial.eval_mul,
    MvPolynomial.eval_C]
  have hzero := evalAtDir_supportAnnihilator_eq_zero
    (reverseLoading m η.1 η.2.1) j
  simp only [evalAtDir] at hzero
  rw [hzero, mul_zero]
  simp

-- @node: lowerForwardApolarKernelIdentity
/-- Proves the stated mathematical property of lower Forward Apolar Kernel Identity. -/
theorem lowerForwardApolarKernelIdentity (m : ℕ) (hm : 3 ≤ m) (θ : ParamSpace ℂ m)
    (hslopes : Function.Injective
      (fun j : Fin (m + 1) => (forwardLoading m θ.1 θ.2.1 j.castSucc).2))
    (hnonzero : ∀ j : Fin (m + 1),
      (forwardLoading m θ.1 θ.2.1 j.castSucc).2 ≠ 0)
    (hrank : Function.Injective (lowerForwardWeightedContraction m θ)) :
    ∀ q : MvPolynomial (Fin 2) ℂ, q.IsHomogeneous (m + 2) →
      ((∀ k, k ≤ m - 1 → diffApply q
          (dividedPowerBlock (forwardCumulantMap m (2 * m + 1) θ) (m + 2 + k)) = 0)
        ↔ ∃ c : ℂ, q = c • supportAnnihilator (forwardLoading m θ.1 θ.2.1)) := by
  intro q hq
  constructor
  · intro hcon
    apply forward_points_imply_supportAnnihilator_multiple m θ q hq hslopes hnonzero
    exact lowerForwardEvaluationsVanish m hm θ q hq hrank hcon
  · rintro ⟨c, rfl⟩ k hk
    apply lowerForwardSupportAnnihilatorInKernel m hm θ _ hq ⟨c, rfl⟩ k hk

-- @node: lowerReverseApolarKernelIdentity
/-- Proves the stated mathematical property of lower Reverse Apolar Kernel Identity. -/
theorem lowerReverseApolarKernelIdentity (m : ℕ) (hm : 3 ≤ m) (η : ParamSpace ℂ m)
    (hslopes : Function.Injective
      (fun j : Fin (m + 1) => (reverseLoading m η.1 η.2.1 j.succ).1))
    (hnonzero : ∀ j : Fin (m + 1), (reverseLoading m η.1 η.2.1 j.succ).1 ≠ 0)
    (hrank : Function.Injective (lowerReverseWeightedContraction m η)) :
    ∀ q : MvPolynomial (Fin 2) ℂ, q.IsHomogeneous (m + 2) →
      ((∀ k, k ≤ m - 1 → diffApply q
          (dividedPowerBlock (reverseCumulantMap m (2 * m + 1) η) (m + 2 + k)) = 0)
        ↔ ∃ c : ℂ, q = c • supportAnnihilator (reverseLoading m η.1 η.2.1)) := by
  intro q hq
  constructor
  · intro hcon
    apply reverse_points_imply_supportAnnihilator_multiple m η q hq hslopes hnonzero
    exact lowerReverseEvaluationsVanish m hm η q hq hrank hcon
  · rintro ⟨c, rfl⟩ k hk
    apply lowerReverseSupportAnnihilatorInKernel m hm η _ hq ⟨c, rfl⟩ k hk

end

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
