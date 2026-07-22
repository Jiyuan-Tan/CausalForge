/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Pinning structural-parameter polynomials to the retained band

This file defines substitution of zero for off-band source-weight coordinates,
the corresponding pinned parameter, and the evaluation identities relating them.
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.Varieties
import Mathlib.Algebra.MvPolynomial.Monad

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

/-- Pinning substitutes zero for every weight coordinate outside orders two through
`L`, while leaving all loading coordinates and retained weight coordinates fixed. -/
noncomputable def pinSubst (m L : ℕ) :
    MvPolynomial (ParamCoord m) ℂ →ₐ[ℂ] MvPolynomial (ParamCoord m) ℂ :=
  MvPolynomial.bind₁ (fun i : ParamCoord m =>
    match i with
    | Sum.inr (Sum.inr jr) =>
        if 2 ≤ jr.2 ∧ jr.2 ≤ L then MvPolynomial.X i else 0
    | _ => MvPolynomial.X i)

/-- A polynomial remains nonzero after pinning whenever it is nonzero at one point
whose out-of-band weight coordinates are already zero. -/
lemma pinSubst_ne_zero_of_pinned_witness {m L : ℕ}
    (P : MvPolynomial (ParamCoord m) ℂ) (θ₀ : ParamSpace ℂ m)
    (hpin : ∀ (j : Fin (m + 2)) (r : ℕ),
      (r < 2 ∨ L < r) → θ₀.2.2 j r = 0)
    (h : MvPolynomial.eval (paramEval θ₀) P ≠ 0) :
    pinSubst m L P ≠ 0 := by
  intro hzero
  apply h
  have hfamily : (fun i : ParamCoord m =>
      MvPolynomial.aeval (paramEval θ₀)
        (match i with
        | Sum.inr (Sum.inr jr) =>
            if 2 ≤ jr.2 ∧ jr.2 ≤ L then MvPolynomial.X i
            else (0 : MvPolynomial (ParamCoord m) ℂ)
        | _ => MvPolynomial.X i)) = paramEval θ₀ := by
    funext i
    rcases i with _ | i
    · simp [paramEval]
    rcases i with i | jr
    · simp [paramEval]
    · by_cases hir : 2 ≤ jr.2 ∧ jr.2 ≤ L
      · simp [hir, paramEval]
      · have hout : jr.2 < 2 ∨ L < jr.2 := by omega
        simp [hir, paramEval, hpin jr.1 jr.2 hout]
  rw [← hfamily]
  change MvPolynomial.aeval (fun i : ParamCoord m =>
    MvPolynomial.aeval (paramEval θ₀)
      (match i with
      | Sum.inr (Sum.inr jr) =>
          if 2 ≤ jr.2 ∧ jr.2 ≤ L then MvPolynomial.X i else 0
      | _ => MvPolynomial.X i)) P = 0
  rw [← MvPolynomial.aeval_bind₁]
  change MvPolynomial.eval (paramEval θ₀) (pinSubst m L P) = 0
  rw [hzero]
  simp

/-- Pinning fixes every loading coordinate, so a latent slope variable remains
the same variable. -/
lemma pinSubst_X_slope (m L : ℕ) (i : Fin m) :
    pinSubst m L (MvPolynomial.X (Sum.inr (Sum.inl i))) =
      (MvPolynomial.X (Sum.inr (Sum.inl i)) : MvPolynomial (ParamCoord m) ℂ) := by
  simp [pinSubst]

/-- A coordinate assignment determines a structural parameter with its loading
coordinates and retained source weights unchanged and all off-band weights set to zero. -/
def pinParam (m L : ℕ) (v : ParamCoord m → ℂ) : ParamSpace ℂ m :=
  (v (Sum.inl ()), fun i => v (Sum.inr (Sum.inl i)),
   fun j r => if 2 ≤ r ∧ r ≤ L then v (Sum.inr (Sum.inr (j, r))) else 0)

/-- Every parameter obtained by pinning a coordinate assignment belongs to the
paper's finite retained-band parameter space. -/
lemma pinParam_mem_band (m L : ℕ) (v : ParamCoord m → ℂ) :
    pinParam m L v ∈ bandSupportedParams m L := by
  intro j r hout
  simp only [pinParam]
  split_ifs with hir
  · omega
  · rfl

/-- Evaluating a pinned polynomial at a coordinate assignment equals evaluating
the original polynomial at the corresponding pinned parameter. -/
lemma eval_pinSubst (m L : ℕ) (v : ParamCoord m → ℂ)
    (P : MvPolynomial (ParamCoord m) ℂ) :
    MvPolynomial.eval v (pinSubst m L P) =
      MvPolynomial.eval (paramEval (pinParam m L v)) P := by
  change MvPolynomial.aeval v (MvPolynomial.bind₁ _ P) = _
  rw [MvPolynomial.aeval_bind₁]
  have hfamily : (fun i : ParamCoord m =>
      MvPolynomial.aeval v
        (match i with
        | Sum.inr (Sum.inr jr) =>
            if 2 ≤ jr.2 ∧ jr.2 ≤ L then MvPolynomial.X i
            else (0 : MvPolynomial (ParamCoord m) ℂ)
        | _ => MvPolynomial.X i)) = paramEval (pinParam m L v) := by
    funext i
    rcases i with _ | i
    · simp [paramEval, pinParam]
    rcases i with i | jr
    · simp [paramEval, pinParam]
    · by_cases hir : 2 ≤ jr.2 ∧ jr.2 ≤ L
      · simp [hir, paramEval, pinParam]
      · simp [hir, paramEval, pinParam]
  rw [hfamily]
  exact congrFun (MvPolynomial.aeval_eq_eval (paramEval (pinParam m L v))) P

/-- At a parameter in the paper's retained band, pinning a polynomial does not
change its value. -/
lemma eval_pinSubst_of_mem_band {m L : ℕ} {θ : ParamSpace ℂ m}
    (hθ : θ ∈ bandSupportedParams m L) (P : MvPolynomial (ParamCoord m) ℂ) :
    MvPolynomial.eval (paramEval θ) (pinSubst m L P) =
      MvPolynomial.eval (paramEval θ) P := by
  rw [eval_pinSubst]
  have hparam : pinParam m L (paramEval θ) = θ := by
    apply Prod.ext
    · rfl
    apply Prod.ext
    · rfl
    funext j r
    by_cases hir : 2 ≤ r ∧ r ≤ L
    · simp [pinParam, paramEval, hir]
    · have hout : r < 2 ∨ L < r := by omega
      simp [pinParam, paramEval, hir, hθ j r hout]
  rw [hparam]

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
