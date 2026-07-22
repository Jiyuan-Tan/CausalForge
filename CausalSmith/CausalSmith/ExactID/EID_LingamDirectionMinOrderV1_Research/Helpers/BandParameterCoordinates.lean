/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Finite coordinates for the retained parameter band
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.AffineSpaceDimension
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.FiberDimensionDefs

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

noncomputable section

/-- Coordinates of the finite retained-band parameter space.  The last `Fin
(L-1)` coordinate represents orders `2, ..., L`. -/
abbrev BandParamCoord (m L : ℕ) :=
  Unit ⊕ Fin m ⊕ (Fin (m + 2) × Fin (L - 1))

/-- Read retained coordinates from a function-valued parameter. -/
def encodeBandParam {m L : ℕ} (θ : ParamSpace ℂ m) : BandParamCoord m L → ℂ
  | Sum.inl _ => θ.1
  | Sum.inr (Sum.inl i) => θ.2.1 i
  | Sum.inr (Sum.inr jk) => θ.2.2 jk.1 (jk.2.val + 2)

/-- Put a finite coordinate vector back into the function-valued parameter
space, setting every off-band weight to zero. -/
def decodeBandParam {m L : ℕ} (x : BandParamCoord m L → ℂ) : ParamSpace ℂ m :=
  (x (Sum.inl ()),
    fun i => x (Sum.inr (Sum.inl i)),
    fun j r => if h : 2 ≤ r ∧ r ≤ L then
      x (Sum.inr (Sum.inr (j, ⟨r - 2, by omega⟩))) else 0)

lemma decodeBandParam_supported {m L : ℕ} (x : BandParamCoord m L → ℂ) :
    decodeBandParam x ∈ bandSupportedParams m L := by
  intro j r hr
  simp only [decodeBandParam]
  split
  · rename_i h
    omega
  · rfl

/-- Proves the stated mathematical property of encode decode Band Param. -/
lemma encode_decodeBandParam {m L : ℕ} (hL : 2 ≤ L)
    (x : BandParamCoord m L → ℂ) :
    encodeBandParam (L := L) (decodeBandParam (L := L) x) = x := by
  funext c
  rcases c with _ | (i | ⟨j, k⟩)
  · rfl
  · rfl
  · simp only [encodeBandParam, decodeBandParam]
    split
    · rename_i h
      congr 2
    · rename_i h
      exfalso
      omega

/-- Proves the stated mathematical property of decode encode Band Param. -/
lemma decode_encodeBandParam {m L : ℕ} (hL : 2 ≤ L)
    {θ : ParamSpace ℂ m} (hθ : θ ∈ bandSupportedParams m L) :
    decodeBandParam (L := L) (encodeBandParam (L := L) θ) = θ := by
  rcases θ with ⟨γ, ρ, w⟩
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  funext j r
  simp only [decodeBandParam, encodeBandParam]
  split
  · rename_i h
    congr 1
    omega
  · rename_i h
    symm
    apply hθ j r
    omega

/-- The actual retained-band subtype is equivalent to an ordinary finite
complex affine space. -/
def bandParamEquiv {m L : ℕ} (hL : 2 ≤ L) :
    {θ : ParamSpace ℂ m // θ ∈ bandSupportedParams m L} ≃
      (BandParamCoord m L → ℂ) where
  toFun θ := encodeBandParam θ
  invFun x := ⟨decodeBandParam x, decodeBandParam_supported x⟩
  left_inv θ := Subtype.ext (decode_encodeBandParam hL θ.property)
  right_inv := encode_decodeBandParam hL

/-- Embed a finite band coordinate among the original natural-number-indexed
polynomial variables. -/
def bandCoordEmbedding {m L : ℕ} : BandParamCoord m L → ParamCoord m
  | Sum.inl u => Sum.inl u
  | Sum.inr (Sum.inl i) => Sum.inr (Sum.inl i)
  | Sum.inr (Sum.inr jk) => Sum.inr (Sum.inr (jk.1, jk.2.val + 2))

lemma bandCoordEmbedding_injective {m L : ℕ} (hL : 2 ≤ L) :
    Function.Injective (bandCoordEmbedding : BandParamCoord m L → ParamCoord m) := by
  intro a b hab
  rcases a with _ | (i | ⟨j, k⟩) <;>
    rcases b with _ | (i' | ⟨j', k'⟩) <;>
    simp [bandCoordEmbedding, Fin.ext_iff] at hab ⊢
  all_goals exact hab

/-- Restrict an original parameter polynomial to the retained band by setting
all off-band weight variables to zero. -/
def restrictParamPolynomial {m L : ℕ}
    (P : MvPolynomial (ParamCoord m) ℂ) : MvPolynomial (BandParamCoord m L) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun c =>
    match c with
    | Sum.inl u => MvPolynomial.X (Sum.inl u)
    | Sum.inr (Sum.inl i) => MvPolynomial.X (Sum.inr (Sum.inl i))
    | Sum.inr (Sum.inr jr) =>
        if h : 2 ≤ jr.2 ∧ jr.2 ≤ L then
          MvPolynomial.X (Sum.inr (Sum.inr
            (jr.1, ⟨jr.2 - 2, by omega⟩))) else 0) P

lemma eval_restrictParamPolynomial {m L : ℕ} (hL : 2 ≤ L)
    (x : BandParamCoord m L → ℂ) (P : MvPolynomial (ParamCoord m) ℂ) :
    MvPolynomial.eval x (restrictParamPolynomial P) =
      MvPolynomial.eval (paramEval (decodeBandParam x)) P := by
  change MvPolynomial.eval x (MvPolynomial.eval₂ MvPolynomial.C _ P) = _
  rw [MvPolynomial.eval_eval₂]
  have hC : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℂ := by
    ext z
    simp
  rw [hC, MvPolynomial.eval₂_id]
  apply MvPolynomial.eval₂_congr
  intro c _ _
  rcases c with _ | (i | ⟨j, r⟩)
  · simp [paramEval, decodeBandParam]
  · simp [paramEval, decodeBandParam]
  · by_cases hr : 2 ≤ r ∧ r ≤ L
    · simp [hr, paramEval, decodeBandParam, encodeBandParam]
    · simp [hr, paramEval, decodeBandParam]

/-- Gives the stated evaluation formula for eval rename band Coord Embedding. -/
lemma eval_rename_bandCoordEmbedding {m L : ℕ}
    (θ : ParamSpace ℂ m) (Q : MvPolynomial (BandParamCoord m L) ℂ) :
    MvPolynomial.eval (paramEval θ) (MvPolynomial.rename bandCoordEmbedding Q) =
      MvPolynomial.eval (encodeBandParam θ) Q := by
  rw [MvPolynomial.eval_rename]
  apply congrArg (fun f => MvPolynomial.eval f Q)
  funext c
  rcases c with _ | (i | ⟨j, k⟩) <;> rfl

/-- Relative closure in the paper's retained-band ambient becomes ordinary
affine algebraic closure under finite-coordinate encoding. -/
theorem encodeBandParam_zariskiClosureParamIn {m L : ℕ} (hL : 2 ≤ L)
    {A : Set (ParamSpace ℂ m)} (hA : A ⊆ bandSupportedParams m L) :
    (encodeBandParam (L := L)) '' zariskiClosureParamIn L A =
      affineZariskiClosure ((encodeBandParam (L := L)) '' A) := by
  ext x
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    change encodeBandParam θ ∈ MvPolynomial.zeroLocus ℂ
      (MvPolynomial.vanishingIdeal ℂ (encodeBandParam '' A))
    rw [MvPolynomial.mem_zeroLocus_iff]
    simp only [MvPolynomial.aeval_def]
    intro Q hQ
    change MvPolynomial.eval (encodeBandParam θ) Q = 0
    rw [← eval_rename_bandCoordEmbedding]
    exact hθ.2 (MvPolynomial.rename bandCoordEmbedding Q) (by
      intro s hs
      rw [eval_rename_bandCoordEmbedding]
      simpa [MvPolynomial.aeval_def, MvPolynomial.eval₂_id] using
        hQ (encodeBandParam s) ⟨s, hs, rfl⟩)
  · intro hx
    change x ∈ MvPolynomial.zeroLocus ℂ
      (MvPolynomial.vanishingIdeal ℂ (encodeBandParam '' A)) at hx
    rw [MvPolynomial.mem_zeroLocus_iff] at hx
    have hx' : ∀ p ∈ MvPolynomial.vanishingIdeal ℂ
        ((encodeBandParam (L := L)) '' A), MvPolynomial.eval x p = 0 := by
      intro p hp
      simpa [MvPolynomial.aeval_def, MvPolynomial.eval₂_id] using hx p hp
    refine ⟨decodeBandParam (L := L) x, ?_, encode_decodeBandParam hL x⟩
    refine ⟨decodeBandParam_supported x, ?_⟩
    intro P hP
    rw [← eval_restrictParamPolynomial hL]
    exact hx' (restrictParamPolynomial P) (by
      rintro y ⟨s, hs, rfl⟩
      change MvPolynomial.eval (encodeBandParam s) (restrictParamPolynomial P) = 0
      rw [eval_restrictParamPolynomial hL,
        decode_encodeBandParam hL (hA hs)]
      exact hP s hs)

end

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
