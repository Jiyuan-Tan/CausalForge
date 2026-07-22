/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Hypersurface complements are Zariski-open and dense

The complement of the vanishing set of a single nonzero polynomial in the
structural-parameter coordinate ring is Zariski-open and Zariski-dense (over the
infinite integral domain `ℂ` with infinitely many coordinate variables).  This
supplies the open/dense clauses of `TApolar.generic_apolar_arrow_recovery` for
the recovery loci `U^right`, `U^left`, each cut out by a nonzero polynomial.
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.PinSubst
import Mathlib.Algebra.MvPolynomial.Funext

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

/-- Every assignment of the structural coordinates is represented by a parameter. -/
lemma paramEval_surjective (m : ℕ) : Function.Surjective (@paramEval m) := by
  intro v
  refine ⟨(v (Sum.inl ()), fun i => v (Sum.inr (Sum.inl i)),
    fun j r => v (Sum.inr (Sum.inr (j, r)))), ?_⟩
  funext x
  rcases x with _ | x
  · rfl
  rcases x with i | jr
  · rfl
  · rfl

/-- The complement of the vanishing set of a nonzero polynomial is Zariski-open and dense. -/
lemma isZariskiOpen_dense_of_poly_ne_zero {m : ℕ} (P : MvPolynomial (ParamCoord m) ℂ) (hP : P ≠ 0) :
    IsZariskiOpenParam {θ : ParamSpace ℂ m | MvPolynomial.eval (paramEval θ) P ≠ 0} ∧
    IsZariskiDenseParam {θ : ParamSpace ℂ m | MvPolynomial.eval (paramEval θ) P ≠ 0} := by
  let U : Set (ParamSpace ℂ m) := {θ | MvPolynomial.eval (paramEval θ) P ≠ 0}
  let Z : Set (ParamSpace ℂ m) := Uᶜ
  have poly_eq_zero_of_eval_zero
      (Q : MvPolynomial (ParamCoord m) ℂ)
      (hQ : ∀ θ : ParamSpace ℂ m, MvPolynomial.eval (paramEval θ) Q = 0) : Q = 0 := by
    apply MvPolynomial.funext
    intro v
    obtain ⟨θ, hθ⟩ := paramEval_surjective m v
    rw [← hθ]
    simpa using hQ θ
  constructor
  · refine ⟨Z, ?_, ?_, ?_⟩
    · apply Set.Subset.antisymm
      · intro θ hθ
        have hP_vanishes : ∀ s ∈ Z, MvPolynomial.eval (paramEval s) P = 0 := by
          intro s hs
          simpa [Z, U] using hs
        have hvanishes := hθ P hP_vanishes
        simpa [Z, U] using hvanishes
      · intro θ hθ Q hQ
        exact hQ θ hθ
    · intro hZ
      apply hP
      apply poly_eq_zero_of_eval_zero P
      intro θ
      have hθZ : θ ∈ Z := by rw [hZ]; exact Set.mem_univ θ
      simpa [Z, U] using hθZ
    · ext θ
      simp [Z, U]
  · ext θ₀
    simp only [Set.mem_univ, iff_true]
    intro Q hQ
    have hmul_eval_zero : ∀ θ : ParamSpace ℂ m,
        MvPolynomial.eval (paramEval θ) (Q * P) = 0 := by
      intro θ
      by_cases hθ : θ ∈ U
      · rw [MvPolynomial.eval_mul, hQ θ hθ, zero_mul]
      · have hPθ : MvPolynomial.eval (paramEval θ) P = 0 := by
          simpa [U] using hθ
        rw [MvPolynomial.eval_mul, hPθ, mul_zero]
    have hmul : Q * P = 0 := poly_eq_zero_of_eval_zero (Q * P) hmul_eval_zero
    have hQ : Q = 0 := (mul_eq_zero.mp hmul).resolve_right hP
    simp [hQ]

/-- The polynomial whose nonvanishing defines the generic parameter locus. -/
noncomputable def genericParameterPolynomial (m L : ℕ) : MvPolynomial (ParamCoord m) ℂ :=
  MvPolynomial.X (Sum.inl ()) *
    (∏ i : Fin m, (MvPolynomial.X (Sum.inl ()) - MvPolynomial.X (Sum.inr (Sum.inl i)))) *
    (∏ i : Fin m, ∏ i' : Fin m,
      if i < i' then MvPolynomial.X (Sum.inr (Sum.inl i)) - MvPolynomial.X (Sum.inr (Sum.inl i'))
      else 1) *
    (∏ j : Fin (m + 2), ∏ r ∈ Finset.Icc 2 L, MvPolynomial.X (Sum.inr (Sum.inr (j, r))))

/-- The polynomial defining the generic parameter restrictions is not identically zero. -/
lemma genericParameterPolynomial_ne_zero (m L : ℕ) : genericParameterPolynomial m L ≠ 0 := by
  unfold genericParameterPolynomial
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · change MvPolynomial.X (Sum.inl () : ParamCoord m) ≠ 0
        exact MvPolynomial.X_ne_zero _
      · rw [Finset.prod_ne_zero_iff]
        intro i hi
        apply sub_ne_zero.mpr
        intro hEq
        have hCoord := MvPolynomial.X_injective hEq
        simp at hCoord
    · rw [Finset.prod_ne_zero_iff]
      intro i hi
      rw [Finset.prod_ne_zero_iff]
      intro i' hi'
      by_cases h : i < i'
      · simp only [h, ↓reduceIte]
        apply sub_ne_zero.mpr
        intro hEq
        have hCoord := MvPolynomial.X_injective hEq
        have : i = i' := by simpa using hCoord
        exact (ne_of_lt h) this
      · simp [h]
  · rw [Finset.prod_ne_zero_iff]
    intro j hj
    rw [Finset.prod_ne_zero_iff]
    intro r hr
    change MvPolynomial.X (Sum.inr (Sum.inr (j, r)) : ParamCoord m) ≠ 0
    exact MvPolynomial.X_ne_zero _

/-- At any complex parameter value, the genericity polynomial equals the product of the direct slope, all slope-separation factors, and all retained cumulant coordinates. -/
lemma eval_genericParameterPolynomial (m L : ℕ) (θ : ParamSpace ℂ m) :
    MvPolynomial.eval (paramEval θ) (genericParameterPolynomial m L) =
      θ.1 * (∏ i : Fin m, (θ.1 - θ.2.1 i)) *
        (∏ i : Fin m, ∏ i' : Fin m, if i < i' then θ.2.1 i - θ.2.1 i' else 1) *
        (∏ j : Fin (m + 2), ∏ r ∈ Finset.Icc 2 L, θ.2.2 j r) := by
  have eval_pair (i i' : Fin m) :
      MvPolynomial.eval (paramEval θ)
          (if i < i' then MvPolynomial.X (Sum.inr (Sum.inl i)) -
            MvPolynomial.X (Sum.inr (Sum.inl i')) else 1) =
        if i < i' then θ.2.1 i - θ.2.1 i' else 1 := by
    by_cases h : i < i' <;> simp [h, paramEval]
  simp_rw [genericParameterPolynomial, MvPolynomial.eval_mul, map_prod, eval_pair]
  simp [paramEval]

/-- The generic parameter locus is the band-supported parameter space with the genericity polynomial nonzero. -/
lemma genericParameterLocus_eq_nonvanishing_poly (m L : ℕ) :
    genericParameterLocus m L =
      bandSupportedParams m L ∩
        {θ : ParamSpace ℂ m |
          MvPolynomial.eval (paramEval θ) (genericParameterPolynomial m L) ≠ 0} := by
  ext θ
  change θ ∈ bandSupportedParams m L ∧
      θ.1 * (∏ i : Fin m, (θ.1 - θ.2.1 i)) *
          (∏ i : Fin m, ∏ i' : Fin m, if i < i' then θ.2.1 i - θ.2.1 i' else 1) *
          (∏ j : Fin (m + 2), ∏ r ∈ Finset.Icc 2 L, θ.2.2 j r) ≠ 0 ↔
    θ ∈ bandSupportedParams m L ∧
      MvPolynomial.eval (paramEval θ) (genericParameterPolynomial m L) ≠ 0
  rw [eval_genericParameterPolynomial]

/-- Within the paper's finite retained-band parameter space, the nonvanishing locus
of any polynomial whose pinned form is nonzero is relatively Zariski-open and dense. -/
lemma isZariskiOpenIn_denseIn_of_pinSubst_ne_zero {m L : ℕ}
    (P : MvPolynomial (ParamCoord m) ℂ) (hP : pinSubst m L P ≠ 0) :
    IsZariskiOpenParamIn L
        (bandSupportedParams m L ∩
          {θ | MvPolynomial.eval (paramEval θ) P ≠ 0}) ∧
    IsZariskiDenseParamIn L
        (bandSupportedParams m L ∩
          {θ | MvPolynomial.eval (paramEval θ) P ≠ 0}) := by
  let Z : Set (ParamSpace ℂ m) :=
    bandSupportedParams m L ∩ {θ | MvPolynomial.eval (paramEval θ) P = 0}
  have hex : ∃ v : ParamCoord m → ℂ, MvPolynomial.eval v (pinSubst m L P) ≠ 0 := by
    by_contra hn
    apply hP
    apply MvPolynomial.funext
    intro v
    by_contra hv
    exact hn ⟨v, hv⟩
  constructor
  · refine ⟨Z, ?_, ?_, ?_⟩
    · apply Set.Subset.antisymm
      · intro θ hθ
        refine ⟨hθ.1, ?_⟩
        exact hθ.2 P (fun s hs => hs.2)
      · intro θ hθ
        refine ⟨hθ.1, ?_⟩
        intro Q hQ
        exact hQ θ hθ
    · obtain ⟨v, hv⟩ := hex
      intro hZ
      have hband : pinParam m L v ∈ bandSupportedParams m L :=
        pinParam_mem_band m L v
      have heval : MvPolynomial.eval (paramEval (pinParam m L v)) P ≠ 0 := by
        rw [← eval_pinSubst]
        exact hv
      have hmem : pinParam m L v ∈ Z := by
        rw [hZ]
        exact hband
      exact heval hmem.2
    · ext θ
      simp [Z]
  · apply Set.Subset.antisymm
    · intro θ hθ
      exact hθ.1
    · intro θ hband
      refine ⟨hband, ?_⟩
      intro Q hQ
      have hmul : pinSubst m L Q * pinSubst m L P = 0 := by
        apply MvPolynomial.funext
        intro v
        rw [MvPolynomial.eval_mul, eval_pinSubst, eval_pinSubst]
        by_cases hv : MvPolynomial.eval (paramEval (pinParam m L v)) P ≠ 0
        · rw [hQ (pinParam m L v) ⟨pinParam_mem_band m L v, hv⟩, zero_mul]
          simp
        · rw [not_ne_iff.mp hv, mul_zero]
          simp
      have hpinQ : pinSubst m L Q = 0 :=
        (mul_eq_zero.mp hmul).resolve_right hP
      calc
        MvPolynomial.eval (paramEval θ) Q =
            MvPolynomial.eval (paramEval θ) (pinSubst m L Q) :=
          (eval_pinSubst_of_mem_band hband Q).symm
        _ = 0 := by rw [hpinQ]; simp

/-- The generic retained-band parameter locus is relatively Zariski-open and dense
in the paper's finite structural parameter space. -/
lemma isZariskiOpen_dense_genericParameterLocus (m L : ℕ) :
    IsZariskiOpenParamIn L (genericParameterLocus m L) ∧
    IsZariskiDenseParamIn L (genericParameterLocus m L) := by
  rw [genericParameterLocus_eq_nonvanishing_poly]
  apply isZariskiOpenIn_denseIn_of_pinSubst_ne_zero
  let θG : ParamSpace ℂ m :=
    (1, (fun i => ((i.val + 2 : ℕ) : ℂ)),
      fun _ r => if 2 ≤ r ∧ r ≤ L then 1 else 0)
  apply pinSubst_ne_zero_of_pinned_witness (genericParameterPolynomial m L) θG
  · intro j r hout
    simp only [θG]
    split_ifs with hir
    · omega
    · rfl
  · rw [eval_genericParameterPolynomial]
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · norm_num [θG]
        · rw [Finset.prod_ne_zero_iff]
          intro i hi
          apply sub_ne_zero.mpr
          intro heq
          change (1 : ℂ) = ((i.val + 2 : ℕ) : ℂ) at heq
          have : (1 : ℕ) = i.val + 2 := by exact_mod_cast heq
          omega
      · rw [Finset.prod_ne_zero_iff]
        intro i hi
        rw [Finset.prod_ne_zero_iff]
        intro i' hi'
        by_cases hii : i < i'
        · simp only [hii, if_true]
          apply sub_ne_zero.mpr
          intro heq
          change ((i.val + 2 : ℕ) : ℂ) = ((i'.val + 2 : ℕ) : ℂ) at heq
          have : i.val + 2 = i'.val + 2 := by exact_mod_cast heq
          omega
        · simp [hii]
    · rw [Finset.prod_ne_zero_iff]
      intro j hj
      rw [Finset.prod_ne_zero_iff]
      intro r hr
      have hr' : 2 ≤ r ∧ r ≤ L := Finset.mem_Icc.mp hr
      simp [θG, hr']

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
