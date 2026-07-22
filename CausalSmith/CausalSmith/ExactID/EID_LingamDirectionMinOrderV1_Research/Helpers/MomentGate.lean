/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Gate (ii): truncated-moment realizability with interior

The truncated-moment-interior statement and its proof are general moment-problem facts; they were
promoted to `Causalean.Stat.MomentProblems` (`TruncatedMomentInterior`,
`truncatedMomentInterior`) and are re-exported here under the run's namespace.  The remaining
declarations in this file derive the run-specific parameter-space consequence used by the flagship
theorem — the pinned-substitution / Zariski-locus bridge, which is coupled to this run's
`ParamSpace` and stays here.
-/

import Causalean.Stat.Nonparametric.MomentProblems.TruncatedCumulantInterior
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ZariskiLocus
import Mathlib.Topology.Algebra.MvPolynomial

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

export Causalean.Stat.MomentProblems (TruncatedMomentInterior truncatedMomentInterior)

/-- The real parameter points at which a fixed complex polynomial does not vanish
after complexification form a Euclidean-open set. -/
lemma isOpen_realNonvanishingLocus {m : ℕ}
    (P : MvPolynomial (ParamCoord m) ℂ) :
    IsOpen {θ : ParamSpace ℝ m |
      MvPolynomial.eval (paramEval (complexifyParam θ)) P ≠ 0} := by
  have hcoord : Continuous (fun θ : ParamSpace ℝ m =>
      paramEval (complexifyParam θ)) := by
    apply continuous_pi
    intro i
    rcases i with _ | i
    · exact Complex.continuous_ofReal.comp continuous_fst
    rcases i with i | jr
    · exact Complex.continuous_ofReal.comp
        ((continuous_apply i).comp continuous_snd.fst)
    · exact Complex.continuous_ofReal.comp
        ((continuous_apply jr.2).comp
          ((continuous_apply jr.1).comp continuous_snd.snd))
  have heval : Continuous (fun θ : ParamSpace ℝ m =>
      MvPolynomial.eval (paramEval (complexifyParam θ)) P) :=
    P.continuous_eval.comp hcoord
  simpa only [Set.preimage_setOf_eq] using
    (isOpen_compl_singleton.preimage heval)

/-- The generic-parameter polynomial stays nonzero after pinning: it is witnessed at the
pinned parameter point whose direct slope is one, whose latent slopes are `2, 3, …, m+1`,
and whose in-band weights are all one. -/
lemma pinSubst_genericParameterPolynomial_ne_zero (m L : ℕ) :
    pinSubst m L (genericParameterPolynomial m L) ≠ 0 := by
  let θG : ParamSpace ℂ m :=
    (1, (fun i => ((i.val + 2 : ℕ) : ℂ)),
      fun _ r => if 2 ≤ r ∧ r ≤ L then 1 else 0)
  apply pinSubst_ne_zero_of_pinned_witness (genericParameterPolynomial m L) θG
  · intro j r hout
    simp only [θG]
    split_ifs with hir
    · omega
    · rfl
  · change MvPolynomial.eval (paramEval θG)
      (genericParameterPolynomial m L) ≠ 0
    rw [eval_genericParameterPolynomial]
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

/-- If the truncated-moment interior gate holds, every polynomial whose pinned form
is nonzero has a nonvanishing point in the real feasible parameter region. -/
theorem exists_feasible_nonvanishing {m L : ℕ}
    (hgate : TruncatedMomentInterior L)
    (P : MvPolynomial (ParamCoord m) ℂ) (hP : pinSubst m L P ≠ 0) :
    (realFeasibleRegion m L ∩
      {θ : ParamSpace ℝ m |
        MvPolynomial.eval (paramEval (complexifyParam θ)) P ≠ 0}).Nonempty := by
  obtain ⟨c, ε, hε, hrealize⟩ := hgate
  let G := genericParameterPolynomial m L
  let Q := P * G
  have hpinG : pinSubst m L G ≠ 0 := pinSubst_genericParameterPolynomial_ne_zero m L
  have hpinQ : pinSubst m L Q ≠ 0 := by
    change pinSubst m L (P * G) ≠ 0
    rw [map_mul]
    exact mul_ne_zero hP hpinG
  let s : ParamCoord m → Set ℂ
    | Sum.inl _ => Set.range Complex.ofReal
    | Sum.inr (Sum.inl _) => Set.range Complex.ofReal
    | Sum.inr (Sum.inr (_, r)) =>
        if 2 ≤ r ∧ r ≤ L then
          (fun x : ℝ => (x : ℂ)) '' Set.Ioo (c r - ε) (c r + ε)
        else Set.range Complex.ofReal
  have hs : ∀ i, (s i).Infinite := by
    intro i
    rcases i with _ | i
    · exact Set.infinite_range_of_injective Complex.ofReal_injective
    rcases i with i | jr
    · exact Set.infinite_range_of_injective Complex.ofReal_injective
    · by_cases hir : 2 ≤ jr.2 ∧ jr.2 ≤ L
      · simp only [s, hir]
        apply (Set.Ioo_infinite (by linarith : c jr.2 - ε < c jr.2 + ε)).image
        exact Complex.ofReal_injective.injOn
      · simp only [s, hir, if_false]
        exact Set.infinite_range_of_injective Complex.ofReal_injective
  have hex : ∃ x : ParamCoord m → ℂ,
      x ∈ Set.pi Set.univ s ∧
        MvPolynomial.eval x (pinSubst m L Q) ≠ 0 := by
    by_contra hn
    apply hpinQ
    apply MvPolynomial.funext_set s hs
    intro x hx
    change MvPolynomial.eval x (pinSubst m L Q) = 0
    by_contra hne
    exact hn ⟨x, hx, hne⟩
  obtain ⟨x, hx, hxQ⟩ := hex
  let xr : ParamCoord m → ℝ := fun i => (x i).re
  have hxreal : ∀ i, ((xr i : ℝ) : ℂ) = x i := by
    intro i
    change (((x i).re : ℝ) : ℂ) = x i
    have hxi : x i ∈ s i := hx i (Set.mem_univ i)
    have hrange : x i ∈ Set.range Complex.ofReal := by
      rcases i with _ | i
      · simpa [s] using hxi
      rcases i with i | jr
      · simpa [s] using hxi
      · by_cases hir : 2 ≤ jr.2 ∧ jr.2 ≤ L
        · rcases (by simpa [s, hir] using hxi) with ⟨y, _, hy⟩
          exact ⟨y, hy⟩
        · simpa [s, hir] using hxi
    rcases hrange with ⟨y, hy⟩
    rw [← hy]
    simp
  let θ : ParamSpace ℝ m :=
    (xr (Sum.inl ()),
      (fun i => xr (Sum.inr (Sum.inl i))),
      fun j r => if 2 ≤ r ∧ r ≤ L then xr (Sum.inr (Sum.inr (j, r))) else 0)
  have heval_family : (fun i : ParamCoord m =>
      MvPolynomial.aeval x
        (match i with
        | Sum.inr (Sum.inr jr) =>
            if 2 ≤ jr.2 ∧ jr.2 ≤ L then MvPolynomial.X i
            else (0 : MvPolynomial (ParamCoord m) ℂ)
        | _ => MvPolynomial.X i)) = paramEval (complexifyParam θ) := by
    funext i
    rcases i with _ | i
    · simp [paramEval, complexifyParam, θ, hxreal]
    rcases i with i | jr
    · simp [paramEval, complexifyParam, θ, hxreal]
    · by_cases hir : 2 ≤ jr.2 ∧ jr.2 ≤ L
      · simp [hir, paramEval, complexifyParam, θ, hxreal]
      · simp [hir, paramEval, complexifyParam, θ]
  have hQθ : MvPolynomial.eval (paramEval (complexifyParam θ)) Q ≠ 0 := by
    rw [← heval_family]
    change MvPolynomial.aeval (fun i : ParamCoord m =>
      MvPolynomial.aeval x
        (match i with
        | Sum.inr (Sum.inr jr) =>
            if 2 ≤ jr.2 ∧ jr.2 ≤ L then MvPolynomial.X i else 0
        | _ => MvPolynomial.X i)) Q ≠ 0
    rw [← MvPolynomial.aeval_bind₁]
    exact hxQ
  have hPθ : MvPolynomial.eval (paramEval (complexifyParam θ)) P ≠ 0 := by
    have hmul := hQθ
    change MvPolynomial.eval (paramEval (complexifyParam θ)) (P * G) ≠ 0 at hmul
    rw [MvPolynomial.eval_mul] at hmul
    exact (mul_ne_zero_iff.mp hmul).1
  have hGθ : MvPolynomial.eval (paramEval (complexifyParam θ)) G ≠ 0 := by
    have hmul := hQθ
    change MvPolynomial.eval (paramEval (complexifyParam θ)) (P * G) ≠ 0 at hmul
    rw [MvPolynomial.eval_mul] at hmul
    exact (mul_ne_zero_iff.mp hmul).2
  have hgenprod :
      (complexifyParam θ).1 *
        (∏ i : Fin m, ((complexifyParam θ).1 - (complexifyParam θ).2.1 i)) *
        (∏ i : Fin m, ∏ i' : Fin m, if i < i' then
          (complexifyParam θ).2.1 i - (complexifyParam θ).2.1 i' else 1) *
        (∏ j : Fin (m + 2), ∏ r ∈ Finset.Icc 2 L,
          (complexifyParam θ).2.2 j r) ≠ 0 := by
    rw [← eval_genericParameterPolynomial]
    exact hGθ
  have hdirectC : (complexifyParam θ).1 ≠ 0 := by
    change (complexifyParam θ).1 *
      (∏ i : Fin m, ((complexifyParam θ).1 - (complexifyParam θ).2.1 i)) *
      (∏ i : Fin m, ∏ i' : Fin m, if i < i' then
        (complexifyParam θ).2.1 i - (complexifyParam θ).2.1 i' else 1) *
      (∏ j : Fin (m + 2), ∏ r ∈ Finset.Icc 2 L,
        (complexifyParam θ).2.2 j r) ≠ 0 at hgenprod
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp
      (mul_ne_zero_iff.mp hgenprod).1).1).1
  have hdirect : θ.1 ≠ 0 := by
    intro hz
    apply hdirectC
    simp [complexifyParam, hz]
  have hgamma : ∀ i : Fin m, θ.1 ≠ θ.2.1 i := by
    intro i hi
    change (complexifyParam θ).1 *
      (∏ i : Fin m, ((complexifyParam θ).1 - (complexifyParam θ).2.1 i)) *
      (∏ i : Fin m, ∏ i' : Fin m, if i < i' then
        (complexifyParam θ).2.1 i - (complexifyParam θ).2.1 i' else 1) *
      (∏ j : Fin (m + 2), ∏ r ∈ Finset.Icc 2 L,
        (complexifyParam θ).2.2 j r) ≠ 0 at hgenprod
    have hp := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp
      (mul_ne_zero_iff.mp hgenprod).1).1).2
    have hfac := Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i)
    apply hfac
    simp [complexifyParam, hi]
  have hrho : Function.Injective θ.2.1 := by
    intro i i' hii
    by_contra hne
    change (complexifyParam θ).1 *
      (∏ i : Fin m, ((complexifyParam θ).1 - (complexifyParam θ).2.1 i)) *
      (∏ i : Fin m, ∏ i' : Fin m, if i < i' then
        (complexifyParam θ).2.1 i - (complexifyParam θ).2.1 i' else 1) *
      (∏ j : Fin (m + 2), ∏ r ∈ Finset.Icc 2 L,
        (complexifyParam θ).2.2 j r) ≠ 0 at hgenprod
    have hp := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hgenprod).1).2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hfac := Finset.prod_ne_zero_iff.mp
        (Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i)) i'
          (Finset.mem_univ i')
      apply hfac
      simp [hlt, complexifyParam, hii]
    · have hfac := Finset.prod_ne_zero_iff.mp
        (Finset.prod_ne_zero_iff.mp hp i' (Finset.mem_univ i')) i
          (Finset.mem_univ i)
      apply hfac
      simp [hgt, complexifyParam, hii]
  have hslopes : Function.Injective
      (Fin.cons θ.1 θ.2.1 : Fin (m + 1) → ℝ) := by
    intro i i' hii
    cases i using Fin.cases with
    | zero =>
        cases i' using Fin.cases with
        | zero => rfl
        | succ b =>
            change θ.1 = θ.2.1 b at hii
            exact (hgamma b hii).elim
    | succ a =>
        cases i' using Fin.cases with
        | zero =>
            change θ.2.1 a = θ.1 at hii
            exact (hgamma a hii.symm).elim
        | succ b =>
            change θ.2.1 a = θ.2.1 b at hii
            simpa using hrho hii
  have hpinθ : ∀ j : Fin (m + 2), ∀ r : ℕ,
      (r < 2 ∨ L < r) → θ.2.2 j r = 0 := by
    intro j r hout
    simp only [θ]
    split_ifs with hir
    · omega
    · rfl
  have hsource : ∀ j : Fin (m + 2), ∃ ν : Measure ℝ,
      IsProbabilityMeasure ν ∧ (∫ x, x ∂ν = 0) ∧ ¬ IsGaussianLaw ν ∧
      MemLp (id : ℝ → ℝ) (L : ℝ≥0∞) ν ∧
      ∀ r, 2 ≤ r → r ≤ L → sourceCumulant ν id r = θ.2.2 j r := by
    intro j
    apply hrealize (fun r => θ.2.2 j r)
    intro r hr2 hrL
    have hxr : xr (Sum.inr (Sum.inr (j, r))) ∈
        Set.Ioo (c r - ε) (c r + ε) := by
      have hm := hx (Sum.inr (Sum.inr (j, r)))
        (Set.mem_univ (Sum.inr (Sum.inr (j, r))))
      rcases (by simpa [s, hr2, hrL] using hm) with ⟨y, hyI, hyx⟩
      have hxy : xr (Sum.inr (Sum.inr (j, r))) = y := by
        change (x (Sum.inr (Sum.inr (j, r)))).re = y
        rw [← hyx]
        simp
      simpa [hxy] using hyI
    simp only [θ, hr2, hrL, and_self, if_true]
    rw [abs_sub_lt_iff]
    constructor <;> linarith [hxr.1, hxr.2]
  refine ⟨θ, ?_, hPθ⟩
  exact ⟨hdirect, hslopes, hpinθ, hsource⟩

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
