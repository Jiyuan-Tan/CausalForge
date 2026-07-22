/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Genericity bridges: distinct nonzero loading slopes

Public consequences of membership in the generic parameter locus, packaged for
the flagship assembly: the direct slope is nonzero and distinct from every latent
slope, the latent slopes are pairwise distinct, and the forward/reverse loading
"slope" families (the second forward components, the first reverse components) are
injective and — on the nonzero-slope locus — nowhere zero.
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Basic

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

/-- On the generic locus the direct slope is nonzero. -/
lemma gamma_ne_zero_of_generic {m L : ℕ} {θ : ParamSpace ℂ m}
    (hθ : θ ∈ genericParameterLocus m L) : θ.1 ≠ 0 := by
  intro h
  exact genericParameterLocus_prod_ne_zero hθ (by simp [h])

/-- On the generic locus the direct slope differs from every latent slope. -/
lemma gamma_ne_rho_of_generic {m L : ℕ} {θ : ParamSpace ℂ m}
    (hθ : θ ∈ genericParameterLocus m L) (i : Fin m) : θ.1 ≠ θ.2.1 i := by
  intro h
  have hz : (∏ x : Fin m, (θ.1 - θ.2.1 x)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h])
  exact genericParameterLocus_prod_ne_zero hθ (by simp [hz])

/-- On the generic locus the latent slopes are pairwise distinct. -/
lemma rho_injective_of_generic {m L : ℕ} {θ : ParamSpace ℂ m}
    (hθ : θ ∈ genericParameterLocus m L) : Function.Injective θ.2.1 := by
  intro i i' h
  by_contra hn
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · have hin : (∏ k : Fin m, if i < k then θ.2.1 i - θ.2.1 k else 1) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i') (by simp [hlt, h])
    have hout :
        (∏ k : Fin m, ∏ l : Fin m,
          if k < l then θ.2.1 k - θ.2.1 l else 1) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hin
    exact genericParameterLocus_prod_ne_zero hθ (by simp [hout])
  · have hin : (∏ k : Fin m, if i' < k then θ.2.1 i' - θ.2.1 k else 1) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hgt, h])
    have hout :
        (∏ k : Fin m, ∏ l : Fin m,
          if k < l then θ.2.1 k - θ.2.1 l else 1) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i') hin
    exact genericParameterLocus_prod_ne_zero hθ (by simp [hout])

/-- The forward loading slopes `(u_j)₂` over `j = 0,…,m` (the direct slope `γ`
followed by the latent slopes `ρ_i`) are pairwise distinct. -/
lemma forward_slopes_injective_of_generic {m L : ℕ} {θ : ParamSpace ℂ m}
    (hθ : θ ∈ genericParameterLocus m L) :
    Function.Injective
      (fun j : Fin (m + 1) => (forwardLoading m θ.1 θ.2.1 (Fin.castSucc j)).2) := by
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · intro k h
    refine Fin.cases (fun _ => rfl) (fun i' h' => ?_) k h
    have hi' : i'.val ≠ m := Nat.ne_of_lt i'.isLt
    exact ((gamma_ne_rho_of_generic hθ i')
      (by simpa [forwardLoading, hi'] using h')).elim
  · intro k h
    have hi : i.val ≠ m := Nat.ne_of_lt i.isLt
    refine Fin.cases (fun h' => ?_) (fun i' h' => ?_) k h
    · exact ((gamma_ne_rho_of_generic hθ i)
        (by simpa [forwardLoading, hi] using h'.symm)).elim
    · have hi' : i'.val ≠ m := Nat.ne_of_lt i'.isLt
      exact congrArg Fin.succ ((rho_injective_of_generic hθ)
        (by simpa [forwardLoading, hi, hi'] using h'))

/-- With nonzero latent slopes, the forward loading slopes `(u_j)₂` over
`j = 0,…,m` are all nonzero. -/
lemma forward_slopes_ne_zero_of_generic {m L : ℕ} {θ : ParamSpace ℂ m}
    (hθ : θ ∈ genericParameterLocus m L) (hρ : ∀ i, θ.2.1 i ≠ 0) :
    ∀ j : Fin (m + 1), (forwardLoading m θ.1 θ.2.1 (Fin.castSucc j)).2 ≠ 0 := by
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa [forwardLoading] using gamma_ne_zero_of_generic hθ
  · have hi : i.val ≠ m := Nat.ne_of_lt i.isLt
    simpa [forwardLoading, hi] using hρ i

/-- The reverse loading slopes `(v_j)₁` over `j = 1,…,m+1` (the latent slopes
`σ_i` followed by the direct slope `δ`) are pairwise distinct. -/
lemma reverse_slopes_injective_of_generic {m L : ℕ} {η : ParamSpace ℂ m}
    (hη : η ∈ genericParameterLocus m L) :
    Function.Injective
      (fun j : Fin (m + 1) => (reverseLoading m η.1 η.2.1 j.succ).1) := by
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · intro k h
    refine Fin.lastCases (fun _ => rfl) (fun i' h' => ?_) k h
    have hi' : i'.val ≠ m := Nat.ne_of_lt i'.isLt
    exact ((gamma_ne_rho_of_generic hη i')
      (by simpa [reverseLoading, hi'] using h')).elim
  · intro k h
    have hi : i.val ≠ m := Nat.ne_of_lt i.isLt
    refine Fin.lastCases (fun h' => ?_) (fun i' h' => ?_) k h
    · exact ((gamma_ne_rho_of_generic hη i)
        (by simpa [reverseLoading, hi] using h'.symm)).elim
    · have hi' : i'.val ≠ m := Nat.ne_of_lt i'.isLt
      exact congrArg Fin.castSucc ((rho_injective_of_generic hη)
        (by simpa [reverseLoading, hi, hi'] using h'))

/-- With nonzero latent slopes, the reverse loading slopes `(v_j)₁` over
`j = 1,…,m+1` are all nonzero. -/
lemma reverse_slopes_ne_zero_of_generic {m L : ℕ} {η : ParamSpace ℂ m}
    (hη : η ∈ genericParameterLocus m L) (hσ : ∀ i, η.2.1 i ≠ 0) :
    ∀ j : Fin (m + 1), (reverseLoading m η.1 η.2.1 j.succ).1 ≠ 0 := by
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa [reverseLoading] using gamma_ne_zero_of_generic hη
  · have hi : i.val ≠ m := Nat.ne_of_lt i.isLt
    simpa [reverseLoading, hi] using hσ i

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
