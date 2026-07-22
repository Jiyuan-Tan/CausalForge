/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The univariate support annihilator `Q_D` and its factorization data

Squarefree degree-`n` univariate polynomial whose roots are exactly the forward
finite-slope set `{γ, ρ_i}` (resp. reverse `{δ, σ_i}`), with `Q_D(0) ≠ 0` on the
nonzero-slope locus.  Feeds the factorization-recovery clause of the flagship.
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ApolarKernel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.FieldTheory.Separable

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

/-! ## A default polynomial for a prescribed finite multiset of roots -/

/-- The monic polynomial with the given multiset of complex roots. -/
noncomputable def qDefault (rts : Multiset ℂ) : Polynomial ℂ :=
  (rts.map (fun r => Polynomial.X - Polynomial.C r)).prod

/-- The default root polynomial is nonzero because every linear factor is nonzero. -/
lemma qDefault_ne_zero (rts : Multiset ℂ) : qDefault rts ≠ 0 := by
  unfold qDefault
  apply Multiset.prod_ne_zero
  simp [Polynomial.X_sub_C_ne_zero]

/-- The roots of `qDefault` have exactly the prescribed multiplicities. -/
lemma qDefault_roots (rts : Multiset ℂ) : (qDefault rts).roots = rts := by
  exact Polynomial.roots_multiset_prod_X_sub_C rts

private lemma qDefault_splits (rts : Multiset ℂ) : (qDefault rts).Splits := by
  induction rts using Multiset.induction_on with
  | empty => simp [qDefault]
  | cons r rts ih =>
    simp only [qDefault, Multiset.map_cons, Multiset.prod_cons]
    exact (Polynomial.Splits.X_sub_C r).mul ih

/-- Distinct prescribed roots make the default root polynomial squarefree. -/
lemma qDefault_squarefree (rts : Multiset ℂ) (h : rts.Nodup) : Squarefree (qDefault rts) := by
  apply Polynomial.Separable.squarefree
  apply (Polynomial.nodup_roots_iff_of_splits (qDefault_ne_zero rts)
    (qDefault_splits rts)).mp
  simpa only [qDefault_roots] using h

/-- If zero is absent from the prescribed roots, the default root polynomial is nonzero at zero. -/
lemma qDefault_eval_zero_ne (rts : Multiset ℂ)
    (h0 : (0 : ℂ) ∉ rts) :
    (qDefault rts).eval 0 ≠ 0 := by
  unfold qDefault
  rw [Polynomial.eval_multiset_prod]
  apply Multiset.prod_ne_zero
  intro hzero
  rw [Multiset.mem_map] at hzero
  obtain ⟨p, hp, hpzero⟩ := hzero
  rw [Multiset.mem_map] at hp
  obtain ⟨r, hr, rfl⟩ := hp
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hpzero
  have hr0 : r = 0 := by simpa using hpzero
  apply h0
  simpa [hr0] using hr

/-! ## The forward finite-slope multiset -/

/-- The finite slopes in the forward parametrization: the direct slope followed by the latent slopes. -/
def rtsF {m : ℕ} (θ : ParamSpace ℂ m) : Multiset ℂ :=
  θ.1 ::ₘ (Finset.univ.val.map fun i => θ.2.1 i)

private lemma generic_gamma_ne_zero {m L : ℕ} {θ : ParamSpace ℂ m}
    (hθ : θ ∈ genericParameterLocus m L) : θ.1 ≠ 0 := by
  replace hθ := genericParameterLocus_prod_ne_zero hθ
  exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hθ).1).1).1

private lemma generic_gamma_ne_rho {m L : ℕ} {θ : ParamSpace ℂ m}
    (hθ : θ ∈ genericParameterLocus m L) (i : Fin m) : θ.1 ≠ θ.2.1 i := by
  replace hθ := genericParameterLocus_prod_ne_zero hθ
  have hp : (∏ i : Fin m, (θ.1 - θ.2.1 i)) ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hθ).1).1).2
  exact sub_ne_zero.mp (Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i))

private lemma generic_rho_injective {m L : ℕ} {θ : ParamSpace ℂ m}
    (hθ : θ ∈ genericParameterLocus m L) : Function.Injective θ.2.1 := by
  replace hθ := genericParameterLocus_prod_ne_zero hθ
  have hp : (∏ i : Fin m, ∏ i' : Fin m,
      if i < i' then θ.2.1 i - θ.2.1 i' else 1) ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hθ).1).2
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hfac := Finset.prod_ne_zero_iff.mp
      (Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i)) j (Finset.mem_univ j)
    simp [hlt, hij] at hfac
  · have hfac := Finset.prod_ne_zero_iff.mp
      (Finset.prod_ne_zero_iff.mp hp j (Finset.mem_univ j)) i (Finset.mem_univ i)
    simp [hlt, hij] at hfac

/-- Genericity makes the direct and latent finite slopes pairwise distinct. -/
lemma rtsF_nodup {m L : ℕ} (θ : ParamSpace ℂ m)
    (hθ : θ ∈ genericParameterLocus m L) (_hρ : ∀ i, θ.2.1 i ≠ 0) :
    (rtsF θ).Nodup := by
  rw [rtsF, Multiset.nodup_cons]
  refine ⟨?_, ?_⟩
  · intro hmem
    rw [Multiset.mem_map] at hmem
    obtain ⟨i, -, hi⟩ := hmem
    exact generic_gamma_ne_rho hθ i hi.symm
  · exact Fintype.nodup_map_univ_iff_injective.mpr (generic_rho_injective hθ)

/-- Under genericity and nonzero latent slopes, zero is absent from the forward slope multiset. -/
lemma zero_notMem_rtsF {m L : ℕ} (θ : ParamSpace ℂ m)
    (hθ : θ ∈ genericParameterLocus m L) (hρ : ∀ i, θ.2.1 i ≠ 0) :
    (0 : ℂ) ∉ rtsF θ := by
  rw [rtsF, Multiset.mem_cons]
  rintro (hzero | hzero)
  · exact generic_gamma_ne_zero hθ hzero.symm
  · rw [Multiset.mem_map] at hzero
    obtain ⟨i, -, hi⟩ := hzero
    exact hρ i hi

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
