import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.BlockScore
import Causalean.Experimentation.DesignBased.ProductBlock
import Causalean.Experimentation.DesignBased.ProductVariance

/-!
# Bernoulli Fourier moments

These are the two product-design identities used by both the block
representer and the global SNIPE variance argument.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased

/-- A centered Bernoulli monomial. -/
noncomputable def centeredMonomial {d : ℕ} (p : ℝ) (S : Finset (Fin d)) :
    (Fin d → Bool) → ℝ :=
  fun z => ∏ j ∈ S, (blockInd z j - p)

/-- Expectation of a coordinatewise product under the common-probability
Bernoulli block design. -/
lemma E_coordinate_prod
    (d : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (g : Fin d → Bool → ℝ) :
    (blockDesign d p hp0 hp1).E (fun z => ∏ i, g i (z i)) =
      ∏ i, (p * g i true + (1 - p) * g i false) := by
  unfold blockDesign bernoulliDesign
  rw [FiniteDesign.E_prod_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [coinDesign_E]

/-- Centered monomials are orthogonal under the product Bernoulli design. -/
lemma E_centeredMonomial_mul
    (d : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S T : Finset (Fin d)) :
    (blockDesign d p hp0 hp1).E
        (fun z => centeredMonomial p S z * centeredMonomial p T z) =
      if S = T then (p * (1 - p)) ^ S.card else 0 := by
  let x : Bool → ℝ := fun b => (if b then 1 else 0) - p
  have hpoint (z : Fin d → Bool) :
      centeredMonomial p S z * centeredMonomial p T z =
        ∏ i, (if i ∈ S then x (z i) else 1) *
          (if i ∈ T then x (z i) else 1) := by
    simp only [centeredMonomial, blockInd, x]
    rw [Finset.prod_mul_distrib]
    congr 1 <;> simp
  rw [show (fun z => centeredMonomial p S z * centeredMonomial p T z) =
      (fun z => ∏ i, ((if i ∈ S then x (z i) else 1) *
        (if i ∈ T then x (z i) else 1))) by
      funext z
      rw [hpoint z, Finset.prod_mul_distrib]]
  rw [E_coordinate_prod d p hp0 hp1
    (fun i b => (if i ∈ S then x b else 1) *
      (if i ∈ T then x b else 1))]
  by_cases hST : S = T
  · subst T
    rw [if_pos rfl]
    have hfactor (i : Fin d) :
        p * ((if i ∈ S then x true else 1) *
            (if i ∈ S then x true else 1)) +
          (1 - p) * ((if i ∈ S then x false else 1) *
            (if i ∈ S then x false else 1)) =
          if i ∈ S then p * (1 - p) else 1 := by
      by_cases hi : i ∈ S <;> simp [hi, x] <;> ring
    simp_rw [hfactor]
    rw [Finset.prod_ite_mem]
    simp
  · rw [if_neg hST]
    have hdiff : ∃ i, (i ∈ S ∧ i ∉ T) ∨ (i ∈ T ∧ i ∉ S) := by
      by_contra h
      apply hST
      ext i
      constructor
      · intro hiS
        by_contra hiT
        exact h ⟨i, Or.inl ⟨hiS, hiT⟩⟩
      · intro hiT
        by_contra hiS
        exact h ⟨i, Or.inr ⟨hiT, hiS⟩⟩
    obtain ⟨i, hi⟩ := hdiff
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rcases hi with hi | hi
    · simp [hi.1, hi.2, x] <;> ring
    · simp [hi.1, hi.2, x] <;> ring

/-- A centered monomial pairs with a raw monomial exactly when its support is
contained in the raw support. -/
lemma E_centeredMonomial_mul_raw
    (d : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S T : Finset (Fin d)) (hS : S.Nonempty) :
    (blockDesign d p hp0 hp1).E
        (fun z => centeredMonomial p S z * rawMonomial T z) =
      if S ⊆ T then
        (p * (1 - p)) ^ S.card * p ^ (T.card - S.card)
      else 0 := by
  let x : Bool → ℝ := fun b => (if b then 1 else 0) - p
  let y : Bool → ℝ := fun b => if b then 1 else 0
  rw [show (fun z => centeredMonomial p S z * rawMonomial T z) =
      (fun z => ∏ i, ((if i ∈ S then x (z i) else 1) *
        (if i ∈ T then y (z i) else 1))) by
      funext z
      simp only [centeredMonomial, rawMonomial, blockInd, x, y]
      rw [Finset.prod_mul_distrib]
      congr 1 <;> simp]
  rw [E_coordinate_prod d p hp0 hp1
    (fun i b => (if i ∈ S then x b else 1) *
      (if i ∈ T then y b else 1))]
  have hfactor (i : Fin d) :
      p * ((if i ∈ S then x true else 1) *
          (if i ∈ T then y true else 1)) +
        (1 - p) * ((if i ∈ S then x false else 1) *
          (if i ∈ T then y false else 1)) =
        if i ∈ S then (if i ∈ T then p * (1 - p) else 0)
        else if i ∈ T then p else 1 := by
    by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T <;>
      simp [hiS, hiT, x, y] <;> ring
  simp_rw [hfactor]
  by_cases hsub : S ⊆ T
  · rw [if_pos hsub]
    have hsimp (i : Fin d) :
        (if i ∈ S then (if i ∈ T then p * (1 - p) else 0)
          else if i ∈ T then p else 1) =
        if i ∈ S then p * (1 - p) else if i ∈ T then p else 1 := by
      by_cases hi : i ∈ S
      · simp [hi, hsub hi]
      · simp [hi]
    simp_rw [hsimp]
    have hsplit (i : Fin d) :
        (if i ∈ S then p * (1 - p) else if i ∈ T then p else 1) =
          (if i ∈ S then p * (1 - p) else 1) *
            (if i ∈ T \ S then p else 1) := by
      by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T <;>
        simp [hiS, hiT]
    simp_rw [hsplit, Finset.prod_mul_distrib]
    have hcard : (T \ S).card = T.card - S.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
    rw [Finset.prod_ite_mem_eq, Finset.prod_ite_mem_eq]
    simp [hcard]
  · rw [if_neg hsub]
    obtain ⟨i, hiS, hiT⟩ :
        ∃ i, i ∈ S ∧ i ∉ T := by
      simpa only [Finset.not_subset] using hsub
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hiS, hiT]

end CausalSmith.Experimentation.SnipeDegreeFrontier
