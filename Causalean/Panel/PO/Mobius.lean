/-
Copyright (c) 2026 Causalean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Möbius / inclusion-exclusion expansion on the Boolean cube `{0,1}^{p+1}`

For `τ : (Fin (p+1) → Fin 2) → ℝ` with `τ 0 = 0`, define for each
`S ⊆ Finset.univ`,

```
δ τ S = ∑ A ∈ S.powerset, (-1)^(|S|-|A|) * τ (𝟙_A)
```

Then for any binary history `h`,

```
τ h = ∑ S ∈ univ.powerset.filter (·.Nonempty), δ τ S * ∏ k ∈ S, ((h k).val : ℝ).
```

This is the standard Mobius / inclusion-exclusion identity on the Boolean cube.

The proof is the elementary combinatorial argument:
1. Restrict the outer sum to `S ⊆ B := {k : h k = 1}` since the indicator
   product vanishes off `B`.
2. Swap sums to obtain `∑ A ⊆ B, c_A · τ (𝟙_A)` with
   `c_A = ∑ S, A ⊆ S ⊆ B, (-1)^(|S|-|A|)`.
3. The coefficient `c_A = (1-1)^(|B|-|A|)` vanishes for `A ⊊ B` and equals `1`
   for `A = B`. The `A = ∅` term vanishes by `τ 0 = 0`.
-/

import Mathlib.Analysis.RCLike.Basic

/-! # Boolean-Cube Mobius Expansion

This file proves the inclusion-exclusion expansion of a binary finite-memory
treatment-history response. The definition `indicator` builds Boolean histories
from subsets of lags, `delta` gives the interaction coefficient for a subset,
and `mobius_expansion` recovers any response normalized to zero at the all-zero
history as a sum of nonempty lag interactions. -/

open Finset BigOperators

namespace Causalean.Panel.PO.Mobius

variable {p : ℕ}

/-- Indicator history `𝟙_A : Fin (p + 1) → Fin 2`, equal to `1` on `A` and `0`
elsewhere. -/
def indicator (A : Finset (Fin (p + 1))) : Fin (p + 1) → Fin 2 :=
  fun k => if k ∈ A then 1 else 0

/-- The indicator history of the empty subset is the all-zero treatment
history. -/
@[simp] lemma indicator_empty :
    indicator (∅ : Finset (Fin (p + 1))) = fun _ => 0 := by
  funext k; simp [indicator]

/-- The interaction effect at a subset `S`. The main lemma uses this only for
non-empty `S`, but the definition is total. -/
noncomputable def delta (τ : (Fin (p + 1) → Fin 2) → ℝ)
    (S : Finset (Fin (p + 1))) : ℝ :=
  ∑ A ∈ S.powerset, (-1 : ℝ) ^ (S.card - A.card) * τ (indicator A)

/-- Indicator product: `∏ k ∈ S, ((h k).val : ℝ)` equals `1` if `S ⊆ B` and
`0` otherwise, where `B = {k : h k = 1}`. -/
lemma prod_indicator_eq (h : Fin (p + 1) → Fin 2)
    (B : Finset (Fin (p + 1))) (hB : ∀ k, k ∈ B ↔ h k = 1)
    (S : Finset (Fin (p + 1))) :
    Finset.prod S (fun k => ((h k).val : ℝ)) = if S ⊆ B then 1 else 0 := by
  classical
  by_cases hSB : S ⊆ B
  · rw [if_pos hSB]
    apply Finset.prod_eq_one
    intro k hk
    have hk1 : h k = 1 := (hB k).mp (hSB hk)
    rw [hk1]; simp
  · rw [if_neg hSB]
    rw [Finset.not_subset] at hSB
    obtain ⟨k, hkS, hkB⟩ := hSB
    apply Finset.prod_eq_zero hkS
    have h0 : h k ≠ 1 := fun hh => hkB ((hB k).mpr hh)
    have h2 : h k = 0 := by
      apply Fin.ext
      have hval_ne : (h k).val ≠ 1 := by
        intro hv
        apply h0
        apply Fin.ext
        simpa using hv
      omega
    rw [h2]; simp

/-- Coefficient sum: for `A ⊆ B`,
`∑ S, A ⊆ S ⊆ B, (-1)^(|S|-|A|) = if A = B then 1 else 0`.

This is the alternating-sum identity that drives Möbius inversion. -/
lemma coeff_sum (A B : Finset (Fin (p + 1))) (hAB : A ⊆ B) :
    (∑ S ∈ B.powerset.filter (A ⊆ ·), (-1 : ℝ) ^ (S.card - A.card))
      = if A = B then 1 else 0 := by
  classical
  set C := B \ A with hCdef
  have hAdisj : Disjoint A C := Finset.disjoint_sdiff
  -- Reindex S = A ∪ T with T ⊆ C.
  have hreindex :
      (∑ S ∈ B.powerset.filter (A ⊆ ·), (-1 : ℝ) ^ (S.card - A.card))
        = ∑ T ∈ C.powerset, (-1 : ℝ) ^ T.card := by
    refine Finset.sum_nbij' (fun S => S \ A) (fun T => A ∪ T) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS
      obtain ⟨hSB, _⟩ := hS
      exact (Finset.mem_powerset.mpr <| by
        intro x hx
        simp only [hCdef, Finset.mem_sdiff] at hx ⊢
        exact ⟨hSB hx.1, hx.2⟩)
    · intro T hT
      simp only [Finset.mem_powerset] at hT
      simp only [Finset.mem_filter, Finset.mem_powerset]
      have hTC : T ⊆ C := hT
      have hTB : T ⊆ B := hTC.trans Finset.sdiff_subset
      exact ⟨Finset.union_subset hAB hTB, Finset.subset_union_left⟩
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS
      obtain ⟨_, hAS⟩ := hS
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (hxA | ⟨hxS, _⟩)
        · exact hAS hxA
        · exact hxS
      · intro hxS
        by_cases hxA : x ∈ A
        · exact Or.inl hxA
        · exact Or.inr ⟨hxS, hxA⟩
    · intro T hT
      simp only [Finset.mem_powerset] at hT
      have hTC : T ⊆ C := hT
      have hTA : Disjoint A T := Finset.disjoint_of_subset_right hTC hAdisj
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hxA | hxT, hxnA⟩
        · exact (hxnA hxA).elim
        · exact hxT
      · intro hxT
        refine ⟨Or.inr hxT, ?_⟩
        intro hxA
        exact (Finset.disjoint_left.mp hTA hxA) hxT
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS
      obtain ⟨_, hAS⟩ := hS
      rw [Finset.card_sdiff_of_subset hAS]
  rw [hreindex]
  by_cases hAB' : A = B
  · subst hAB'
    have hC0 : C = ∅ := by simp [hCdef]
    simp [hC0]
  · have hCne : C ≠ ∅ := by
      intro hC0
      apply hAB'
      refine le_antisymm hAB ?_
      intro x hxB
      by_contra hxA
      have hxC : x ∈ C := by simp [hCdef, hxB, hxA]
      rw [hC0] at hxC
      exact Finset.notMem_empty _ hxC
    have hCne' : C.Nonempty := Finset.nonempty_iff_ne_empty.mpr hCne
    have hint : (∑ T ∈ C.powerset, (-1 : ℤ) ^ T.card) = 0 :=
      Finset.sum_powerset_neg_one_pow_card_of_nonempty (x := C) hCne'
    have hreal : (∑ T ∈ C.powerset, (-1 : ℝ) ^ T.card) = 0 := by
      exact_mod_cast hint
    simpa [hAB'] using hreal

/-- Any binary finite-memory response normalized to zero at the all-zero history can be
recovered as the sum of its nonempty inclusion-exclusion interaction coefficients, with an
interaction contributing only when all of its lags are active in the history.

In Lean notation, for `τ : (Fin (p + 1) → Fin 2) → ℝ` with
`τ (fun _ => 0) = 0` and any binary history `h`,
```
τ h = ∑ S ∈ univ.powerset.filter (·.Nonempty),
        δ τ S * ∏ k ∈ S, ((h k).val : ℝ).
```
-/
theorem mobius_expansion
    (τ : (Fin (p + 1) → Fin 2) → ℝ)
    (hτ0 : τ (fun _ => 0) = 0)
    (h : Fin (p + 1) → Fin 2) :
    τ h =
      ∑ S ∈ (((Finset.univ : Finset (Fin (p + 1))).powerset.filter (·.Nonempty)) :
        Finset (Finset (Fin (p + 1)))),
        delta τ S * Finset.prod S (fun k => ((h k).val : ℝ)) := by
  classical
  let B : Finset (Fin (p + 1)) := Finset.univ.filter (fun k => h k = 1)
  have hBmem : ∀ k, k ∈ B ↔ h k = 1 := by
    intro k
    simp [B, Finset.mem_filter]
  have hh_indB : h = indicator B := by
    funext k
    by_cases hk : k ∈ B
    · have hk' := (hBmem k).1 hk
      simp [indicator, hk, hk']
    · have h0 : h k ≠ 1 := by
        intro hh
        exact hk ((hBmem k).2 hh)
      have h2 : h k = 0 := by
        apply Fin.ext
        have hval_ne : (h k).val ≠ 1 := by
          intro hv
          apply h0
          apply Fin.ext
          simpa using hv
        omega
      simp [indicator, hk, h2]
  let u : Finset (Finset (Fin (p + 1))) :=
    (Finset.univ : Finset (Fin (p + 1))).powerset.filter (·.Nonempty)
  let s : Finset (Finset (Fin (p + 1))) := B.powerset.filter (·.Nonempty)
  change τ h = ∑ S ∈ u, delta τ S * Finset.prod S (fun k => ((h k).val : ℝ))
  have hstep1 :
      (∑ S ∈ u, delta τ S * Finset.prod S (fun k => ((h k).val : ℝ)))
        = ∑ S ∈ s, delta τ S := by
    have hmul :
        ∀ S ∈ u,
          delta τ S * Finset.prod S (fun k => ((h k).val : ℝ)) =
            if S ⊆ B then delta τ S else 0 := by
      intro S hS
      rw [prod_indicator_eq h B hBmem S]
      by_cases hSB : S ⊆ B <;> simp [hSB]
    rw [Finset.sum_congr rfl hmul]
    have hfilter :
        u.filter (fun S => S ⊆ B) = s := by
      ext S
      simp [u, s, and_comm]
    rw [← Finset.sum_filter]
    rw [hfilter]
  have hstep2 :
      (∑ S ∈ s, delta τ S)
        = ∑ A ∈ B.powerset,
            (∑ S ∈ s, if A ⊆ S then (-1 : ℝ) ^ (S.card - A.card) else 0)
              * τ (indicator A) := by
    rw [show s = B.powerset.filter (·.Nonempty) by rfl]
    calc
      (∑ S ∈ B.powerset.filter (·.Nonempty), delta τ S)
          = ∑ S ∈ B.powerset.filter (·.Nonempty),
              ∑ A ∈ B.powerset,
                if A ⊆ S then (-1 : ℝ) ^ (S.card - A.card) * τ (indicator A) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro S hS
            rw [delta]
            have hSsub : S ⊆ B := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
            have hcard :
                (∑ A ∈ S.powerset, (-1 : ℝ) ^ (S.card - A.card) * τ (indicator A))
                  = ∑ A ∈ B.powerset,
                      if A ⊆ S then (-1 : ℝ) ^ (S.card - A.card) * τ (indicator A) else 0 := by
              rw [← Finset.sum_filter]
              have hPowEq : S.powerset = B.powerset.filter (fun A => A ⊆ S) := by
                ext A
                constructor
                · intro hAS
                  exact Finset.mem_filter.mpr
                    ⟨Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hAS).trans hSsub),
                      Finset.mem_powerset.mp hAS⟩
                · intro hAS
                  exact Finset.mem_powerset.mpr (Finset.mem_filter.mp hAS).2
              simp [hPowEq]
            simp [hcard]
      _ = ∑ S ∈ B.powerset.filter (·.Nonempty),
              ∑ A ∈ B.powerset,
                (if A ⊆ S then (-1 : ℝ) ^ (S.card - A.card) else 0) * τ (indicator A) := by
            simp [ite_mul]
      _ = ∑ A ∈ B.powerset,
              ∑ S ∈ B.powerset.filter (·.Nonempty),
                (if A ⊆ S then (-1 : ℝ) ^ (S.card - A.card) else 0) * τ (indicator A) := by
            rw [Finset.sum_comm]
      _ = ∑ A ∈ B.powerset,
              (∑ S ∈ B.powerset.filter (·.Nonempty),
                if A ⊆ S then (-1 : ℝ) ^ (S.card - A.card) else 0) * τ (indicator A) := by
            simp [Finset.sum_mul]
  have hstep3 :
      (∑ A ∈ B.powerset,
          (∑ S ∈ s, if A ⊆ S then (-1 : ℝ) ^ (S.card - A.card) else 0) * τ (indicator A))
        = τ (indicator B) := by
    have hterms :
        ∀ A ∈ B.powerset,
          (∑ S ∈ s, if A ⊆ S then (-1 : ℝ) ^ (S.card - A.card) else 0) *
              τ (indicator A)
            = if A = B then τ (indicator B) else 0 := by
      intro A hA
      by_cases hA0 : A = ∅
      · subst hA0
        by_cases hB0 : B = ∅
        · rw [hB0]
          simp [hτ0]
        · have hne : (∅ : Finset (Fin (p + 1))) ≠ B := by
            intro h
            exact hB0 h.symm
          simp [hτ0, hne]
      · have hAne : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hA0
        have hAS : A ⊆ B := Finset.mem_powerset.mp hA
        have hfilter :
            s.filter (fun S => A ⊆ S) = B.powerset.filter (A ⊆ ·) := by
          ext S
          constructor
          · intro hS
            rcases Finset.mem_filter.mp hS with ⟨hSs, hSA⟩
            exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hSs).1, hSA⟩
          · intro hS
            rcases Finset.mem_filter.mp hS with ⟨hSsub, hSA⟩
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_filter.mpr ⟨hSsub, hAne.mono hSA⟩, hSA⟩
        have hinner :
            (∑ S ∈ s, if A ⊆ S then (-1 : ℝ) ^ (S.card - A.card) else 0)
              = ∑ S ∈ B.powerset.filter (A ⊆ ·), (-1 : ℝ) ^ (S.card - A.card) := by
          rw [← Finset.sum_filter]
          have hEq : s.filter (fun S => A ⊆ S) = B.powerset.filter (A ⊆ ·) := hfilter
          simp [hEq]
        rw [hinner]
        have hcoeff := coeff_sum A B hAS
        by_cases hABeq : A = B
        · subst hABeq
          simp [hcoeff]
        · simp [hcoeff, hABeq]
    calc
      (∑ A ∈ B.powerset,
          (∑ S ∈ s, if A ⊆ S then (-1 : ℝ) ^ (S.card - A.card) else 0) * τ (indicator A))
          = ∑ A ∈ B.powerset, if A = B then τ (indicator B) else 0 := by
            exact Finset.sum_congr rfl hterms
      _ = τ (indicator B) := by
            rw [Finset.sum_eq_single B]
            · simp
            · intro A hA hAB
              simp [hAB]
            · intro hB
              simp at hB
  rw [hstep1, hstep2, hstep3]
  simp [hh_indB]

end Causalean.Panel.PO.Mobius
